#!/usr/bin/env python3
"""Check the staged CDF products and exact timed inputs outside timing."""
import argparse
import ctypes as C
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import struct

import mpmath as mp

ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('run', type=Path)
args = ap.parse_args()
out = args.run.resolve()
manifest = json.loads((out / 'qualification-manifest.json').read_text())
D = C.POINTER(C.c_double)


def bits(x):
    return struct.pack('>d', x).hex()


def value(word):
    return struct.unpack('>d', bytes.fromhex(word))[0]


libraries = {}
for filename, expected in manifest['binary_pins'].items():
    assert hashlib.sha256(Path(filename).read_bytes()).hexdigest() == expected
    lib = C.CDLL(filename)
    for prefix in ('prod_', 'control_'):
        scalar = getattr(lib, prefix + 'norm_cdf')
        scalar.argtypes, scalar.restype = [C.c_double], C.c_double
        vector = getattr(lib, prefix + 'norm_cdf_slice')
        vector.argtypes, vector.restype = [D, D, C.c_size_t], None
    libraries[filename] = lib
reference = json.loads((Path(__file__).resolve().parents[2] / 'crates/reference/fixtures/fast.json').read_text())
fixtures = [row for row in reference['cases'] if row['primitive'] == 'cdf' and 'high' in row]
assert fixtures, 'No independent CDF fixtures found'
results, canonical = [], {}
timed_oracles = {}
assert mp.__version__ == '1.3.0', 'Use scripts/bench_fast/requirements.txt'


def timed_oracle(word):
    if word not in timed_oracles:
        x = value(word)
        with mp.workprec(200):
            lo = mp.erfc(-mp.mpf(x) / mp.sqrt(2)) / 2
        with mp.workprec(400):
            hi = mp.erfc(-mp.mpf(x) / mp.sqrt(2)) / 2
            uncertainty = abs(hi - lo) + abs(hi) * mp.mpf(2)**-180
        timed_oracles[word] = (hi, uncertainty)
    return timed_oracles[word]


for build in manifest['builds']:
    backend = build['name']
    baseline_cell = next(c for c in manifest['cells'] if c['backend'] == backend and c['reference'] == 'baseline')
    composition_cell = next((c for c in manifest['cells'] if c['backend'] == backend and c['reference'] == 'composition'), None)
    candidate = libraries[baseline_cell['product']]
    baseline = libraries[baseline_cell['reference_product']]
    composition = libraries[composition_cell['reference_product']] if composition_cell else None
    checked = set()
    max_relative = 0.0
    max_oracle_relative = 0.0
    max_composition_relative = 0.0
    for cell in (c for c in manifest['cells'] if c['backend'] == backend):
        path = cell['input']['file']
        if path in checked:
            continue
        checked.add(path)
        words = json.loads(Path(path).read_text())
        xs = [value(w) for w in words]
        x, y = (C.c_double * len(xs))(*xs), (C.c_double * len(xs))()
        baseline.prod_norm_cdf_slice(x, y, len(xs))
        assert all(bits(y[i]) == bits(baseline.prod_norm_cdf(v)) for i, v in enumerate(xs)), (backend, path, 'baseline slice')
        if composition is not None:
            composition.prod_norm_cdf_slice(x, y, len(xs))
            assert all(bits(y[i]) == bits(composition.prod_norm_cdf(v)) for i, v in enumerate(xs)), (backend, path, 'composition slice')
        for label, library in (('candidate', candidate), ('baseline', baseline)):
            library.control_norm_cdf_slice(x, y, len(xs))
            assert all(bits(y[i]) == bits(library.control_norm_cdf(v)) for i, v in enumerate(xs)), (backend, path, label, 'strong slice')
        candidate.prod_norm_cdf_slice(x, y, len(xs))
        for i, v in enumerate(xs):
            got = candidate.prod_norm_cdf(v)
            assert bits(got) == bits(y[i]), (backend, path, i, 'slice')
            assert canonical.setdefault(words[i], bits(got)) == bits(got), (backend, v, 'backend')
            old = baseline.prod_norm_cdf(v)
            if not -22.5 <= v < -8:
                assert bits(got) == bits(old), (backend, v, 'unchanged domain')
            if 2.**-33 <= abs(v) <= 8 or -22.5 <= v < -8:
                oracle, uncertainty = timed_oracle(words[i])
                with mp.workprec(400):
                    error = abs(mp.mpf(got) - oracle) + uncertainty
                    assert error <= mp.mpf(2)**-49, (backend, v, 'timed absolute')
                    if v < 0:
                        relative = error / (oracle - uncertainty)
                        assert relative <= mp.mpf(2)**-48, (backend, v, 'timed relative')
                        max_oracle_relative = max(max_oracle_relative, float(relative))
                        if -22.5 <= v < -8 and composition is not None:
                            comp_error = abs(mp.mpf(composition.prod_norm_cdf(v)) - oracle) + uncertainty
                            max_composition_relative = max(max_composition_relative, float(comp_error / (oracle - uncertainty)))
            strong = candidate.control_norm_cdf(v)
            assert bits(strong) == bits(baseline.control_norm_cdf(v)), (backend, v, 'strong')
            if -22.5 <= v < -8:
                # Diagnostic against strong, independent fixture checks follow.
                max_relative = max(max_relative, abs(got - strong) / strong)
    count = 0
    for row in fixtures:
        x = value(row['x'])
        if not (2.**-33 <= abs(x) <= 8 or -22.5 <= x < -8):
            continue
        high, low = Fraction(value(row['high'])), Fraction(value(row['low']))
        oracle = high + low
        uncertainty = abs(high) * Fraction(1, 2**104) + Fraction(1, 2**1074)
        error = abs(Fraction(candidate.prod_norm_cdf(x)) - oracle) + uncertainty
        assert error <= Fraction(1, 2**49), (backend, x, 'absolute bound')
        if x < 0:
            assert error <= Fraction(1, 2**48) * (oracle - uncertainty), (backend, x, 'relative bound')
        count += 1
    results.append(dict(backend=backend, banks=len(checked), independent_fixture_cases=count,
                        far_max_relative_vs_strong=max_relative, scalar_slice_identical=True,
                        timed_max_negative_relative_with_uncertainty=max_oracle_relative,
                        composition_far_max_relative_with_uncertainty=max_composition_relative if composition is not None else None,
                        composition_scalar_slice_identical=True if composition is not None else None,
                        strong_scalar_slice_identical=True,
                        timed_oracle='mpmath 1.3.0, 200/400 bits; uncertainty = difference + abs(high)*2^-180 (observation)',
                        unchanged_domain_identical=True, strong_identical=True))
(out / 'observations.json').write_text(json.dumps(results, indent=2) + '\n')
print(json.dumps(results, indent=2))
