#!/usr/bin/env python3
"""The constants of ln_1p's stages H and B (docs/ln.md, section 7).

Writes crates/morphiq-numerics/src/ln/stage_tables.rs and
formal/ln/Ln1pTables.v; with --check, fails if a committed file differs from
a fresh generation. Needs mpmath (generators/requirements.txt). Every value is
computed from its definition, the reciprocals and grid roundings in exact
rational arithmetic and the logarithms with mpmath at 600 bits, and rounded
once; each bound the derivation relies on is checked here, and proved again
in Coq by one reflective check per table (formal/ln/Ln1pTables.v,
formal/ln/Ln1pCheck.v).

- The reduction: 1 + x = h + l, h = 2^E y with y in [0x1.6ap-1, 0x1.6ap0).
  bits(y) - OFF, OFF = bits(0x1.6ap-1), has its top J = 9 fraction bits as
  the index i: interval i holds the 2^43 encodings OFF + i 2^43 ..
  OFF + (i+1) 2^43 - 1, from YA[i] to YB[i] (intervals 0..299 lie below 1,
  300..511 above, and none straddles 1).
- R[i]: J + 1 = 10 significant bits, chosen so that |y R[i] - 1| <= 2^-9 over
  the interval: R0 = 1/y at the interval's centre rounded to 10 bits, and of
  R0 + d 2^-10 (d = -2..2) rounded to 10 bits the one with the least
  max |y R - 1| at the interval's two end encodings (the first, on a tie).
  The three intervals around 1, i = 298, 299, 300 (y within 2^-9 of 1), take
  R[i] = 1, so arguments near 0 reduce with no table term.
- T[i] = (TH, TL): -ln R[i] = TH + TL + eT, TH = -ln R[i] rounded to the
  2^-43 grid, TL = RN(-ln R[i] - TH); TH = TL = 0 where R[i] = 1.
- L1, L0: ln 2 = L1 + L0 + eL, L1 rounded to the 2^-43 grid, L0 binary64. So
  E L1 + TH is exact: both on 2^-43's grid, below 2^10 in magnitude for
  |E| <= 1020.
- EL[k] = (E L1, RN(E L0)) for E = k - 64, k = 0..127: stage H's E ln 2
  (|E| <= 53).
- The polynomials h3..h6 (stage H) and b3..b8 (stage B): read from
  generators/ln_poly.out, which generators/ln_poly.sollya writes.
"""
from fractions import Fraction
import pathlib
import struct
import sys

import mpmath

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUTPUT = ROOT / 'crates/morphiq-numerics/src/ln/stage_tables.rs'
COQ_OUTPUT = ROOT / 'formal/ln/Ln1pTables.v'
POLY = ROOT / 'generators/ln_poly.out'
PREC = 600
J = 9
N = 1 << J
OFF = 0x3FE6A00000000000  # bits(0x1.6ap-1)
WIDTH = 1 << (52 - J)  # encodings per interval
NEAR_ONE = (298, 299, 300)  # the intervals with R[i] = 1
Z_MAX = Fraction(1, 2**J)  # |y R[i] - 1| <= 2^-9
EL_BIAS = 64  # EL[k] holds E = k - 64

# Bounds the derivation relies on; each is checked below and in Coq.
T_ERR = Fraction(1, 2**97)  # |-ln R[i] - TH - TL|
TL_MAX = Fraction(1, 2**44)  # |TL|
TH_MAX = Fraction(711, 2048)  # |TH|
S_MIN = Fraction(181, 2**18)  # |TH| - max |z| over the interval, where E = 0 and R[i] != 1
L_ERR = Fraction(1, 2**101)  # |ln 2 - L1 - L0|
L0_MAX = Fraction(1, 2**44)  # |L0|


def to_bits(x):
    return struct.unpack('<Q', struct.pack('<d', x))[0]


def value(bits):
    """A finite encoding's value, exactly."""
    sign, biased, frac = bits >> 63, (bits >> 52) & 0x7FF, bits & ((1 << 52) - 1)
    assert biased != 0x7FF
    m, e = (frac, -1074) if biased == 0 else (frac | 1 << 52, biased - 1075)
    v = Fraction(m) * Fraction(2) ** e
    return -v if sign else v


def to_float(fr):
    f = float(fr)
    assert Fraction(f) == fr, 'representable'
    return f


def rn_bits(v, bits):
    """A nonzero Fraction rounded to nearest-even with `bits` significant bits."""
    sign = -1 if v < 0 else 1
    a = abs(v)
    e = a.numerator.bit_length() - a.denominator.bit_length()
    if Fraction(2) ** e > a:
        e -= 1
    scale = Fraction(2) ** (bits - 1 - e)
    m = a * scale
    whole = m.numerator // m.denominator
    rest = m - whole
    if rest > Fraction(1, 2) or (rest == Fraction(1, 2) and whole % 2 == 1):
        whole += 1
    return sign * Fraction(whole) / scale


def mp(fr):
    return mpmath.mpf(fr.numerator) / fr.denominator


def frac(v):
    """An mpf as a Fraction, exactly."""
    v = mpmath.mpf(v)
    man, exp = abs(v).man_exp
    return (-1 if v < 0 else 1) * Fraction(int(man)) * Fraction(2) ** int(exp)


def grid(v, k):
    """An mpf rounded to the nearest multiple of 2^-k, as a Fraction."""
    return Fraction(int(mpmath.nint(v * mpmath.mpf(2) ** k)), 2**k)


def read_poly():
    values = dict(line.split() for line in POLY.read_text().split('\n') if line.strip())
    h = [float.fromhex(values[f'h{k}']) for k in range(3, 7)]
    b = [float.fromhex(values[f'b{k}']) for k in range(3, 9)]
    return h, b, values['h_relative_error_bound'], values['b_relative_error_bound']


def ends(i):
    """The values of interval i's first and last encodings."""
    return value(OFF + i * WIDTH), value(OFF + (i + 1) * WIDTH - 1)


def derive():
    mpmath.mp.prec = PREC
    r, t = [], []
    worst_z, worst_t, worst_tl, worst_th, least_s = 0, 0, 0, 0, None
    for i in range(N):
        ya, yb = ends(i)
        assert (ya < 1) == (yb < 1), 'no interval straddles 1'
        if i in NEAR_ONE:
            ri = Fraction(1)
        else:
            r0 = rn_bits(2 / (ya + yb), J + 1)
            ri, zi = r0, max(abs(ya * r0 - 1), abs(yb * r0 - 1))
            for d in range(-2, 3):
                rc = rn_bits(r0 + d * Fraction(1, 2 ** (J + 1)), J + 1)
                zc = max(abs(ya * rc - 1), abs(yb * rc - 1))
                if zc < zi:
                    ri, zi = rc, zc
        zi = max(abs(ya * ri - 1), abs(yb * ri - 1))
        assert zi <= Z_MAX
        assert (ri == 1) == (i in NEAR_ONE)
        worst_z = max(worst_z, zi)
        r.append(to_float(ri))
        if ri == 1:
            t.append((0.0, 0.0))
            continue
        v = -mpmath.log(mp(ri))
        th = grid(v, 43)
        tl = rn_bits(frac(v) - th, 53)
        worst_t = max(worst_t, abs(frac(v) - th - tl))
        worst_tl = max(worst_tl, abs(tl))
        worst_th = max(worst_th, abs(th))
        s = abs(th) - zi
        least_s = s if least_s is None else min(least_s, s)
        t.append((to_float(th), to_float(tl)))
    assert worst_t <= T_ERR and worst_tl <= TL_MAX and worst_th <= TH_MAX and least_s >= S_MIN

    ln2 = mpmath.log(2)
    l1 = grid(ln2, 43)
    l0 = rn_bits(frac(ln2) - l1, 53)
    l_err = abs(frac(ln2) - l1 - l0)
    assert 0 < l1 < 1 and l_err <= L_ERR and abs(l0) <= L0_MAX
    l1f, l0f = to_float(l1), to_float(l0)
    el = []
    for k in range(128):
        e = k - EL_BIAS
        eh = e * l1f
        assert Fraction(eh) == e * l1, 'E L1 exact'
        el.append((eh, e * l0f))

    h, b, h_bound, b_bound = read_poly()
    return dict(r=r, t=t, l1=l1f, l0=l0f, el=el, h=h, b=b, h_bound=h_bound, b_bound=b_bound,
                worst_z=worst_z, worst_t=worst_t, worst_tl=worst_tl, worst_th=worst_th,
                least_s=least_s, l_err=l_err)


def log2(v):
    return float(mpmath.log(mp(Fraction(v)), 2))


def rust(d):
    f = lambda x: f'f64::from_bits(0x{to_bits(x):016x})'  # noqa: E731
    # A table entry as rustfmt lays it out.
    pair = lambda h, l: ['    (', f'        {f(h)},', f'        {f(l)},', '    ),']  # noqa: E731
    lines = [
        '//! Constants of `ln_1p`\'s stages H and B, written by `generators/ln1p_constants.py`;',
        '//! do not edit. Each comment states the definition and the bound the generator',
        '//! checked; `docs/ln.md` (section 7) gives the derivation, and',
        '//! `formal/ln/Ln1pTables.v` proves each bound again.',
        '',
        '/// `bits(0x1.6ap-1)`: the reduced `y` lies in `[0x1.6ap-1, 0x1.6ap0)`, and the',
        '/// index is the top 9 fraction bits of `bits(y) - OFF`.',
        f'pub(super) const OFF: u64 = 0x{OFF:016x};',
        f'/// The reciprocals `R[i]`, as encodings: 10 significant bits, `|y R[i] - 1| <= 2^{log2(d["worst_z"]):.2f}`',
        '/// over interval `i`; `R[i] = 1` for `i = 298, 299, 300`.',
        f'pub(super) static R: [u64; {N}] = [',
        *[f'    0x{to_bits(v):016x},' for v in d['r']],
        '];',
        f'/// `-ln R[i] = TH + TL` within 2^{log2(d["worst_t"]):.1f}, `TH` on the `2^-43` grid,',
        f'/// `|TL| <= 2^{log2(d["worst_tl"]):.1f}`; zero where `R[i] = 1`.',
        f'pub(super) static T: [(f64, f64); {N}] = [',
        *[line for h, l in d['t'] for line in pair(h, l)],
        '];',
        f'/// `ln 2 = L1 + L0` within 2^{log2(d["l_err"]):.1f}, `L1` on the `2^-43` grid.',
        f'pub(super) const L1: f64 = {f(d["l1"])};',
        f'pub(super) const L0: f64 = {f(d["l0"])};',
        f'/// `(E L1, RN(E L0))` for `E = k - {EL_BIAS}` at `k`: `E L1` exact.',
        'pub(super) static EL: [(f64, f64); 128] = [',
        *[line for h, l in d['el'] for line in pair(h, l)],
        '];',
        '/// Stage H\'s polynomial (`generators/ln_poly.sollya`): `h3..h6`, with relative',
        f'/// error at most {d["h_bound"]} to `ln(1 + z) - z + z^2/2` on `|z| <= 2^-9`.',
        'pub(super) const H: [f64; 4] = [',
        *[f'    {f(c)},' for c in d['h']],
        '];',
        '/// Stage B\'s polynomial (`generators/ln_poly.sollya`): `b3..b8`, with relative',
        f'/// error at most {d["b_bound"]} to `ln(1 + z) - z + z^2/2` on `|z| <= 2^-9`.',
        'pub(super) const B: [f64; 6] = [',
        *[f'    {f(c)},' for c in d['b']],
        '];',
    ]
    return '\n'.join(lines) + '\n'


def coq_dy(v):
    """A dyadic Fraction as Ln1pCheck's (m, e), value m 2^e."""
    v = Fraction(v)
    k = v.denominator.bit_length() - 1
    assert v.denominator == 1 << k
    return f'({v.numerator}%Z, (-{k})%Z)'


def coq(d):
    lines = [
        '(** Constants of [ln_1p]\'s stages H and B, written by',
        '    generators/ln1p_constants.py; do not edit. Each is given by its binary64',
        '    encoding, as in crates/morphiq-numerics/src/ln/stage_tables.rs; the',
        '    bounds the proofs take about them are proved by one reflective check per',
        '    table (formal/ln/Ln1pCheck.v). *)',
        '',
        'From Coq Require Import ZArith List.',
        'Require Import Ln1pCheck.',
        'Import ListNotations.',
        '',
        'Open Scope Z_scope.',
        '',
        f'Definition st_r_bits : list Z := [{"; ".join(str(to_bits(v)) for v in d["r"])}].',
        '',
        f'Definition st_t_bits : list (Z * Z) := [{"; ".join(f"({to_bits(h)}, {to_bits(l)})" for h, l in d["t"])}].',
        '',
        f'Definition st_el_bits : list (Z * Z) := [{"; ".join(f"({to_bits(h)}, {to_bits(l)})" for h, l in d["el"])}].',
        '',
        f'Definition st_l1_bits : Z := {to_bits(d["l1"])}.',
        f'Definition st_l0_bits : Z := {to_bits(d["l0"])}.',
        f'Definition st_h_bits : list Z := [{"; ".join(str(to_bits(c)) for c in d["h"])}].',
        f'Definition st_b_bits : list Z := [{"; ".join(str(to_bits(c)) for c in d["b"])}].',
        '',
        '(** The bounds the generator checked, as [(m, e)] for [m·2^e]. *)',
        f'Definition st_bounds : bounds := {{| b_t_err := {coq_dy(T_ERR)}; b_tl_max := {coq_dy(TL_MAX)};',
        f'  b_th_max := {coq_dy(TH_MAX)}; b_s_min := {coq_dy(S_MIN)}; b_l_err := {coq_dy(L_ERR)};',
        f'  b_l0_max := {coq_dy(L0_MAX)} |}}.',
        '',
        '(** The reciprocals and [-ln R[i]]: one check over the 512 intervals. *)',
        'Theorem st_rt_check : rt_check st_bounds st_r_bits st_t_bits = true.',
        'Proof. vm_compute. reflexivity. Qed.',
        '',
        '(** [ln 2 = L1 + L0] and stage H\'s [E·ln 2] table. *)',
        'Theorem st_l_check : l_check st_bounds st_l1_bits st_l0_bits st_el_bits = true.',
        'Proof. vm_compute. reflexivity. Qed.',
    ]
    return '\n'.join(lines) + '\n'


def generate():
    d = derive()
    return {OUTPUT: rust(d), COQ_OUTPUT: coq(d)}


def main():
    check = '--check' in sys.argv[1:]
    for path, text in generate().items():
        if check:
            if path.read_text() != text:
                sys.exit(f'{path} differs from a fresh generation')
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)


if __name__ == '__main__':
    main()
