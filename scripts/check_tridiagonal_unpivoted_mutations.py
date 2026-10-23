#!/usr/bin/env python3
"""Named unpivoted admission/pivot-policy rejection controls; retain receipts.

Usage: check_tridiagonal_unpivoted_mutations.py OUTPUT_DIRECTORY
The isolated source snapshot is deleted on success or failure; build output uses
CARGO_TARGET_DIR when supplied. A compiler error or zero tests is never a kill.
"""
import json
import os
import re
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

root = Path(__file__).resolve().parents[1]
output = Path(sys.argv[1]).resolve()
output.mkdir(parents=True, exist_ok=True)
with tempfile.TemporaryDirectory(prefix='source-', dir=output) as directory:
    work = Path(directory)
    names = subprocess.check_output(['git', 'ls-files', '--cached', '--others', '--exclude-standard', '-z'], cwd=root).decode().split('\0')
    for name in names:
        if name and (root / name).is_file():
            dest = work / name
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(root / name, dest)
    path = work / 'crates/morphiq-numerics/src/linalg/tridiagonal.rs'
    original = path.read_text()
    start = original.index("impl<'a> UnpivotedTridiagonal<'a>")
    end = original.index('/// Factors tied to one immutable matrix', start)
    section = original[start:end]
    scan_mutations = {
        'finite-reduction-disjunction': 'finite | x.is_finite()',
        'finite-reduction-last-element': 'x.is_finite()',
    }
    mutations = [
        *[(name, 'finite & x.is_finite()', replacement) for name, replacement in scan_mutations.items()],
        ('finite-check', '!all_finite(lower) || !all_finite(diagonal) || !all_finite(upper)', 'false'),
        ('lower-shape', 'lower.len() != n.saturating_sub(1)', 'false'),
        ('upper-shape', 'upper.len() != n.saturating_sub(1)', 'false'),
        ('minimum-is-maximum', '.reduce(|a, b| if a < b { a } else { b })', '.reduce(|a, b| if a > b { a } else { b })'),
        ('signed-minimum', '.map(|p| p.abs())', '.map(|p| *p)'),
        ('minimum-missing', 'self.factors\n            .pivots\n            .iter()\n            .map(|p| p.abs())\n            .reduce(|a, b| if a < b { a } else { b })', 'None'),
    ]
    results = []
    for name, old, new in [('baseline', '', '')] + mutations:
        if name == 'baseline':
            path.write_text(original)
        elif name in scan_mutations:
            assert original.count(old) == 1, (name, original.count(old))
            path.write_text(original.replace(old, new))
        else:
            assert section.count(old) == 1, (name, section.count(old))
            path.write_text(original[:start] + section.replace(old, new) + original[end:])
        log = output / (name + '.log')
        with log.open('w') as stream:
            run = subprocess.run(['cargo', 'test', '--locked', '-p', 'morphiq-numerics', '--all-features', '--lib', 'linalg::tridiagonal::tests::'], cwd=work, env=os.environ, stdout=stream, stderr=subprocess.STDOUT, timeout=180)
        content = log.read_text()
        executed = re.search(r'test result: ok\. (\d+) passed;', content)
        passed = bool(executed and int(executed[1]) > 0 and run.returncode == 0
                      and 'finite_preflight_covers_vector_tails_and_preserves_outputs ... ok' in content)
        killed = 'test result: FAILED.' in content and 'linalg::tridiagonal::tests::' in content and run.returncode == 101
        expected = passed if name == 'baseline' else killed
        results.append(dict(name=name, exit_status=run.returncode, expected=expected))
        (output / 'receipt.json').write_text(json.dumps(results, indent=2) + '\n')
        print(name, 'PASS' if expected else 'FAIL', flush=True)
        assert expected, name
