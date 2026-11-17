"""Harness behavior checks; tiny counts and synthetic samples are not timings."""
import ctypes as C
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
D = C.POINTER(C.c_double)


@unittest.skipUnless(shutil.which('cc'), 'native C compiler required')
class NativeHarness(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.scratch = tempfile.TemporaryDirectory(prefix='cdf-harness-test-')
        cls.root = Path(cls.scratch.name)
        (cls.root/'bin').mkdir()
        (cls.root/'references').mkdir()
        for name in ['native-matrix', 'native-cache']:
            subprocess.run(['cc', '-O3', '-fPIC',
                            '-dynamiclib' if platform.system() == 'Darwin' else '-shared',
                            '-DNO_SLEEF', '-ffp-contract=off', str(HERE/'x86'/f'{name}.c'),
                            '-o', str(cls.root/'bin'/f'{name}.so')], check=True)
        for name in ['qualify-cell.py', 'run-qualification.py']:
            shutil.copy2(HERE/'x86'/name, cls.root/name)
        for name in ['protocol.py', 'inputs.py']:
            shutil.copy2(HERE/name, cls.root/name)
        cpu = min(os.sched_getaffinity(0)) if hasattr(os, 'sched_getaffinity') else 0
        (cls.root/'config.json').write_text(json.dumps(dict(cpu=cpu)))

    @classmethod
    def tearDownClass(cls):
        cls.scratch.cleanup()

    def test_metadata_preserves_scalar_packet_chain_and_cache_work(self):
        x = (C.c_double*4)(1, 2, 3, 4)
        y = (C.c_double*4)()
        for library, names in [
            ('native-matrix', ['measure1', 'measure2', 'measure_packet', 'measure_chain1', 'measure_chain2']),
            ('native-cache', ['measure1_cache', 'measure_packet_cache']),
        ]:
            lib = C.CDLL(str(self.root/'bin'/f'{library}.so'))
            lib.bench_last_stack_address.restype = C.c_size_t
            for name in names:
                with self.subTest(timer=name):
                    calls = []
                    skip_arguments = []

                    def scalar(value):
                        calls.append(value)
                        return value+1

                    def scalar2(value, skip):
                        skip_arguments.append(skip)
                        return scalar(value)

                    def packet(a, b, n):
                        calls.append(n)
                        for i in range(n):
                            b[i] = a[i]+1

                    if 'packet' in name:
                        callback = C.CFUNCTYPE(None, D, D, C.c_size_t)(packet)
                    elif name in ['measure2', 'measure_chain2']:
                        callback = C.CFUNCTYPE(C.c_double, C.c_double, C.c_int)(scalar2)
                    else:
                        callback = C.CFUNCTYPE(C.c_double, C.c_double)(scalar)
                    cache = name.endswith('_cache')
                    timer = getattr(lib, name)
                    timer.argtypes = [C.c_void_p, D, D, C.c_size_t, C.c_uint64]+([C.c_size_t] if cache else [])
                    timer.restype = C.c_uint64
                    timer(callback, x, y, 2, 3, *([2] if cache else []))
                    expected = (2 if cache else 100)+3
                    if 'packet' not in name:
                        expected *= 2
                    self.assertEqual(len(calls), expected)
                    if name in ['measure2', 'measure_chain2']:
                        self.assertEqual(skip_arguments, [1]*expected)
                    self.assertGreater(lib.bench_last_stack_address(), 0)
                    self.assertEqual(lib.bench_last_stack_address() % 8, 0)

    def test_diagnostic_matrix_cannot_report_qualification(self):
        # Complete synthetic records exercise reporting without collecting timings.
        with tempfile.TemporaryDirectory(dir=self.root) as directory:
            run = Path(directory)
            product = run/'product.so'
            product.write_bytes(b'synthetic product; never loaded')
            inputs = run/'inputs.json'
            inputs.write_text('["0000000000000000"]')
            cell = dict(id='diagnostic', product=str(product), backend='test',
                        input=dict(file=str(inputs), sha256=hashlib.sha256(bytes(8)).hexdigest()),
                        required_parity=False)
            manifest = dict(cells=[cell], builds=[dict(name='test', sha256=hashlib.sha256(product.read_bytes()).hexdigest())],
                            protocol=dict(upper95_t9=1.833), purpose='synthetic diagnostic')
            (run/'qualification-manifest.json').write_text(json.dumps(manifest))
            shutil.copy2(HERE/'x86/run-qualification.py', run/'run-qualification.py')
            out = run/'qualification/diagnostic'
            out.mkdir(parents=True)
            (out/'calibration.complete').touch()
            for process in range(10):
                path = out/str(process)
                path.mkdir()
                rows = [dict(name=name, kind='timed', round=r, elapsed_ns=600_000_000,
                             ns_per_call=1000) for r in range(2) for name in ['ours', 'reference']]
                (path/'samples.jsonl').write_text(''.join(json.dumps(row)+'\n' for row in rows))
                (out/f'{process}.complete').touch()
            subprocess.run([sys.executable, str(run/'run-qualification.py')], check=True, capture_output=True)
            result = json.loads((run/'qualification/result.json').read_text())
            self.assertTrue(result['complete'])
            self.assertEqual(result['required'], 0)
            self.assertIsNone(result['all_required_pass'])

    def test_identical_control_staging_preserves_bytes_and_rejects_changed_product(self):
        with tempfile.TemporaryDirectory(dir=self.root) as directory:
            root = Path(directory)
            source = root/'source'
            shutil.copytree(self.root/'bin', source/'bin')
            (source/'references').mkdir()
            for name in ['qualify-cell.py', 'run-qualification.py', 'protocol.py', 'inputs.py', 'config.json']:
                shutil.copy2(self.root/name, source/name)
            product = source/'bin/native-matrix.so'
            inputs = source/'inputs.json'
            inputs.write_text('["0000000000000000"]')
            cell = dict(id='body', primitive='cdf', control=False, required_parity=True,
                        product=str(product), backend='test',
                        input=dict(file=str(inputs), sha256=hashlib.sha256(bytes(8)).hexdigest()))
            manifest = dict(cells=[cell], builds=[dict(name='test', sha256=hashlib.sha256(product.read_bytes()).hexdigest())])
            (source/'qualification-manifest.json').write_text(json.dumps(manifest))
            command = [sys.executable, str(HERE/'stage-cdf-aa.py'), '--run', str(source),
                       '--cell', 'body', '--out', str(root/'aa')]
            subprocess.run(command, check=True, capture_output=True)
            staged = json.loads((root/'aa/qualification-manifest.json').read_text())['cells'][0]
            self.assertFalse(staged['required_parity'])
            self.assertNotEqual(Path(staged['reference_product']), product)
            self.assertEqual(Path(staged['reference_product']).read_bytes(), product.read_bytes())
            product.write_bytes(b'changed product')
            command[-1] = str(root/'changed')
            rejected = subprocess.run(command, capture_output=True, text=True)
            self.assertNotEqual(rejected.returncode, 0)
            self.assertIn('Product changed', rejected.stderr)
            self.assertFalse((root/'changed').exists())


if __name__ == '__main__':
    unittest.main()
