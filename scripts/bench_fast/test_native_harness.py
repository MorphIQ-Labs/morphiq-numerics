"""Harness behavior checks; tiny counts and synthetic samples are not timings."""
import ctypes as C
import errno
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

HERE = Path(__file__).resolve().parent
D = C.POINTER(C.c_double)


class HostMetadata(unittest.TestCase):
    def setUp(self):
        self.scratch = tempfile.TemporaryDirectory(prefix='cdf-host-test-')
        self.addCleanup(self.scratch.cleanup)
        self.root = Path(self.scratch.name)
        spec = importlib.util.spec_from_file_location('qualify_cell', HERE/'x86/qualify-cell.py')
        self.cell = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self.cell)

    def cpu(self, number, state=None):
        cpu = self.root/f'cpu{number}'
        path = cpu/'cpufreq/scaling_cur_freq'
        path.parent.mkdir(parents=True)
        path.write_text('3000000\n')
        if state is not None:
            (cpu/'online').write_text(state+'\n')
        return path

    def test_offline_frequency_is_not_read_and_offline_cpu_is_recorded(self):
        boot, active, offline = self.cpu(0), self.cpu(2, '1'), self.cpu(14, '0')
        read = Path.read_text

        def unavailable(path, *args, **kwargs):
            if path == offline:
                raise OSError(errno.EBUSY, 'offline frequency unavailable')
            return read(path, *args, **kwargs)

        with mock.patch.object(Path, 'read_text', unavailable):
            frequencies, offline_cpus = self.cell.cpu_frequencies(self.root)
        self.assertEqual(frequencies, {str(boot): '3000000', str(active): '3000000'})
        self.assertEqual(offline_cpus, ['cpu14'])

    def test_online_frequency_read_failure_is_not_suppressed(self):
        frequency = self.cpu(2, '1')
        read = Path.read_text

        def unavailable(path, *args, **kwargs):
            if path == frequency:
                raise OSError(errno.EBUSY, 'online frequency unavailable')
            return read(path, *args, **kwargs)

        with mock.patch.object(Path, 'read_text', unavailable):
            with self.assertRaises(OSError) as failure:
                self.cell.cpu_frequencies(self.root)
        self.assertEqual(failure.exception.errno, errno.EBUSY)


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
        if not C.CDLL(str(cls.root/'bin/native-matrix.so')).bench_supported():
            cls.scratch.cleanup()
            raise unittest.SkipTest('native x86 performance timers require AVX')
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

    @unittest.skipUnless(platform.machine() in ['x86_64', 'AMD64'], 'x86 SIMD state')
    def test_all_timers_clear_inherited_upper_register_state(self):
        fixture = self.root/'state.so'
        subprocess.run(['cc', '-O3', '-fPIC',
                        '-dynamiclib' if platform.system() == 'Darwin' else '-shared',
                        '-mavx', '-mno-vzeroupper',
                        str(HERE/'test-native-state.c'), '-o', str(fixture)], check=True)
        state = C.CDLL(str(fixture))
        state.invoke_dirty.argtypes = [C.c_void_p, C.c_void_p, D, D,
                                      C.c_size_t, C.c_uint64, C.c_size_t]
        state.invoke_dirty.restype = None
        state.probe_calls.restype = C.c_size_t
        x = (C.c_double*4)(1, 2, 3, 4)
        y = (C.c_double*4)()
        for library, names in [
            ('native-matrix', ['measure1', 'measure2', 'measure_packet', 'measure_chain1', 'measure_chain2']),
            ('native-cache', ['measure1_cache', 'measure_packet_cache']),
        ]:
            lib = C.CDLL(str(self.root/'bin'/f'{library}.so'))
            for name in names:
                with self.subTest(timer=name):
                    callback = (state.probe_packet if 'packet' in name else
                                state.probe2 if name in ['measure2', 'measure_chain2'] else state.probe1)
                    slots = 2 if name.endswith('_cache') else 0
                    state.invoke_dirty(getattr(lib, name), callback, x, y, 2, 3, slots)
                    expected = (slots or 100)+3
                    if 'packet' not in name:
                        expected *= 2
                    self.assertEqual(state.probe_calls(), expected)
                    self.assertEqual(state.probe_dirty_seen(), 0)

    @unittest.skipUnless(platform.system() == 'Linux' and platform.machine() == 'x86_64'
                         and shutil.which('objdump'), 'native x86 GNU disassembler')
    def test_timer_float_instructions_use_vex_encoding(self):
        legacy = {'movsd', 'movapd', 'movupd', 'movaps', 'movups', 'addsd',
                  'subsd', 'mulsd', 'divsd', 'xorpd', 'xorps', 'pxor'}
        for library, names in [
            ('native-matrix', ['measure1', 'measure2', 'measure_packet', 'measure_chain1', 'measure_chain2']),
            ('native-cache', ['measure1_cache', 'measure_packet_cache']),
        ]:
            for name in names:
                with self.subTest(timer=name):
                    assembly = subprocess.check_output(
                        ['objdump', '-d', '--no-show-raw-insn', '--disassemble='+name,
                         str(self.root/'bin'/f'{library}.so')], text=True)
                    mnemonics = set(re.findall(r'^\s*[0-9a-f]+:\s+([a-z0-9]+)', assembly, re.M))
                    self.assertIn('vzeroupper', mnemonics)
                    self.assertFalse(mnemonics & legacy, mnemonics & legacy)

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

    def test_declared_cost_limit_preserves_duration_gate_and_strict_default(self):
        for limit, ratio, duration, passes in [
            (None, 1.005, 600_000_000, False),
            (1.01, 1.005, 600_000_000, True),
            (1.01, 1.02, 600_000_000, False),
            (1.01, .995, 249_000_000, False),
        ]:
            with self.subTest(limit=limit, ratio=ratio, duration=duration), \
                    tempfile.TemporaryDirectory(dir=self.root) as directory:
                run = Path(directory)
                product = run/'product.so'
                product.write_bytes(b'synthetic product; never loaded')
                inputs = run/'inputs.json'
                inputs.write_text('["0000000000000000"]')
                cell = dict(id='control', product=str(product), backend='test',
                            input=dict(file=str(inputs), sha256=hashlib.sha256(bytes(8)).hexdigest()),
                            required_parity=True)
                if limit is not None:
                    cell['max_time_ratio'] = limit
                manifest = dict(cells=[cell], builds=[dict(name='test', sha256=hashlib.sha256(product.read_bytes()).hexdigest())],
                                protocol=dict(upper95_t9=1.8331129326536335))
                (run/'qualification-manifest.json').write_text(json.dumps(manifest))
                shutil.copy2(HERE/'x86/run-qualification.py', run/'run-qualification.py')
                out = run/'qualification/control'
                out.mkdir(parents=True)
                (out/'calibration.complete').touch()
                for process in range(10):
                    path = out/str(process)
                    path.mkdir()
                    rows = [dict(name='ours', kind='warmup', round=-1,
                                 elapsed_ns=1, ns_per_call=1)]
                    rows += [dict(name=name, kind='timed', round=r, elapsed_ns=duration,
                                  ns_per_call=1000*(ratio if name == 'ours' else 1))
                             for r in range(2) for name in ['ours', 'reference']]
                    (path/'samples.jsonl').write_text(''.join(json.dumps(row)+'\n' for row in rows))
                    (out/f'{process}.complete').touch()
                result = subprocess.run([sys.executable, str(run/'run-qualification.py')], capture_output=True)
                self.assertEqual(result.returncode == 0, passes)
                summary = json.loads((out.parent/'summary.json').read_text())[0]
                self.assertEqual(summary['passes'], passes)
                self.assertEqual(summary['max_time_ratio'], limit or 1)
                self.assertAlmostEqual(summary['upper95'], ratio)

    @unittest.skipUnless(platform.machine() == 'x86_64', 'x86 stack placement')
    def test_stack_trampoline_preserves_callback_count_and_results(self):
        lib = C.CDLL(str(self.root/'bin/native-matrix.so'))
        lib.bench_set_inner_warmup.argtypes = [C.c_int]
        lib.bench_set_inner_warmup.restype = None
        lib.bench_last_stack_address.restype = C.c_size_t
        lib.bench_with_stack.argtypes = [C.c_void_p, C.c_void_p, D, D,
                                        C.c_size_t, C.c_uint64, C.c_size_t]
        lib.bench_with_stack.restype = C.c_uint64
        x = (C.c_double*2)(1, 2)
        y = (C.c_double*2)()
        calls = []

        def callback(value):
            calls.append(value)
            return value+1

        function = C.CFUNCTYPE(C.c_double, C.c_double)(callback)
        lib.bench_set_inner_warmup(0)
        try:
            lib.bench_with_stack(lib.measure1, function, x, y, 2, 0, 0)
            base = lib.bench_last_stack_address()
            self.assertEqual(calls, [])
            for offset in range(0, 4096, 16):
                lib.bench_with_stack(lib.measure1, function, x, y, 2, 3, (base-offset) % 4096)
                self.assertEqual(lib.bench_last_stack_address() % 4096, offset)
                self.assertEqual(list(y), [2, 3])
            self.assertEqual(calls, [1, 2]*(3*256))
        finally:
            lib.bench_set_inner_warmup(1)

    @unittest.skipUnless(platform.machine() == 'x86_64', 'x86 stack placement')
    def test_balanced_sampling_preserves_work_and_all_stack_positions(self):
        # A tiny native identity workload exercises the actual subprocess runner.
        with tempfile.TemporaryDirectory(dir=self.root) as directory:
            run = Path(directory)
            source = run/'product.c'
            source.write_text('double prod_norm_cdf(double x) { return x; }\n')
            product = run/'product.so'
            subprocess.run(['cc', '-O3', '-fPIC',
                            '-dynamiclib' if platform.system() == 'Darwin' else '-shared',
                            str(source), '-o', str(product)], check=True)
            counts = run/'counts.json'
            counts.write_text(json.dumps(dict(ours=512, reference=1024)))
            inputs = run/'inputs.json'
            inputs.write_text('["3ff0000000000000"]')
            out = run/'samples'
            command = [sys.executable, str(self.root/'qualify-cell.py'),
                       '--product', str(product), '--reference-product', str(product),
                       '--reference', 'baseline', '--primitive', 'cdf', '--kind', 'scalar',
                       '--length', '1', '--population', str(inputs), '--process', '0',
                       '--counts', str(counts), '--out', str(out), '--diagnostic',
                       '--balanced-stack']
            subprocess.run(command, check=True, capture_output=True)
            rows = [json.loads(line) for line in (out/'samples.jsonl').read_text().splitlines()]
            self.assertEqual([(row['name'], row['count'], row['round']) for row in rows if row['kind'] == 'timed'],
                             [('ours', 512, 0), ('reference', 1024, 0), ('ours', 512, 1), ('reference', 1024, 1)])
            chunks = [json.loads(line) for line in (out/'chunks.jsonl').read_text().splitlines()]
            self.assertEqual(len(chunks), 2*2*2*256)
            for role, count in [('ours', 512), ('reference', 1024)]:
                for kind, expected in [('warmup', count//2), ('timed', count)]:
                    for r in range(2):
                        group = [row for row in chunks if row['name'] == role and row['kind'] == kind and row['round'] == r]
                        self.assertEqual(sum(row['count'] for row in group), expected)
                        self.assertEqual([row['stack_address'] % 4096 for row in group], list(range(0, 4096, 16)))
                        aggregate = next(row for row in rows if row['name'] == role and row['kind'] == kind and row['round'] == r)
                        self.assertEqual(aggregate['elapsed_ns'], sum(row['elapsed_ns'] for row in group))
            self.assertEqual([row['name'] for row in chunks[:8]],
                             ['ours', 'ours', 'reference', 'reference', 'reference', 'reference', 'ours', 'ours'])
            # An unbalanced count must fail before collecting measured chunks.
            counts.write_text(json.dumps(dict(ours=513, reference=1024)))
            command[command.index('--out')+1] = str(run/'invalid')
            result = subprocess.run(command, capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('Balanced counts must be divisible', result.stderr)



if __name__ == '__main__':
    unittest.main()
