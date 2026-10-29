"""Lifecycle tests use synthetic subprocesses; they establish no timing claim."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

from scripts.bench_campaign import campaign as c
from scripts.bench_campaign import selection

TEST_ROOT = c.REPO / 'target/bench-campaign-tests'


def cells():
    return [{'id': str(i), 'reference': ref, 'required_parity': i < 4,
             'primitive': ['exp', 'exp', 'erfcx', 'cdf', 'exp'][i],
             'backend': 'auto', 'population': 'ordinary', 'length': 52,
             'kind': 'vector' if i in [1, 2] else 'scalar'}
            for i, ref in enumerate(['core_math_exp', 'sleef_exp_scalar_fma', 'libcerf_erfcx', 'scipy_ndtr', 'strong-control'])]


def rows():
    return [{'id': str(i), 'passes': True, 'valid_duration': True, 'ratio': .9, 'upper95': .99} for i in range(5)]


class CampaignTests(unittest.TestCase):
    def setUp(self):
        TEST_ROOT.mkdir(parents=True, exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(dir=TEST_ROOT)
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / 'qualification').mkdir()
        c.write(self.root / 'qualification-manifest.json', {'cells': cells()})
        c.write(self.root / 'qualification/summary.json', rows())

    def test_complete_canonical_and_baseline_reports_remain_separate(self):
        report = c.comparison_rows(self.root, 'x86-linux')
        self.assertTrue(report['complete'])
        self.assertEqual(report['required_failed'], [])
        self.assertEqual([r['comparison_kind'] for r in report['cells']], ['canonical'] * 4 + ['baseline-control'])
        self.assertEqual(report['cells'][-1]['candidate_contract'], 'strong')

    def test_missing_reference_measurement_cannot_pass(self):
        c.write(self.root / 'qualification/summary.json', rows()[:-2])
        report = c.comparison_rows(self.root, 'x86-linux')
        self.assertFalse(report['complete'])
        self.assertEqual(report['required_failed'], ['3'])
        self.assertEqual(report['missing'], ['3', '4'])

    def test_dropping_canonical_participant_from_matrix_is_rejected(self):
        c.write(self.root / 'qualification-manifest.json', {'cells': cells()[1:]})
        c.write(self.root / 'qualification/summary.json', rows()[1:])
        with self.assertRaisesRegex(ValueError, 'must include'):
            c.comparison_rows(self.root, 'x86-linux')

    def test_duplicate_or_unexpected_summary_is_rejected(self):
        for measured in [rows() + [rows()[0]], rows() + [{'id': 'unknown'}]]:
            with self.subTest(measured=measured):
                c.write(self.root / 'qualification/summary.json', measured)
                with self.assertRaisesRegex(ValueError, 'Duplicate or unexpected'):
                    c.comparison_rows(self.root, 'x86-linux')

    def test_duration_failure_cannot_be_hidden_by_good_ratio(self):
        measured = rows()
        measured[0]['valid_duration'] = False
        c.write(self.root / 'qualification/summary.json', measured)
        self.assertEqual(c.comparison_rows(self.root, 'x86-linux')['required_failed'], ['0'])

    def test_changed_binary_or_input_is_rejected(self):
        binary = self.root / 'reference.so'
        binary.write_bytes(b'original')
        hashes = {str(binary): c.sha(binary)}
        c.verify_files(hashes)
        binary.write_bytes(b'changed')
        with self.assertRaisesRegex(ValueError, 'Frozen file changed'):
            c.verify_files(hashes)

    def test_reference_lock_rejects_wrong_revision_library_or_environment(self):
        catalogue = c.read(Path(c.__file__).with_name('references.json'))
        records = {}
        for name, pin in c.PINS.items():
            files = {}
            for filename in c.LIBRARIES['x86-linux'][name]:
                path = self.root / filename
                path.write_bytes(name.encode())
                files[str(path)] = c.sha(path)
            records[name] = {**catalogue[name], 'revision': pin, 'files': files}
        log = self.root / 'build.log'
        log.write_text('synthetic reference build')
        lock = {'schema': 1, 'platform': 'x86-linux', 'references': records,
                'packages': {'synthetic': True}, 'scipy_contract': catalogue['scipy'],
                'build_log': {'path': str(log), 'sha256': c.sha(log)}}
        with patch.object(c, 'package_receipt', return_value={'synthetic': True}):
            c.validate_lock(lock, 'x86-linux', self.root)
            lock['references']['sleef']['revision'] = '0' * 40
            with self.assertRaisesRegex(ValueError, 'identity or contract'):
                c.validate_lock(lock, 'x86-linux', self.root)
            lock['references']['sleef']['revision'] = c.PINS['sleef']
            lock['packages'] = {'changed': True}
            with self.assertRaisesRegex(ValueError, 'packages differ'):
                c.validate_lock(lock, 'x86-linux', self.root)
            lock['packages'] = {'synthetic': True}
            (self.root / 'libcerf.so').write_bytes(b'changed')
            with self.assertRaisesRegex(ValueError, 'Frozen file changed'):
                c.validate_lock(lock, 'x86-linux', self.root)

    def test_arm_partial_group_preserves_missing_and_failed_cells(self):
        arm_cells = [{'id': cell['id'], 'primitive': cell['primitive'], 'pair': ['ours', cell['reference']], 'parity_required': True}
                     for cell in cells()[:4]]
        c.write(self.root / 'cells.json', arm_cells)
        c.write(self.root / 'qualification-summary.json', {'cells': [
            {**arm_cells[0], 'meets_cost': True, 'duration_pass': True},
            {**arm_cells[1], 'meets_cost': True, 'duration_pass': False}]})
        report = c.comparison_rows(self.root, 'arm-macos')
        self.assertFalse(report['complete'])
        self.assertEqual(report['missing'], ['2', '3'])
        self.assertEqual(report['required_failed'], ['1', '2', '3'])

    def test_failure_retains_output_and_exit_code(self):
        log = self.root / 'failure.log'
        code = c.run_stage([sys.executable, '-c', "print('failed observation', flush=True); raise SystemExit(7)"], self.root, log, time.monotonic() + 10)
        self.assertEqual(code, 7)
        self.assertIn('failed observation', log.read_text())
        with self.assertRaises(FileExistsError):
            c.run_stage([sys.executable, '-c', 'pass'], self.root, log, time.monotonic() + 10)

    def test_timeout_kills_grandchild_and_preserves_log(self):
        child_pid = self.root / 'child-pid'
        script = "import subprocess,sys,time,pathlib; p=subprocess.Popen([sys.executable,'-c','import time; time.sleep(60)']); pathlib.Path(sys.argv[1]).write_text(str(p.pid)); print('running',flush=True); time.sleep(60)"
        log = self.root / 'timeout.log'
        with self.assertRaises(subprocess.TimeoutExpired):
            c.run_stage([sys.executable, '-c', script, str(child_pid)], self.root, log, time.monotonic() + 1)
        self.assertIn('running', log.read_text())
        pid = int(child_pid.read_text())
        # Reparented killed children may briefly remain zombies until init reaps them.
        state = subprocess.run(['ps', '-o', 'stat=', '-p', str(pid)], text=True, capture_output=True).stdout.strip()
        self.assertTrue(not state or state.startswith('Z'), state)

    def test_elapsed_deadline_starts_no_process(self):
        log = self.root / 'never.log'
        with self.assertRaises(TimeoutError):
            c.run_stage([sys.executable, '-c', 'pass'], self.root, log, time.monotonic() - 1)
        self.assertFalse(log.exists())

    def fixture_campaign(self, fail_observe=False, tamper=False):
        harness = self.root / 'scripts/bench_fast'
        harness.mkdir(parents=True)
        native = self.root / 'target/campaign/native'
        observe = "raise SystemExit(3)" if fail_observe else "print('synthetic observations')"
        measure = f"""import json,pathlib
p=pathlib.Path(__file__).parent
(p/'qualification').mkdir()
selected={{c['id'] for c in json.loads((p/'qualification-manifest.json').read_text())['cells']}}
(p/'qualification/summary.json').write_text(json.dumps([r for r in json.loads({json.dumps(rows())!r}) if r['id'] in selected]))
"""
        if tamper:
            measure += "(p/'input.bin').write_bytes(b'changed during timing')\n"
        prepare = f"""import pathlib,sys,json
p=pathlib.Path(sys.argv[sys.argv.index('--out')+1]); p.mkdir(parents=True)
(p/'input.bin').write_bytes(b'exact inputs')
cells=json.loads({json.dumps(cells())!r})
for cell in cells: cell.update(product=str(p/'input.bin'),input={{'file':str(p/'input.bin')}})
(p/'qualification-manifest.json').write_text(json.dumps({{'cells':cells}}))
(p/'observe.py').write_text({observe!r})
(p/'run-qualification.py').write_text({measure!r})
"""
        (harness / 'prepare.py').write_text(prepare)
        (harness / 'freeze.py').write_text("import pathlib,sys,json,hashlib\np=pathlib.Path(sys.argv[1]); files={str(f):hashlib.sha256(f.read_bytes()).hexdigest() for f in p.iterdir() if f.is_file()}; (p/'source.json').write_text(json.dumps({'files':files}))\n")
        notes = self.root / 'notes'
        notes.write_text('Synthetic host; test only')
        lock = self.root / 'lock.json'
        c.write(lock, {'build_log': {'path': str(notes)}})
        args = argparse.Namespace(command='run', prepared=None, sleef_include=None, suite='full', primitive=[], backend=[], cell=[], platform='x86-linux', commit='a' * 40, control_commit='a' * 40,
                                  control_source=self.root, reference_bin=self.root, reference_lock=lock,
                                  host_notes=notes, cpu=min(os.sched_getaffinity(0)), timeout_hours=.01,
                                  out=native.parent)
        return args, harness

    @unittest.skipUnless(sys.platform == 'linux', 'Synthetic x86 controller fixture uses Linux affinity')
    def test_controller_success_failure_and_corruption_keep_receipts(self):
        for failure, tamper, expected in [(False, False, 0), (True, False, 1), (False, True, 1)]:
            with self.subTest(failure=failure, tamper=tamper):
                # Each attempt owns a distinct tree and cannot resume previous data.
                original = self.root
                self.root = original / f'attempt-{failure}-{tamper}'
                self.root.mkdir()
                args, harness = self.fixture_campaign(failure, tamper)
                with patch.object(c, 'REPO', self.root), patch.object(c, 'NATIVE', harness), \
                     patch.object(c, 'git_revision', return_value='a' * 40), \
                     patch.object(c, 'validate_lock'), patch.object(c, 'host_snapshot', return_value={'synthetic': True}), \
                     patch.object(c.platform, 'system', return_value='Linux'), \
                     patch.object(c.platform, 'machine', return_value='x86_64'), \
                     patch.object(c, 'check_x86_host'):
                    self.assertEqual(c.execute(args), expected)
                    with self.assertRaises(FileExistsError):
                        c.execute(args)
                receipt = c.read(args.out / 'campaign.json')
                self.assertEqual(bool(receipt.get('qualification_passed')), expected == 0)
                self.assertTrue((args.out / 'artifacts.json').exists())
                if failure:
                    self.assertEqual([s['stage'] for s in receipt['stages']], ['prepare', 'observe'])
                if tamper:
                    self.assertIn('Frozen file changed', receipt['verification_error'])
                self.root = original

    @unittest.skipUnless(sys.platform == 'linux', 'Synthetic controller uses Linux affinity')
    def test_bootstrap_reused_for_multiple_subsets_without_full_qualification(self):
        args, harness = self.fixture_campaign()
        args.command = 'bootstrap'
        prepared = args.out
        with patch.object(c, 'REPO', self.root), patch.object(c, 'NATIVE', harness), \
             patch.object(c, 'git_revision', return_value='a' * 40), \
             patch.object(c, 'validate_lock'), patch.object(c, 'host_snapshot', return_value={'synthetic': True}), \
             patch.object(c.platform, 'system', return_value='Linux'), \
             patch.object(c.platform, 'machine', return_value='x86_64'), \
             patch.object(c, 'check_x86_host'):
            self.assertEqual(c.execute(args), 0)
            bootstrap = c.read(prepared / 'campaign.json')
            self.assertEqual(bootstrap['state'], 'prepared')
            self.assertFalse(bootstrap['qualification_passed'])
            self.assertEqual([s['stage'] for s in bootstrap['stages']], ['prepare', 'freeze'])
            for suite in ['smoke', 'subset', 'full']:
                run = argparse.Namespace(**vars(args))
                run.command, run.prepared, run.suite = 'run', prepared, suite
                run.out = self.root / 'target' / suite
                run.primitive = ['exp'] if suite == 'subset' else []
                for key in bootstrap['configuration']:
                    setattr(run, key, None)
                self.assertEqual(c.execute(run), 0)
                receipt = c.read(run.out / 'campaign.json')
                self.assertTrue(receipt['selected_passed'])
                self.assertEqual(receipt['qualification_passed'], suite == 'full')
                self.assertEqual(receipt['stages'][0]['stage'], 'reuse-prepared')
                report = c.read(run.out / 'comparisons.json')
                self.assertEqual(report['suite'], suite)
                if suite == 'subset':
                    self.assertEqual(report['excluded'], ['2', '3'])
                    self.assertEqual(report['missing'], [])
                c.verify_files(c.read(prepared / 'native/source.json')['files'])
            (prepared / 'native/qualification').mkdir()
            with self.assertRaisesRegex(ValueError, 'prior observations or measurements'):
                c.verify_prepared(prepared / 'native')
            # A prior attempt is not a fresh bootstrap, even if its cells passed.
            run.prepared = run.out
            run.out = self.root / 'target/rejected'
            with self.assertRaisesRegex(ValueError, 'successful bootstrap'):
                c.execute(run)

    def test_subset_report_preserves_full_matrix_and_detects_changed_scope(self):
        args = argparse.Namespace(suite='subset', primitive=['exp'], backend=[], cell=[])
        c.apply_selection(self.root, 'x86-linux', args)
        c.write(self.root / 'qualification/summary.json', [r for r in rows() if r['id'] in ['0', '1', '4']])
        report = c.comparison_rows(self.root, 'x86-linux')
        self.assertEqual(report['excluded'], ['2', '3'])
        self.assertEqual(report['full_cell_count'], 5)
        self.assertTrue(report['complete'])
        self.assertEqual(c.read(self.root / 'matrix-full.json')['cells'], cells())
        plan = c.read(self.root / 'selection.json')
        plan['suite'] = 'full'
        c.write(self.root / 'selection.json', plan)
        with self.assertRaisesRegex(ValueError, 'Filters require'):
            c.comparison_rows(self.root, 'x86-linux')

    def test_sparse_arm_selection_keeps_ids_and_filters_groups(self):
        arm = [{'id': f'{14+i*5:03d}', 'primitive': cell['primitive'], 'length': 52,
                'bank': cell['primitive']+'-ordinary', 'mode': 'throughput',
                'pair': ['prod_'+cell['primitive']+('_slice' if i in [1, 2] else ''), cell['reference']],
                'parity_required': True} for i, cell in enumerate(cells()[:4])]
        c.write(self.root / 'cells.json', arm)
        c.write(self.root / 'groups.json', {'critical': [r['id'] for r in arm[:2]], 'remaining': [r['id'] for r in arm[2:]]})
        args = argparse.Namespace(suite='subset', primitive=['cdf'], backend=[], cell=[])
        plan = c.apply_selection(self.root, 'arm-macos', args)
        self.assertEqual(plan['selected_ids'], ['029'])
        self.assertEqual(c.read(self.root / 'groups.json'), {'remaining': ['029']})
        self.assertEqual(c.read(self.root / 'cells.json'), arm[-1:])

    def test_arm_cell_runner_uses_declared_id_not_list_index(self):
        # Execute the real runner against a tiny fake timer, with a non-positional ID.
        import shutil
        shutil.copy2(c.NATIVE / 'arm/qualify-cell.py', self.root / 'qualify-cell.py')
        (self.root / 'matrix.py').write_text("from pathlib import Path\nP=Path(__file__).parent\nCELLS=[{'id':'029','pair':['ours','ref']}]\nclass E: QOS_RESULT=0\ndef measure(cell,name,count): return 300000000\n")
        base = self.root / 'qualified/029'
        base.mkdir(parents=True)
        c.write(base / 'counts.json', {'ours': 1, 'ref': 1})
        subprocess.run([sys.executable, str(self.root / 'qualify-cell.py'), '029', '0'], check=True, capture_output=True)
        self.assertTrue((base / '0/samples.csv').exists())
        self.assertEqual(c.read(base / '0/metadata.json')['cell']['id'], '029')


class SelectionTests(unittest.TestCase):
    def test_smoke_covers_each_canonical_family_and_control(self):
        full = cells() + [{**cells()[1], 'id': 'long', 'length': 65536}]
        plan = selection.select(full, 'x86-linux', 'smoke')
        self.assertEqual(plan['selected_ids'], ['0', '1', '2', '3', '4'])
        self.assertEqual(plan['excluded_ids'], ['long'])
        self.assertEqual(plan['timed_work_target_seconds'], 120)

    def test_filter_union_within_field_intersection_between_fields(self):
        full = cells() + [{**cells()[1], 'id': 'avx2-exp', 'backend': 'avx2'}]
        plan = selection.select(full, 'x86-linux', 'subset', primitives=['exp', 'cdf'], backends=['avx2'])
        self.assertEqual(plan['selected_ids'], ['avx2-exp'])
        plan = selection.select(full, 'x86-linux', 'subset', cell_ids=['3', '0'])
        self.assertEqual(plan['selected_ids'], ['0', '3'])

    def test_rejects_empty_unknown_or_misleading_selections(self):
        for kwargs in [{'suite':'full','primitives':['exp']}, {'suite':'subset'},
                       {'suite':'subset','cell_ids':['missing']},
                       {'suite':'subset','primitives':['cdf'],'cell_ids':['0']},
                       {'suite':'subset','backends':['avx2']}]:
            with self.subTest(kwargs=kwargs), self.assertRaises(ValueError):
                selection.select(cells(), 'x86-linux', **kwargs)

    def test_full_is_exactly_original_order_and_cells(self):
        full = cells()
        plan = selection.select(full, 'x86-linux')
        self.assertEqual(selection.selected_cells(full, plan), full)
        self.assertEqual(plan['excluded_ids'], [])
        self.assertEqual(plan['full_matrix_sha256'], selection.fingerprint(full))



if __name__ == '__main__':
    unittest.main()
