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
from scripts.bench_campaign.cost import estimate

TEST_ROOT = c.REPO / 'target/bench-campaign-tests'


def cells():
    return [{'id': str(i), 'reference': ref, 'required_parity': i < 4}
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
        arm_cells = [{'id': cell['id'], 'pair': ['ours', cell['reference']], 'parity_required': True}
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
(p/'qualification/summary.json').write_text({json.dumps(rows())!r})
"""
        if tamper:
            measure += "(p/'input.bin').write_bytes(b'changed during timing')\n"
        prepare = f"""import pathlib,sys,json
p=pathlib.Path(sys.argv[sys.argv.index('--out')+1]); p.mkdir(parents=True)
(p/'input.bin').write_bytes(b'exact inputs')
(p/'qualification-manifest.json').write_text({json.dumps({'cells': cells()})!r})
(p/'observe.py').write_text({observe!r})
(p/'run-qualification.py').write_text({measure!r})
"""
        (harness / 'prepare.py').write_text(prepare)
        (harness / 'freeze.py').write_text("import pathlib,sys,json,hashlib\np=pathlib.Path(sys.argv[1]); files={str(f):hashlib.sha256(f.read_bytes()).hexdigest() for f in p.iterdir() if f.is_file()}; (p/'source.json').write_text(json.dumps({'files':files}))\n")
        notes = self.root / 'notes'
        notes.write_text('Synthetic host; test only')
        lock = self.root / 'lock.json'
        c.write(lock, {'build_log': {'path': str(notes)}})
        args = argparse.Namespace(platform='x86-linux', commit='a' * 40, control_commit='a' * 40,
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


class CostTests(unittest.TestCase):
    def test_full_campaign_includes_machine_disk_ip_and_storage(self):
        result = estimate('c3-standard-8', 8, download_gib=1)
        self.assertAlmostEqual(result['components_usd_per_campaign']['compute'], 8 * .403216)
        self.assertAlmostEqual(result['components_usd_per_campaign']['boot_disk'], 8 * 100 * .000136986)
        self.assertAlmostEqual(result['components_usd_per_campaign']['evidence_download'], .12)
        self.assertGreater(result['per_campaign_usd'], 8 * .403216)

    def test_monthly_and_failed_attempt_costs_are_additive(self):
        one = estimate('c4a-standard-4', 4, failed_hours=1)
        many = estimate('c4a-standard-4', 4, failed_hours=1, campaigns=20)
        self.assertAlmostEqual(many['total_usd'], one['total_usd'] * 20)
        self.assertAlmostEqual(one['components_usd_per_campaign']['compute'], 5 * .1796)

    def test_rejects_nonfinite_negative_and_zero_runtime(self):
        for hours in [float('nan'), float('inf'), -1, 0]:
            with self.assertRaises(ValueError):
                estimate('c3-standard-8', hours)
        with self.assertRaises(ValueError):
            estimate('c3-standard-8', 1, artifact_gib=-1)

    def test_compute_minimum_applies_to_each_attempt(self):
        result = estimate('c3-standard-8', .001, failed_hours=.001)
        self.assertAlmostEqual(result['components_usd_per_campaign']['compute'], .403216 / 30)


if __name__ == '__main__':
    unittest.main()
