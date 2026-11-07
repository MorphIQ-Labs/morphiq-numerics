"""Behavioral checks for the feasibility harness; no native build required."""
import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import Mock, patch

SPEC = importlib.util.spec_from_file_location("normal_pair_screen", Path(__file__).with_name("screen.py"))
screen = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(screen)


class ScreenTests(unittest.TestCase):
    def test_only_supported_native_platforms_are_admitted(self):
        for system, machine, expected in [("Linux", "x86_64", "x86-linux"),
                                           ("Darwin", "arm64", "arm-macos")]:
            with patch.object(screen.host.platform, "system", return_value=system), \
                 patch.object(screen.host.platform, "machine", return_value=machine):
                self.assertEqual(screen.host.configuration()["name"], expected)
        for system, machine in [("Darwin", "x86_64"), ("Linux", "aarch64"), ("Windows", "ARM64")]:
            with patch.object(screen.host.platform, "system", return_value=system), \
                 patch.object(screen.host.platform, "machine", return_value=machine):
                with self.assertRaisesRegex(RuntimeError, "Unsupported native host"):
                    screen.host.configuration()

    def test_mac_rejects_a_claimed_cpu_affinity(self):
        with patch.object(screen.host, "configuration", return_value={"name": "arm-macos"}):
            screen.host.validate_cpu(None)
            with self.assertRaisesRegex(ValueError, "omit --cpu"):
                screen.host.validate_cpu(2)

    def test_linux_requires_an_allowed_cpu(self):
        with patch.object(screen.host, "configuration", return_value={"name": "x86-linux"}), \
             patch.object(screen.host.os, "sched_getaffinity", return_value={2, 3}, create=True):
            screen.host.validate_cpu(2)
            for cpu in [None, 0]:
                with self.assertRaisesRegex(ValueError, "allowed affinity"):
                    screen.host.validate_cpu(cpu)

    def test_failed_mac_qos_is_not_reported_as_configured(self):
        native = Mock()
        native.bench_set_qos.return_value = 1
        with patch.object(screen.host, "configuration", return_value={"name": "arm-macos"}):
            with self.assertRaisesRegex(RuntimeError, "Cannot establish"):
                screen.host.configure(None, native)

    def test_preparation_for_another_platform_is_refused_before_loading(self):
        with tempfile.TemporaryDirectory(prefix="normal-pair-screen-test-") as directory:
            out = Path(directory)
            (out / "manifest.json").write_text(json.dumps(dict(
                files={}, source_files={}, native_platform={"name": "different-host"})))
            with self.assertRaisesRegex(RuntimeError, "different native platform"):
                screen.load(out)

    def test_qualification_covers_the_declared_interfaces_and_short_slices(self):
        spec = importlib.util.spec_from_file_location("normal_pair_qualify", Path(__file__).with_name("qualify.py"))
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        cells = module.cells()
        self.assertEqual(len(cells), 32)
        self.assertEqual(len({cell['id'] for cell in cells}), 32)
        for reference in ['libm_direct', 'libm_folded']:
            selected = [cell for cell in cells if cell['reference'] == reference]
            self.assertEqual({c['kind'] for c in selected}, {'scalar', 'latency', 'slice', 'stream', 'antithetic'})
            self.assertEqual({c['n'] for c in selected if c['kind'] == 'slice' and c['population'] == 'ordinary'},
                             {1, 2, 7, 8, 9, 17, 4096})

    def test_word_stream_replays_known_splitmix_outputs(self):
        stream = screen.splitmix(0)
        self.assertEqual([next(stream) for _ in range(3)], [
            0xe220a8397b1dcdaf, 0x6e789e6aa1b965f4, 0x06c45d188009454f])

    def test_endpoint_banks_cover_all_octants_and_radial_endpoints(self):
        banks = screen.banks()
        self.assertEqual({len(bank) for bank in banks.values()}, {4096})
        radial = {w1 for w1, _ in banks["radial_edges"]}
        self.assertIn(0, radial)
        self.assertIn((1 << 64) - 1, radial)
        angular = {w2 for _, w2 in banks["octant_edges"]}
        for octant in range(1, 8):
            for delta in [-2048, 0, 2048]:
                self.assertIn((octant << 61) + delta, angular)
        self.assertEqual({w2 >> 61 for w2 in angular}, set(range(8)))
        for bank in banks.values():
            self.assertTrue(all(0 <= word < 1 << 64 for pair in bank for word in pair))

    def test_modified_frozen_input_is_refused_before_native_loading(self):
        with tempfile.TemporaryDirectory(prefix="normal-pair-screen-test-") as directory:
            out = Path(directory)
            frozen = out / "input"
            frozen.write_bytes(b"declared inputs")
            metadata = dict(files={str(frozen): hashlib.sha256(frozen.read_bytes()).hexdigest()},
                            source_files={})
            (out / "manifest.json").write_text(json.dumps(metadata))
            frozen.write_bytes(b"different inputs")
            with self.assertRaisesRegex(RuntimeError, "Frozen screen input changed"):
                screen.load(out)


if __name__ == "__main__":
    unittest.main()
