"""The certificate consumer must reject a weakened reduction premise."""
import pathlib
import sys
import tempfile
import unittest
from unittest.mock import patch

import mpmath

from generators import trig_certificates as certificates


class TrigCertificatePremiseTest(unittest.TestCase):
    def test_current_reduction_supports_the_floor(self):
        certificates.check_reduction_premise()

    def test_distance_is_converted_to_radians(self):
        # pi/2 > 1 leaves room for the reduction error at this distance.
        with patch.object(certificates.trig_reduction, 'closest_approach',
                          return_value=(mpmath.mpf(2) ** -62, 797, 6381956970095103)):
            certificates.check_reduction_premise()

    def test_adapting_the_window_does_not_hide_a_weaker_closest_approach(self):
        reduction = certificates.trig_reduction
        current = reduction.derive()
        # pi/2 < 2: this distance cannot support |r| >= 2^-62.
        with patch.object(reduction, 'closest_approach',
                          return_value=(mpmath.mpf(2) ** -63, 797, 6381956970095103)):
            self.assertGreater(reduction.derive()['F'], current['F'])
            for arguments in ([], ['--check']):
                with self.subTest(arguments=arguments), tempfile.TemporaryDirectory() as tmp:
                    directory = pathlib.Path(tmp)
                    before = {p.name: p.read_bytes() for p in certificates.DIR.glob('*.g')}
                    for name, data in before.items():
                        (directory / name).write_bytes(data)
                    with patch.object(certificates, 'DIR', directory), \
                         patch.object(sys, 'argv', ['trig_certificates.py', *arguments]):
                        with self.assertRaisesRegex(ValueError, r'closest approach.*2\^-62'):
                            certificates.main()
                    after = {p.name: p.read_bytes() for p in directory.iterdir()}
                    self.assertEqual(after, before)

    def test_nonfinite_distance_cannot_satisfy_the_premise(self):
        for distance in (mpmath.nan, mpmath.inf, -mpmath.inf):
            with self.subTest(distance=distance), \
                 patch.object(certificates.trig_reduction, 'derive',
                              return_value={'d_min': distance}):
                with self.assertRaisesRegex(ValueError, 'trig certificate premise failed'):
                    certificates.check_reduction_premise()


if __name__ == '__main__':
    unittest.main()
