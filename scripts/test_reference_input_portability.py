"""Input witnesses for platform-independent fixture generation.

The expected encodings below agree with the interval oracle at 128/256 bits
and independently evaluated 600/1000-bit mpmath powers. The first catches the
observed macOS pow rounding; the second catches the recorded Linux rounding.
"""
import pathlib
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / 'generators'))
import double_word_exp_reference as generator  # noqa: E402

# Seed 266, after 6,000 uniform samples: log-space samples 350 and 512.
WITNESSES = (
    (350, '-0x1.f3dca05151ac2p+2', '3e509e037df40566'),
    (512, '-0x1.676529ec13884p+3', '3d99d508745e73a1'),
)


class ReferenceInputPortabilityTest(unittest.TestCase):
    def test_log_spaced_magnitudes_round_to_the_oracle_bits(self):
        for _, exponent, expected in WITNESSES:
            with self.subTest(exponent=exponent):
                actual = generator.log_spaced_magnitude(float.fromhex(exponent))
                self.assertEqual(f'{generator.bits(actual):016x}', expected)

    def test_seeded_fixture_uses_the_portable_magnitudes(self):
        rows = generator.cases()
        self.assertEqual(len(rows), 22030)
        for index, _, expected in WITNESSES:
            with self.subTest(sample=index):
                self.assertEqual(rows[6000 + index]['hi'], expected)


if __name__ == '__main__':
    unittest.main()
