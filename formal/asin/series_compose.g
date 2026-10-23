# The series' fast result (docs/asin.md, section 4): F = (z + c)(1 + ea) with
# z = zh + zl exactly, c = RN(RN(zh u) p), against A = asin z = z (1 + rc),
# relative. rc = (asin z - z)/z <= z^2/6 (1 + z^2) <= 1.1e-5 on z <= 0.0078126; c
# differs from A - z by the relative eps, at most 2^-50: the tail's 2^-51
# (formal/asin/series_tail.g), Sollya's 2^-54 (1 + 2^-23) for the polynomial
# (asin_poly.out) and 3.1 2^-53 for zl and the rounding of zh^2 inside z^3 P(z^2);
# generators/asin_certificates.py asserts their sum is at most 2^-50.
# ea: add_f64, 2u^2 (docs/double-word.md). Written by
# generators/asin_certificates.py.

A = z * (1 + rc);
F = (z * (1 + rc * (1 + eps))) * (1 + ea);

{ z in [1b-28, 0.0078126] /\ rc in [0, 1.1e-5] /\ eps in [-1b-50, 1b-50] /\ ea in [-1b-104, 1b-104]
  -> (F - A) / A in [-746b-76, 746b-76] }

(F - A) / A -> (rc * eps + (1 + rc * (1 + eps)) * ea) / (1 + rc) { z <> 0, 1 + rc <> 0 };
