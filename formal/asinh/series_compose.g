# The series' fast result (docs/asinh.md, section 3): F = (z - c)(1 + ea) with
# c = -RN(RN(z u) p) = RN(RN(z u) |p|) (the cubic term, positive), against
# A = asinh z = z (1 - rc), relative. rc = (z - asinh z)/z <= z^2/6 <= 1.1e-5 on
# z <= 0.0078126; c differs from z - A by the relative eps, at most 2^-50: the
# tail's 2^-51 (formal/asinh/series_tail.g), Sollya's 2^-54 (1 + 2^-23) for the
# polynomial (asinh_poly.out) and 3.1 2^-53 for the rounding of z^2 inside
# z^3 Q(z^2); generators/asinh_certificates.py asserts their sum is at most
# 2^-50. ea: add_f64, 2u^2 (docs/double-word.md). Written by
# generators/asinh_certificates.py.

A = z * (1 - rc);
F = (z * (1 - rc * (1 + eps))) * (1 + ea);

{ z in [1b-26, 0.0078126] /\ rc in [0, 1.1e-5] /\ eps in [-1b-50, 1b-50] /\ ea in [-1b-104, 1b-104]
  -> (F - A) / A in [-746b-76, 746b-76] }

(F - A) / A -> ea - (rc * eps * (1 + ea)) / (1 - rc) { z <> 0, 1 - rc <> 0 };
