# The series' fast result (docs/asin.md, section 4): F = (z + c)(1 + ea) with
# z = zh + zl exactly, c = RN(RN(zh u) p), against A = asin z = z (1 + rc),
# relative. rc = (asin z - z)/z <= z^2/5 <= 1.3e-6 on z <= 0.0078126; c differs from
# the series' cubic term by the relative eps, at most 2^-49: the tail's 2^-49
# (formal/asin/series_tail.g, widened to include Sollya's 2^-54 for the
# polynomial, in asin_poly.out, and zl's 3 2^-53 in zh^3 against z^3).
# ea: add_f64, 2u^2 (docs/double-word.md). Written by
# generators/asin_certificates.py.

A = z * (1 + rc);
F = (z * (1 + rc * (1 + eps))) * (1 + ea);

{ z in [1b-26, 0.0078126] /\ rc in [0, 13b-23] /\ eps in [-1b-49, 1b-49] /\ ea in [-1b-104, 1b-104]
  -> (F - A) / A in [-882b-75, 882b-75] }

(F - A) / A -> (rc * eps * (1 + ea)) / (1 + rc) + ea * (1 + rc * (1 + eps)) / (1 + rc) { z <> 0 };
