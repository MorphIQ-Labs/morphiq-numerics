# Segment 51's fast result (docs/atan2.md, section 4): F = (Y + V)(1 + ea) against
# A = atan(a + s), relative, with Y = atan(a) and V = c1 s + s^2 G(s) the tail.
# The errors of X = Yv + Vv against A, each certified elsewhere or derived in
# exact rational arithmetic by generators/atan2_certificates.py:
#   dY: the table's double-word of atan(a), relative error 2^-107
#   dc: (c_hi + c_lo - c1) s, the double-word of c1 = 1/(1 + a^2)
#   dP: s^2 (G - G_true), Sollya's supnorm plus the Taylor remainder (atan2_poly.out)
#   dV: the tail's evaluation (formal/atan2/eval_51.g)
#   ea: AccurateDWPlusDW, 3u^2/(1 - 4u) (docs/double-word.md)

X = A + dY + dc + dP + dV;
F = X * (1 + ea);

{ A in [677b-10, 701b-10] /\ dY in [-696b-117, 696b-117] /\ dc in [-633b-124, 633b-124]
  /\ dP in [-844b-86, 844b-86] /\ dV in [-1004b-76, 1004b-76] /\ ea in [-776b-114, 776b-114]
  -> (F - A) / A in [-768b-75, 768b-75] }

(F - A) / A -> ((dY + dc + dP + dV) * (1 + ea)) / A + ea { A <> 0 };
