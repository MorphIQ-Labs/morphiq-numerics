# Segment 38's fast result (docs/asin.md, section 4): F = (Y + V)(1 + ea) against
# A = asin(a + t), relative, with Y = asin(a) and V = c1 t + t^2 G(t) the tail.
# The errors of X = Yv + Vv against A, each certified elsewhere or derived in
# exact rational arithmetic by generators/asin_certificates.py:
#   dY: the table's double-word of asin(a), relative error 2^-107
#   dc: (c_hi + c_lo - c1) t, the double-word of c1 = 1/sqrt(1 - a^2)
#   dP: t^2 (G - G_true), Sollya's supnorm plus the Taylor remainder (asin_poly.out)
#   dV: the tail's evaluation (formal/asin/eval_38.g)
#   ea: AccurateDWPlusDW, 3u^2/(1 - 4u) (docs/double-word.md)

X = A + dY + dc + dP + dV;
F = X * (1 + ea);

{ A in [634b-10, 668b-10] /\ dY in [-658b-117, 658b-117] /\ dc in [-643b-123, 643b-123]
  /\ dP in [-629b-78, 629b-78] /\ dV in [-597b-74, 597b-74] /\ ea in [-776b-114, 776b-114]
  -> (F - A) / A in [-519b-73, 519b-73] }

(F - A) / A -> ((dY + dc + dP + dV) * (1 + ea)) / A + ea { A <> 0 };
