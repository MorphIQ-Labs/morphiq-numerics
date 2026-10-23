# Segment 23's fast result (docs/asin.md, section 4): F = (Y + V)(1 + ea) against
# A = asin(a + t), relative, with Y = asin(a) and V = c1 t + t^2 G(t) the tail.
# The errors of X = Yv + Vv against A, each certified elsewhere or derived in
# exact rational arithmetic by generators/asin_certificates.py:
#   dY: the table's double-word of asin(a), relative error 2^-107
#   dc: (c_hi + c_lo - c1) t, the double-word of c1 = 1/sqrt(1 - a^2)
#   dP: t^2 (G - G_true), Sollya's supnorm plus the Taylor remainder (asin_poly.out)
#   dV: the tail's evaluation (formal/asin/eval_23.g)
#   ea: AccurateDWPlusDW, 3u^2/(1 - 4u) (docs/double-word.md)

X = A + dY + dc + dP + dV;
F = X * (1 + ea);

{ A in [728b-11, 778b-11] /\ dY in [-761b-118, 761b-118] /\ dc in [-555b-123, 555b-123]
  /\ dP in [-939b-81, 939b-81] /\ dV in [-925b-76, 925b-76] /\ ea in [-776b-114, 776b-114]
  -> (F - A) / A in [-678b-74, 678b-74] }

(F - A) / A -> ((dY + dc + dP + dV) * (1 + ea)) / A + ea { A <> 0 };
