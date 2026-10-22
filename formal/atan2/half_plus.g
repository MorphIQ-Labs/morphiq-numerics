# The form pi/2 + phi (docs/atan2.md, section 3): y = (C + F)(1 + ea) with C
# the double-word constant (relative error eC <= 2^-107; for pi, twice pi/2's, exact),
# F the fast value phi (1 + eF), eF within 1007b-73 (the largest of formal/atan2/compose_*.g and
# series_compose.g plus the ratio's 2^-104, section 3), against the angle A = C + phi.
# ea: AccurateDWPlusDW, 3u^2/(1 - 4u) (docs/double-word.md). Written by
# generators/atan2_certificates.py.

A = C + phi;
y = (C * (1 + eC) + phi * (1 + eF)) * (1 + ea);

{ C in [1.5707963267948966, 1.5707963267948967] /\ phi in [0, 0.7853981633974484] /\ A in [1.5707963267948966, 2.356194490192345]
  /\ eC in [-1b-107, 1b-107] /\ eF in [-1007b-73, 1007b-73] /\ ea in [-776b-114, 776b-114]
  -> (y - A) / A in [-822b-72, 822b-72] }

(y - A) / A -> ((C * eC + phi * eF) * (1 + ea)) / A + ea { A <> 0 };
