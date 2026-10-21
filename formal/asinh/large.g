# The large form's result (docs/asinh.md, section 3): A = asinh x = ln x + ln 2
# + t4 + r, t4 = 1/(4x^2) <= 2^-58 and |r| <= 2^-114 (r = -3 t^2/32 + ..., t =
# 1/x^2 <= 2^-56). Lx = ln x (1 + eL), eL within 2^-64 (formal/ln/fast_*.g); LN2 is
# the double-word ln 2 within 2^-109 (generators/asinh_constants.py); the sum
# is a double-word addition (3u^2/(1 - 4u), docs/double-word.md), and c =
# RN(RN(1/4x)/x) differs from t4 by at most 2^-110 absolutely (the relative
# 2^-52 of 2^-58, and the underflow of c for x near 2^1024, below 2^-1074
# absolutely); the last addition is add_f64 (2u^2). Written by
# generators/asinh_certificates.py.

Ax = ax_;
A = Ax + l2 + t4 + r;
y = (((Ax * (1 + eL)) + l2 * (1 + e2)) * (1 + ea1) + t4 + ec) * (1 + ea2);

{ ax_ in [19, 710.5] /\ l2 in [0.6931471805599453, 0.6931471805599454] /\ t4 in [0, 1b-58]
  /\ r in [-1b-114, 1b-114] /\ eL in [-1b-64, 1b-64] /\ e2 in [-1b-109, 1b-109]
  /\ ea1 in [-776b-114, 776b-114] /\ ec in [-1b-110, 1b-110] /\ ea2 in [-1b-104, 1b-104]
  -> (y - A) / A in [-1b-63, 1b-63] }

(y - A) / A -> ((Ax * eL + l2 * e2) + (Ax * (1 + eL) + l2 * (1 + e2)) * ea1 + ec - r
  + ((Ax * (1 + eL) + l2 * (1 + e2)) * (1 + ea1) + t4 + ec) * ea2) / A { A <> 0 };
