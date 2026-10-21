# The logarithmic form's result (docs/asinh.md, section 3): A = asinh x = ln V,
# V = x + S, S = sqrt(x^2 + 1). The double-word v = (x + s)(1 + ev) with s from
# formal/asinh/root.g, so v = V (1 + ew), |ew| <= 2^-99 + 2^-105 (S/V <= 1; ES
# in the generator); Av = ln v = A + dw, |dw| <= 1.0001 |ew| <= 2^-98. vh = RN(v), vl = v - vh, d = ln(v/vh) =
# ln(1 + vl/vh), |d| <= 2^-52, and c = RN(vl/vh) satisfies |c - d| <= 1.5 2^-106
# (the rounding of the quotient and the quadratic term of ln(1 + t)). ln vh = Av - d
# from ln's fast value, within 2^-64 relatively (formal/ln/fast_a.g, fast_b.g
# and fast_c.g; docs/ln.md section 4), so L = (Av - d)(1 + eL), and
# y = (L + c)(1 + ea) with ea, add_f64's 2u^2 (docs/double-word.md). A is at
# least asinh(2^-7) > 0.0077. Written by generators/asinh_certificates.py.

A = a_;
Av = A + dw;
y = (((Av - d) * (1 + eL)) + d + cd) * (1 + ea);

{ a_ in [0.0077, 21] /\ dw in [-1b-98, 1b-98] /\ d in [-1b-52, 1b-52] /\ cd in [-1b-105, 1b-105]
  /\ eL in [-1b-64, 1b-64] /\ ea in [-1b-104, 1b-104]
  -> (y - A) / A in [-1b-63, 1b-63] }

(y - A) / A -> (dw + (A + dw - d) * eL + cd + ((A + dw) + (A + dw - d) * eL + cd) * ea) / A { A <> 0 };
