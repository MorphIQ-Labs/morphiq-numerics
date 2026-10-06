# ln_1p's fast path on its general branch (docs/ln.md, section 7), |x| >= 2^-7:
# (h, l) = two_sum(1, x), so ln(1 + x) = ln h + delta, delta = ln(1 + l/h).
#   Yh = ln h (1 + eh): ln's fast path at h (formal/ln/fast_b.g, fast_c.g);
#   d = RN(l / h) = (l / h)(1 + eq); Y = add_f64(Yh, d), relative error e3.
# Over v = ln(1 + x), |v| >= ln(1 + 2^-7): kd = delta / v and kw = ln h / v =
# 1 - kd; rr = (l/h - delta) / v. Written by generators/ln_certificates.py.

kw = 1 - kd;
Y = (kw * (1 + eh) + (kd + rr) * (1 + eq)) * (1 + e3);

{ kd in [-520b-55, 520b-55] /\ rr in [-520b-109, 520b-109] /\ eh in [-1b-64, 1b-64]
  /\ eq in [-1b-53, 1b-53] /\ e3 in [-1b-105, 1b-105]
  -> Y - 1 in [-1b-63, 1b-63] }

Y - 1 -> (kw * eh + rr + (kd + rr) * eq) * (1 + e3) + e3;
