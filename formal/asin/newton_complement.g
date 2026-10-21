# The accurate path's Newton step for x > SPLIT (docs/asin.md, section 5):
#   d1 = d0 + (cos d0 - x)/sin d0, result pi/2 - d1
# in Q256 from d0 = D (1 + eta), D = acos x in [2^-27, pi/4), against Ax = pi/2 - D,
# relative. The start is the fast path's delta, accurate relative to D.
#   x = cos D = c0 - s0 d - R', d = D - d0, R' = rr d^2   (Taylor, rr in [0, 1/2])
#   s0 = sin d0 = d0 fs, fs in [0.9, 1] (sin t/t >= 0.9 for t <= pi/4)
#   C = c0 (1 + gamma); rho = (C - x) + ea mx; ri = (1 + e)/(s0 (1 + sigma))
#   q = (rho ri)(1 + m); d1 = (d0 + q) + eb d0; yf = (H (1 + eH) - d1) + ec H
# so d1 - D = D (u1 + (u2 + u3 + u4)(1 + kk) + u5) with kk = (1 + e)(1 + m)/(1 + sigma) - 1,
# u1 = -eta kk, u2 = rr eta^2/((1 + eta) fs), u3 = c0 gamma/(D^2 (1 + eta) fs),
# u4 = ea mx/(D^2 (1 + eta) fs), u5 = eb (1 + eta). H is pi/2 in Q256 (relative
# error 2^-257.3); ec is the final sum's error.
# Hypotheses certified elsewhere or exact: eta, the start's relative error, is at
# most eps1 = 2^-62 (the fast path's bound, formal/asin/compose_*.g and
# complement.g, asserted by generators/asin_certificates.py; the start is
# y_hi + y_lo added in Q256, which errs by at most 2^-254 more); sigma and gamma,
# sin's and cos's relative errors at an exact argument, 1b-198
# (formal/trig/accurate_sin.g, accurate_cos.g, whose reduction term is zero here);
# e, Q256::recip's c y = 1 + e (formal/trig/recip_3.g); m, a Q256 product's
# truncation, [-2^-255, 0]; ea and eb, a Q256 sum's error, 2^-254 of its larger
# operand (docs/sin_cos.md, section 5). The Taylor remainder is the mean value
# theorem's: rr is half the sine (or cosine) at the intermediate point, at most
# 1/2. Written by generators/asin_certificates.py.

d0 = Dt * (1 + eta);
s0 = d0 * fs;
d = Dt - d0;
x = c0 - s0 * d - rr * d * d;
rho = (c0 * (1 + gamma) - x) + ea * mx;
ri = (1 + e) / (s0 * (1 + sigma));
q = (rho * ri) * (1 + m);
d1 = (d0 + q) + eb * d0;
yf = (H * (1 + eH) - d1) + ec * H;
Ax = H - Dt;
kk = (1 + e) * (1 + m) / (1 + sigma) - 1;
u1 = -eta * kk;
u2 = rr * eta * eta / ((1 + eta) * fs);
u3 = c0 * gamma / (Dt * Dt * (1 + eta) * fs);
u4 = ea * mx / (Dt * Dt * (1 + eta) * fs);
u5 = eb * (1 + eta);

{ Dt in [1b-27, 0.7854] /\ eta in [-1b-62, 1b-62] /\ fs in [0.9, 1] /\ c0 in [0.7071, 1]
  /\ rr in [0, 0.5000001] /\ sigma in [-1b-198, 1b-198] /\ gamma in [-1b-198, 1b-198]
  /\ ea in [-1b-254, 1b-254] /\ mx in [0, 1.0001] /\ e in [-650b-262, 650b-262] /\ m in [-1b-255, 0]
  /\ eb in [-1b-254, 1b-254] /\ ec in [-1b-254, 1b-254] /\ eH in [-1b-257, 1b-257]
  /\ H in [1.570796326794896619, 1.570796326794896620]
  -> (yf - Ax) / Ax in [-1b-124, 1b-124] }

(yf - Ax) / Ax -> ((H * eH + ec * H) - Dt * (u1 + (u2 + u3 + u4) * (1 + kk) + u5)) / Ax { Ax <> 0, Dt <> 0, fs <> 0 };
