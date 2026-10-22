# The series' cubic term (docs/atan2.md, section 4): with zh a binary64,
# 2^-100 <= zh <= 0.0078126,
#   u = RN(zh^2), p = q0 - u (q1 - u (q2 - u q3)), tail = RN(RN(zh u) p)
# against zh^3 Q(zh^2), Q the same polynomial evaluated exactly. The kernel
# evaluates P = -Q with the signs of the coefficients, which is the same
# operations negated (rounding to nearest is odd). Each subtraction's second
# term is at most 2^-13 of the first, so every operation is a relative one. For
# zh below 2^-100 the cubic term is below 2^-200 zh, negligible against every
# bound it enters. Written by generators/atan2_certificates.py.

@rnd = float<ieee_64, ne>;

q0 = 0x1.5555555555555p-2;
q1 = 0x1.99999999843bbp-3;
q2 = 0x1.24923e6cf67ebp-3;
q3 = 0x1.c40518de2ad7bp-4;

zh = rnd(zh_);
uh rnd= zh * zh;
p3 rnd= q2 - uh * q3;
p2 rnd= q1 - uh * p3;
ps rnd= q0 - uh * p2;
a3 rnd= zh * uh;
tail rnd= a3 * ps;
P3 = q2 - zh * zh * q3;
P2 = q1 - zh * zh * P3;
P = q0 - zh * zh * P2;
Tx = zh * zh * zh * P;

{ zh_ in [1b-100, 0.0078126] -> (tail - Tx) / Tx in [-1b-51, 1b-51] }

(tail - Tx) / Tx -> (1 + (a3 - zh * zh * zh) / (zh * zh * zh)) * (1 + (ps - P) / P) * (1 + (tail - a3 * ps) / (a3 * ps)) - 1
  { Tx <> 0, zh <> 0, P <> 0, a3 <> 0, ps <> 0 };
(a3 - zh * zh * zh) / (zh * zh * zh) -> (1 + (uh - zh * zh) / (zh * zh)) * (1 + (a3 - zh * uh) / (zh * uh)) - 1
  { zh <> 0, uh <> 0 };
