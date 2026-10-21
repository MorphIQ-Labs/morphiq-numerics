# The series' cubic term (docs/asin.md, section 4): with zh a binary64,
# 2^-28 <= zh <= 0.0078126,
#   u = RN(zh^2), p = q0 + u (q1 + u (q2 + u q3)), tail = RN(RN(zh u) p)
# against zh^3 P(zh^2), P the same polynomial evaluated exactly. All four
# coefficients are positive, so every operation is a relative one. Written by
# generators/asin_certificates.py.

@rnd = float<ieee_64, ne>;

q0 = 0x1.5555555555555p-3;
q1 = 0x1.33333333488cbp-4;
q2 = 0x1.6db6c60bc57c9p-5;
q3 = 0x1.f7ea6b818f67p-6;

zh = rnd(zh_);
uh rnd= zh * zh;
p3 rnd= q2 + uh * q3;
p2 rnd= q1 + uh * p3;
ps rnd= q0 + uh * p2;
a3 rnd= zh * uh;
tail rnd= a3 * ps;
P3 = q2 + zh * zh * q3;
P2 = q1 + zh * zh * P3;
P = q0 + zh * zh * P2;
Tx = zh * zh * zh * P;

{ zh_ in [1b-28, 0.0078126] -> (tail - Tx) / Tx in [-1b-51, 1b-51] }

(tail - Tx) / Tx -> (1 + (a3 - zh * zh * zh) / (zh * zh * zh)) * (1 + (ps - P) / P) * (1 + (tail - a3 * ps) / (a3 * ps)) - 1
  { Tx <> 0, zh <> 0, P <> 0, a3 <> 0, ps <> 0 };
(a3 - zh * zh * zh) / (zh * zh * zh) -> (1 + (uh - zh * zh) / (zh * zh)) * (1 + (a3 - zh * uh) / (zh * uh)) - 1
  { zh <> 0, uh <> 0 };
