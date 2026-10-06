# The fast path's sine tail (docs/sin_cos.md, section 4): with t_hi a binary64,
# 1b-60 <= |t_hi| <= 0.0078126,
#   u = RN(t_hi^2), ps = s0 + u (s1 + u s2), tail = RN(RN(t_hi u) ps)
# against t_hi^3 Ps(t_hi^2). Written by generators/trig_certificates.py.

@rnd = float<ieee_64, ne>;

s0 = -0x1.5555555555555p-3;
s1 = 0x1.11111110bb1a8p-7;
s2 = -0x1.a0159d0d83966p-13;

th = rnd(th_);
uh rnd= th * th;
p2 rnd= s1 + uh * s2;
ps rnd= s0 + uh * p2;
a3 rnd= th * uh;
tail rnd= a3 * ps;
P = s0 + th * th * (s1 + th * th * s2);
T = th * th * th * P;

{ |th| in [1b-60, 0.0078126] -> (tail - T) / T in [-1b-50, 1b-50] }

(tail - T) / T -> (1 + (a3 - th * th * th) / (th * th * th)) * (1 + (ps - P) / P) * (1 + (tail - a3 * ps) / (a3 * ps)) - 1;
(a3 - th * th * th) / (th * th * th) -> (1 + (uh - th * th) / (th * th)) * (1 + (a3 - th * uh) / (th * uh)) - 1;
