# The fast path's cosine tail (docs/sin_cos.md, section 4): with t_hi a
# binary64, 1b-60 <= |t_hi| <= 0.0078126,
#   u = RN(t_hi^2), pc = c0 + u (c1 + u c2), tail = RN(RN(u u) pc)
# against t_hi^4 Pc(t_hi^2). Written by generators/trig_certificates.py.

@rnd = float<ieee_64, ne>;

c0 = 0x1.5555555555555p-5;
c1 = -0x1.6c16c16b6b967p-10;
c2 = 0x1.a0115f5073e76p-16;

th = rnd(th_);
uh rnd= th * th;
p2 rnd= c1 + uh * c2;
pc rnd= c0 + uh * p2;
a4 rnd= uh * uh;
tail rnd= a4 * pc;
P = c0 + th * th * (c1 + th * th * c2);
T = th * th * th * th * P;

{ |th| in [1b-60, 0.0078126] -> (tail - T) / T in [-1b-50, 1b-50] }

(tail - T) / T -> (1 + (a4 - th * th * th * th) / (th * th * th * th)) * (1 + (pc - P) / P) * (1 + (tail - a4 * pc) / (a4 * pc)) - 1
  { T <> 0, th <> 0, P <> 0, a4 <> 0, pc <> 0 };
(a4 - th * th * th * th) / (th * th * th * th) -> (1 + (uh - th * th) / (th * th)) * (1 + (uh - th * th) / (th * th)) * (1 + (a4 - uh * uh) / (uh * uh)) - 1
  { th <> 0, uh <> 0 };
