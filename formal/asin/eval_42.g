# Segment 42's evaluation (docs/asin.md, section 4): with th, tl binary64
# (the reduced argument t = th + tl, |tl| <= 2^-53 T), ph + pl = th c_hi exactly
# (two_prod), and the rounded tail
#   tail = s1 + n, s1 = pl + (th c_lo + tl c_hi), n = RN(th^2) g, g = Horner(th),
# against the exact value of (c_hi + c_lo) t + t^2 G(t) after ph, and the Horner
# value hh0 within [-2, 2] (the fast sum's exactness needs it). dg bounds
# G(th + tl) - G(th) by the mean value theorem with sup|G'| from the
# coefficients, in exact rational arithmetic. Written by
# generators/asin_certificates.py.

@rnd = float<ieee_64, ne>;

c_hi = 0x1.5347295041c22p+0; c_lo = -0x1.45133f9151092p-55;
g0 = 0x1.87125aa7283aap-1;
g1 = 0x1.44b4b4d99b491p+0;
g2 = 0x1.2329ae70747f4p+1;
g3 = 0x1.2b16e17d222d9p+2;
g4 = 0x1.46bfa82b41562p+3;
g5 = 0x1.7618ede0b3d30p+4;
g6 = 0x1.baaa93229f800p+5;
g7 = 0x1.0cb250824fa7ep+7;
g8 = 0x1.08094b59a117dp+8;

th = rnd(th_);
tl = rnd(tl_);
ph rnd= th * c_hi;
pl = th * c_hi - ph;
m1 rnd= th * c_lo;
m2 rnd= tl * c_hi;
m3 rnd= m1 + m2;
s1 rnd= pl + m3;
t2 rnd= th * th;
hh8 = g8;
q7 rnd= th * hh8;
hh7 rnd= g7 + q7;
HH7 = g7 + th * g8;
q6 rnd= th * hh7;
hh6 rnd= g6 + q6;
HH6 = g6 + th * HH7;
q5 rnd= th * hh6;
hh5 rnd= g5 + q5;
HH5 = g5 + th * HH6;
q4 rnd= th * hh5;
hh4 rnd= g4 + q4;
HH4 = g4 + th * HH5;
q3 rnd= th * hh4;
hh3 rnd= g3 + q3;
HH3 = g3 + th * HH4;
q2 rnd= th * hh3;
hh2 rnd= g2 + q2;
HH2 = g2 + th * HH3;
q1 rnd= th * hh2;
hh1 rnd= g1 + q1;
HH1 = g1 + th * HH2;
q0 rnd= th * hh1;
hh0 rnd= g0 + q0;
HH0 = g0 + th * HH1;
n rnd= t2 * hh0;
tail rnd= s1 + n;
tt = th + tl;
Vx = pl + c_lo * th + c_hi * tl + c_lo * tl + tt * tt * (HH0 + dg);

{ th_ in [-0.0078126, 0.0078126] /\ tl_ in [-8.7e-19, 8.7e-19] /\ dg in [-677b-69, 677b-69]
  -> tail - Vx in [-801b-74, 801b-74] /\ hh0 in [-2, 2] }

hh7 - HH7 -> (hh7 - (g7 + q7)) + (q7 - th * g8);
hh6 - HH6 -> (hh6 - (g6 + q6)) + (q6 - th * hh7) + th * (hh7 - HH7);
hh5 - HH5 -> (hh5 - (g5 + q5)) + (q5 - th * hh6) + th * (hh6 - HH6);
hh4 - HH4 -> (hh4 - (g4 + q4)) + (q4 - th * hh5) + th * (hh5 - HH5);
hh3 - HH3 -> (hh3 - (g3 + q3)) + (q3 - th * hh4) + th * (hh4 - HH4);
hh2 - HH2 -> (hh2 - (g2 + q2)) + (q2 - th * hh3) + th * (hh3 - HH3);
hh1 - HH1 -> (hh1 - (g1 + q1)) + (q1 - th * hh2) + th * (hh2 - HH2);
hh0 - HH0 -> (hh0 - (g0 + q0)) + (q0 - th * hh1) + th * (hh1 - HH1);
tail - Vx -> (tail - (s1 + n)) + (s1 - (pl + m3)) + (m3 - (m1 + m2)) + (m1 - th * c_lo)
  + (m2 - tl * c_hi) + (n - t2 * hh0) + hh0 * (t2 - th * th) + th * th * (hh0 - HH0)
  - c_lo * tl + (th * th - tt * tt) * HH0 - tt * tt * dg;
th * th - tt * tt -> -tl * (th + tt);
