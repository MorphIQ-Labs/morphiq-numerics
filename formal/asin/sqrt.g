# The complement's square root as a double-word (docs/asin.md, section 3): with w
# the real root of the exact u = (1 - x)/2, s = RN(w) (sqrt is correctly rounded),
# (ph, pl) = two_prod(s, s), s_lo = RN(RN(RN(u - ph) - pl)/(2 s)) and z = s + s_lo
# exactly (two_sum), z against w, relative. With e = s - w, u - s^2 = -e (s + w)
# and z - w = e^2/(2 s) plus the three roundings. Written by
# generators/asin_certificates.py.

@rnd = float<ieee_64, ne>;

w = w_;
u = w * w;
s = rnd(w);
s2 = 2 * s;
ph rnd= s * s;
pl = s * s - ph;
rr1 rnd= u - ph;
r2 rnd= rr1 - pl;
sl rnd= r2 / s2;
zv = s + sl;

{ w_ in [1b-27, 0.3827] -> (zv - w) / w in [-1b-103, 1b-103] }

(zv - w) / w -> ((s - w) * (s - w) / s2 + (rr1 - (u - ph)) / s2 + (r2 - (rr1 - pl)) / s2 + (sl - r2 / s2)) / w { w <> 0 };
