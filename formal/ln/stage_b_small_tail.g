# ln_1p's stage B, |x| < 2^-9 (docs/ln.md, section 7): the tail
# tail = RN(RN(x RN(x^2)) W), W = Q(x) by Horner's scheme rounded to binary64,
# against x^3 Q(x) evaluated exactly, relative to x^3; b3..b8 are
# generators/ln_poly.out's. Written by generators/ln1p_certificates.py.

@rnd = float<ieee_64, ne>;

b3 = 0x1.5555555555555p-2;
b4 = -0x1p-2;
b5 = 0x1.9999999a3e0b6p-3;
b6 = -0x1.555555558204cp-3;
b7 = 0x1.249076a775a54p-3;
b8 = -0x1.fffec39c0bf07p-4;

p = rnd(x * x);
xp = rnd(x * p);
w4 = rnd(rnd(x * b8) + b7);
w3 = rnd(rnd(x * w4) + b6);
w2 = rnd(rnd(x * w3) + b5);
w1 = rnd(rnd(x * w2) + b4);
w0 = rnd(rnd(x * w1) + b3);
tail = rnd(xp * w0);
W = x * (x * (x * (x * (x * b8 + b7) + b6) + b5) + b4) + b3;

{ |x| in [1b-54, 1b-9]
  -> (tail - x * x * x * W) / (x * x * x) in [-655b-62, 655b-62] /\ W in [681b-11, 684b-11] }

(tail - x * x * x * W) / (x * x * x) -> ((tail - xp * w0) / (xp * w0)) * (xp / (x * x * x)) * w0
  + ((xp - x * x * x) / (x * x * x)) * w0 + (w0 - W) { x <> 0, xp * w0 <> 0 };
xp / (x * x * x) -> 1 + (xp - x * x * x) / (x * x * x) { x <> 0 };
(xp - x * x * x) / (x * x * x) -> ((xp - x * p) / (x * p)) * (p / (x * x)) + (p - x * x) / (x * x) { x <> 0, x * p <> 0 };
p / (x * x) -> 1 + (p - x * x) / (x * x) { x <> 0 };
xp -> (x * p) * (1 + (xp - x * p) / (x * p)) { x * p <> 0 };
