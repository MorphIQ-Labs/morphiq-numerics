# erfcx arithmetic component; see docs/erfcx.md for assumptions and scope.
@rnd = float<ieee_64, ne>;
yh = rnd(yh_);
yl = rnd(yl_);
p = rnd(yh * yh);
e = yh * yh - p;
c = rnd(2 * yh * yl);
l = rnd(e + c);
T = p + l;
S = (yh + yl) * (yh + yl);
{ yh in [1b-9, 1b-4] /\ yl in [-1b-56, 1b-56] /\ yl / yh in [-0x1.01p-53, 0x1.01p-53]
  -> (T - S) / S in [-1b-95, 1b-95] /\ l / p in [-1b-51, 1b-51] }
T - S -> (l - (e + c)) + (c - 2 * yh * yl) - yl * yl;
yl -> yh * (yl / yh) { yh <> 0 };
l / p -> (l - (e + c)) / p + (c - 2 * yh * yl) / p + 2 * (yl / yh) * (yh * yh / p) + e / p { yh <> 0, p <> 0 };
e / p -> -((p - yh * yh) / (yh * yh)) * (yh * yh / p) { yh <> 0, p <> 0 };
yh * yh / p -> 1 / (1 + (p - yh * yh) / (yh * yh)) { yh <> 0, p <> 0 };
