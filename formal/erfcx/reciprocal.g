# erfcx arithmetic component; see docs/erfcx.md for assumptions and scope.
@rnd = float<ieee_64, ne>;
x = rnd(x_);
y = 1 / x;
yh = rnd(y);
p = rnd(x * yh);
pe = x * yh - p;
r = rnd((1 - p) - pe);
yl = rnd(r * yh);
Y = yh + yl;
{ x in [16, 512] -> (Y - y) / y in [-1b-98, 1b-98] /\ yl / yh in [-0x1.01p-53, 0x1.01p-53]
 /\ yh in [1b-9, 1b-4] /\ p in [0.5, 2] /\ pe in [-1b-46, 1b-46]
 /\ r in [-1, 1] /\ yl in [-1b-56, 1b-56] }
(Y - y) / y -> (yl - r * yh) / y + (r - ((1 - p) - pe)) * (yh / y) - ((yh - y) / y) * ((yh - y) / y) { x <> 0, y <> 0 };
yh / y -> 1 + (yh - y) / y { x <> 0, y <> 0 };
1 - p - pe -> -((yh - y) / y) { x <> 0, y <> 0 };

yl / yh -> (yl - r * yh) / yh + r { yh <> 0 };

p -> 1 - ((1 - p) - pe) - pe;
