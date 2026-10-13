# erfcx arithmetic component; see docs/erfcx.md for assumptions and scope.
@rnd = float<ieee_64, ne>;
t = rnd(t_);
v = rnd(0.75 - rnd(1.875 * t));
w = rnd(-0.5 + rnd(t * v));
u = rnd(t * w);
P = t * (-0.5 + t * (0.75 - 1.875 * t));
{ t in [0, 1b-17] -> u - P in [-0x1.01p-71, 0x1.01p-71] }
