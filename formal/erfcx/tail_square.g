# erfcx arithmetic component; see docs/erfcx.md for assumptions and scope.
# Square of the binary64 reciprocal over x >= 512. The reciprocal is normal;
# the square may underflow, represented by an absolute half-subnormal error.
y = (1 + dy);
t0 = T * y * y;
t = t0 * (1 + dt) + at;
{ T in [0, 1b-18] /\ dy in [-1b-53, 1b-53] /\ dt in [-1b-53, 1b-53]
  /\ at in [-1b-1075, 1b-1075]
  -> t - T in [-0x1.81p-70, 0x1.81p-70] }
t - T -> T * (2 * dy + dy * dy) + t0 * dt + at;
