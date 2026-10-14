# erfcx arithmetic component; see docs/erfcx.md for assumptions and scope.
# Combine reciprocal and square errors against the mathematical 1/x^2.
y = 1 + ey;
t = T * y * y * (1 + es);
{ T in [1b-18, 1b-8] /\ ey in [-1b-98, 1b-98] /\ es in [-1b-95, 1b-95]
  -> t - T in [-1b-102, 1b-102] }
t - T -> T * (2 * ey + ey * ey + y * y * es);
