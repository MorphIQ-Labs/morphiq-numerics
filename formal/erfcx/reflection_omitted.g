# erfcx arithmetic component; see docs/erfcx.md for assumptions and scope.
# k > 104: 2^(-(k+1)) <= 2^-106. This omits G entirely.
Y = E + de;
F = E - G * sc;
{ E in [0.999, 2.001] /\ G in [0, 1] /\ sc in [0, 1b-106]
  /\ de in [-0x1.a2p-71, 0x1.a2p-71]
  -> G * sc / E in [0, 1b-105] /\ (Y - F) / F in [-1b-69, 1b-69] }
Y - F -> de + G * sc;
