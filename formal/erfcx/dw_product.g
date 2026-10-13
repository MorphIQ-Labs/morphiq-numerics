# erfcx arithmetic component; see docs/erfcx.md for assumptions and scope.
# Relative rounding model for erfcx's dw_mul, conditional on exact two_prod,
# exact final Fast2Sum and normal (or exact-zero) intermediate roundings.
# Low words may be up to four unit roundoffs of their leading words.
a = 1 + da;
b = 1 + db;
p = 1 + dp;
e = -dp;
c = (da * (1 + d1) + db * (1 + d2)) * (1 + d3);
t = (e + c) * (1 + d4);
Y = p + t;
P = a * b;
{ da in [-1b-51, 1b-51] /\ db in [-1b-51, 1b-51]
  /\ dp in [-1b-53, 1b-53] /\ d1 in [-1b-53, 1b-53]
  /\ d2 in [-1b-53, 1b-53] /\ d3 in [-1b-53, 1b-53]
  /\ d4 in [-1b-53, 1b-53]
  -> (Y - P) / P in [-1b-100, 1b-100] }
Y - P -> da * d1 + db * d2 + (da * (1 + d1) + db * (1 + d2)) * d3 + (e + c) * d4 - da * db;
