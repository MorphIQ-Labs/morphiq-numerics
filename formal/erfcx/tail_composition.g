# erfcx arithmetic component; see docs/erfcx.md for assumptions and scope.
# Normalized YB reconstruction. Quotient error eq includes the generated C.
# dm/da are relative rounding errors; am/aa cover gradual underflow divided
# by q. This is conditional on normalization and the named component bounds.
P = T * (-(1/2) + T * ((3/4) - (15/8) * T));
u = P + eu;
z = u * (1 + dm) + am;
r = (l + z) * (1 + da) + aa;
Y = 1 + r;
S = 1 + P + rem;
Q = (1 + l) / (1 + eq);
F = Q * S;
{ T in [0, 1b-18] /\ eu in [-1b-69, 1b-69]
  /\ rem in [0, 7b-72] /\ eq in [-1b-69, 1b-69]
  /\ l in [-1b-51, 1b-51] /\ dm in [-1b-53, 1b-53] /\ da in [-1b-53, 1b-53]
  /\ am in [-1b-170, 1b-170] /\ aa in [-1b-170, 1b-170]
  -> (Y - F) / F in [-1b-67, 1b-67] /\ r in [-1b-17,1b-17] /\ S in [0.99,1.01] }
Y - F -> (Y - (1 + l) * S) + ((1 + l) - Q) * S { 1 + eq <> 0 };
Y - (1 + l) * S -> eu + u * dm + am + (l + z) * da + aa - rem - l * (P + rem);
(1 + l) - Q -> Q * eq { 1 + eq <> 0 };
