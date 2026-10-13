# erfcx arithmetic component; see docs/erfcx.md for assumptions and scope.
# Normalized YB reconstruction. Quotient error eq includes the generated C.
# dm/da are relative rounding errors; am/aa cover gradual underflow divided
# by q. This is conditional on normalization and the named component bounds.
t = T + dt;
Pt = t * (-0.5 + t * (0.75 - 1.875 * t));
PT = T * (-0.5 + T * (0.75 - 1.875 * T));
u = Pt + ep;
z = u * (1 + dm) + am;
r = (l + z) * (1 + da) + aa;
Y = 1 + r;
S = 1 + PT + rem;
Q = (1 + l) / (1 + eq);
F = Q * S;
{ T in [0, 1b-18] /\ dt in [-0x1.81p-70, 0x1.81p-70]
  /\ ep in [-0x1.01p-71, 0x1.01p-71]
  /\ rem in [0, 7b-72] /\ eq in [-1b-69, 1b-69]
  /\ l in [-1b-51, 1b-51] /\ dm in [-1b-53, 1b-53] /\ da in [-1b-53, 1b-53]
  /\ am in [-1b-170, 1b-170] /\ aa in [-1b-170, 1b-170]
  -> (Y - F) / F in [-1b-67, 1b-67] }
Y - F -> (Y - (1 + l) * S) + ((1 + l) - Q) * S { 1 + eq <> 0 };
Y - (1 + l) * S -> (Pt - PT) + ep + u * dm + am + (l + z) * da + aa - rem - l * (PT + rem);
(1 + l) - Q -> Q * eq { 1 + eq <> 0 };
Pt - PT -> dt * (-0.5 + 0.75 * (t + T) - 1.875 * (t * t + t * T + T * T));
