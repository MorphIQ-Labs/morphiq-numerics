# The fast sin(a + t) (docs/sin_cos.md, section 4):
#   R = S.add(S.mul(CM).add(C.mul(SN)))
# relative to sin(a + t) = S + S (cos t - 1) + C sin t. Written by
# generators/trig_certificates.py. With ks, ka, kb those three terms over
# sin(a + t) (ks + ka + kb = 1; bounds enclosed by generators/trig_constants.py):
#   S, C: the table's double-words, relative error eS, eC (generated)
#   SN, CM: sin t, cos t - 1 (formal/trig/sin_t.g, cos_t.g)
#   m1, m2: mul, 5u^2; a1, a2: add, 3u^2/(1 - 4u)
#   er: r's double-word against Q256's r, as an effect on sin(a + t)

ks = 1 - ka - kb;
X = (1 + eS) * (1 + eCM) * (1 + m1);
Z = (1 + eC) * (1 + eSN) * (1 + m2);
R = (ks * (1 + eS) + (ka * X + kb * Z) * (1 + a1)) * (1 + a2) * (1 + er);

{ ka in [-518b-23, 518b-23] /\ kb in [-518b-9, 518b-9] /\ eS in [-953b-117, 953b-117] /\ eC in [-953b-117, 953b-117]
  /\ eSN in [-1b-65, 1b-65] /\ eCM in [-1b-65, 1b-65] /\ m1 in [-5b-106, 5b-106] /\ m2 in [-5b-106, 5b-106]
  /\ a1 in [-776b-114, 776b-114] /\ a2 in [-776b-114, 776b-114] /\ er in [-1b-104, 1b-104]
  -> R - 1 in [-1b-62, 1b-62] }

R - 1 -> (ks * eS + (ka * (X - 1) + kb * (Z - 1)) * (1 + a1) + (ka + kb) * a1
          + (ks * (1 + eS) + (ka * X + kb * Z) * (1 + a1)) * a2) * (1 + er) + er;
