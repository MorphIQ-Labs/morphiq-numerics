# The fast cos(a + t) (docs/sin_cos.md, section 4):
#   R = C.add(C.mul(CM).sub(S.mul(SN)))
# relative to cos(a + t) = C + C (cos t - 1) - S sin t, with kc, kca, ksb those
# terms over cos(a + t) (kc + kca - ksb = 1). Written by
# generators/trig_certificates.py; the hypotheses are as for fast_sin.g.

kc = 1 - kca + ksb;
X = (1 + eC) * (1 + eCM) * (1 + m1);
Z = (1 + eS) * (1 + eSN) * (1 + m2);
R = (kc * (1 + eC) + (kca * X - ksb * Z) * (1 + a1)) * (1 + a2) * (1 + er);

{ kca in [-522b-24, 522b-24] /\ ksb in [-515b-16, 515b-16] /\ eS in [-953b-117, 953b-117] /\ eC in [-953b-117, 953b-117]
  /\ eSN in [-1b-65, 1b-65] /\ eCM in [-1b-65, 1b-65] /\ m1 in [-5b-106, 5b-106] /\ m2 in [-5b-106, 5b-106]
  /\ a1 in [-776b-114, 776b-114] /\ a2 in [-776b-114, 776b-114] /\ er in [-1b-104, 1b-104]
  -> R - 1 in [-1b-62, 1b-62] }

R - 1 -> (kc * eC + (kca * (X - 1) - ksb * (Z - 1)) * (1 + a1) + (kca - ksb) * a1
          + (kc * (1 + eC) + (kca * X - ksb * Z) * (1 + a1)) * a2) * (1 + er) + er;
