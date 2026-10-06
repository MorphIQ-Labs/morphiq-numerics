# expm1's accurate result for |x| >= 2^-5 (docs/expm1.md, section 5):
# V = e^x (1 + eV) from exp's accurate path, then V - 1 in Q128 with absolute
# error s <= 2^-126 max(V, 1). Relative to e^x - 1: kq eV + s/(e^x - 1), and
# max(V, 1)/|e^x - 1| <= max(|kq| (1 + eV), |kq - 1|) <= KQ + 1.
# Written by generators/expm1_certificates.py.

M = 1 + kq * eV + sr;

{ kq in [-526b-4, 526b-4] /\ eV in [-1097b-134, 1097b-134] /\ sr in [-542b-130, 542b-130]
  -> M - 1 in [-1b-118, 1b-118] }
