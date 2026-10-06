# expm1's fast result for |x| >= 2^-5 (docs/expm1.md, section 5):
#   M = (Y.add_f64(-2^-k)) 2^k, Y = 2^(j/128) e^R (1 + eY) from exp's fast path
# against e^x - 1 = 2^k (2^(j/128) e^R - 2^-k), relative. With
# kq = e^x/(e^x - 1), |kq| <= KQ (enclosed at |x| = 2^-5), the relative error
# is kq eY (1 + ea) + ea. The scaling by 2^k is exact.
# Written by generators/expm1_certificates.py.

M = (1 + kq * eY) * (1 + ea);

{ kq in [-526b-4, 526b-4] /\ eY in [-1b-69, 1b-69] /\ ea in [-1b-105, 1b-105]
  -> M - 1 in [-1b-62, 1b-62] }

M - 1 -> kq * eY * (1 + ea) + ea;
