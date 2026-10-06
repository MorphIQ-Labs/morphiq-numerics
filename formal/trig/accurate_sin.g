# sin's accurate result (docs/sin_cos.md, section 5) relative to sin of the
# exact r. H_1 is within E1 of the exact series value X1 (sin r / r), the levels'
# error, the product s = r^2 and the truncation together; the product r H_1 is
# truncated (m1); the reduction's error enters as dr. Written by
# generators/trig_certificates.py.

Y = (1 + m1) * (1 + E1 / X1) * (1 + dr);

{ X1 in [0.9, 1] /\ E1 in [-518b-219, 518b-219] /\ dr in [-575b-208, 575b-208] /\ m1 in [-1b-255, 0]
  -> Y - 1 in [-1b-198, 1b-198] }
