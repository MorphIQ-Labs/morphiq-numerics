# cos's accurate result (docs/sin_cos.md, section 5) relative to cos of the
# exact r. H_1 is within E1 of the exact series value X1 (cos r), the levels'
# error, the product s = r^2 and the truncation together; the reduction's error enters as dr. Written by
# generators/trig_certificates.py.

Y = (1 + E1 / X1) * (1 + dr);

{ X1 in [0.7, 1] /\ E1 in [-518b-219, 518b-219] /\ dr in [-903b-209, 903b-209]
  -> Y - 1 in [-1b-198, 1b-198] }
