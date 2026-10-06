# Q256::recip's first guess (docs/sin_cos.md, section 8): y_0 = RN(1/RN(c))
# for c of a normal binary64's magnitude; c y_0 = (1 + d2)/(1 + d1), with d1, d2
# the two roundings to nearest. Written by generators/trig_certificates.py.

E = (1 + d2) / (1 + d1) - 1;

{ d1 in [-1b-53, 1b-53] /\ d2 in [-1b-53, 1b-53] -> E in [-518b-61, 518b-61] }
