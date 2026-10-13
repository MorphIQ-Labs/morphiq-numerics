# Q256::recip's first guess (docs/sin_cos.md, section 8): y_0 = RN(1/RN(c))
# with |c| >= 2^-1022 and RN(c) finite; c y_0 = (1 + d2)/(1 + d1).
# The reciprocal can be subnormal: its magnitude is >= 2^-1024 and the
# absolute rounding error <= 2^-1075, hence |d2| <= 2^-51. For a normal
# reciprocal the tighter 2^-53 also fits. Written by generators/trig_certificates.py.

E = (1 + d2) / (1 + d1) - 1;

{ d1 in [-1b-53, 1b-53] /\ d2 in [-1b-51, 1b-51] -> E in [-647b-60, 647b-60] }
