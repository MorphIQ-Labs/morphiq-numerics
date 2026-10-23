# The exponential's accurate value (docs/asinh.md, section 4): m = H_1 against
# exp r for the reduced r = y - k ln 2 of the exact y. H_1 is within E1 of the exact
# series value X1 = exp(r_c) at the computed r_c (the levels' error and the
# truncated tail, 2^-262); r_c = r + dr with |dr| <= 711 (2^-258 + 2^-255 +
# 2^-254) (the Q256 constant ln 2, the truncated product k L, the sum); and
# exp(r_c)/exp(r) = 1 + dx with |dx| <= 1.001 |dr| (mean value theorem, e^|dr|).
# Written by generators/asinh_certificates.py.

Y = (1 + E1 / X1) * (1 + dx);

{ X1 in [0.7, 1.42] /\ E1 in [-974b-262, 974b-262] /\ dx in [-569b-253, 569b-253]
  -> Y - 1 in [-578b-253, 578b-253] }
