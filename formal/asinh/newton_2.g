# Newton step 2 for sinh y = x in Q256 (docs/asinh.md, section 4): y_0 = y* (1 +
# eps), |eps| <= 719b-127; the exact step lands at y* + q with q = c2 (eps y*)^2 / 2,
# c2 = sinh(xi)/cosh(y_0) in [0, 1.001] (xi between y_0 and y*, |xi - y_0| <=
# 2^-52); the computed correction is (q - eps y* + ex)(1 + er) with ex the sinh and
# cosh error (absolute, at most 585b-253: the exponential's 578b-253, formal/asinh/
# exp.g, with the sums' truncations) and er the product's and the reciprocal's
# error (formal/trig/recip_3.g: 2^-252.6; the product 2^-255); the last sum adds tr.
# Written by generators/asinh_certificates.py.

q = c2 * (eps * ystar) * (eps * ystar) / 2;
ynew = (ystar * (1 + eps) + (q - eps * ystar + ex) * (1 + er)) * (1 + tr);

{ ystar in [1b-27, 711] /\ eps in [-719b-127, 719b-127] /\ c2 in [0, 1.001]
  /\ ex in [-585b-253, 585b-253] /\ er in [-1b-251, 1b-251] /\ tr in [-1b-254, 1b-254]
  -> (ynew - ystar) / ystar in [-592b-226, 592b-226] }

(ynew - ystar) / ystar -> ((q + ex + (q - eps * ystar + ex) * er)
  + (ystar + q + ex + (q - eps * ystar + ex) * er) * tr) / ystar { ystar <> 0 };
