# The accurate path's Newton step for d sin(phi) = n cos(phi) in Q256 (docs/atan2.md,
# section 5): phi_0 = phi* (1 + eps), |eps| <= 1007b-73, delta = eps phi*. With R =
# sqrt(n^2 + d^2) the numerator is -R sin(delta) and the denominator R cos(delta),
# so the exact step is phi_0 - tan(delta) = phi* + delta - tan(delta), and
# tan(delta) = delta + c3 delta^3 / 3 with c3 in [0, 1.001] (|delta| <= 2^-52). The
# computed correction adds ex = phi* exr, the error of the Q256 sine and cosine
# (relative 2^-198, formal/trig/accurate_*.g) carried through n cos - d sin over
# d cos + n sin: at most 2^-197 n/(0.7 d) <= 2^-196.5 t <= 2^-196 phi*
# (t/atan t <= 4/pi); er the product's and the reciprocal's error relative to
# the correction (formal/trig/recip_3.g: 2^-252.6; the product 2^-255); tr the last
# sum. Written by generators/atan2_certificates.py.

delta = eps * phistar;
q3 = c3 * delta * delta * delta / 3;
phinew = (phistar * (1 + eps) + (-(delta + q3) + phistar * exr) * (1 + er)) * (1 + tr);

{ phistar in [1b-900, 0.7853981633974484] /\ eps in [-1007b-73, 1007b-73] /\ c3 in [0, 1.001]
  /\ exr in [-1b-196, 1b-196] /\ er in [-1b-251, 1b-251] /\ tr in [-1b-254, 1b-254]
  -> (phinew - phistar) / phistar in [-673b-200, 673b-200] }

(phinew - phistar) / phistar -> ((-(c3 * eps * eps * eps * phistar * phistar / 3) + exr
    - (eps + c3 * eps * eps * eps * phistar * phistar / 3) * er + exr * er)
  + (1 - (c3 * eps * eps * eps * phistar * phistar / 3) + exr
    - (eps + c3 * eps * eps * eps * phistar * phistar / 3) * er + exr * er) * tr) { phistar <> 0 };
