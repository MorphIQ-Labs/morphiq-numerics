# The accurate tan (docs/sin_cos.md, section 8): N.mul(D.recip()), with N, D the
# accurate sin r and cos r in either order, each within 2^-198
# (formal/trig/accurate_sin.g, accurate_cos.g); D.recip() is (1/D)(1 + er)
# (formal/trig/recip_3.g); the product is truncated (m). Written by
# generators/trig_certificates.py.

Q = (1 + eN) / (1 + eD) * (1 + er) * (1 + m);

{ eN in [-1b-198, 1b-198] /\ eD in [-1b-198, 1b-198] /\ er in [-657b-262, 657b-262] /\ m in [-1b-255, 0]
  -> Q - 1 in [-1b-196, 1b-196] }
