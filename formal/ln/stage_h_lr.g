# ln_1p's stage H (docs/ln.md, section 7): the l term, lrt = RN(RN(L) RN(1 - z))
# with L = l R 2^-E exact, |L| <= 2^-53 (1 + 2^-9), against L (1 - z), absolute.
# Written by generators/ln1p_certificates.py.

@rnd = float<ieee_64, ne>;

lr = rnd(L);
omz = rnd(1 - z);
lrt = rnd(lr * omz);

{ L in [-519b-62, 519b-62] /\ z in [-1b-9, 1b-9]
  -> lrt - L * (1 - z) in [-1b-104, 1b-104] /\ lrt in [-526b-62, 526b-62] }

lrt - L * (1 - z) -> (lrt - lr * omz) + (lr - L) * omz + L * (omz - (1 - z));
