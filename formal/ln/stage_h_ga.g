# ln_1p's stage H (docs/ln.md, section 7): the absolute error terms. t5: the
# l term (formal/ln/stage_h_lr.g); t6: ln(1 + u) - u, u = L / (1 + z);
# d1..d3: the roundings of w, pre and lo, times lrt.
# Written by generators/ln1p_certificates.py.

GA = - t5 + t6 - d1 * lrt - d2 * lrt * (1 + d1) - d3 * (1 + d2) * lrt * (1 + d1);

{ t5 in [-1b-104, 1b-104] /\ t6 in [-534b-115, 534b-115] /\ lrt in [-526b-62, 526b-62]
  /\ d1 in [-1b-53, 1b-53] /\ d2 in [-1b-53, 1b-53] /\ d3 in [-1b-53, 1b-53]
  -> GA in [-526b-112, 526b-112] }
