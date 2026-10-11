# ln_1p's stage B, |x| >= 2^-9 (docs/ln.md, section 7): the total error,
# absolute. t1: the tables', E ln 2's and ln0's errors; ap: the approximation
# (formal/ln/Ln1pApprox.v); lt: ln(1 + z + L) - ln(1 + z) - L (1 - z + z^2 - z^3);
# g: lo's evaluation (formal/ln/stage_b_lo.g). Written by
# generators/ln1p_certificates.py.

Y = t1 + ap + lt - g;

{ t1 in [-533b-95, 533b-95] /\ ap in [-698b-92, 698b-92] /\ lt in [-526b-98, 526b-98] /\ g in [-830b-89, 830b-89]
  -> Y in [-936b-89, 936b-89] }
