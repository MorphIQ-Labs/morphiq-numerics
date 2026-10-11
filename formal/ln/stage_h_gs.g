# ln_1p's stage H (docs/ln.md, section 7): the error terms proportional to |s|,
# over s. tau: the tables' and E ln 2's errors; kap = ln0 / s; eta = e1 / s,
# Fast2Sum's error; d0..d3: the roundings of ln0, w, pre and lo.
# Written by generators/ln1p_certificates.py.

Gs = tau - d0 * kap / (1 + d0) - d1 * kap - d2 * (eta + kap * (1 + d1)) - d3 * (1 + d2) * (eta + kap * (1 + d1));

{ tau in [-732b-96, 732b-96] /\ kap in [-732b-43, 732b-43] /\ eta in [-1b-53, 1b-53]
  /\ d0 in [-1b-53, 1b-53] /\ d1 in [-1b-53, 1b-53] /\ d2 in [-1b-53, 1b-53] /\ d3 in [-1b-53, 1b-53]
  -> Gs in [-925b-94, 925b-94] }
