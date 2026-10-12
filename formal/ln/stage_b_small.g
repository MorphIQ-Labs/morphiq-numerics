# ln_1p's stage B, |x| < 2^-9 (docs/ln.md, section 7): the error over x^3 (Gx3)
# and over x (Gx1). al: the approximation, |ln(1 + x) - x + x^2/2 - x^3 W(x)|
# <= al |x|^3 (proved in formal/ln/Ln1pApprox.v); be: the tail's evaluation
# (formal/ln/stage_b_small_tail.g); pi = pl / x^2, two_prod's error; eta = e1 / x,
# Fast2Sum's error; d1, d2: the roundings of w and lo; m = x.
# Written by generators/ln1p_certificates.py.

Gx3 = al - be - d1 * (W + be) - d2 * (1 + d1) * (W + be);
Gx1 = m * (d1 + d2 * (1 + d1)) * pi / 2 - d2 * eta;

{ al in [-691b-65, 691b-65] /\ be in [-655b-62, 655b-62] /\ W in [681b-11, 684b-11]
  /\ pi in [-518b-62, 518b-62] /\ eta in [-519b-62, 519b-62] /\ m in [-1b-9, 1b-9]
  /\ d1 in [-1b-53, 1b-53] /\ d2 in [-1b-53, 1b-53]
  -> Gx3 in [-548b-61, 548b-61] /\ Gx1 in [-526b-115, 526b-115] }
