# ln_1p's stage H (docs/ln.md, section 7): the error terms proportional to z^2,
# over z^2. t4: q's evaluation (formal/ln/stage_h_q.g); t3: the approximation,
# |ln(1 + z) - z - z^2 P(z)| <= t3 z^2 (generators/ln_poly.sollya, proved in
# formal/ln/Ln1pApprox.v); L / (1 + z): from ln(1 + L/(1 + z)) - L (1 - z);
# d3: lo's rounding, times q / z^2. Written by generators/ln1p_certificates.py.

Gz = - t4 + t3 + L / (1 + z) - d3 * (Pz + t4);

{ t4 in [-577b-61, 577b-61] /\ t3 in [-592b-60, 592b-60] /\ L in [-519b-62, 519b-62] /\ z in [-1b-9, 1b-9]
  /\ d3 in [-1b-53, 1b-53] /\ Pz in [-513b-10, -511b-10]
  -> Gz in [-543b-59, 543b-59] }
