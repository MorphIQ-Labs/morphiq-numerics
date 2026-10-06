# The accurate path's result over ln x (docs/ln.md, section 6), case C: E != 0.
# Written by generators/ln_certificates.py. In Q128: G = z G_1 with
# |G_1 - ln(1 + z)/z| <= E1 (the levels and the truncation), X1 = ln(1 + z)/z;
# mz, mL: products' truncations; eN, eL: -ln R[i]'s and ln 2's constants;
# s1, s2: the additions, 2^-126 max(|a|, |b|), over |ln x|; dz: ln_1p's
# rounding of z' (section 7), 0 for ln.
#   ln x = E ln 2 + N + z X1, with k1, k2, k3 those terms over ln x (generated).

k1 = 1 - k2 - k3;
q = E1 / X1;
Y = k1 * (1 + eL) * (1 + mL) + k2 * (1 + eN) + s1 + k3 * (1 + q) * (1 + mz) + dz + s2;

{ k2 in [-514b-9, 514b-9] /\ k3 in [-752b-16, 752b-16] /\ E1 in [-818b-135, 818b-135] /\ X1 in [0.995118, 1.004931] /\ mz in [-1b-127, 0]
  /\ eN in [-1b-127, 1b-127] /\ eL in [-1b-127, 1b-127] /\ mL in [-1b-127, 0]
  /\ s1 in [-518b-134, 518b-134] /\ s2 in [-523b-135, 523b-135] /\ dz in [-524b-135, 524b-135]
  -> Y - 1 in [-1b-123, 1b-123] }

Y - 1 -> k1 * ((1 + eL) * (1 + mL) - 1) + k2 * eN + k3 * (q + (1 + q) * mz) + dz + s1 + s2;
