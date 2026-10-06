# The accurate path's result over ln x (docs/ln.md, section 6), case A: E = 0 and R[i] = 1, so ln x = z X1.
# Written by generators/ln_certificates.py. In Q128: G = z G_1 with
# |G_1 - ln(1 + z)/z| <= E1 (the levels and the truncation), X1 = ln(1 + z)/z;
# mz, mL: products' truncations; eN, eL: -ln R[i]'s and ln 2's constants;
# s1, s2: the additions, 2^-126 max(|a|, |b|), over |ln x|; dz: ln_1p's
# rounding of z' (section 7), 0 for ln.

Y = (X1 + E1) * (1 + mz) / X1;

{ E1 in [-818b-135, 818b-135] /\ X1 in [0.995118, 1.004931] /\ mz in [-1b-127, 0]
  -> Y - 1 in [-1b-123, 1b-123] }

Y - 1 -> E1 / X1 + (1 + E1 / X1) * mz { X1 <> 0 };
