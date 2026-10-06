# expm1's small-argument accurate result (docs/expm1.md, section 4):
# x H_2 in Q128 against e^x - 1 = x G, G = (e^x - 1)/x, relative.
# |H_2 - G| <= E2: the levels and the truncation. The product is truncated.
# Written by generators/expm1_certificates.py.

Y = (G + E2) * (1 + m) / G;

{ G in [0.974032205, 1.026290376] /\ E2 in [-646b-135, 646b-135] /\ m in [-1b-127, 0]
  -> Y - 1 in [-1b-123, 1b-123] }

Y - 1 -> E2 / G + (1 + E2 / G) * m;
