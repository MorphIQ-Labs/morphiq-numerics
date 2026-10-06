# log10's accurate path (docs/log2.md, section 5): ln's accurate result
# ln x (1 + eA) (formal/ln/accurate_sum_*.g) times 1/ln 10 in Q128 (1 + eC),
# the product truncated. Written by generators/radix_certificates.py.

Y = (1 + eA) * (1 + eC) * (1 + m);

{ eA in [-1b-123, 1b-123] /\ eC in [-586b-139, 586b-139] /\ m in [-1b-127, 0]
  -> Y - 1 in [-1b-122, 1b-122] }
