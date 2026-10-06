# log2's accurate path (docs/log2.md, section 4) in Q128, relative to
# log2 x = E + w. Written by generators/radix_certificates.py.
#   A = ln y (1 + eA): ln's accurate path for ln y (formal/ln/accurate_sum_a.g, _b.g)
#   C = (1/ln 2)(1 + eC), and the product truncated, m in [-2^-127, 0]
#   E = 0: the result is A C.  E != 0: E converts exactly, and the addition
#   errs by at most 2^-126 max(|E|, |w|) (1 + 2^-120), over |E + w|: s.

ke = 1 - kw;
Y = ke + kw * (1 + eA) * (1 + eC) * (1 + m) + s;
Y0 = (1 + eA) * (1 + eC) * (1 + m);

{ kw in [-518b-9, 518b-9] /\ eA in [-1b-123, 1b-123] /\ eC in [-926b-141, 926b-141]
  /\ m in [-1b-127, 0] /\ s in [-518b-134, 518b-134]
  -> Y - 1 in [-1b-122, 1b-122] /\ Y0 - 1 in [-1b-122, 1b-122] }

Y - 1 -> kw * ((1 + eA) * (1 + eC) * (1 + m) - 1) + s;
