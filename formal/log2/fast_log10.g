# log10's fast path (docs/log2.md, section 5): ln's fast result
# ln x (1 + eL) (formal/ln/fast_a.g, _b.g, _c.g), times the double-word
# 1/ln 10 (1 + eC), by mul (5u^2). Written by generators/radix_certificates.py.

Y = (1 + eL) * (1 + eC) * (1 + em);

{ eL in [-1b-64, 1b-64] /\ eC in [-575b-119, 575b-119] /\ em in [-5b-106, 5b-106]
  -> Y - 1 in [-1b-63, 1b-63] }
