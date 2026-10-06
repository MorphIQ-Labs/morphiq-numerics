# log2's fast path (docs/log2.md, section 3), relative to log2 x = E + w,
# w = log2 y = (ln y)/ln 2. Written by generators/radix_certificates.py.
#   S = ln y (1 + eS): ln's fast path for ln y (formal/ln/fast_a.g, fast_b.g with E = 0)
#   C = (1/ln 2)(1 + eC): the double-word constant (generated)
#   W = S.mul(C), relative error em: mul, 5u^2
#   E = 0: the result is W.  E != 0: Y = E.add(W), relative error ea.
# kw = w/(E + w) and ke = E/(E + w) = 1 - kw, |kw| bounded by enclosure.

ke = 1 - kw;
Y = (ke + kw * (1 + eS) * (1 + eC) * (1 + em)) * (1 + ea);
Y0 = (1 + eS) * (1 + eC) * (1 + em);

{ kw in [-518b-9, 518b-9] /\ eS in [-1b-64, 1b-64] /\ eC in [-988b-120, 988b-120]
  /\ em in [-5b-106, 5b-106] /\ ea in [-776b-114, 776b-114]
  -> Y - 1 in [-1b-63, 1b-63] /\ Y0 - 1 in [-1b-63, 1b-63] }

Y - 1 -> kw * ((1 + eS) * (1 + eC) * (1 + em) - 1) * (1 + ea) + ea;
