# The fast path's ln x (docs/ln.md, section 4), case A: E = 0 and R[i] = 1,
# so ln x = ln(1 + z), and the result is P through two exact additions of zero;
# their bounds are kept so the pipeline is one. Relative to ln x:
#   Y = (1 + dP) (1 + e1) (1 + e2), dP from formal/ln/p.g.
# Written by generators/ln_certificates.py.

Y = (1 + dP) * (1 + e1) * (1 + e2);

{ dP in [-3b-66, 3b-66] /\ e1 in [-776b-114, 776b-114] /\ e2 in [-776b-114, 776b-114]
  -> Y - 1 in [-1b-64, 1b-64] }
