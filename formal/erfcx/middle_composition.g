# erfcx arithmetic component; see docs/erfcx.md for assumptions and scope.
# Composition of middle-tail components; all error hypotheses have their own
# certificate or generated approximation bound. S = x*sqrt(pi)*erfcx(x).
A = (1 + ec) * (1 + ey);
W = S + ep + ev + ea;
B = A * W * (1 + em1);
Y = B * (1 + em2);
{ S in [0.998, 1] /\ ec in [-1b-110, 1b-110] /\ ey in [-1b-98, 1b-98]
  /\ ep in [-0x1.5p-68, 0x1.5p-68] /\ ev in [-1b-101, 1b-101]
  /\ ea in [-1b-74, 1b-74] /\ em1 in [-1b-100, 1b-100] /\ em2 in [-1b-100, 1b-100]
  -> (Y - S) / S in [-1b-67, 1b-67] }
Y - S -> ep + ev + ea + (A - 1) * W + A * W * em1 + B * em2;
A - 1 -> ec + ey + ec * ey;
