# The fast path's ln x (docs/ln.md, section 4), case B: E = 0 and R[i] != 1.
# Written by generators/ln_certificates.py.
#
# ln x = E ln 2 + (-ln R[i]) + ln(1 + z). With k1, k2, k3 those three terms over
# ln x (k1 + k2 + k3 = 1; their bounds from generators/ln_constants.py, least
# |ln x| = 0.003914), the result over ln x is
#   Y = (k1 (1 + lam) + (k2 (1 + dT) + k3 (1 + dP)) (1 + e1)) (1 + e2)
#   dT: -ln R[i]'s double-word error (generated), lam: E ln 2's (generated);
#   dP: formal/ln/p.g; e1, e2: the double-word additions, 3u^2/(1 - 4u) each.

k2 = 1 - k3;
k1 = 0;
Y = (k1 * (1 + lam) + (k2 * (1 + dT) + k3 * (1 + dP)) * (1 + e1)) * (1 + e2);

{ k3 in [-533b-10, 533b-10] /\ dT in [-984b-117, 984b-117] /\ lam in [-745b-106, 745b-106]
  /\ dP in [-3b-66, 3b-66] /\ e1 in [-776b-114, 776b-114] /\ e2 in [-776b-114, 776b-114]
  -> Y - 1 in [-1b-64, 1b-64] }

Y - 1 -> k1 * lam + (k2 * dT + k3 * dP) * (1 + e1) + (k2 + k3) * e1
         + (k1 * (1 + lam) + (k2 * (1 + dT) + k3 * (1 + dP)) * (1 + e1)) * e2;
