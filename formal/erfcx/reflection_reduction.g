# erfcx exp_dw reduction for s = RN(x*x), se = x*x-s.
# CONDITIONAL: n is the shifter integer, |n| <= 525000, R=s-n*ln(2)/512;
# r1=s-n*L1 and both differences forming u are exact; rh=r0+dh is
# the shifter result with |dh| <= 2^-41. The integer/grid hypotheses are discharged by
# ErfcxReflectionReduction.v using the shared |s|<710 reduction theorem.
# |se| <= 2^-44 follows for |x| below the overflow boundary, s < 710.
# L2/L3 and |dL| <= 2^-129 are the shared generated exp constants.
# The extra final rounding of rt0+se makes the bound 2^-92, not 2^-93.
@rnd = float<ieee_64, ne>;

L2 = -0x1.718432ap-44;
L3 = -0x1.b0e2633fe0685p-76;

n = int<ne>(n_);
r1 = R + n * (L2 + L3 + dL);
r0 = rnd(r1 - n * L2);
rh = r0 + dh;
u = r1 - rh - n * L2;
p3 rnd= n * L3;
rt0 rnd= u - p3;
rt rnd= rt0 + se;
Exact = R + se;

{ n in [-525000, 525000] /\ R in [-0.000677, 0.000677] /\ dL in [-1b-129, 1b-129]
  /\ se in [-1b-44, 1b-44] /\ dh in [-1b-41, 1b-41]
  -> rh + rt - Exact in [-1b-92, 1b-92] /\ rt in [-1b-40, 1b-40] /\ rh in [-0.000678, 0.000678] }

# The roundings of n*L3 and of r_t, and the untracked tail of L.
rh + rt - Exact -> (rt - (rt0 + se)) + (rt0 - (u - p3)) + (n * L3 - p3) + n * dL;
u - p3 -> (r1 - n * L2 - r0) - dh - p3;
