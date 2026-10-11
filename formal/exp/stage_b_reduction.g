# Stage B's reduced argument (docs/exp.md, section 3): r_h + r_t against the
# exact r = x - n*L, L = ln 2 / 512, for every integer |n| <= 520018 and
# every exact |r| <= 0.000677.
#
# Taken as exact, each with its argument in docs/exp.md and its proof in
# formal/exp/ExpStageReduction.v:
#   r1 = x - n*L1           (n*L1 exact: L1 has 31 bits; the difference exact)
#   n*L2                    (L2 has 31 bits)
#   r_h = r0 + dh, |dh| <= 2^-41   (r0 rounded to a multiple of 2^-40)
#   u = r1 - r_h - n*L2     (both differences exact)
# L = L1 + L2 + L3 + dL with |dL| <= 2^-129 (formal/exp/ExpStageTables.v), so
# r1 = r + n*(L2 + L3 + dL).

@rnd = float<ieee_64, ne>;

L2 = -0x1.718432ap-44;
L3 = -0x1.b0e2633fe0685p-76;

n = int<ne>(n_);
r1 = R + n * (L2 + L3 + dL);
r0 = rnd(r1 - n * L2);
rh = r0 + dh;
u = r1 - rh - n * L2;
p3 rnd= n * L3;
rt rnd= u - p3;

{ n in [-520018, 520018] /\ R in [-0.000677, 0.000677] /\ dL in [-1b-129, 1b-129]
  /\ dh in [-1b-41, 1b-41]
  -> rh + rt - R in [-1b-93, 1b-93] /\ rt in [-1b-40, 1b-40] /\ rh in [-0.000678, 0.000678] }

# The roundings of n*L3 and of r_t, and the untracked tail of L.
rh + rt - R -> (rt - (u - p3)) + (n * L3 - p3) + n * dL;
u - p3 -> (r1 - n * L2 - r0) - dh - p3;
