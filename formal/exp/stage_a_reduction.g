# Stage A's reduced argument (docs/exp.md, section 3): r1 - RN(n*L2D) against
# the exact r = x - n*L, L = ln 2 / 512, for every integer |n| <= 520018
# and every exact |r| <= 0.000677.
#
# Taken as exact, each with its argument in docs/exp.md and its proof in
# formal/exp/ExpStageReduction.v:
#   r1 = x - n*L1           (n*L1 exact: L1 has 31 bits; the difference exact)
# L = L1 + L2D + dL with |dL| <= 2^-98 (formal/exp/ExpStageTables.v), so
# r1 = r + n*(L2D + dL).

@rnd = float<ieee_64, ne>;

L2D = -0x1.718432a1b0e26p-44;

n = int<ne>(n_);
r1 = R + n * (L2D + dL);
p rnd= n * L2D;

{ n in [-520018, 520018] /\ R in [-0.000677, 0.000677] /\ dL in [-1b-98, 1b-98]
  -> r1 - p - R in [-1b-77, 1b-77] }

# The rounding of n*L2D and the untracked tail of L.
r1 - p - R -> n * dL + (n * L2D - p);
