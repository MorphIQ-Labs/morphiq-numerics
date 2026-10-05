# The fast path's reduced argument (docs/exp.md, section 3, step 4): the
# error of the double-word (r_hi, r_lo) against the exact r = x - n*L, for
# every integer |n| <= 137601 and every exact |r| <= A.
#
# Taken as exact, each with its argument in docs/exp.md:
#   r1 = x - n*L1           (Sterbenz; n*L1 exact since L1 has 35 bits)
#   p2 + e2 = n*L2          (two_prod, within its domain)
#   s + t = r1 - p2         (two_sum)
#   r_hi + r_lo = s + rr    (two_sum)
# and every other operation is rounded to binary64, nearest-even.

@rnd = float<ieee_64, ne>;

L2 = -0x1.c610ca86c3899p-44;
L3 = 0x1.803f2f6af40f3p-99;
L4 = 0x1.0c99ca62d8b63p-153;

n = int<ne>(n_);
# L = L1 + L2 + L3 + L4 + dL exactly, with |dL| < 2^-206 (generated).
# r1 = x - n*L1 = R + n*(L2 + L3 + L4 + dL).
r1 = R + n * (L2 + L3 + L4 + dL);

p2 = rnd(n * L2);
e2 = n * L2 - p2;
s = rnd(r1 - p2);
t = (r1 - p2) - s;
u1 rnd= t - e2;
u2 rnd= n * L3;
rr rnd= u1 - u2;

{ n in [-137601, 137601] /\ R in [-0.0027077, 0.0027077] /\ dL in [-1b-206, 1b-206]
  -> (s + rr) - R in [-1b-113, 1b-113] }

# The error is the three roundings plus the untracked tail of L.
(s + rr) - R -> (u1 - (t - e2)) - (u2 - n * L3) + (rr - (u1 - u2)) + n * (L4 + dL);
