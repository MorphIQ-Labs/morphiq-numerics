# exp2's reduced argument (docs/exp2.md, section 3): r ln 2 as the double-word
# (p, v) against the exact r ln 2, for every binary64 |r| <= 2^-8.
# Written by generators/radix_certificates.py.
#
#   (p, e) = two_prod(r, H), exact: p + e = r H
#   v = RN(e + RN(r Lo));  (r_hi, r_lo) = two_sum(p, v), exact
# with H = RN(ln 2), Lo = RN(ln 2 - H), and ln 2 = H + Lo + d.

@rnd = float<ieee_64, ne>;

H = 0x1.62e42fefa39efp-1;
Lo = 0x1.abc9e3b39803fp-56;

r = rnd(r_);
p = rnd(r * H);
e = r * H - p;
u rnd= r * Lo;
v rnd= e + u;
R = r * (H + Lo + dl);

{ r in [-1b-8, 1b-8] /\ dl in [-767b-120, 767b-120]
  -> (p + v) - R in [-1b-113, 1b-113] }

(p + v) - R -> (v - (e + u)) + (u - r * Lo) - r * dl;
