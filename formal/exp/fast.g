# The fast path's relative error eps1 (docs/exp.md, section 4): Y against
# T_j * e^R, where R = x - n*L is the exact reduced argument.
#
# Hypotheses, each from its own certificate or proof:
#   rhi + rlo = R + dr,  |dr| <= 2^-113     (formal/exp/reduction.g)
#   |rlo| <= 2^-62                          (|rhi| <= 2^-8.5, so ulp(rhi)/2 <= 2^-62)
#   e^R = 1 + R + Q(rhi) + m + a,
#     |a| <= 0x1.ae822a1a2323630c07ceap-78  (generators/exp_poly.sollya, supnorm)
#     |m| = |Q(R) - Q(rhi)| <= 0x1.9p-71    (formal/exp/mvt.g)
#   the double-word operations' relative bounds, machine-checked in binary64
#   (formal/binary64): add_f64 2u^2, add 3u^2/(1-4u), mul 5u^2;
#   T_j's double-word table entry within 2^-107 (generators/exp_constants.py).

@rnd = float<ieee_64, ne>;

c3 = 0x1.555555555549p-3;
c4 = 0x1.55555555554bfp-5;
c5 = 0x1.111115b678249p-7;
c6 = 0x1.6c16c6fd917b6p-10;

rhi = rnd(rhi_);

# The polynomial, as formal/exp/poly.g evaluates it, and exactly.
t5 rnd= c5 + rhi * c6;
t4 rnd= c4 + rhi * t5;
t3 rnd= c3 + rhi * t4;
h  rnd= 0.5 + rhi * t3;
r2 rnd= rhi * rhi;
q  rnd= r2 * h;
Q = rhi * rhi * (0.5 + rhi * (c3 + rhi * (c4 + rhi * (c5 + rhi * c6))));

R = rhi + rlo - dr;
expR = 1 + R + Q + m + a;

P = (rhi + rlo + q) * (1 + d1);
E = (1 + P) * (1 + d2);
Y = (Tj * (1 + d4)) * E * (1 + d3);

{ rhi in [-0.0027077, 0.0027077] /\ rlo in [-1b-62, 1b-62] /\ dr in [-1b-113, 1b-113]
  /\ a in [-0x1.ae822a1a2323630c07ceap-78, 0x1.ae822a1a2323630c07ceap-78]
  /\ m in [-0x1.9p-71, 0x1.9p-71]
  /\ d1 in [-1b-105, 1b-105] /\ d2 in [-0x1.9p-105, 0x1.9p-105]
  /\ d3 in [-0x1.5p-104, 0x1.5p-104] /\ d4 in [-1b-107, 1b-107] /\ Tj in [1, 2]
  -> (Y - Tj * expR) / (Tj * expR) in [-1b-69, 1b-69] }

# The relative error is the polynomial's and the hypotheses' errors over e^R,
# plus the double-word steps' relative errors.
(Y - Tj * expR) / (Tj * expR) -> (1 + d4) * (1 + d3) * (1 + d2) * (1 + (1 + P - expR) / expR) - 1
  { Tj <> 0, expR <> 0 };
1 + P - expR -> dr + (q - Q) - m - a + (rhi + rlo + q) * d1;
