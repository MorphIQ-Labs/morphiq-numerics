# Stage B's absolute error (docs/exp.md, section 6): y + l against T_j * e^R
# before scaling, where R = x - n*L is the exact reduced argument and
# T_j = 2^(j/512).
#
# Hypotheses, each from its own certificate or proof:
#   r_h + r_t = R + dr, |dr| <= 2^-93, |r_h| <= 0.000678, |r_t| <= 2^-40
#                                           (formal/exp/stage_b_reduction.g)
#   q = RN(q_), q - Q(r_hi) = eq, |eq| <= 2^-73, 0 <= q <= 2^-22
#                                           (formal/exp/stage_b_poly.g)
#   e^R = 1 + R + Q(r_hi) + m + a,
#     |a| <= 0x1.11efe3daa4fb92df2df8cp-76  (generators/exp_poly.sollya, supnorm;
#                                            formal/exp/ExpStageTables.v)
#     |m| = |Q(R) - Q(r_hi)| <= 2^-74       (formal/exp/stage_mvt.g)
#   Th + Tl = T_j + Dt, |Dt| <= 2^-104, Th in [1, 2), |Tl| <= 2^-53
#                                           (formal/exp/ExpStageTables.v)
#   d = Th - A, where A is Th's leading 21 bits: 0 <= d < 2^-20, and d,
#   A*r_h and Fast2Sum(Th, A*r_h) are exact  (formal/exp/ExpStageB.v)
# Every other operation is rounded to binary64, nearest-even. The bounds on
# l, y and the intermediates are what the rounding test and the
# transcription's finiteness need.

@rnd = float<ieee_64, ne>;

rhi = rnd(rh + rt);
q = rnd(q_);
Qr = q - eq;

ph = (Th - d) * rh;
y = rnd(Th + ph);
e = Th + ph - y;
s1 rnd= rt + q;
s2 rnd= Th * s1;
s3 rnd= d * rh;
s4 rnd= s3 + s2;
s5 rnd= Tl * rhi;
s6 rnd= s5 + s4;
rest rnd= Tl + s6;
l rnd= e + rest;

R = rh + rt - dr;
QR = Qr + m;
expR = 1 + R + QR + a;
T = Th + Tl - Dt;
Y = y + l;
Ideal = Tl + Tl * rhi + d * rh + Th * (rt + q);

{ rh in [-0.000678, 0.000678] /\ rt in [-1b-40, 1b-40] /\ dr in [-1b-93, 1b-93]
  /\ q in [0, 1b-22] /\ eq in [-1b-73, 1b-73]
  /\ a in [-0x1.11efe3daa4fb92df2df8cp-76, 0x1.11efe3daa4fb92df2df8cp-76] /\ m in [-1b-74, 1b-74]
  /\ Th in [1, 2] /\ Tl in [-1b-53, 1b-53] /\ Dt in [-1b-104, 1b-104]
  /\ d in [0, 1b-20]
  -> Y - T * expR in [-0x1.a2p-71, 0x1.a2p-71] /\ l in [-1b-20, 1b-20] /\ y in [0.5, 4]
     /\ rhi in [-1, 1] /\ s1 in [-1, 1] /\ s2 in [-1, 1] /\ s3 in [-1, 1] /\ s4 in [-1, 1]
     /\ s5 in [-1, 1] /\ s6 in [-1, 1] /\ rest in [-1, 1] }

# Y = Th (1 + r_h + r_t + q) + Tl (1 + r_hi) up to the roundings of rest and
# l, since y + e = Th + A*r_h exactly; the rest is the hypotheses' errors.
Y - T * expR -> (rest - Ideal) + (l - (e + rest)) + Th * (dr + eq - m - a) + Tl * (rhi - R) - Tl * (QR + a)
  + Dt * expR;
rest - Ideal -> (rest - (Tl + s6)) + (s6 - (s5 + s4)) + (s5 - Tl * rhi) + (s4 - (s3 + s2))
  + (s3 - d * rh) + (s2 - Th * s1) + Th * (s1 - (rt + q));
rhi - R -> (rhi - (rh + rt)) + dr;
