# Stage A at a double-word argument s + se (docs/exp.md, section 5a):
# y + l = th + fl against T_j * e^R before scaling, where
# R = s + se - n*L = R0 + se, R0 = s - n*L the exact reduced argument of
# the stages' reduction of s (docs/exp.md, section 3), and T_j = 2^(j/512).
#
# Hypotheses, each from its own certificate or proof:
#   r0 = RN(R0 + dr), |dr| <= 2^-77        (formal/exp/stage_a_reduction.g)
#   |se| <= 2^-42                          (the caller's low word)
#   e^R = 1 + R + Q(r) + m + a,
#     |a| <= 0x1.11efe3daa4fb92df2df8cp-76 (generators/exp_poly.sollya, supnorm;
#                                           formal/exp/ExpStageTables.v)
#     |m| = |Q(R) - Q(r)| <= 2^-73         (formal/exp/stage_mvt_dw.g)
#   th + tl = T_j + Dt, |Dt| <= 2^-104, th in [1, 2), |tl| <= 2^-53
#                                          (formal/exp/ExpStageTables.v)
# Every operation below is rounded to binary64, nearest-even.

@rnd = float<ieee_64, ne>;

d3 = 0x1.5555555555554p-3;
d4 = 0x1.555555a38ed84p-5;
d5 = 0x1.11111177013d7p-7;

r0 = rnd(R0 + dr);
r rnd= r0 + se;
t4 rnd= d4 + r * d5;
t3 rnd= d3 + r * t4;
h  rnd= 0.5 + r * t3;
r2 rnd= r * r;
w  rnd= r2 * h;
u  rnd= r + w;
p  rnd= th * u;
fl rnd= tl + p;

R = R0 + se;
Qr = r * r * (0.5 + r * (d3 + r * (d4 + r * d5)));
QR = Qr + m;
expR = 1 + R + QR + a;
T = th + tl - Dt;
Y = th + fl;

{ R0 in [-0.000677, 0.000677] /\ dr in [-1b-77, 1b-77] /\ se in [-1b-42, 1b-42]
  /\ a in [-0x1.11efe3daa4fb92df2df8cp-76, 0x1.11efe3daa4fb92df2df8cp-76] /\ m in [-1b-73, 1b-73]
  /\ th in [1, 2] /\ tl in [-1b-53, 1b-53] /\ Dt in [-1b-104, 1b-104]
  -> Y - T * expR in [-0x1.7p-61, 0x1.7p-61] /\ fl in [-0x1.6ap-10, 0x1.6ap-10]
     /\ r - R in [-0x1.01p-63, 0x1.01p-63]
     /\ r in [-1, 1] /\ t4 in [-1, 1] /\ t3 in [-1, 1] /\ h in [-1, 1] /\ r2 in [-1, 1] /\ w in [-1, 1]
     /\ u in [-1, 1] /\ p in [-1, 1] }

Y - T * expR -> th * (r - R) - th * m + th * (u - (r + Qr)) - th * a - tl * (R + QR + a)
  + (fl - (tl + th * u)) + Dt * expR;
fl - (tl + th * u) -> (fl - (tl + p)) + (p - th * u);
u - (r + Qr) -> (u - (r + w)) + (w - Qr);
r - R -> (r - (r0 + se)) + (r0 - (R0 + dr)) + dr;
