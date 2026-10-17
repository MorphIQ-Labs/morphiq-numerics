# The central first stage's polynomial (docs/normal.md, the central first
# stage), operation for operation as normal_distribution::center_first_parts,
# from the binary64 tail t4 = c4 + z·(c5 + ...) on: e1h + e1l + e2 against
# P(x²) - 1 with the exact coefficients -1/6, 1/40, -1/336 and the exact
# tail TZ = T(x²), |x| <= 1/2.
#
# Hypotheses, each proved in formal/normal/NormalCenterFirst.v:
#   |t4 - TH| <= 2^-62, TH = T(zh)        (NormalCenterFastTail.normal_center_tail_ieee)
#   |TH - TZ| <= 2^-64                     (normal_center_tail_lipschitz, |zh - x²| <= 2^-56)
#   |TZ| <= 2^-9                           (normal_center_tail_polynomial_range)
# zl and e1p are the exact error words of two_prod.

@rnd = float<ieee_64, ne>;

c1h = -0x1.5555555555555p-3;
c1l = -0x1.5555555555555p-57;
c2 = 0x1.999999999999ap-6;
c3 = -0x1.8618618618618p-9;

# The exact square, two_prod(x, x).
zh = rnd(x * x);
zl = x * x - zh;
# c1·z: the exact high product and the low terms.
e1h = rnd(c1h * zh);
e1p = c1h * zh - e1h;
r1 = rnd(c1h * zl);
r2 = rnd(c1l * zh);
r = rnd(r1 + r2);
e1l = rnd(e1p + r);
# c3 + z·tail, then z²·(c2 + z·(c3 + z·tail)).
t3 rnd= c3 + zh * t4;
zz = rnd(zh * zh);
m = rnd(zh * t3);
w = rnd(c2 + m);
e2 = rnd(zz * w);

# The reference with the exact coefficients.
Z = x * x;
T3 = -1/336 + Z * TZ;
W = 1/40 + Z * T3;
E = -1/6 * Z + Z * Z * W;

{ x in [-0.5, 0.5] /\ t4 - TH in [-1b-62, 1b-62] /\ TH - TZ in [-1b-64, 1b-64] /\ TZ in [-1b-9, 1b-9]
  -> e1h + e1l + e2 - E in [-1b-60, 1b-60]
     /\ e1h in [-0.0417, 0] /\ e1l in [-1b-55, 1b-55] /\ e2 in [0, 0.0016]
     /\ zh in [0, 0.25]
     /\ c1h * zl in [-1, 1] /\ c1l * zh in [-1, 1] /\ r1 + r2 in [-1, 1] /\ e1p + r in [-1, 1]
     /\ zh * t4 in [-1, 1] /\ c3 + rnd(zh * t4) in [-1, 1] /\ zh * zh in [-1, 1] /\ zh * t3 in [-1, 1]
     /\ c2 + m in [-1, 1] /\ zz * w in [-1, 1] /\ c1h * zh in [-1, 1] }

e1h + e1l + e2 - E -> (e1l - (e1p + c1h * zl + c1l * zh)) + (c1h + c1l + 1/6) * Z - c1l * zl + (e2 - Z * Z * W);
e1l - (e1p + c1h * zl + c1l * zh) -> (e1l - (e1p + r)) + (r - (r1 + r2)) + (r1 - c1h * zl) + (r2 - c1l * zh);
e2 - Z * Z * W -> (e2 - zz * w) + (zz - Z * Z) * w + Z * Z * (w - W);
zz - Z * Z -> (zz - zh * zh) + (zh - Z) * (zh + Z);
w - W -> (w - (c2 + m)) + (c2 - 1/40) + (m - zh * t3) + zh * (t3 - T3) + (zh - Z) * T3;
t3 - T3 -> (t3 - (c3 + zh * t4)) + (c3 + 1/336) + zh * (t4 - TH) + zh * (TH - TZ) + (zh - Z) * TZ;
