# The fast path's ln(1 + z) (docs/ln.md, section 4), z = z_hi + z_lo exact
# and double-word (|z_lo| <= 2^-53 |z_hi|): the computed P against ln(1 + z), as
# a relative error. Written by generators/ln_certificates.py.
#
#   P = add_f64(add(z, (-z_hi^2/2 as a double-word)), RN(t - RN(z_hi z_lo)))
#
# Each binary64 rounding is modelled by its relative error, at most 2^-53: no
# intermediate underflows (1b-64 <= |z_hi| keeps every magnitude above
# 2^-200, or exactly zero). From their own certificates:
#   t = T (1 + et), |et| <= 1b-50                 (formal/ln/tail.g)
#   ln(1 + z) - z + z^2/2 = Tz + a, |a| <= rho |Tz|, rho = 0x1.0881be9fed09429c32c7bp-54
#     (generators/ln_poly.sollya, supnorm, relative; Tz = z^3 W(z))
#   the double-word additions' relative bounds, machine-checked in binary64
#   (docs/double-word.md): add 3u^2/(1 - 4u) (d1), add_f64 2u^2 (d2).
# -z_hi^2 / 2 is exact: z_hi^2 = sh + sl by two_prod, and halving is exact.

c3 = 0x1.5555555555555p-2;
c4 = -0x1.000000000002dp-2;
c5 = 0x1.99999999aef53p-3;
c6 = -0x1.5555554a1cd18p-3;
c7 = 0x1.24923e6ed17a8p-3;
c8 = -0x1.00059a9bca3b7p-3;
c9 = 0x1.ca33216abd50bp-4;

zl = zh * dl;
z = zh + zl;
W = (c3 + zh * (c4 + zh * (c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9))))));
Wz = (c3 + z * (c4 + z * (c5 + z * (c6 + z * (c7 + z * (c8 + z * c9))))));
T = zh * zh * zh * W;
Tz = z * z * z * Wz;
D = c4 * (1) + c5 * (zh + z) + c6 * (zh*zh + z*zh + z*z) + c7 * (zh*zh*zh + z*zh*zh + z*z*zh + z*z*z) + c8 * (zh*zh*zh*zh + z*zh*zh*zh + z*z*zh*zh + z*z*z*zh + z*z*z*z) + c9 * (zh*zh*zh*zh*zh + z*zh*zh*zh*zh + z*z*zh*zh*zh + z*z*z*zh*zh + z*z*z*z*zh + z*z*z*z*z);

t = T * (1 + et);
c = zh * zl * (1 + ec);
u = (t - c) * (1 + eu);
B = -(zh * zh) / 2;
P1 = (z + B) * (1 + d1);
P = (P1 + u) * (1 + d2);
a = al * Tz;
L = z - z * z / 2 + Tz + a;

{ |zh| in [1b-64, 0.0078126] /\ dl in [-1b-53, 1b-53] /\ et in [-1b-50, 1b-50]
  /\ ec in [-1b-53, 1b-53] /\ eu in [-1b-53, 1b-53] /\ al in [-535b-63, 535b-63]
  /\ d1 in [-776b-114, 776b-114] /\ d2 in [-1b-105, 1b-105]
  -> (P - L) / L in [-3b-66, 3b-66] }

# P - L = zl^2/2 + (T - Tz) + T et - zh zl ec + (t - c) eu - a + (z + B) d1
#         + ((z + B)(1 + d1) + u) d2; each term divided by zh, then by L / zh.
(P - L) / L -> ((P - L) / zh) / (L / zh) { zh <> 0, L <> 0 };
L / zh -> (1 + dl) - zh * (1 + dl) * (1 + dl) / 2 + Tz / zh + al * (Tz / zh) { zh <> 0 };
(P - L) / zh -> zh * dl * dl / 2 + (T - Tz) / zh + (zh * zh * W) * et - zh * dl * ec
               + ((t - c) / zh) * eu - al * (Tz / zh) + ((z + B) / zh) * d1
               + (((z + B) * (1 + d1) + u) / zh) * d2 { zh <> 0 };
# z^3 W(z) - zh^3 W(zh) = (z^3 - zh^3) W(z) + zh^3 (W(z) - W(zh)), and
# z^k - zh^k = zl (z^(k-1) + ... + zh^(k-1)).
(T - Tz) / zh -> -dl * ((z * z + z * zh + zh * zh) * Wz + zh * zh * zh * D) { zh <> 0 };
Tz / zh -> (1 + dl) * z * z * Wz { zh <> 0 };
(t - c) / zh -> zh * zh * W * (1 + et) - zh * dl * (1 + ec) { zh <> 0 };
(z + B) / zh -> 1 + dl - zh / 2 { zh <> 0 };
u / zh -> ((t - c) / zh) * (1 + eu) { zh <> 0 };
((z + B) * (1 + d1) + u) / zh -> ((z + B) / zh) * (1 + d1) + u / zh { zh <> 0 };
