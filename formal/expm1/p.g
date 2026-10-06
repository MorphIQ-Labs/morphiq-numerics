# expm1's small-argument result (docs/expm1.md, section 3):
#   P = add_f64(add(x, x^2/2 as a double-word), t)
# against e^x - 1, relative. Written by generators/expm1_certificates.py.
#   t = T (1 + et), |et| <= 1b-50                (formal/expm1/tail.g)
#   e^x - 1 = x + x^2/2 + T + a, |a| <= rho |T|, rho = 0x1.0012p-54
#     (generators/expm1_poly.sollya, supnorm, relative)
#   x^2/2 is exact: x^2 = s_hi + s_lo by two_prod, and halving is exact.
#   the double-word additions' relative bounds (docs/double-word.md):
#   add 3u^2/(1 - 4u) (d1), add_f64 2u^2 (d2).

c3 = 0x1.5555555555555p-3;
c4 = 0x1.5555555555559p-5;
c5 = 0x1.111111111bbb8p-7;
c6 = 0x1.6c16c16b1d8abp-10;
c7 = 0x1.a019ec4b15b4p-13;
c8 = 0x1.a01c0085130ccp-16;
c9 = 0x1.7e0fb35411f23p-19;

W = (c3 + x * (c4 + x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9))))));
T = x * x * x * W;
t = T * (1 + et);
B = x * x / 2;
P1 = (x + B) * (1 + d1);
P = (P1 + t) * (1 + d2);
L = x + B + T * (1 + al);

{ |x| in [1b-54, 0.0312501] /\ et in [-1b-50, 1b-50] /\ al in [-518b-63, 518b-63]
  /\ d1 in [-776b-114, 776b-114] /\ d2 in [-1b-105, 1b-105]
  -> (P - L) / L in [-13b-66, 13b-66] }

(P - L) / L -> ((P - L) / x) / (L / x) { x <> 0, L <> 0 };
L / x -> 1 + x / 2 + x * x * W * (1 + al) { x <> 0 };
(P - L) / x -> x * x * W * (et - al) + (1 + x / 2) * d1 + ((1 + x / 2) * (1 + d1) + x * x * W * (1 + et)) * d2
  { x <> 0 };
