# For |t_hi| below 2^-60: t = r_lo, and a tail may underflow; it lies
# within [0, 3] times its value (et in [-1, 2]).
# cos t - 1 for the double-word t (docs/sin_cos.md, section 4):
#   CM = add_f64(-t_hi^2/2 as an exact double-word, v),
#   v = RN(tail - RN(t_hi t_lo))
# against cos t - 1, relative. Written by generators/trig_certificates.py.
#   tail = t_hi^4 Pc(t_hi^2) (1 + et)                (formal/trig/cos_tail.g)
#   cos t - 1 = -t^2/2 + t^4 Pc(t^2) (1 + al), |al| <= rho
#   t_hi t_lo = t_hi^2 dl, rounded (ec); the subtraction rounded (eu);
#   add_f64: 2u^2.

c0 = 0x1.5555555555555p-5;
c1 = -0x1.6c16c16b6b967p-10;
c2 = 0x1.a0115f5073e76p-16;

t = th * (1 + dl);
Ph = c0 + th * th * (c1 + th * th * c2);
Pt = c0 + t * t * (c1 + t * t * c2);
V = (th * th * th * th * Ph * (1 + et) - th * th * dl * (1 + ec)) * (1 + eu);
CM = (-(th * th) / 2 + V) * (1 + d2);
CT = -(t * t) / 2 + t * t * t * t * Pt * (1 + al);

{ |th| in [1b-320, 1b-60] /\ dl in [-1b-53, 1b-53] /\ et in [-1, 2] /\ al in [-518b-63, 518b-63]
  /\ ec in [-1b-53, 1b-53] /\ eu in [-1b-53, 1b-53] /\ d2 in [-1b-105, 1b-105]
  -> (CM - CT) / CT in [-1b-65, 1b-65] }

(CM - CT) / CT -> ((CM - CT) / (th * th)) / (CT / (th * th));
CT / (th * th) -> -(1 + dl) * (1 + dl) / 2 + (1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt * (1 + al);
(CM - CT) / (th * th) ->
  th * th * (Ph * ((1 + et) * (1 + eu) * (1 + d2) - 1) - Pt * ((1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * (1 + al) - 1)
             - th * th * ((1 + dl) * (1 + dl) - 1) * (c1 + c2 * th * th * (1 + (1 + dl) * (1 + dl))))
  + dl * (1 - (1 + ec) * (1 + eu) * (1 + d2)) + dl * dl / 2 - d2 / 2;
