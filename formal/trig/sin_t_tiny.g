# For |t_hi| below 2^-60: t = r_lo, and a tail may underflow; it lies
# within [0, 3] times its value (et in [-1, 2]).
# sin t for the double-word t = t_hi + t_lo, |t_lo| <= 2^-53 |t_hi|
# (docs/sin_cos.md, section 4): SN = add_f64(t, tail) against sin t, relative.
# Written by generators/trig_certificates.py.
#   tail = t_hi^3 Ps(t_hi^2) (1 + et)              (formal/trig/sin_tail.g)
#   sin t = t + t^3 Ps(t^2) (1 + al), |al| <= rho   (generators/trig_poly.sollya)
#   add_f64: 2u^2 (docs/double-word.md)

s0 = -0x1.5555555555555p-3;
s1 = 0x1.11111110bb1a8p-7;
s2 = -0x1.a0159d0d83966p-13;

t = th * (1 + dl);
Ph = s0 + th * th * (s1 + th * th * s2);
Pt = s0 + t * t * (s1 + t * t * s2);
SN = (t + th * th * th * Ph * (1 + et)) * (1 + d2);
ST = t + t * t * t * Pt * (1 + al);

{ |th| in [1b-320, 1b-60] /\ dl in [-1b-53, 1b-53] /\ et in [-1, 2] /\ al in [-518b-63, 518b-63]
  /\ d2 in [-1b-105, 1b-105]
  -> (SN - ST) / ST in [-1b-65, 1b-65] }

(SN - ST) / ST -> ((SN - ST) / th) / (ST / th) { th <> 0, ST <> 0 };
ST / th -> (1 + dl) + (1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt * (1 + al) { th <> 0 };
(SN - ST) / th -> (1 + dl) * d2 + th * th * (Ph * (1 + et) * (1 + d2) - (1 + dl) * (1 + dl) * (1 + dl) * Pt * (1 + al))
  { th <> 0 };
Ph * (1 + et) * (1 + d2) - (1 + dl) * (1 + dl) * (1 + dl) * Pt * (1 + al) ->
  Ph * ((1 + et) * (1 + d2) - 1) - Pt * ((1 + dl) * (1 + dl) * (1 + dl) * (1 + al) - 1)
  - th * th * ((1 + dl) * (1 + dl) - 1) * (s1 + s2 * th * th * (1 + (1 + dl) * (1 + dl)));
