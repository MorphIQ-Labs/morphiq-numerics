# Q256::recip's Newton step 1 (docs/sin_cos.md, section 8), with c y = 1 + e,
# |e| <= 518b-61 (formal/trig/recip_0.g):
#   p = c.mul(y)          truncated: (1 + e)(1 + m1)
#   g = ONE.add(p.neg())  within 2^-254 max(1, |p|) <= 2^-254 (1 + |e|): s1
#   q = y.mul(g)          truncated: (1 + m2)
#   y' = y.add(q)         within 2^-254 max(|y|, |q|) = 2^-254 |y|: s2, relative to y
# so c y' = (1 + e)(1 + g (1 + m2) + s2). Written by generators/trig_certificates.py.

G = 1 - (1 + e) * (1 + m1) + s1;
P = (1 + e) * (1 + G * (1 + m2) + s2);

{ e in [-518b-61, 518b-61] /\ m1 in [-1b-255, 0] /\ m2 in [-1b-255, 0]
  /\ s1 in [-518b-263, 518b-263] /\ s2 in [-1b-254, 1b-254]
  -> P - 1 in [-530b-113, 530b-113] }

P - 1 -> -e * m2 - e * e * (1 + m2) + (1 + e) * (1 + m2) * (s1 - (1 + e) * m1) + (1 + e) * s2;
