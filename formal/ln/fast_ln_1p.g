# ln_1p's general fast path (docs/ln.md, section 7), |x| >= 2^-7.
# q = l/h, delta = ln(1+q), v = ln(1+x), and ln h = v-delta.
# The split gives |q| <= 2^-52 and |v| >= 2^-8. Binary64 rounding
# gives |RN(q)-q| <= 2^-104, including subnormal quotients. Together
# with |ln(1+q)-q| <= 2^-102, this gives |(RN(q)-delta)/v| <= 2^-93.
# Thus kd=delta/v and ed=(RN(q)-delta)/v cover gradual underflow.
# Ln1pFastGeneral.v proves these bounds from the executable split and division.
# Written by generators/ln_certificates.py.

kw = 1 - kd;
Y = (kw * (1 + eh) + kd + ed) * (1 + e3);

{ kd in [-1b-43, 1b-43] /\ ed in [-1b-93, 1b-93] /\ eh in [-1b-64, 1b-64]
  /\ e3 in [-1b-105, 1b-105]
  -> Y - 1 in [-1b-63, 1b-63] }

Y - 1 -> (kw * eh + ed) * (1 + e3) + e3;
