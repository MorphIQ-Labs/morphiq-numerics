# The accurate path's Newton step for x <= SPLIT (docs/asin.md, section 5):
#   y1 = y0 + (x - sin y0)/cos y0
# in Q256 from y0 = Y (1 + eta), Y = asin x in [2^-26, pi/4), against Y, relative.
#   x = sin Y = s0 + c0 d + R, d = Y - y0, R = -rr d^2   (Taylor, rr in [-2^-60, 0.5000001], formal/asin/AsinFacts.v)
#   S = s0 (1 + sigma); rho = (x - S) + ea mx; ri = (1 + e)/(c0 (1 + gamma))
#   q = (rho ri)(1 + m); y1 = (y0 + q) + eb y0
# so (y1 - Y)/Y = -eta kk + (t2 + t3 + t4)(1 + kk) + eb (1 + eta) with
# kk = (1 + e)(1 + m)/(1 + gamma) - 1 and t2 = R/(c0 Y), t3 = -s0 sigma/(c0 Y),
# t4 = ea mx/(c0 Y): the quadratic term t2 dominates.
# Hypotheses certified elsewhere or exact: eta, the start's relative error, is at
# most eps1 = 2^-62 (the fast path's bound, formal/asin/compose_*.g and
# complement.g, asserted by generators/asin_certificates.py; the start is
# y_hi + y_lo added in Q256, which errs by at most 2^-254 more); sigma and gamma,
# sin's and cos's relative errors at an exact argument, 1b-198
# (formal/trig/accurate_sin.g, accurate_cos.g, whose reduction term is zero here);
# e, Q256::recip's c y = 1 + e (formal/trig/recip_3.g); m, a Q256 product's
# truncation, [-2^-255, 0]; ea and eb, a Q256 sum's error, 2^-254 of its larger
# operand (docs/sin_cos.md, section 5). The Taylor remainder, the argument ranges
# and sin t/t >= 0.89 are proved in Coq in formal/asin/AsinFacts.v
# (taylor_sin, taylor_cos, quarter_pi_ranges, sin_ratio, sin_split_range,
# cos_split_range, y_lower, d_lower). Written by generators/asin_certificates.py.

y0 = Y * (1 + eta);
d = Y - y0;
R = -rr * d * d;
x = s0 + c0 * d + R;
S = s0 * (1 + sigma);
rho = (x - S) + ea * mx;
ri = (1 + e) / (c0 * (1 + gamma));
q = (rho * ri) * (1 + m);
y1 = (y0 + q) + eb * y0;
kk = (1 + e) * (1 + m) / (1 + gamma) - 1;
t2 = -rr * Y * eta * eta / c0;
t3 = -s0 * sigma / (c0 * Y);
t4 = ea * mx / (c0 * Y);

{ Y in [1b-26, 0.7854] /\ eta in [-1b-62, 1b-62] /\ s0 in [0, 0.7072] /\ c0 in [0.7071, 1]
  /\ rr in [-1b-60, 0.5000001] /\ sigma in [-1b-198, 1b-198] /\ gamma in [-1b-198, 1b-198]
  /\ ea in [-1b-254, 1b-254] /\ mx in [0, 0.7072] /\ e in [-650b-262, 650b-262] /\ m in [-1b-255, 0]
  /\ eb in [-1b-254, 1b-254]
  -> (y1 - Y) / Y in [-1b-124, 1b-124] }

(y1 - Y) / Y -> -eta * kk + (t2 + t3 + t4) * (1 + kk) + eb * (1 + eta) { Y <> 0, c0 <> 0, 1 + gamma <> 0 };
