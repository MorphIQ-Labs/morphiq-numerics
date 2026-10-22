# The logarithmic form's square root as a double-word (docs/asinh.md, section 3):
# u = uh + ul is the double-word 1 + x^2 (uh = RN(uh + ul), so |ul| <= 2^-53 uh),
# U = uh + ul = w^2 its exact value, root a binary64 with e = root - w, |e| <=
# 2^-51 (root = RN(sqrt(uh)), sqrt(uh) within 2^-54 of w relatively, the rounding
# of root at most 2^-52), (ph, pl) = two_prod(root, root) so ph + pl = root^2 and
# |pl| <= 2^-53 ph, r1 = uh - ph, r2 = r1 - pl, r3 = r2 + ul, corr = r3/(2 root),
# s = root + corr exactly (two_sum). Each of r1, r2, r3 and corr is one binary64
# operation, a relative error a1..a4 of at most 2^-53 (every value is normal). With
# e = root - w, U - root^2 = -e (root + w), so root + (U - root^2)/(2 root) - w =
# e^2/(2 root); the other terms are the four roundings. Every operation commutes
# with scaling u by 4^k (no subnormal or overflow for w between 1 and 2^29), so
# w in [1, 2] covers every w the logarithmic form reaches. Written by
# generators/asinh_certificates.py.

w = w_;
root = w + e;
uh = (w * w) / (1 + ulr);
ul = uh * ulr;
ph = (root * root) / (1 + plr);
pl = ph * plr;
r1 = (uh - ph) * (1 + a1);
r2 = (r1 - pl) * (1 + a2);
r3 = (r2 + ul) * (1 + a3);
s2 = 2 * root;
corr = (r3 / s2) * (1 + a4);
sv = root + corr;

{ w_ in [1, 2] /\ e in [-1b-51, 1b-51] /\ ulr in [-1b-53, 1b-53] /\ plr in [-1b-53, 1b-53]
  /\ a1 in [-1b-53, 1b-53] /\ a2 in [-1b-53, 1b-53] /\ a3 in [-1b-53, 1b-53] /\ a4 in [-1b-53, 1b-53]
  -> (sv - w) / w in [-1b-100, 1b-100] }

uh - ph -> -ul - e * (w + root) + pl { 1 + ulr <> 0, 1 + plr <> 0 };
(sv - w) / w -> (e * e / s2 + (uh - ph) * a1 / s2 + (r1 - pl) * a2 / s2 + (r2 + ul) * a3 / s2 + r3 * a4 / s2) / w { w <> 0, root <> 0, 1 + ulr <> 0, 1 + plr <> 0 };
