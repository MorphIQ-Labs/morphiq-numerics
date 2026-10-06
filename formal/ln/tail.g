# The fast path's cubic tail for ln(1 + z) (docs/ln.md, section 4): with z_hi
# a binary64, 1b-64 <= |z_hi| <= 0.0078126,
#   w = c3 + z_hi*(c4 + ... + z_hi*c9),  z3 = RN(z_hi * RN(z_hi^2)),  t = RN(z3 * w)
# rounded to binary64, nearest-even, against z_hi^3 * W(z_hi) evaluated exactly.
# Written by generators/ln_certificates.py.

@rnd = float<ieee_64, ne>;

c3 = 0x1.5555555555555p-2;
c4 = -0x1.000000000002dp-2;
c5 = 0x1.99999999aef53p-3;
c6 = -0x1.5555554a1cd18p-3;
c7 = 0x1.24923e6ed17a8p-3;
c8 = -0x1.00059a9bca3b7p-3;
c9 = 0x1.ca33216abd50bp-4;

zh = rnd(zh_);

w8 rnd= c8 + zh * c9;
w7 rnd= c7 + zh * w8;
w6 rnd= c6 + zh * w7;
w5 rnd= c5 + zh * w6;
w4 rnd= c4 + zh * w5;
w  rnd= c3 + zh * w4;
sh rnd= zh * zh;
z3 rnd= zh * sh;
t  rnd= z3 * w;

W = (c3 + zh * (c4 + zh * (c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9))))));
T = zh * zh * zh * W;

{ |zh| in [1b-64, 0.0078126] -> (t - T) / T in [-1b-50, 1b-50] }

# t / T = (1 + e_z3) (1 + e_w) (1 + e_t), the relative errors of z3, w and the
# last product.
(t - T) / T -> (1 + (z3 - zh * zh * zh) / (zh * zh * zh)) * (1 + (w - W) / W) * (1 + (t - z3 * w) / (z3 * w)) - 1
  { T <> 0, zh <> 0, W <> 0, z3 <> 0, w <> 0 };
(z3 - zh * zh * zh) / (zh * zh * zh) -> (1 + (sh - zh * zh) / (zh * zh)) * (1 + (z3 - zh * sh) / (zh * sh)) - 1
  { zh <> 0, sh <> 0 };
