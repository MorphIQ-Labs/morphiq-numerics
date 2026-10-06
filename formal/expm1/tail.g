# expm1's small-argument tail (docs/expm1.md, section 3): with x a binary64,
# 1b-54 <= |x| <= 0.0312501,
#   w = c3 + x*(c4 + ... + x*c9),  x3 = RN(x * RN(x^2)),  t = RN(x3 * w)
# rounded to binary64, nearest-even, against x^3 W(x) evaluated exactly.
# Written by generators/expm1_certificates.py.

@rnd = float<ieee_64, ne>;

c3 = 0x1.5555555555555p-3;
c4 = 0x1.5555555555559p-5;
c5 = 0x1.111111111bbb8p-7;
c6 = 0x1.6c16c16b1d8abp-10;
c7 = 0x1.a019ec4b15b4p-13;
c8 = 0x1.a01c0085130ccp-16;
c9 = 0x1.7e0fb35411f23p-19;

x = rnd(x_);

w8 rnd= c8 + x * c9;
w7 rnd= c7 + x * w8;
w6 rnd= c6 + x * w7;
w5 rnd= c5 + x * w6;
w4 rnd= c4 + x * w5;
w  rnd= c3 + x * w4;
sh rnd= x * x;
x3 rnd= x * sh;
t  rnd= x3 * w;

W = (c3 + x * (c4 + x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9))))));
T = x * x * x * W;

{ |x| in [1b-54, 0.0312501] -> (t - T) / T in [-1b-50, 1b-50] }

(t - T) / T -> (1 + (x3 - x * x * x) / (x * x * x)) * (1 + (w - W) / W) * (1 + (t - x3 * w) / (x3 * w)) - 1;
(x3 - x * x * x) / (x * x * x) -> (1 + (sh - x * x) / (x * x)) * (1 + (x3 - x * sh) / (x * sh)) - 1;
