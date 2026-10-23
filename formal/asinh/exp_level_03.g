# Level 3 of the exponential's Q256 series (docs/asinh.md, section 4):
# H_3 = 1 + (r c) H_4 against X_3 = 1 + r c X_4, c = 1/3,
# given |H_4 - X_4| <= 618b-262. Q256 products are truncated toward zero
# (relative [-2^-255, 0]), the constant c is within 2^-255 relatively, and a sum
# is within 2^-254 of its larger operand (here at most 1.42: 2^-253).
# Written by generators/asinh_certificates.py.

Hn = Xn + En;
b = ((r * (1 / 3) * (1 + kk)) * (1 + ma)) * Hn * (1 + mb);
H = 1 + b + sa;
X = 1 + r * (1 / 3) * Xn;

{ r in [-0.3467, 0.3467] /\ Xn in [0.7, 1.42]
  /\ En in [-618b-262, 618b-262]
  /\ kk in [-1b-255, 1b-255] /\ ma in [-1b-255, 0] /\ mb in [-1b-255, 0] /\ sa in [-1b-253, 1b-253]
  -> H - X in [-653b-262, 653b-262] }

H - X -> (r * (1 / 3)) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)) + sa;
