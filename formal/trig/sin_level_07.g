# Level 7 of sin's Q256 series (docs/sin_cos.md, section 5):
# H_7 = 1 - (s c) H_8 against X_7 = 1 - s c X_8, c = 1/210,
# given |H_8 - X_8| <= 521b-263. Written by generators/trig_certificates.py.

Hn = Xn + En;
b = ((s * (1 / 210) * (1 + kk)) * (1 + ma)) * Hn * (1 + mb);
H = 1 - b + sa;
X = 1 - s * (1 / 210) * Xn;

{ s in [0, 0.61685] /\ Xn in [0.987754847, 1]
  /\ En in [-521b-263, 521b-263]
  /\ kk in [-1b-255, 1b-255] /\ ma in [-1b-255, 0] /\ mb in [-1b-255, 0] /\ sa in [-1b-254, 1b-254]
  -> H - X in [-521b-263, 521b-263] }

H - X -> -(s * (1 / 210)) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)) + sa;
