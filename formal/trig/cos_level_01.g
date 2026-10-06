# Level 1 of cos's Q256 series (docs/sin_cos.md, section 5):
# H_1 = 1 - (s c) H_2 against X_1 = 1 - s c X_2, c = 1/2,
# given |H_2 - X_2| <= 586b-263. Written by generators/trig_certificates.py.

Hn = Xn + En;
b = ((s * (1 / 2) * (1 + kk)) * (1 + ma)) * Hn * (1 + mb);
H = 1 - b + sa;
X = 1 - s * (1 / 2) * Xn;

{ s in [0, 0.61685] /\ Xn in [0.939109875, 1]
  /\ En in [-586b-263, 586b-263]
  /\ kk in [-1b-255, 1b-255] /\ ma in [-1b-255, 0] /\ mb in [-1b-255, 0] /\ sa in [-1b-254, 1b-254]
  -> H - X in [-939b-263, 939b-263] }

H - X -> -(s * (1 / 2)) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)) + sa;
