# Level 8 of cos's Q256 series (docs/sin_cos.md, section 5):
# H_8 = 1 - (s c) H_9 against X_8 = 1 - s c X_9, c = 1/240,
# given |H_9 - X_9| <= 520b-263. Written by generators/trig_certificates.py.

Hn = Xn + En;
b = ((s * (1 / 240) * (1 + kk)) * (1 + ma)) * Hn * (1 + mb);
H = 1 - b + sa;
X = 1 - s * (1 / 240) * Xn;

{ s in [0, 0.61685] /\ Xn in [0.988004309, 1]
  /\ En in [-520b-263, 520b-263]
  /\ kk in [-1b-255, 1b-255] /\ ma in [-1b-255, 0] /\ mb in [-1b-255, 0] /\ sa in [-1b-254, 1b-254]
  -> H - X in [-521b-263, 521b-263] }

H - X -> -(s * (1 / 240)) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)) + sa;
