# Level 19 of cos's Q256 series (docs/sin_cos.md, section 5):
# H_19 = 1 - (s c) H_20 against X_19 = 1 - s c X_20, c = 1/1406,
# given |H_20 - X_20| <= 518b-263. Written by generators/trig_certificates.py.

Hn = Xn + En;
b = ((s * (1 / 1406) * (1 + kk)) * (1 + ma)) * Hn * (1 + mb);
H = 1 - b + sa;
X = 1 - s * (1 / 1406) * Xn;

{ s in [0, 0.61685] /\ Xn in [0.989608537, 1]
  /\ En in [-518b-263, 518b-263]
  /\ kk in [-1b-255, 1b-255] /\ ma in [-1b-255, 0] /\ mb in [-1b-255, 0] /\ sa in [-1b-254, 1b-254]
  -> H - X in [-518b-263, 518b-263] }

H - X -> -(s * (1 / 1406)) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)) + sa;
