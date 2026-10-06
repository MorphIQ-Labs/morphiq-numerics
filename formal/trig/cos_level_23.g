# Level 23 of cos's Q256 series (docs/sin_cos.md, section 5):
# H_23 = 1 - (s c) H_24 against X_23 = 1 - s c X_24, c = 1/2070,
# given |H_24 - X_24| <= 0. Written by generators/trig_certificates.py.

Hn = Xn + En;
b = ((s * (1 / 2070) * (1 + kk)) * (1 + ma)) * Hn * (1 + mb);
H = 1 - b + sa;
X = 1 - s * (1 / 2070) * Xn;

{ s in [0, 0.61685] /\ Xn in [0.989729308, 1]
  /\ En in [-0, 0]
  /\ kk in [-1b-255, 1b-255] /\ ma in [-1b-255, 0] /\ mb in [-1b-255, 0] /\ sa in [-1b-254, 1b-254]
  -> H - X in [-518b-263, 518b-263] }

H - X -> -(s * (1 / 2070)) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)) + sa;
