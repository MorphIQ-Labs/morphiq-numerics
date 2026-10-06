# Level 20 of sin's Q256 series (docs/sin_cos.md, section 5):
# H_20 = 1 - (s c) H_21 against X_20 = 1 - s c X_21, c = 1/1640,
# given |H_21 - X_21| <= 518b-263. Written by generators/trig_certificates.py.

Hn = Xn + En;
b = ((s * (1 / 1640) * (1 + kk)) * (1 + ma)) * Hn * (1 + mb);
H = 1 - b + sa;
X = 1 - s * (1 / 1640) * Xn;

{ s in [0, 0.61685] /\ Xn in [0.989661860, 1]
  /\ En in [-518b-263, 518b-263]
  /\ kk in [-1b-255, 1b-255] /\ ma in [-1b-255, 0] /\ mb in [-1b-255, 0] /\ sa in [-1b-254, 1b-254]
  -> H - X in [-518b-263, 518b-263] }

H - X -> -(s * (1 / 1640)) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)) + sa;
