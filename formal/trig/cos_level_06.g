# Level 6 of cos's Q256 series (docs/sin_cos.md, section 5):
# H_6 = 1 - (s c) H_7 against X_6 = 1 - s c X_7, c = 1/132,
# given |H_7 - X_7| <= 522b-263. Written by generators/trig_certificates.py.

Hn = Xn + En;
b = ((s * (1 / 132) * (1 + kk)) * (1 + ma)) * Hn * (1 + mb);
H = 1 - b + sa;
X = 1 - s * (1 / 132) * Xn;

{ s in [0, 0.61685] /\ Xn in [0.986644607, 1]
  /\ En in [-522b-263, 522b-263]
  /\ kk in [-1b-255, 1b-255] /\ ma in [-1b-255, 0] /\ mb in [-1b-255, 0] /\ sa in [-1b-254, 1b-254]
  -> H - X in [-524b-263, 524b-263] }

H - X -> -(s * (1 / 132)) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)) + sa;
