# Level 3 of cos's Q256 series (docs/sin_cos.md, section 5):
# H_3 = 1 - (s c) H_4 against X_3 = 1 - s c X_4, c = 1/30,
# given |H_4 - X_4| <= 532b-263. Written by generators/trig_certificates.py.

Hn = Xn + En;
b = ((s * (1 / 30) * (1 + kk)) * (1 + ma)) * Hn * (1 + mb);
H = 1 - b + sa;
X = 1 - s * (1 / 30) * Xn;

{ s in [0, 0.61685] /\ Xn in [0.979094973, 1]
  /\ En in [-532b-263, 532b-263]
  /\ kk in [-1b-255, 1b-255] /\ ma in [-1b-255, 0] /\ mb in [-1b-255, 0] /\ sa in [-1b-254, 1b-254]
  -> H - X in [-545b-263, 545b-263] }

H - X -> -(s * (1 / 30)) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)) + sa;
