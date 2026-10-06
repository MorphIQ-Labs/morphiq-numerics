# Level 11 of sin's Q256 series (docs/sin_cos.md, section 5):
# H_11 = 1 - (s c) H_12 against X_11 = 1 - s c X_12, c = 1/506,
# given |H_12 - X_12| <= 519b-263. Written by generators/trig_certificates.py.

Hn = Xn + En;
b = ((s * (1 / 506) * (1 + kk)) * (1 + ma)) * Hn * (1 + mb);
H = 1 - b + sa;
X = 1 - s * (1 / 506) * Xn;

{ s in [0, 0.61685] /\ Xn in [0.988982197, 1]
  /\ En in [-519b-263, 519b-263]
  /\ kk in [-1b-255, 1b-255] /\ ma in [-1b-255, 0] /\ mb in [-1b-255, 0] /\ sa in [-1b-254, 1b-254]
  -> H - X in [-519b-263, 519b-263] }

H - X -> -(s * (1 / 506)) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)) + sa;
