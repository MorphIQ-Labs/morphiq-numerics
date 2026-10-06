# Level 5 of sin's Q256 series (docs/sin_cos.md, section 5):
# H_5 = 1 - (s c) H_6 against X_5 = 1 - s c X_6, c = 1/110,
# given |H_6 - X_6| <= 523b-263. Written by generators/trig_certificates.py.

Hn = Xn + En;
b = ((s * (1 / 110) * (1 + kk)) * (1 + ma)) * Hn * (1 + mb);
H = 1 - b + sa;
X = 1 - s * (1 / 110) * Xn;

{ s in [0, 0.61685] /\ Xn in [0.986085375, 1]
  /\ En in [-523b-263, 523b-263]
  /\ kk in [-1b-255, 1b-255] /\ ma in [-1b-255, 0] /\ mb in [-1b-255, 0] /\ sa in [-1b-254, 1b-254]
  -> H - X in [-525b-263, 525b-263] }

H - X -> -(s * (1 / 110)) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)) + sa;
