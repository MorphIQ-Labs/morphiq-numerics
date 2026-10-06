# Level 16 of expm1's small-argument series in Q128 (docs/expm1.md, section 4):
# H_16 = 1 + (x (1/16)) H_17 against X_16 = 1 + (x/16) X_17, given
# |H_17 - X_17| <= 0. Written by generators/expm1_certificates.py.

Hn = Xn + En;
b = ((x * ((1 / 16) * (1 + kk))) * (1 + ma)) * Hn * (1 + mb);
H = 1 + b + s;
X = 1 + (x / 16) * Xn;

{ x in [-0.0312501, 0.0312501] /\ Xn in [0.988121436, 1.011916515]
  /\ En in [-0, 0]
  /\ kk in [-1b-127, 1b-127] /\ ma in [-1b-127, 0] /\ mb in [-1b-127, 0] /\ s in [-1b-126, 1b-126]
  -> H - X in [-519b-135, 519b-135] }

H - X -> (x / 16) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)) + s;
