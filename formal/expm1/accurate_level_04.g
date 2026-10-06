# Level 4 of expm1's small-argument series in Q128 (docs/expm1.md, section 4):
# H_4 = 1 + (x (1/4)) H_5 against X_4 = 1 + (x/4) X_5, given
# |H_5 - X_5| <= 526b-135. Written by generators/expm1_certificates.py.

Hn = Xn + En;
b = ((x * ((1 / 4) * (1 + kk))) * (1 + ma)) * Hn * (1 + mb);
H = 1 + b + s;
X = 1 + (x / 4) * Xn;

{ x in [-0.0312501, 0.0312501] /\ Xn in [0.983612882, 1.016516151]
  /\ En in [-526b-135, 526b-135]
  /\ kk in [-1b-127, 1b-127] /\ ma in [-1b-127, 0] /\ mb in [-1b-127, 0] /\ s in [-1b-126, 1b-126]
  -> H - X in [-528b-135, 528b-135] }

H - X -> (x / 4) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)) + s;
