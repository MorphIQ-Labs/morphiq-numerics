# Level 7 of expm1's small-argument series in Q128 (docs/expm1.md, section 4):
# H_7 = 1 + (x (1/7)) H_8 against X_7 = 1 + (x/7) X_8, given
# |H_8 - X_8| <= 523b-135. Written by generators/expm1_certificates.py.

Hn = Xn + En;
b = ((x * ((1 / 7) * (1 + kk))) * (1 + ma)) * Hn * (1 + mb);
H = 1 + b + s;
X = 1 + (x / 7) * Xn;

{ x in [-0.0312501, 0.0312501] /\ Xn in [0.986008051, 1.014072594]
  /\ En in [-523b-135, 523b-135]
  /\ kk in [-1b-127, 1b-127] /\ ma in [-1b-127, 0] /\ mb in [-1b-127, 0] /\ s in [-1b-126, 1b-126]
  -> H - X in [-523b-135, 523b-135] }

H - X -> (x / 7) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)) + s;
