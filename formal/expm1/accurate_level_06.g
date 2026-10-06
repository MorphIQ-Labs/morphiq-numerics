# Level 6 of expm1's small-argument series in Q128 (docs/expm1.md, section 4):
# H_6 = 1 + (x (1/6)) H_7 against X_6 = 1 + (x/6) X_7, given
# |H_7 - X_7| <= 523b-135. Written by generators/expm1_certificates.py.

Hn = Xn + En;
b = ((x * ((1 / 6) * (1 + kk))) * (1 + ma)) * Hn * (1 + mb);
H = 1 + b + s;
X = 1 + (x / 6) * Xn;

{ x in [-0.0312501, 0.0312501] /\ Xn in [0.985437773, 1.014654393]
  /\ En in [-523b-135, 523b-135]
  /\ kk in [-1b-127, 1b-127] /\ ma in [-1b-127, 0] /\ mb in [-1b-127, 0] /\ s in [-1b-126, 1b-126]
  -> H - X in [-524b-135, 524b-135] }

H - X -> (x / 6) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)) + s;
