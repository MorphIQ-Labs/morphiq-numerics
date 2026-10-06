# Level 5 of expm1's small-argument series in Q128 (docs/expm1.md, section 4):
# H_5 = 1 + (x (1/5)) H_6 against X_5 = 1 + (x/5) X_6, given
# |H_6 - X_6| <= 524b-135. Written by generators/expm1_certificates.py.

Hn = Xn + En;
b = ((x * ((1 / 5) * (1 + kk))) * (1 + ma)) * Hn * (1 + mb);
H = 1 + b + s;
X = 1 + (x / 5) * Xn;

{ x in [-0.0312501, 0.0312501] /\ Xn in [0.984677402, 1.015430125]
  /\ En in [-524b-135, 524b-135]
  /\ kk in [-1b-127, 1b-127] /\ ma in [-1b-127, 0] /\ mb in [-1b-127, 0] /\ s in [-1b-126, 1b-126]
  -> H - X in [-526b-135, 526b-135] }

H - X -> (x / 5) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)) + s;
