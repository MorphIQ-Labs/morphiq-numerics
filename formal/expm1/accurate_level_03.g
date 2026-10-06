# Level 3 of expm1's small-argument series in Q128 (docs/expm1.md, section 4):
# H_3 = 1 + (x (1/3)) H_4 against X_3 = 1 + (x/3) X_4, given
# |H_4 - X_4| <= 528b-135. Written by generators/expm1_certificates.py.

Hn = Xn + En;
b = ((x * ((1 / 3) * (1 + kk))) * (1 + ma)) * Hn * (1 + mb);
H = 1 + b + s;
X = 1 + (x / 3) * Xn;

{ x in [-0.0312501, 0.0312501] /\ Xn in [0.982016103, 1.018145188]
  /\ En in [-528b-135, 528b-135]
  /\ kk in [-1b-127, 1b-127] /\ ma in [-1b-127, 0] /\ mb in [-1b-127, 0] /\ s in [-1b-126, 1b-126]
  -> H - X in [-531b-135, 531b-135] }

H - X -> (x / 3) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)) + s;
