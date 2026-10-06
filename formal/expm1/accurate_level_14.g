# Level 14 of expm1's small-argument series in Q128 (docs/expm1.md, section 4):
# H_14 = 1 + (x (1/14)) H_15 against X_14 = 1 + (x/14) X_15, given
# |H_15 - X_15| <= 520b-135. Written by generators/expm1_certificates.py.

Hn = Xn + En;
b = ((x * ((1 / 14) * (1 + kk))) * (1 + ma)) * Hn * (1 + mb);
H = 1 + b + s;
X = 1 + (x / 14) * Xn;

{ x in [-0.0312501, 0.0312501] /\ Xn in [0.987870961, 1.012172050]
  /\ En in [-520b-135, 520b-135]
  /\ kk in [-1b-127, 1b-127] /\ ma in [-1b-127, 0] /\ mb in [-1b-127, 0] /\ s in [-1b-126, 1b-126]
  -> H - X in [-521b-135, 521b-135] }

H - X -> (x / 14) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)) + s;
