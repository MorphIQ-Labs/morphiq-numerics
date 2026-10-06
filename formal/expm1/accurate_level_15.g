# Level 15 of expm1's small-argument series in Q128 (docs/expm1.md, section 4):
# H_15 = 1 + (x (1/15)) H_16 against X_15 = 1 + (x/15) X_16, given
# |H_16 - X_16| <= 519b-135. Written by generators/expm1_certificates.py.

Hn = Xn + En;
b = ((x * ((1 / 15) * (1 + kk))) * (1 + ma)) * Hn * (1 + mb);
H = 1 + b + s;
X = 1 + (x / 15) * Xn;

{ x in [-0.0312501, 0.0312501] /\ Xn in [0.988004026, 1.012036297]
  /\ En in [-519b-135, 519b-135]
  /\ kk in [-1b-127, 1b-127] /\ ma in [-1b-127, 0] /\ mb in [-1b-127, 0] /\ s in [-1b-126, 1b-126]
  -> H - X in [-520b-135, 520b-135] }

H - X -> (x / 15) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)) + s;
