# Level 2 of expm1's small-argument series in Q128 (docs/expm1.md, section 4):
# H_2 = 1 + (x (1/2)) H_3 against X_2 = 1 + (x/2) X_3, given
# |H_3 - X_3| <= 531b-135. Written by generators/expm1_certificates.py.

Hn = Xn + En;
b = ((x * ((1 / 2) * (1 + kk))) * (1 + ma)) * Hn * (1 + mb);
H = 1 + b + s;
X = 1 + (x / 2) * Xn;

{ x in [-0.0312501, 0.0312501] /\ Xn in [0.979354804, 1.020860251]
  /\ En in [-531b-135, 531b-135]
  /\ kk in [-1b-127, 1b-127] /\ ma in [-1b-127, 0] /\ mb in [-1b-127, 0] /\ s in [-1b-126, 1b-126]
  -> H - X in [-538b-135, 538b-135] }

H - X -> (x / 2) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)) + s;
