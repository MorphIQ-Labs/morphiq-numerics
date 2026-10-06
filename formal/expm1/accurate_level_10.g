# Level 10 of expm1's small-argument series in Q128 (docs/expm1.md, section 4):
# H_10 = 1 + (x (1/10)) H_11 against X_10 = 1 + (x/10) X_11, given
# |H_11 - X_11| <= 521b-135. Written by generators/expm1_certificates.py.

Hn = Xn + En;
b = ((x * ((1 / 10) * (1 + kk))) * (1 + ma)) * Hn * (1 + mb);
H = 1 + b + s;
X = 1 + (x / 10) * Xn;

{ x in [-0.0312501, 0.0312501] /\ Xn in [0.987096765, 1.012961887]
  /\ En in [-521b-135, 521b-135]
  /\ kk in [-1b-127, 1b-127] /\ ma in [-1b-127, 0] /\ mb in [-1b-127, 0] /\ s in [-1b-126, 1b-126]
  -> H - X in [-522b-135, 522b-135] }

H - X -> (x / 10) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)) + s;
