# Level 5 of ln(1 + z)'s series in Q128 (docs/ln.md, section 6):
# G_5 = (1/5) - z G_6 against X_5 = 1/5 - z X_6, given
# |G_6 - X_6| <= 565b-135. Written by generators/ln_certificates.py.

Gn = Xn + En;
G = (1 / 5) * (1 + kk) - (z * Gn) * (1 + m) + s;
X = 1 / 5 - z * Xn;

{ z in [-0.0078126, 0.0078126] /\ Xn in [0.163895075, 0.169460580]
  /\ En in [-565b-135, 565b-135]
  /\ kk in [-1b-127, 1b-127] /\ m in [-1b-127, 0] /\ s in [-1b-126, 1b-126]
  -> G - X in [-574b-135, 574b-135] }

G - X -> (1 / 5) * kk - z * (En + Gn * m) + s;
