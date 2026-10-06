# Level 12 of ln(1 + z)'s series in Q128 (docs/ln.md, section 6):
# G_12 = (1/12) - z G_13 against X_12 = 1/12 - z X_13, given
# |G_13 - X_13| <= 542b-135. Written by generators/ln_certificates.py.

Gn = Xn + En;
G = (1 / 12) * (1 + kk) - (z * Gn) * (1 + m) + s;
X = 1 / 12 - z * Xn;

{ z in [-0.0078126, 0.0078126] /\ Xn in [0.075601384, 0.078255931]
  /\ En in [-542b-135, 542b-135]
  /\ kk in [-1b-127, 1b-127] /\ m in [-1b-127, 0] /\ s in [-1b-126, 1b-126]
  -> G - X in [-544b-135, 544b-135] }

G - X -> (1 / 12) * kk - z * (En + Gn * m) + s;
