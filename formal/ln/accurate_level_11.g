# Level 11 of ln(1 + z)'s series in Q128 (docs/ln.md, section 6):
# G_11 = (1/11) - z G_12 against X_11 = 1/11 - z X_12, given
# |G_12 - X_12| <= 544b-135. Written by generators/ln_certificates.py.

Gn = Xn + En;
G = (1 / 11) * (1 + kk) - (z * Gn) * (1 + m) + s;
X = 1 / 11 - z * Xn;

{ z in [-0.0078126, 0.0078126] /\ Xn in [0.081905040, 0.084773646]
  /\ En in [-544b-135, 544b-135]
  /\ kk in [-1b-127, 1b-127] /\ m in [-1b-127, 0] /\ s in [-1b-126, 1b-126]
  -> G - X in [-546b-135, 546b-135] }

G - X -> (1 / 11) * kk - z * (En + Gn * m) + s;
