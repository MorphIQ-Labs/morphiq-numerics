# Level 16 of ln(1 + z)'s series in Q128 (docs/ln.md, section 6):
# G_16 = (1/16) - z G_17 against X_16 = 1/16 - z X_17, given
# |G_17 - X_17| <= 533b-135. Written by generators/ln_certificates.py.

Gn = Xn + En;
G = (1 / 16) * (1 + kk) - (z * Gn) * (1 + m) + s;
X = 1 / 16 - z * Xn;

{ z in [-0.0078126, 0.0078126] /\ Xn in [0.057805601, 0.059850138]
  /\ En in [-533b-135, 533b-135]
  /\ kk in [-1b-127, 1b-127] /\ m in [-1b-127, 0] /\ s in [-1b-126, 1b-126]
  -> G - X in [-538b-135, 538b-135] }

G - X -> (1 / 16) * kk - z * (En + Gn * m) + s;
