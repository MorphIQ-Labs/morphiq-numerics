# Level 1 of ln(1 + z)'s series in Q128 (docs/ln.md, section 6):
# G_1 = (1/1) - z G_2 against X_1 = 1/1 - z X_2, given
# |G_2 - X_2| <= 652b-135. Written by generators/ln_certificates.py.

Gn = Xn + En;
G = (1 / 1) * (1 + kk) - (z * Gn) * (1 + m) + s;
X = 1 / 1 - z * Xn;

{ z in [-0.0078126, 0.0078126] /\ Xn in [0.492421842, 0.507630242]
  /\ En in [-652b-135, 652b-135]
  /\ kk in [-1b-127, 1b-127] /\ m in [-1b-127, 0] /\ s in [-1b-126, 1b-126]
  -> G - X in [-782b-135, 782b-135] }

G - X -> (1 / 1) * kk - z * (En + Gn * m) + s;
