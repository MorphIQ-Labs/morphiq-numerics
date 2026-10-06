# Level 9 of ln(1 + z)'s series in Q128 (docs/ln.md, section 6):
# G_9 = (1/9) - z G_10 against X_9 = 1/9 - z X_10, given
# |G_10 - X_10| <= 548b-135. Written by generators/ln_certificates.py.

Gn = Xn + En;
G = (1 / 9) * (1 + kk) - (z * Gn) * (1 + m) + s;
X = 1 / 9 - z * Xn;

{ z in [-0.0078126, 0.0078126] /\ Xn in [0.098296866, 0.101717339]
  /\ En in [-548b-135, 548b-135]
  /\ kk in [-1b-127, 1b-127] /\ m in [-1b-127, 0] /\ s in [-1b-126, 1b-126]
  -> G - X in [-551b-135, 551b-135] }

G - X -> (1 / 9) * kk - z * (En + Gn * m) + s;
