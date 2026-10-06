# Level 6 of ln(1 + z)'s series in Q128 (docs/ln.md, section 6):
# G_6 = (1/6) - z G_7 against X_6 = 1/6 - z X_7, given
# |G_7 - X_7| <= 559b-135. Written by generators/ln_certificates.py.

Gn = Xn + En;
G = (1 / 6) * (1 + kk) - (z * Gn) * (1 + m) + s;
X = 1 / 6 - z * Xn;

{ z in [-0.0078126, 0.0078126] /\ Xn in [0.140461762, 0.145272055]
  /\ En in [-559b-135, 559b-135]
  /\ kk in [-1b-127, 1b-127] /\ m in [-1b-127, 0] /\ s in [-1b-126, 1b-126]
  -> G - X in [-565b-135, 565b-135] }

G - X -> (1 / 6) * kk - z * (En + Gn * m) + s;
