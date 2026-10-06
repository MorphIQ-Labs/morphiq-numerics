# Level 13 of ln(1 + z)'s series in Q128 (docs/ln.md, section 6):
# G_13 = (1/13) - z G_14 against X_13 = 1/13 - z X_14, given
# |G_14 - X_14| <= 540b-135. Written by generators/ln_certificates.py.

Gn = Xn + En;
G = (1 / 13) * (1 + kk) - (z * Gn) * (1 + m) + s;
X = 1 / 13 - z * Xn;

{ z in [-0.0078126, 0.0078126] /\ Xn in [0.070198654, 0.072668906]
  /\ En in [-540b-135, 540b-135]
  /\ kk in [-1b-127, 1b-127] /\ m in [-1b-127, 0] /\ s in [-1b-126, 1b-126]
  -> G - X in [-542b-135, 542b-135] }

G - X -> (1 / 13) * kk - z * (En + Gn * m) + s;
