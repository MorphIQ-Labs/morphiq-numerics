# Level 4 of ln(1 + z)'s series in Q128 (docs/ln.md, section 6):
# G_4 = (1/4) - z G_5 against X_4 = 1/4 - z X_5, given
# |G_5 - X_5| <= 574b-135. Written by generators/ln_certificates.py.

Gn = Xn + En;
G = (1 / 4) * (1 + kk) - (z * Gn) * (1 + m) + s;
X = 1 / 4 - z * Xn;

{ z in [-0.0078126, 0.0078126] /\ Xn in [0.196710921, 0.203315121]
  /\ En in [-574b-135, 574b-135]
  /\ kk in [-1b-127, 1b-127] /\ m in [-1b-127, 0] /\ s in [-1b-126, 1b-126]
  -> G - X in [-587b-135, 587b-135] }

G - X -> (1 / 4) * kk - z * (En + Gn * m) + s;
