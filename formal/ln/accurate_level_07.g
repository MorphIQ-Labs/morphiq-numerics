# Level 7 of ln(1 + z)'s series in Q128 (docs/ln.md, section 6):
# G_7 = (1/7) - z G_8 against X_7 = 1/7 - z X_8, given
# |G_8 - X_8| <= 555b-135. Written by generators/ln_certificates.py.

Gn = Xn + En;
G = (1 / 7) * (1 + kk) - (z * Gn) * (1 + m) + s;
X = 1 / 7 - z * Xn;

{ z in [-0.0078126, 0.0078126] /\ Xn in [0.122890614, 0.127126747]
  /\ En in [-555b-135, 555b-135]
  /\ kk in [-1b-127, 1b-127] /\ m in [-1b-127, 0] /\ s in [-1b-126, 1b-126]
  -> G - X in [-559b-135, 559b-135] }

G - X -> (1 / 7) * kk - z * (En + Gn * m) + s;
