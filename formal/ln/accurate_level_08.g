# Level 8 of ln(1 + z)'s series in Q128 (docs/ln.md, section 6):
# G_8 = (1/8) - z G_9 against X_8 = 1/8 - z X_9, given
# |G_9 - X_9| <= 551b-135. Written by generators/ln_certificates.py.

Gn = Xn + En;
G = (1 / 8) * (1 + kk) - (z * Gn) * (1 + m) + s;
X = 1 / 8 - z * Xn;

{ z in [-0.0078126, 0.0078126] /\ Xn in [0.109226553, 0.113011295]
  /\ En in [-551b-135, 551b-135]
  /\ kk in [-1b-127, 1b-127] /\ m in [-1b-127, 0] /\ s in [-1b-126, 1b-126]
  -> G - X in [-555b-135, 555b-135] }

G - X -> (1 / 8) * kk - z * (En + Gn * m) + s;
