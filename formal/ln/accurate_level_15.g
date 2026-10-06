# Level 15 of ln(1 + z)'s series in Q128 (docs/ln.md, section 6):
# G_15 = (1/15) - z G_16 against X_15 = 1/15 - z X_16, given
# |G_16 - X_16| <= 538b-135. Written by generators/ln_certificates.py.

Gn = Xn + En;
G = (1 / 15) * (1 + kk) - (z * Gn) * (1 + m) + s;
X = 1 / 15 - z * Xn;

{ z in [-0.0078126, 0.0078126] /\ Xn in [0.061420031, 0.063589160]
  /\ En in [-538b-135, 538b-135]
  /\ kk in [-1b-127, 1b-127] /\ m in [-1b-127, 0] /\ s in [-1b-126, 1b-126]
  -> G - X in [-539b-135, 539b-135] }

G - X -> (1 / 15) * kk - z * (En + Gn * m) + s;
