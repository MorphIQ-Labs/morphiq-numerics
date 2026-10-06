# Level 14 of ln(1 + z)'s series in Q128 (docs/ln.md, section 6):
# G_14 = (1/14) - z G_15 against X_14 = 1/14 - z X_15, given
# |G_15 - X_15| <= 539b-135. Written by generators/ln_certificates.py.

Gn = Xn + En;
G = (1 / 14) * (1 + kk) - (z * Gn) * (1 + m) + s;
X = 1 / 14 - z * Xn;

{ z in [-0.0078126, 0.0078126] /\ Xn in [0.065516595, 0.067826504]
  /\ En in [-539b-135, 539b-135]
  /\ kk in [-1b-127, 1b-127] /\ m in [-1b-127, 0] /\ s in [-1b-126, 1b-126]
  -> G - X in [-540b-135, 540b-135] }

G - X -> (1 / 14) * kk - z * (En + Gn * m) + s;
