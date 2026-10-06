# Level 3 of ln(1 + z)'s series in Q128 (docs/ln.md, section 6):
# G_3 = (1/3) - z G_4 against X_3 = 1/3 - z X_4, given
# |G_4 - X_4| <= 587b-135. Written by generators/ln_certificates.py.

Gn = Xn + En;
G = (1 / 3) * (1 + kk) - (z * Gn) * (1 + m) + s;
X = 1 / 3 - z * Xn;

{ z in [-0.0078126, 0.0078126] /\ Xn in [0.245953105, 0.254078145]
  /\ En in [-587b-135, 587b-135]
  /\ kk in [-1b-127, 1b-127] /\ m in [-1b-127, 0] /\ s in [-1b-126, 1b-126]
  -> G - X in [-609b-135, 609b-135] }

G - X -> (1 / 3) * kk - z * (En + Gn * m) + s;
