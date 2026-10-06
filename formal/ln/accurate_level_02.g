# Level 2 of ln(1 + z)'s series in Q128 (docs/ln.md, section 6):
# G_2 = (1/2) - z G_3 against X_2 = 1/2 - z X_3, given
# |G_3 - X_3| <= 609b-135. Written by generators/ln_certificates.py.

Gn = Xn + En;
G = (1 / 2) * (1 + kk) - (z * Gn) * (1 + m) + s;
X = 1 / 2 - z * Xn;

{ z in [-0.0078126, 0.0078126] /\ Xn in [0.328066382, 0.338639348]
  /\ En in [-609b-135, 609b-135]
  /\ kk in [-1b-127, 1b-127] /\ m in [-1b-127, 0] /\ s in [-1b-126, 1b-126]
  -> G - X in [-652b-135, 652b-135] }

G - X -> (1 / 2) * kk - z * (En + Gn * m) + s;
