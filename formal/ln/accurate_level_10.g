# Level 10 of ln(1 + z)'s series in Q128 (docs/ln.md, section 6):
# G_10 = (1/10) - z G_11 against X_10 = 1/10 - z X_11, given
# |G_11 - X_11| <= 546b-135. Written by generators/ln_certificates.py.

Gn = Xn + En;
G = (1 / 10) * (1 + kk) - (z * Gn) * (1 + m) + s;
X = 1 / 10 - z * Xn;

{ z in [-0.0078126, 0.0078126] /\ Xn in [0.089355460, 0.092475742]
  /\ En in [-546b-135, 546b-135]
  /\ kk in [-1b-127, 1b-127] /\ m in [-1b-127, 0] /\ s in [-1b-126, 1b-126]
  -> G - X in [-548b-135, 548b-135] }

G - X -> (1 / 10) * kk - z * (En + Gn * m) + s;
