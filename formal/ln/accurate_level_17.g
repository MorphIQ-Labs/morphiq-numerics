# Level 17 of ln(1 + z)'s series in Q128 (docs/ln.md, section 6):
# G_17 = (1/17) - z G_18 against X_17 = 1/17 - z X_18, given
# |G_18 - X_18| <= 920b-141. Written by generators/ln_certificates.py.

Gn = Xn + En;
G = (1 / 17) * (1 + kk) - (z * Gn) * (1 + m) + s;
X = 1 / 17 - z * Xn;

{ z in [-0.0078126, 0.0078126] /\ Xn in [0.054592922, 0.056526412]
  /\ En in [-920b-141, 920b-141]
  /\ kk in [-1b-127, 1b-127] /\ m in [-1b-127, 0] /\ s in [-1b-126, 1b-126]
  -> G - X in [-533b-135, 533b-135] }

G - X -> (1 / 17) * kk - z * (En + Gn * m) + s;
