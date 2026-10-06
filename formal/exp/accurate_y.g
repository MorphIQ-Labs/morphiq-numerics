# The accurate path's result Y = T_j * H_1 against T_j * X_1
# (generators/exp_accurate_certificates.py).

H1 = X1 + E1;
Y = (Tj * (1 + eT)) * H1 * (1 + mY);

{ Tj in [1, 2] /\ X1 in [0.997, 1.003] /\ eT in [-1b-127, 1b-127] /\ mY in [-1b-127, 0]
  /\ E1 in [-521b-135, 521b-135]
  -> (Y - Tj * X1) / (Tj * X1) in [-1b-124, 1b-124] }

(Y - Tj * X1) / (Tj * X1) -> (1 + eT) * (1 + mY) * (1 + E1 / X1) - 1;
