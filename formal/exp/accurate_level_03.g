# Level 3 of the accurate path's series (generators/exp_accurate_certificates.py).

Hn = Xn + En;
b = ((r * ((1 / 3) * (1 + k))) * (1 + ma)) * Hn * (1 + mb);
H = 1 + b + s;
X = 1 + (r / 3) * Xn;

{ r in [-0.0027078, 0.0027078] /\ Xn in [0.99, 1.01]
  /\ En in [-519b-135, 519b-135]
  /\ k in [-1b-127, 1b-127] /\ ma in [-1b-127, 0] /\ mb in [-1b-127, 0]
  /\ s in [-1b-126, 1b-126]
  -> H - X in [-519b-135, 519b-135] }

H - X -> (r / 3) * (En + Hn * ((1 + k) * (1 + ma) * (1 + mb) - 1)) + s;
