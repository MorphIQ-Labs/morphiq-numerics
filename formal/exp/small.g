# The accurate path for small arguments, 2^-54 <= |x| < 2^-30 (docs/exp.md,
# section 6): d = e^x - 1 - x to degree 5, in Horner form
#   d = (x * x * k2) * (1 + (x * k3) * (1 + (x * k4) * (1 + x * k5)))
# in 128-bit significand arithmetic (Q128), against the same expression
# evaluated exactly. Each Q128 operation is modelled by its contract:
# multiplication relative error in [-2^-127, 0]; addition absolute error at
# most 2^-126 * max(|a|, |b|), here max = 1. k_i = 1/i with relative error
# below 2^-127 (generators/exp_constants.py).

g5 = 1 + ((x * ((1 / 5) * (1 + k5))) * (1 + m5)) + s5;
g4 = 1 + ((x * ((1 / 4) * (1 + k4))) * (1 + m4a)) * g5 * (1 + m4b) + s4;
g3 = 1 + ((x * ((1 / 3) * (1 + k3))) * (1 + m3a)) * g4 * (1 + m3b) + s3;
d = (((x * x) * (1 + m2a)) * ((1 / 2) * (1 + k2))) * (1 + m2b) * g3 * (1 + m2c);

G5 = 1 + x / 5;
G4 = 1 + (x / 4) * G5;
G3 = 1 + (x / 3) * G4;
D = (x * x / 2) * G3;

{ x in [-1b-30, 1b-30] /\ x <> 0
  /\ k2 in [-1b-127, 1b-127] /\ k3 in [-1b-127, 1b-127] /\ k4 in [-1b-127, 1b-127] /\ k5 in [-1b-127, 1b-127]
  /\ m5 in [-1b-127, 0] /\ m4a in [-1b-127, 0] /\ m4b in [-1b-127, 0] /\ m3a in [-1b-127, 0] /\ m3b in [-1b-127, 0]
  /\ m2a in [-1b-127, 0] /\ m2b in [-1b-127, 0] /\ m2c in [-1b-127, 0]
  /\ s5 in [-1b-126, 1b-126] /\ s4 in [-1b-126, 1b-126] /\ s3 in [-1b-126, 1b-126]
  -> (d - D) / D in [-1b-122, 1b-122] }

g5 - G5 -> (x / 5) * ((1 + k5) * (1 + m5) - 1) + s5;
g4 - G4 -> (x / 4) * ((g5 - G5) + g5 * ((1 + k4) * (1 + m4a) * (1 + m4b) - 1)) + s4;
g3 - G3 -> (x / 3) * ((g4 - G4) + g4 * ((1 + k3) * (1 + m3a) * (1 + m3b) - 1)) + s3;
(d - D) / D -> (1 + m2a) * (1 + k2) * (1 + m2b) * (1 + m2c) * (1 + (g3 - G3) / G3) - 1
  { D <> 0, G3 <> 0 };
