# Stage B's polynomial evaluation (docs/exp.md, section 6), with every
# operation rounded to binary64, nearest-even:
#   q = r^2 * (1/2 + r*(d3 + r*(d4 + r*d5)))
# against the same polynomial evaluated exactly, for every binary64 r with
# |r| <= 0.00068. d3..d5 are the generated coefficients
# (generators/exp_poly.out). The bounds on the intermediates are what the
# transcription's finiteness needs (formal/exp/ExpStageB.v).

@rnd = float<ieee_64, ne>;

d3 = 0x1.5555555555554p-3;
d4 = 0x1.555555a38ed84p-5;
d5 = 0x1.11111177013d7p-7;

r = rnd(r_);
t4 rnd= d4 + r * d5;
t3 rnd= d3 + r * t4;
h  rnd= 0.5 + r * t3;
r2 rnd= r * r;
q  rnd= r2 * h;
Q = r * r * (0.5 + r * (d3 + r * (d4 + r * d5)));

{ r in [-0.00068, 0.00068]
  -> q - Q in [-1b-73, 1b-73] /\ q in [0, 1b-22]
     /\ t4 in [-1, 1] /\ t3 in [-1, 1] /\ h in [-1, 1] /\ r2 in [-1, 1] }
