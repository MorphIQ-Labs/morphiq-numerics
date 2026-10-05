# The fast path's polynomial evaluation (docs/exp.md, section 4, step 1), with
# every operation rounded to binary64, nearest-even:
#   q = r^2 * (1/2 + r*(c3 + r*(c4 + r*(c5 + r*c6))))
# against the same polynomial evaluated exactly, for every binary64 r with
# |r| <= 0.0027077. c3..c6 are the generated coefficients (generators/exp_poly.out).

@rnd = float<ieee_64, ne>;

c3 = 0x1.555555555549p-3;
c4 = 0x1.55555555554bfp-5;
c5 = 0x1.111115b678249p-7;
c6 = 0x1.6c16c6fd917b6p-10;

r = rnd(r_);

t5 rnd= c5 + r * c6;
t4 rnd= c4 + r * t5;
t3 rnd= c3 + r * t4;
h  rnd= 0.5 + r * t3;
r2 rnd= r * r;
q  rnd= r2 * h;

T5 = c5 + r * c6;
T4 = c4 + r * T5;
T3 = c3 + r * T4;
H  = 0.5 + r * T3;
Q  = r * r * H;

{ r in [-0.0027077, 0.0027077] -> q - Q in [-1b-70, 1b-70] }
