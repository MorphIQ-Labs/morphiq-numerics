# Rounded Horner evaluation of the generated log-tail correction table.
@rnd = float<ieee_64,ne>;
p6 = rnd(c6+rnd(d*c7));
p5 = rnd(c5+rnd(d*p6));
p4 = rnd(c4+rnd(d*p5));
p3 = rnd(c3+rnd(d*p4));
p2 = rnd(c2+rnd(d*p3));
p1 = rnd(c1+rnd(d*p2));
c = rnd(c0+rnd(d*p1));
P = c0+d*(c1+d*(c2+d*(c3+d*(c4+d*(c5+d*(c6+d*c7))))));
{d in [-0.5,0.5] /\ c0 in [4,6] /\ c1 in [0,0.03] /\ c2 in [-0.0004,0] /\ c3 in [0,0.000007] /\ c4 in [-0.00000013,0] /\ c5 in [0,0.000000003] /\ c6 in [-0.00000000007,0] /\ c7 in [0,0.000000000002] -> c-P in [-9b-54,9b-54] /\ c in [3,7]}
