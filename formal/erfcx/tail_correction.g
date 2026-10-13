# Direct IEEE reciprocal, square and correction, including underflow.
@rnd = float<ieee_64, ne>;
y = rnd(Y);
t = rnd(y*y);
v = rnd((3/4)-rnd((15/8)*t));
w = rnd(-(1/2)+rnd(t*v));
u = rnd(t*w);
T = Y*Y;
P = T*(-(1/2)+T*((3/4)-(15/8)*T));
{ Y in [0,1b-9] -> u-P in [-1b-69,1b-69]
 /\ y in [0,1b-9] /\ t in [0,1b-18] /\ v in [0.749,0.75]
 /\ w in [-0.5,-0.499] /\ u in [-1b-18,0] }
u-P -> (u-t*w) + t*(w-(-(1/2)+t*v)) + t*t*(v-((3/4)-(15/8)*t))
 + (t-T)*(-(1/2)+(3/4)*(t+T)-(15/8)*(t*t+t*T+T*T));
t-T -> (t-y*y)+(y-Y)*(y+Y);
