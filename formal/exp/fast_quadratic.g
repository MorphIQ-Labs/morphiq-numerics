# Parallel quadratic with one-word reduction, preserving exp(0)=1.
# C1 = RN(1+A^2/8), A=0.000338451: the leading residual is a scaled T3.
@rnd = float<ieee_64, ne>;
d3 = 0x1.5555555555554p-3;
d4 = 0x1.555555a38ed84p-5;
d5 = 0x1.11111177013d7p-7;
c1 = 0x1.0000003d7f817p0;
r = rnd(R+dr);
a1 = rnd(c1*r);
p = rnd(1+a1);
a2 = rnd(0.5*r);
v = rnd(a2*r);
q = rnd(p+v);
Qr = r*r*(0.5+r*(d3+r*(d4+r*d5)));
expR = 1+R+Qr+m+a;
{ R in [-0.000338451, 0.000338451] /\ dr in [-1b-42, 1b-42]
 /\ a in [-0x1.11efe3daa4fb92df2df8cp-76, 0x1.11efe3daa4fb92df2df8cp-76]
 /\ m in [-1b-52, 1b-52]
 -> q-expR in [-9b-42,9b-42] /\ q in [0.999,1.001]
 /\ r in [-1b-10,1b-10] /\ a1 in [-1,1] /\ p in [0.5,2]
 /\ a2 in [-1,1] /\ v in [-1,1] }
q-expR -> (q-(p+v))+(p-(1+a1))+(a1-c1*r)+(v-a2*r)
 +(a2-0.5*r)*r+(c1-1)*r-r*r*r*(d3+r*(d4+r*d5))+(r-R)-m-a;
r-R -> (r-(R+dr))+dr;
q-expR $ r in 64;
