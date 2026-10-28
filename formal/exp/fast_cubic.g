# Constrained cubic, preserving u(0)=0, on the 1024-way reduction interval.
@rnd = float<ieee_64, ne>;
d3 = 0x1.5555555555554p-3;
d4 = 0x1.555555a38ed84p-5;
d5 = 0x1.11111177013d7p-7;
c2 = 0x1.00000021f6e5ep-1;
delta = c2-0.5;
r = rnd(R+dr);
r2 = rnd(r*r);
p = rnd(c2+rnd(r*d3));
u = rnd(r+rnd(r2*p));
Qr = r*r*(0.5+r*(d3+r*(d4+r*d5)));
expR = 1+R+Qr+m+a;
{ R in [-0.000338451, 0.000338451] /\ dr in [-1b-77, 1b-77]
 /\ a in [-0x1.11efe3daa4fb92df2df8cp-76, 0x1.11efe3daa4fb92df2df8cp-76]
 /\ m in [-1b-74, 1b-74]
 -> u-(expR-1) in [-7b-56, 7b-56] /\ u in [-1b-10,1b-10]
 /\ r in [-1,1] /\ r2 in [-1,1] /\ p in [-1,1] }
u-(expR-1) -> (u-(r+Qr))+(r-R)-m-a;
u-(r+Qr) -> (u-(r+rnd(r2*p)))+(rnd(r2*p)-r2*p)
 + (r2-r*r)*p+r*r*(p-(c2+r*d3))
 + delta*delta/(4*d4)-d4*(r*r-delta/(2*d4))*(r*r-delta/(2*d4))-d5*r*r*r*r*r { d4 <> 0 };
r-R -> (r-(R+dr))+dr;
p-(c2+r*d3) -> (p-(c2+rnd(r*d3)))+(rnd(r*d3)-r*d3);
