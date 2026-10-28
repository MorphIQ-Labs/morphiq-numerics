# Bounded exp, using the existing stage reduction, table and approximation bounds.
@rnd = float<ieee_64, ne>;
d3 = 0x1.5555555555554p-3;
d4 = 0x1.555555a38ed84p-5;
d5 = 0x1.11111177013d7p-7;
r = rnd(R+dr);
r2 = rnd(r*r);
left = rnd(r+rnd(0.5*r2));
p = rnd(d3+rnd(r*d4));
u = rnd(left+rnd(rnd(r2*r)*p));
Qr = r*r*(0.5+r*(d3+r*(d4+r*d5)));
expR = 1+R+Qr+m+a;
{ R in [-0.000677, 0.000677] /\ dr in [-1b-77, 1b-77]
 /\ a in [-0x1.11efe3daa4fb92df2df8cp-76, 0x1.11efe3daa4fb92df2df8cp-76]
 /\ m in [-1b-74, 1b-74]
 -> u-(expR-1) in [-1b-59, 1b-59] /\ u in [-1b-10,1b-10]
 /\ r in [-1,1] /\ r2 in [-1,1] /\ left in [-1,1] /\ p in [-1,1] }
u-(expR-1) -> (u-(r+Qr))+(r-R)-m-a;
u-(r+Qr) -> (u-(left+rnd(rnd(r2*r)*p)))+(left-(r+rnd(0.5*r2)))
 + (rnd(0.5*r2)-0.5*r2)+0.5*(r2-r*r)
 + (rnd(rnd(r2*r)*p)-rnd(r2*r)*p)+(rnd(r2*r)-r2*r)*p
 + (r2-r*r)*r*p+r*r*r*(p-(d3+r*d4))-r*r*r*r*r*d5;
r-R -> (r-(R+dr))+dr;
p-(d3+r*d4) -> (p-(d3+rnd(r*d4)))+(rnd(r*d4)-r*d4);
