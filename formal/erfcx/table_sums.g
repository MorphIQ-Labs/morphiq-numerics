# Generic Fast2Sum entry conditions for the erfcx table polynomial.
@rnd = float<ieee_64, ne>;
a0 = rnd(a0x);
p1 = a0*r1;
p2 = a0*r2;
rest = rnd(restx);
s = rnd(a0+p1);
e1 = a0+p1-s;
s2 = rnd(s+p2);
e2 = s+p2-s2;
lo = rnd(rnd(e1+e2)+rest);
{ a0 in [9b-8,2] /\ r1 in [-1b-2,1b-2] /\ r2 in [-1b-4,1b-4] /\ rest in [-21b-10,21b-10] ->
 s in [13b-9,3] /\ s2 in [3b-7,4] /\ s-p2 in [3b-7,3] /\ s+p2 in [3b-7,3] /\ lo in [-11b-9,11b-9] /\
 e1 in [-1b-51,1b-51] /\ e2 in [-1b-50,1b-50] }
a0+p1 -> a0*(1+r1);
s+p2 -> a0*(1+r1+r2) + (s-(a0+p1));
s-p2 -> a0*(1+r1-r2) + (s-(a0+p1));
