# Normalized reconstruction budget. IEEE rounding bounds establish ep and ey.
Y = 1+u+ep+ey;
Z = (1+dt)*(1+u+du);
{ u in [-1b-10,1b-10] /\ du in [-1b-59,1b-59]
 /\ dt in [-0x1.0000000000002p-53,0x1.0000000000002p-53]
 /\ ep in [-1b-58,1b-58] /\ ey in [-3b-54,3b-54]
 -> (Y-Z)/Z in [-1b-51,1b-51] }
Y-Z -> ep+ey-du-dt*(1+u+du);
