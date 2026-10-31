# The normalized product rounding error ey is proved for normal h*q.
Y = q+ey;
Z = (1+dt)*(q+dq);
{ q in [0.999,1.001] /\ dq in [-9b-42,9b-42]
 /\ dt in [-0x1.0000000000002p-53,0x1.0000000000002p-53]
 /\ ey in [-1026b-63,1026b-63]
 -> (Y-Z)/Z in [-1b-38,1b-38] }
Y-Z -> ey-dq-dt*(q+dq);
