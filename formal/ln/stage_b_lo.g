# ln_1p's stage B, |x| >= 2^-9 (docs/ln.md, section 7): the low word lo, every
# operation rounded to binary64 as crates/morphiq-numerics/src/ln/stages.rs
# does, against Ideal = e1 + e2 + ln0 + L (1 - z + z^2 - z^3) - pl/2 + z^3 Q(z).
# z binary64, |z| <= 2^-9 (zero included); p + pl = z^2 exactly (two_prod); L = l R 2^-E exact,
# |L| <= 2^-53 (1 + 2^-9); e1, e2 the Fast2Sum errors, binary64, below 2^-44
# (|s| < 1024); ln0 binary64, |ln0| <= 2^-34 (|E| <= 1020). -0.5 pl is exact.
# Written by generators/ln1p_certificates.py.

@rnd = float<ieee_64, ne>;

b3 = 0x1.5555555555555p-2;
b4 = -0x1p-2;
b5 = 0x1.9999999a3e0b6p-3;
b6 = -0x1.555555558204cp-3;
b7 = 0x1.249076a775a54p-3;
b8 = -0x1.fffec39c0bf07p-4;

p = rnd(z * z);
pl = z * z - p;
zp = rnd(z * p);
w4 = rnd(rnd(z * b8) + b7);
w3 = rnd(rnd(z * w4) + b6);
w2 = rnd(rnd(z * w3) + b5);
w1 = rnd(rnd(z * w2) + b4);
w0 = rnd(rnd(z * w1) + b3);
W = z * (z * (z * (z * (z * b8 + b7) + b6) + b5) + b4) + b3;
tail = rnd(zp * w0);
r1 = rnd(tail - pl / 2);
lr = rnd(L);
omz = rnd(1 - z);
aa = rnd(omz + p);
bb = rnd(aa - zp);
lrt = rnd(lr * bb);
r2 = rnd(ln0 + lrt);
r3 = rnd(r2 + r1);
r4 = rnd(e1 + e2);
lo = rnd(r4 + r3);
Ideal = e1 + e2 + ln0 + L * (1 - z + z * z - z * z * z) - pl / 2 + z * z * z * W;

{ z in [-1b-9, 1b-9] /\ L in [-519b-62, 519b-62]
  /\ e1 in [-1b-44, 1b-44] /\ e2 in [-1b-44, 1b-44] /\ ln0 in [-1b-34, 1b-34]
  /\ @FIX(e1, -1074) /\ @FIX(e2, -1074) /\ @FIX(ln0, -1074)
  -> lo - Ideal in [-830b-89, 830b-89] /\ lo in [-1b-28, 1b-28] }

lo - Ideal -> (lo - (r4 + r3)) + (r4 - (e1 + e2)) + (r3 - (r2 + r1)) + (r2 - (ln0 + lrt)) + (r1 - (tail - pl / 2))
  + (tail - z * z * z * W) + (lrt - L * (1 - z + z * z - z * z * z));
lrt - L * (1 - z + z * z - z * z * z) -> (lrt - lr * bb) + (lr - L) * bb + L * (bb - (1 - z + z * z - z * z * z));
bb - (1 - z + z * z - z * z * z) -> (bb - (aa - zp)) + (aa - (omz + p)) + (omz - (1 - z)) + (p - z * z) - (zp - z * z * z);
tail - z * z * z * W -> (tail - zp * w0) + (zp - z * z * z) * w0 + z * z * z * (w0 - W);
zp - z * z * z -> (zp - z * p) + z * (p - z * z);
