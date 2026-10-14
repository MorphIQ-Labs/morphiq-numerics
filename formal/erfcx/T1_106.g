# erfcx region T, T1 interval 106, c = 10.625, hm = 0.125 (generated)
@rnd = float<ieee_64, ne>;
@fx = fixed<-20, ne>;
a0h = 0x1.b11860c362a18p-5; a0l = 0x1.cd9346d7f8cdcp-60;
a1h = -0x1.4344c26a378fbp-8; a1l = -0x1.771d4d7e15fdbp-62;
a2h = 0x1.e08747286b530p-12; a2l = 0x1.59e22201fd151p-66;
A1 = -0x1.4344c26a00000p-8; A2 = 0x1.e087000000000p-12;
a3 = -0x1.63a4632018db4p-15;
a4 = 0x1.061e70394bdd7p-18;
a5 = -0x1.80cad0cd54434p-22;
a6 = 0x1.194aecd4a7766p-25;
a7 = -0x1.999d56595348ep-29;
a8 = 0x1.292653d6da835p-32;
a9 = -0x1.ad4bd10cac6d4p-36;
h = rnd(hx);
H = fx(h);
L = h - H;
B1 = rnd(a1h - A1 + a1l);
B2 = rnd(a2h - A2 + a2l);
p1 = A1 * H;
sq = H * H;
p2 = A2 * sq;
q8 = rnd(a8 + rnd(h * a9));
q7 = rnd(a7 + rnd(h * q8));
q6 = rnd(a6 + rnd(h * q7));
q5 = rnd(a5 + rnd(h * q6));
q4 = rnd(a4 + rnd(h * q5));
q3 = rnd(a3 + rnd(h * q4));
lh = rnd(L * rnd(h + H));
h2 = rnd(sq + lh);
t3 = rnd(rnd(h2 * h) * q3);
r1 = rnd(rnd(A1 * L) + rnd(B1 * h));
r2 = rnd(rnd(a2h * lh) + rnd(B2 * sq));
ra = rnd(rnd(a0l + r1) + r2);
rest = rnd(ra + t3);
s = rnd(a0h + p1);
e1 = a0h + p1 - s;
s2 = rnd(s + p2);
e2 = s + p2 - s2;
lo = rnd(rnd(e1 + e2) + rest);
Y = s2 + lo;
B1x = a1h - A1 + a1l;
B2x = a2h - A2 + a2l;
a2x = a2h + a2l;
Q = a3 + h * (a4 + h * (a5 + h * (a6 + h * (a7 + h * (a8 + h * (a9))))));
ideal = a0l + (A1 * L + B1x * h) + (a2x * (L * (h + H)) + B2x * sq) + h * h * h * Q;
P = a0h + a0l + (a1h + a1l) * h + a2x * h * h + h * h * h * Q;

{ hx in [-0x1.0000000000000p-3, 0x1.0000000000000p-3] -> (Y - P) / P in [-0x1p-67, 0x1p-67] }

Y - P -> (lo - (rnd(e1 + e2) + rest)) + (rnd(e1 + e2) - (e1 + e2)) + (rest - ideal);
rest - ideal -> (rest - (ra + t3)) + (ra - (rnd(a0l + r1) + r2)) + (rnd(a0l + r1) - (a0l + r1))
  + (r1 - (A1 * L + B1x * h)) + (r2 - (a2x * (L * (h + H)) + B2x * sq)) + (t3 - h * h * h * Q);
r1 - (A1 * L + B1x * h) -> (r1 - (rnd(A1 * L) + rnd(B1 * h))) + (rnd(A1 * L) - A1 * L) + (rnd(B1 * h) - B1 * h) + (B1 - B1x) * h;
r2 - (a2x * (L * (h + H)) + B2x * sq) -> (r2 - (rnd(a2h * lh) + rnd(B2 * sq))) + (rnd(a2h * lh) - a2h * lh) + a2h * (lh - L * (h + H)) - a2l * (L * (h + H)) + (rnd(B2 * sq) - B2 * sq) + (B2 - B2x) * sq;
t3 - h * h * h * Q -> (t3 - rnd(h2 * h) * q3) + (rnd(h2 * h) - h2 * h) * q3 + (h2 - h * h) * h * q3 + h * h * h * (q3 - Q);
h2 - h * h -> (h2 - (sq + lh)) + (lh - L * (h + H));
lh - L * (h + H) -> (lh - L * rnd(h + H)) + L * (rnd(h + H) - (h + H));
