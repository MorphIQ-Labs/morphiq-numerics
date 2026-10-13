# erfcx region T, T1 interval 118, c = 13.625, hm = 0.125 (generated)
@rnd = float<ieee_64, ne>;
@fx = fixed<-20, ne>;
a0h = 0x1.524fb3c90d680p-5; a0l = 0x1.32db755f1fa94p-61;
a1h = -0x1.8b2bd5e898803p-9; a1l = 0x1.359752dedffe8p-63;
a2h = 0x1.cc5fa0fb8adc7p-13; a2l = 0x1.b9e8ca7f58650p-70;
A1 = -0x1.8b2bd5e880000p-9; A2 = 0x1.cc5f000000000p-13;
a3 = -0x1.0b779b76c0263p-16;
a4 = 0x1.35fb0d52e7641p-20;
a5 = -0x1.66540c0fd60b5p-24;
a6 = 0x1.9d2904181d258p-28;
a7 = -0x1.db2d3604e1e7dp-32;
a8 = 0x1.109e5e9fae1ecp-35;
a9 = -0x1.37ff79c6f0803p-39;
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
