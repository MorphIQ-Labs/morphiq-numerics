# Transfer the existing exponential approximation to the short reduction.
d3 = 0x1.5555555555554p-3;
d4 = 0x1.555555a38ed84p-5;
d5 = 0x1.11111177013d7p-7;

R = r + delta;
QR = R * R * (0.5 + R * (d3 + R * (d4 + R * d5)));
QH = r * r * (0.5 + r * (d3 + r * (d4 + r * d5)));

{ r in [-0.000339, 0.000339] /\ delta in [-1b-41, 1b-41]
  -> QR - QH in [-1b-52, 1b-52] }

# a^n - b^n = (a - b) (a^(n-1) + a^(n-2) b + ... + b^(n-1)).
QR - QH -> delta * (0.5 * (R + r) + d3 * (R * R + R * r + r * r)
                    + d4 * (R * R * R + R * R * r + R * r * r + r * r * r)
                    + d5 * (R * R * R * R + R * R * R * r + R * R * r * r + R * r * r * r + r * r * r * r));
