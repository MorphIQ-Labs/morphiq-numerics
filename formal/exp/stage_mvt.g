# Stages A and B evaluate their polynomial at a binary64 r (stage A's r,
# stage B's r_hi), not at the exact reduced argument R = r + delta, with
# |delta| <= ulp(r)/2 + 2^-77 (formal/exp/stage_a_reduction.g) or
# ulp(r_hi)/2 + 2^-93 (formal/exp/stage_b_reduction.g), both below
# 0x1.01p-64. This bounds m = Q(R) - Q(r), which formal/exp/stage_a.g and
# stage_b.g assume, where Q(r) = r^2 (1/2 + r (d3 + r (d4 + r d5))).

d3 = 0x1.5555555555554p-3;
d4 = 0x1.555555a38ed84p-5;
d5 = 0x1.11111177013d7p-7;

R = r + delta;
QR = R * R * (0.5 + R * (d3 + R * (d4 + R * d5)));
QH = r * r * (0.5 + r * (d3 + r * (d4 + r * d5)));

{ r in [-0.00068, 0.00068] /\ delta in [-0x1.01p-64, 0x1.01p-64]
  -> QR - QH in [-1b-74, 1b-74] }

# a^n - b^n = (a - b) (a^(n-1) + a^(n-2) b + ... + b^(n-1)).
QR - QH -> delta * (0.5 * (R + r) + d3 * (R * R + R * r + r * r)
                    + d4 * (R * R * R + R * R * r + R * r * r + r * r * r)
                    + d5 * (R * R * R * R + R * R * R * r + R * R * r * r + R * r * r * r + r * r * r * r));
