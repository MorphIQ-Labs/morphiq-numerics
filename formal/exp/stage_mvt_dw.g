# Stage A at a double-word argument (formal/exp/stage_a_dw.g) evaluates its
# polynomial at r = RN(RN(R0 + dr) + se), not at the exact R = R0 + se, with
# |r - R| <= 0x1.01p-63 (certified there). This bounds m = Q(R) - Q(r), where
# Q(r) = r^2 (1/2 + r (d3 + r (d4 + r d5))), as formal/exp/stage_mvt.g does
# for stage A's single-word argument.

d3 = 0x1.5555555555554p-3;
d4 = 0x1.555555a38ed84p-5;
d5 = 0x1.11111177013d7p-7;

R = r + delta;
QR = R * R * (0.5 + R * (d3 + R * (d4 + R * d5)));
QH = r * r * (0.5 + r * (d3 + r * (d4 + r * d5)));

{ r in [-0.00068, 0.00068] /\ delta in [-0x1.01p-63, 0x1.01p-63]
  -> QR - QH in [-1b-73, 1b-73] }

QR - QH -> delta * (0.5 * (R + r) + d3 * (R * R + R * r + r * r)
                    + d4 * (R * R * R + R * R * r + R * r * r + r * r * r)
                    + d5 * (R * R * R * R + R * R * R * r + R * R * r * r + R * r * r * r + r * r * r * r));
