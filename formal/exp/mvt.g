# The fast path evaluates its polynomial at r_hi, not at the exact reduced
# argument R = r_hi + delta, with |delta| <= |r_lo| + |dr| <= 2^-62 + 2^-113
# (formal/exp/reduction.g). This bounds m = Q(R) - Q(r_hi), which
# formal/exp/fast.g assumes, where Q(r) = r^2 (1/2 + r (c3 + r (c4 + r (c5 + r c6)))).

c3 = 0x1.555555555549p-3;
c4 = 0x1.55555555554bfp-5;
c5 = 0x1.111115b678249p-7;
c6 = 0x1.6c16c6fd917b6p-10;

R = rhi + delta;
QR = R * R * (0.5 + R * (c3 + R * (c4 + R * (c5 + R * c6))));
QH = rhi * rhi * (0.5 + rhi * (c3 + rhi * (c4 + rhi * (c5 + rhi * c6))));

{ rhi in [-0.0027077, 0.0027077] /\ delta in [-0x1.0000000000002p-62, 0x1.0000000000002p-62]
  -> QR - QH in [-0x1.9p-71, 0x1.9p-71] }

# a^n - b^n = (a - b) (a^(n-1) + a^(n-2) b + ... + b^(n-1)).
QR - QH -> delta * (0.5 * (R + rhi)
                    + c3 * (R * R + R * rhi + rhi * rhi)
                    + c4 * (R * R * R + R * R * rhi + R * rhi * rhi + rhi * rhi * rhi)
                    + c5 * (R * R * R * R + R * R * R * rhi + R * R * rhi * rhi + R * rhi * rhi * rhi + rhi * rhi * rhi * rhi)
                    + c6 * (R * R * R * R * R + R * R * R * R * rhi + R * R * R * rhi * rhi + R * R * rhi * rhi * rhi + R * rhi * rhi * rhi * rhi + rhi * rhi * rhi * rhi * rhi));
