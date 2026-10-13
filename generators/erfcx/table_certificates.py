"""Write one conditional Gappa certificate per region-T interval.

Each bounds |Y - P(h)|, the evaluation error of `t_eval` against the
interval's polynomial P (exact coefficients), for every binary64 h in
[-hm, hm]. Hypotheses taken from separate lemmas (not Gappa's):
  - H = h rounded to the 2^(e-23) grid (the shifter), L = h - H exactly;
  - A1·H, H·H and A2·(H·H) are exact (bit counts: 35 + 18, 18 + 18, 17 + 36);
  - a1h - A1 and a2h - A2 are exact (A is a1h, a2h truncated);
  - fast_two_sum is exact (its operand-magnitude conditions remain entry
    proof obligations; generator reports alone do not discharge them).
The relative bound composes |Y - P| / min|P| with Sollya's approximation bound.

Invoked by generators/erfcx_certificates.py with tables.out and an output directory.
"""
import os
import struct
import sys
from fractions import Fraction


def h2f(s):
    return float.fromhex(s) if "p" in s else struct.unpack(">d", bytes.fromhex(s[2:].rjust(16, "0")))[0]


def bits(x):
    return struct.unpack(">Q", struct.pack(">d", x))[0]


def trunc(x, keep):
    """x's encoding with all but the top `keep` significand bits cleared."""
    b = bits(x) & ~((1 << (53 - keep)) - 1)
    return struct.unpack(">d", struct.pack(">Q", b))[0]


def g(x):
    return float(x).hex()


tab = {}
for line in open(sys.argv[1]):
    t = line.split()
    if t and t[0] in ("T0", "T1"):
        d = tab.setdefault((t[0], int(t[1])), {"A": {}, "L": {}})
        if t[2] in ("C", "HM"):
            d[t[2]] = h2f(t[3])
        elif t[2] in ("A", "L"):
            d[t[2]][int(t[3])] = h2f(t[4])
        elif t[2] == "ERR":
            d["ERR"] = float(t[3])
outdir = sys.argv[2]
os.makedirs(outdir, exist_ok=True)
for (tag, idx), d in sorted(tab.items()):
    a, lo, hm, c = d["A"], d["L"], d["HM"], d["C"]
    deg = max(a)
    e = 0 if tag == "T0" else idx // 32
    A1 = trunc(a[1], 35)
    A2 = trunc(a[2], 17)
    # least |P| on the interval, rigorously (exact rationals): a0 - sum |ak| hm^k
    a0 = Fraction(a[0]) + Fraction(lo[0])
    rest = sum(abs(Fraction(a[k]) + Fraction(lo.get(k, 0.0))) * Fraction(hm) ** k for k in range(1, deg + 1))
    pmin = abs(a0) - rest
    horner = f"a{deg}"
    lines = []
    for k in range(deg - 1, 2, -1):
        lines.append(f"q{k} = rnd(a{k} + rnd(h * {'q' + str(k + 1) if k + 1 < deg else 'a' + str(deg)}));")
    qexpr = f"a{deg}"
    for k in range(deg - 1, 2, -1):
        qexpr = f"a{k} + h * ({qexpr})"
    coef = "\n".join(f"a{k} = {g(a[k])};" for k in range(3, deg + 1))
    src = f"""# erfcx region T, {tag} interval {idx}, c = {c!r}, hm = {hm!r} (generated)
@rnd = float<ieee_64, ne>;
@fx = fixed<{e - 23}, ne>;
a0h = {g(a[0])}; a0l = {g(lo[0])};
a1h = {g(a[1])}; a1l = {g(lo[1])};
a2h = {g(a[2])}; a2l = {g(lo[2])};
A1 = {g(A1)}; A2 = {g(A2)};
{coef}
h = rnd(hx);
H = fx(h);
L = h - H;
B1 = rnd(a1h - A1 + a1l);
B2 = rnd(a2h - A2 + a2l);
p1 = A1 * H;
sq = H * H;
p2 = A2 * sq;
{chr(10).join(lines)}
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
Q = {qexpr};
ideal = a0l + (A1 * L + B1x * h) + (a2x * (L * (h + H)) + B2x * sq) + h * h * h * Q;
P = a0h + a0l + (a1h + a1l) * h + a2x * h * h + h * h * h * Q;

{{ hx in [{g(-hm)}, {g(hm)}] -> (Y - P) / P in [-0x1p-67, 0x1p-67] }}

Y - P -> (lo - (rnd(e1 + e2) + rest)) + (rnd(e1 + e2) - (e1 + e2)) + (rest - ideal);
rest - ideal -> (rest - (ra + t3)) + (ra - (rnd(a0l + r1) + r2)) + (rnd(a0l + r1) - (a0l + r1))
  + (r1 - (A1 * L + B1x * h)) + (r2 - (a2x * (L * (h + H)) + B2x * sq)) + (t3 - h * h * h * Q);
r1 - (A1 * L + B1x * h) -> (r1 - (rnd(A1 * L) + rnd(B1 * h))) + (rnd(A1 * L) - A1 * L) + (rnd(B1 * h) - B1 * h) + (B1 - B1x) * h;
r2 - (a2x * (L * (h + H)) + B2x * sq) -> (r2 - (rnd(a2h * lh) + rnd(B2 * sq))) + (rnd(a2h * lh) - a2h * lh) + a2h * (lh - L * (h + H)) - a2l * (L * (h + H)) + (rnd(B2 * sq) - B2 * sq) + (B2 - B2x) * sq;
t3 - h * h * h * Q -> (t3 - rnd(h2 * h) * q3) + (rnd(h2 * h) - h2 * h) * q3 + (h2 - h * h) * h * q3 + h * h * h * (q3 - Q);
h2 - h * h -> (h2 - (sq + lh)) + (lh - L * (h + H));
lh - L * (h + H) -> (lh - L * rnd(h + H)) + L * (rnd(h + H) - (h + H));
"""
    with open(os.path.join(outdir, f"{tag}_{idx:03d}.g"), "w") as fh:
        fh.write(src)
    with open(os.path.join(outdir, f"{tag}_{idx:03d}.meta"), "w") as fh:
        fh.write(f"{float(pmin)!r} {d['ERR']!r}\n")
