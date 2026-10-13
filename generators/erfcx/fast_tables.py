"""Turn generators/erfcx/tables.out (Sollya) into src/consts.rs for the erfcx prototype.

Also reports, per interval, the quantities the fast path's error analysis
assumes: the approximation bound, |a1|·hm/|a0|, the size of the terms the
evaluation keeps in binary64 (sum over k >= 3 of |a_k|·hm^k, relative to
the least value of the polynomial), and that every a_l (k >= 3) is zero.

usage: python to_rust.py tables.out > ../src/consts.rs 2> tables.report
"""
import sys
from fractions import Fraction as F
import struct
import math


def h2f(s):
    s = s.strip()
    if s.startswith("0x") and "p" not in s:
        return struct.unpack(">d", bytes.fromhex(s[2:].rjust(16, "0")))[0]
    return float.fromhex(s)


def bits(x):
    return struct.unpack(">Q", struct.pack(">d", x))[0]


tab = {}
pa = {}
misc = {}
for line in open(sys.argv[1]):
    t = line.split()
    if not t:
        continue
    if t[0] in ("T0", "T1"):
        key = (t[0], int(t[1]))
        d = tab.setdefault(key, {"A": {}, "L": {}})
        if t[2] in ("C", "HM"):
            d[t[2]] = h2f(t[3])
        elif t[2] in ("A", "L"):
            d[t[2]][int(t[3])] = h2f(t[4])
        elif t[2] == "ERR":
            d["ERR"] = F(t[3])
    elif t[0] == "PA":
        pa[int(t[1])] = h2f(t[2])
    elif t[0] in ("PA_ERR", "PREM", "CS_ERR"):
        misc[t[0]] = float(t[1])
    elif t[0] in ("CS", "CSL"):
        misc[t[0]] = h2f(t[1])

keys = sorted([k for k in tab if k[0] == "T0"], key=lambda k: k[1]) + sorted(
    [k for k in tab if k[0] == "T1"], key=lambda k: k[1]
)
deg = max(tab[keys[0]]["A"])
W = 6 + (deg - 2)
worst_err = 0
worst_tail = 0
worst_a1 = 0
print("//! Fast-path tables for the erfcx prototype; written by generators/erfcx/fast_tables.py from")
print("//! generators/erfcx/tables.out (Sollya 8.0, fpminimax/supnorm). Do not edit.")
print(f"/// Polynomial degree of every table interval.")
print(f"pub const DEG: usize = {deg};")
print(f"/// Per interval: a0 (hi, lo), a1 (hi, lo), a2 (hi, lo), a3..a{deg}; binary64 encodings.")
print(f"pub static T: [[u64; {W}]; {len(keys)}] = [")
for k in keys:
    d = tab[k]
    a = d["A"]
    lo = d["L"]
    for j in range(3, deg + 1):
        assert lo[j] == 0.0, (k, j)
    row = [a[0], lo[0], a[1], lo[1], a[2], lo[2]] + [a[j] for j in range(3, deg + 1)]
    print("    [" + ", ".join(f"0x{bits(v):016x}" for v in row) + f"], // {k[0]} {k[1]} c={d['C']!r}")
    assert 0 < d["ERR"] < F(1, 2**69), (k, d["ERR"])
    hm = d["HM"]
    # Least |p| over the interval, crudely: a0 - sum |a_k| hm^k.
    least = abs(a[0]) - sum(abs(a[j]) * hm**j for j in range(1, deg + 1))
    tail = sum(abs(a[j]) * hm**j for j in range(3, deg + 1)) / least
    a1r = abs(a[1]) * hm / abs(a[0])
    worst_err = max(worst_err, d["ERR"])
    worst_tail = max(worst_tail, tail)
    worst_a1 = max(worst_a1, a1r)
    print(f"{k[0]} {k[1]} c={d['C']} err=2^{math.log2(d['ERR']):.2f} tail=2^{math.log2(tail):.2f} a1hm/a0=2^{math.log2(a1r):.2f}", file=sys.stderr)
print("];")
print(f"/// The asymptotic form's P(t) on t in [2^-18, 2^-8], Horner order from t^0.")
print(f"pub const PA: [u64; {len(pa)}] = [" + ", ".join(f"0x{bits(pa[j]):016x}" for j in sorted(pa)) + "];")
print(f"/// 1/sqrt(pi) as a double-word (relative error {misc['CS_ERR']:.3e}).")
print(f"pub const CS: (u64, u64) = (0x{bits(misc['CS']):016x}, 0x{bits(misc['CSL']):016x});")
print(f"WORST approx 2^{math.log2(worst_err):.3f}, tail 2^{math.log2(worst_tail):.3f}, a1hm/a0 2^{math.log2(worst_a1):.3f}", file=sys.stderr)
print(f"PA_ERR 2^{math.log2(misc['PA_ERR']):.3f} PREM 2^{math.log2(misc['PREM']):.3f}", file=sys.stderr)
