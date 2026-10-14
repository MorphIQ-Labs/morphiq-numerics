"""Q256 constants for the erfcx accurate-path prototype (issue #34).

Emits erfcx at every table centre, 1/sqrt(pi),
2/sqrt(pi), 1/k (k = 1..100), 2^(j/128) (j = 0..127) and ln 2 / 128, each the
exact value rounded to nearest to a normalized 256-bit significand
(relative error below 2^-256). mpmath at 600 bits.
Invoked by generators/erfcx_constants.py, which writes accurate_tables.rs
and checks agreement between 600-bit and 1000-bit generation.
"""
import mpmath as mp

mp.mp.prec = 600


def q256(v):
    v = mp.mpf(v)
    assert v > 0
    e = int(mp.floor(mp.log(v, 2))) - 255
    m = int(mp.nint(v / mp.mpf(2) ** e))
    if m >= 2**256:
        m //= 2
        e += 1
    while m < 2**255:
        m *= 2
        e -= 1
    assert abs(mp.mpf(m) * mp.mpf(2) ** e / v - 1) < mp.mpf(2) ** -256
    limbs = [(m >> (64 * i)) & (2**64 - 1) for i in range(4)]
    return "([" + ", ".join(f"0x{l:016x}" for l in limbs) + f"], {e})"


def erfcx(c):
    c = mp.mpf(c)
    return mp.exp(c * c) * mp.erfc(c)


cs = [mp.mpf(k) / 32 for k in range(-16, 33)] + [mp.mpf(2) ** e * (1 + mp.mpf(2 * i + 1) / 64) for e in range(4) for i in range(32)]
print("//! Q256 constants; written by generators/erfcx/accurate_tables.py (mpmath %s, 600 bits), each rounded to nearest." % mp.__version__)
print("pub type C = ([u64; 4], i32);")
print(f"pub const CS: C = {q256(1 / mp.sqrt(mp.pi))};")
print(f"pub const C2: C = {q256(2 / mp.sqrt(mp.pi))};")
print(f"pub const LN2_128: C = {q256(mp.log(2) / 128)};")
print(f"pub const F_AT_C: [C; {len(cs)}] = [")
for c in cs:
    print(f"    {q256(erfcx(c))},")
print("];")
print("pub const RECIP: [C; 100] = [")
for k in range(1, 101):
    print(f"    {q256(mp.mpf(1) / k)},")
print("];")
print("pub const T2: [C; 128] = [")
for j in range(128):
    print(f"    {q256(mp.mpf(2) ** (mp.mpf(j) / 128))},")
print("];")
