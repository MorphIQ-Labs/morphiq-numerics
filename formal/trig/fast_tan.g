# The fast tan (docs/sin_cos.md, section 8): N.checked_div(D), with N, D the
# fast sin r and cos r in either order, each within 1b-62 (formal/trig/fast_sin.g,
# fast_cos.g), and the division within 15u^2 + 56u^3 (docs/double-word.md).
# Written by generators/trig_certificates.py.

Q = (1 + eN) / (1 + eD) * (1 + ed);

{ eN in [-1b-62, 1b-62] /\ eD in [-1b-62, 1b-62] /\ ed in [-970b-112, 970b-112] -> Q - 1 in [-1b-60, 1b-60] }
