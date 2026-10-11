# ln_1p's stage H (docs/ln.md, section 7): the polynomial P(z) = -1/2 + z Q(z),
# evaluated by Estrin's scheme with every operation rounded to binary64,
# nearest-even, as crates/morphiq-numerics/src/ln/stages.rs does, and
# q = RN(RN(z^2) P), against z^2 P(z) evaluated exactly, relative to z^2.
# h3..h6 are generators/ln_poly.out's. Written by generators/ln1p_certificates.py.

@rnd = float<ieee_64, ne>;

h3 = 0x1.555555555430cp-2;
h4 = -0x1.fffffffffd249p-3;
h5 = 0x1.9999e2be5698ep-3;
h6 = -0x1.555599e7b76d7p-3;

z2 = rnd(z * z);
t0 = rnd(rnd(z * h3) - 1b-1);
t1 = rnd(rnd(z * h5) + h4);
a1 = rnd(rnd(z2 * h6) + t1);
p = rnd(rnd(z2 * a1) + t0);
q = rnd(z2 * p);
Pz = z * z * (z * z * h6 + (z * h5 + h4)) + (z * h3 - 1b-1);

{ |z| in [1b-62, 1b-9]
  -> (q - z * z * Pz) / (z * z) in [-577b-61, 577b-61] /\ Pz in [-513b-10, -511b-10] }

(q - z * z * Pz) / (z * z) -> ((q - z2 * p) / (z2 * p)) * p * (z2 / (z * z)) + ((z2 - z * z) / (z * z)) * p + (p - Pz)
  { z <> 0, z2 * p <> 0 };
z2 / (z * z) -> 1 + (z2 - z * z) / (z * z) { z <> 0 };
