# The double-word ratio (docs/atan2.md, section 3): with n and d scaled so that
# d is in [1, 2) and n/d = tt in [2^-900, 1], q = RN(n/d) = tt (1 + e0), |e0| <= 2^-53.
# (p, pe) = two_prod(q, d) is exact and n - p is exact (Sterbenz), so the exact
# remainder is n - q d = -tt e0 d; its computed value is that times (1 + a) (the
# subtraction of pe) and ql = RN(r/d) = r (1 + b)/d. Then t = q + ql (fast_two_sum,
# exact) = tt + e0 tt - tt e0 (1 + a) (1 + b). Written by
# generators/atan2_certificates.py.

q = tt * (1 + e0);
ql = -(tt * e0) * (1 + a) * (1 + b);
t = q + ql;

{ tt in [1b-900, 1] /\ e0 in [-1b-53, 1b-53] /\ a in [-1b-53, 1b-53] /\ b in [-1b-53, 1b-53]
  -> (t - tt) / tt in [-1b-104, 1b-104] }

(t - tt) / tt -> -e0 * (a + b + a * b) { tt <> 0 };
