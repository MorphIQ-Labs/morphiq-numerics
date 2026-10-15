# Conditional reconstruction for the normal log-CDF first stage on 37 <= a <= 64.
# h+l is the reciprocal logarithm stage; ch+cl is ln(sqrt(2*pi));
# p is the evaluated Mills correction. e is the exact FastTwoSum residual
# of the negative high square minus c; t is the square's trailing word.
# The owning Coq composition discharges these bounds and EFT identities.
@rnd = float<ieee_64, ne>;
hc = rnd(h+ch);
cp = rnd(cl+p);
lc = rnd(l+cp);
c = rnd(hc+lc);
z = rnd(e+t);
E = -(c-(h+l+ch+cl+p))+(z-(e+t));
{ h in [3,5] /\ l in [-1b-12,1b-12] /\ ch in [0.9,1] /\ cl in [-1b-54,1b-54] /\ t in [-1b-43,1b-43] /\ e in [-1b-40,1b-40] /\ p in [0,0.001] -> E in [-5b-52,5b-52] /\ z in [-1b-39,1b-39] /\ c in [3,7] }
c-(h+l+ch+cl+p) -> (c-(hc+lc))+(hc-(h+ch))+(lc-(l+cp))+(cp-(cl+p));
