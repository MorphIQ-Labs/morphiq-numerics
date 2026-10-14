# erfcx arithmetic component; see docs/erfcx.md for assumptions and scope.
# TwoSum and final Fast2Sum are exact; sc is an exact power of two.
# The high table word scales exactly; ds bounds rounding the scaled low
# word, including gradual underflow (ErfcxReflectionScale.v).
# The bounds on de/dg are supplied by the exponential/table components.
@rnd = float<ieee_64, ne>;
eh = rnd(eh_); el = rnd(el_);
gh = rnd(gh_); gl = rnd(gl_);
dh = rnd(eh - gh * sc);
dl = eh - gh * sc - dh;
gls = gl * sc + ds;
l0 = rnd(el - gls);
l = rnd(dl + l0);
Y = dh + l;
E = eh + el - de;
G = gh + gl - dg;
F = E - G * sc;
{ eh in [0.999, 2.001] /\ el in [-1b-52, 1b-52]
  /\ gh in [0, 0.617] /\ gl in [-1b-53, 1b-53] /\ sc in [0, 0.5]
  /\ ds in [-1b-800, 1b-800]
  /\ de in [-0x1.a2p-71, 0x1.a2p-71] /\ dg in [-1b-67, 1b-67]
  -> (Y - F) / F in [-1b-67, 1b-67] /\ dh in [0.69, 2.01] /\ l in [-1b-50, 1b-50] }
Y - F -> (l - (dl + l0)) + (l0 - (el - gls)) + de - dg * sc - ds;
