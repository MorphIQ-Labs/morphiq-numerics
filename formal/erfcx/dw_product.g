# IEEE binary64 double-word product, including gradual underflow.
# Exact TwoProd and Fast2Sum are discharged by ErfcxProduct.v.
@rnd = float<ieee_64, ne>;
ah = rnd(ah_); al = rnd(al_); bh = rnd(bh_); bl = rnd(bl_);
p = rnd(ah * bh); pe = ah * bh - p;
u = rnd(ah * bl); v = rnd(al * bh); c = rnd(u + v); t = rnd(pe + c);
h = rnd(p + t); l = p + t - h;
P = (ah + al) * (bh + bl); Y = h + l;
{ ah in [1b-10,4] /\ bh in [1b-10,4] /\ ah*bh in [0,4]
 /\ al / ah in [-1b-51,1b-51] /\ bl / bh in [-1b-51,1b-51]
 -> (Y-P)/P in [-1b-77,1b-77] /\ h in [1b-21,8]
 /\ l / h in [-1b-51,1b-51] /\ t / p in [-1b-27,1b-27]
 /\ h / (ah*bh) in [0.999,1.001] }
al -> ah * (al/ah) { ah <> 0 };
bl -> bh * (bl/bh) { bh <> 0 };
Y-P -> (t - (pe+c)) + (c - (u+v)) + (u-ah*bl) + (v-al*bh) - al*bl;
p + t -> p * (1 + t/p) { p <> 0 };
h / (ah*bh) -> (1+(h-(p+t))/(p+t)) * (1+t/p) * (1+(p-ah*bh)/(ah*bh)) { ah <> 0, bh <> 0, p <> 0, p+t <> 0 };
