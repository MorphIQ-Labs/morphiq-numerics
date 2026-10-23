# The complement's result (docs/asin.md, section 3): y = (H - D')(1 + ea) with
# H = pi/2 as a double-word (relative error eH <= 2^-107), D' = 2 F(z) exactly
# (F the fast result at the double-word z), against asin x = pi/2 - D, D = 2 asin w
# for w = sqrt((1 - x)/2). F = asin(zv)(1 + eF), eF the fast path's bound at its
# segment (formal/asin/compose_*.g, series_compose.g); zv = w (1 + ez) with ez
# from formal/asin/sqrt.g; asin(zv)/asin(w) - 1 = es, at most 1.1 ez since
# (w / asin w)/sqrt(1 - w^2) <= 1.055 on w <= 0.3827. ea: sub, 3u^2/(1 - 4u).
# Written by generators/asin_certificates.py.

Ax = H - D;
y = (H * (1 + eH) - D * (1 + es) * (1 + eF)) * (1 + ea);

{ H in [1.570796326794896619, 1.570796326794896620] /\ D in [0, 0.7854] /\ Ax in [0.78539816339744, 1.5707963267948967]
  /\ eH in [-1b-107, 1b-107] /\ es in [-569b-112, 569b-112] /\ eF in [-667b-73, 667b-73]
  /\ ea in [-776b-114, 776b-114]
  -> (y - Ax) / Ax in [-674b-73, 674b-73] }

(y - Ax) / Ax -> ((H * eH - D * ((1 + es) * (1 + eF) - 1)) * (1 + ea)) / Ax + ea { Ax <> 0 };
