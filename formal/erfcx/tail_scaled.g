# erfcx arithmetic component; see docs/erfcx.md for assumptions and scope.
# Above 1e270, x^-2/2 < 2^-1794. The first omitted asymptotic term bounds
# the relative correction to C/x. q includes the generated constant error.
Y = 1 + eq;
F = 1 - correction;
{ eq in [-1b-69, 1b-69] /\ correction in [0, 1b-1794]
  -> (Y - F) / F in [-1b-68, 1b-68] }
Y - F -> eq + correction;
