# Security policy

morphiq-numerics computes numerical results that downstream systems rely on.
These count as security issues:
- **Wrong rounding:** a result that isn't the correctly rounded value where
  the documentation claims it is.
- **Target dependence:** a result that differs between targets.
- **Crashes:** a panic or hang on any input.
- **Soundness:** a soundness bug.

## Reporting a vulnerability

Report privately through GitHub: on this repository's **Security** tab, choose
**Report a vulnerability**. Please don't open a public issue, pull request, or
discussion for a suspected vulnerability.

A useful report gives:
- the function, version or commit, and target;
- the input as exact bits (hex);
- the result returned and the result expected, with your reference, such as
  MPFR at a stated precision.

The report is acknowledged and tracked in the private advisory. A fix is
developed there, released, and then disclosed through a GitHub security
advisory, crediting the reporter unless they ask otherwise.

## Supported versions

morphiq-numerics is pre-1.0. Fixes land on `main` and ship in the next release
of the current `0.x` series; earlier releases are not patched.
