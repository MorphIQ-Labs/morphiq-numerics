with import <nixpkgs> {};
stdenv.mkDerivation {
  name = "double-double";
  buildInputs = with coqPackages_8_11; [ coq mathcomp.ssreflect flocq ];
}
