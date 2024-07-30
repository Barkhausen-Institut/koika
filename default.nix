{
  lib,
  mkCoqDerivation,
  coq,
  boost,
  python3,
  clang-tools,
  sphinx,
  doCheck ? false,
}:
mkCoqDerivation rec {
  pname = "koika";
  defaultVersion = "0.0.1";

  opam-name = "koika";
  useDune = true;

  release."0.0.1" = {
    src = lib.const (lib.cleanSourceWith {
      src = lib.cleanSource ./.;
      filter = let
        inherit (lib) all hasSuffix;
        ignorePaths = xs: path: all (x: ! hasSuffix x path) xs;
      in
        path: _: ignorePaths (import ./ignored_paths.nix) path;
    });
  };

  enableParallelBuilding = true;

  nativeBuildInputs = [
    python3
    sphinx
    clang-tools
  ];

  buildInputs = [
    boost
  ];

  propagatedBuildInputs = with coq.ocamlPackages; [
    findlib
    base
    core
    core_unix
    stdio
    parsexp
    hashcons
    zarith
  ];

  preInstall = ''
    dune build README.html
    mkdir -p $out/doc/koika
    cp README.html $out/doc/koika/
  '';

  inherit doCheck;
  checkPhase = ''
    runHook preCheck
    ./coq.kernel.hack.sh
    dune build --always-show-command-line --no-config --profile release @runtest
    runHook postCheck
  '';

  shellHook = ''
    [ -x coq.kernel.hack.sh ] && ./coq.kernel.hack.sh
  '';
}
