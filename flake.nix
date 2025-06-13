{
  description = "Basic Haskell Project Flake";
  inputs = {
    haskellProjectFlake.url = "github:mstksg/haskell-project-flake";
    nixpkgs.follows = "haskellProjectFlake/nixpkgs";
  };
  outputs =
    { self
    , nixpkgs
    , flake-utils
    , haskellProjectFlake
    }:
    flake-utils.lib.eachDefaultSystem (system:
    let
      name = "functor-combinators";
      pkgs = import nixpkgs {
        inherit system;
        overlays = [ haskellProjectFlake.overlays."${system}".default ];
      };
      project-flake = pkgs.haskell-project-flake
        {
          inherit name;
          src = ./.;
          excludeCompilerMajors = [ "ghc94" "ghc913" ];
          defaultCompiler = "ghc984";
        };
    in
    {
      packages = project-flake.packages;
      apps = project-flake.apps;
      checks = project-flake.checks;
      devShells = project-flake.devShells;
      legacyPackages."${name}" = project-flake;
    }
    );
}

