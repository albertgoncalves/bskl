with import <nixpkgs> {};
mkShell.override { stdenv = llvmPackages_12.stdenv; } {
    buildInputs = [
        ghc
        glibcLocales
        gmp
        hlint
        libffi
        llvmPackages_12.lld
        ormolu
        shellcheck
    ];
    APPEND_LIBRARY_PATH = lib.makeLibraryPath [
        gmp
        libffi
    ];
    shellHook = ''
        export LD_LIBRARY_PATH="$APPEND_LIBRARY_PATH:$LD_LIBRARY_PATH"
        . .shellhook
    '';
}
