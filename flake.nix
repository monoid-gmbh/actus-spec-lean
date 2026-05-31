{
  description = "ACTUS Formal Specification in Lean 4";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    lean4.url = "github:leanprover/lean4/v4.30.0";
  };

  outputs = { self, nixpkgs, flake-utils, lean4 }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
        };

        pythonEnv = pkgs.python3.withPackages (ps: with ps; [
          pip
          setuptools
          wheel
          requests
          pyyaml
          jinja2
          markdown
          pygments
	  leanblueprint
	  plasTeX
        ]);

        # Lean 4 from the input
        lean = pkgs.lean4; 

      in {
        # Development shell
        devShells.default = pkgs.mkShell {
          buildInputs = [
            # NOTE: Lean/Lake are intentionally NOT provided by nix here.  They
            # come from elan, which reads ./lean-toolchain and fetches the exact
            # upstream release (currently v4.30.0) matching Mathlib's prebuilt
            # cache (`lake exe cache get`).  A nix-pinned Lean tends to mismatch
            # that toolchain and shadow elan, breaking `lake build`.

            # Python for blueprint
            pythonEnv
            
            # Useful development tools
            pkgs.git
            pkgs.curl
            pkgs.wget
            
            # Documentation tools
            pkgs.graphviz  # For dependency graphs
            pkgs.pandoc    # For documentation conversion
            
            # Optional: LaTeX for PDF generation
            pkgs.texlive.combined.scheme-medium
          ];

          shellHook = ''
            echo "🎯 ACTUS Lean 4 Development Environment"
            echo ""

            # Lean/Lake are provided by elan (not nix): elan's shims read
            # ./lean-toolchain and dispatch to the pinned release.  We do NOT
            # prepend a nix Lean to PATH, which would shadow elan with the wrong
            # version.
            if ! command -v elan >/dev/null 2>&1; then
              echo "⚠ elan not found on PATH — install it from https://github.com/leanprover/elan"
              echo "  so that 'lake' uses the toolchain pinned in ./lean-toolchain."
            fi

            # # Create local Python environment for leanblueprint
            # if [ ! -d .venv ]; then
            #   echo "📦 Creating Python virtual environment..."
            #   python -m venv .venv
            # fi
            # 
            # source .venv/bin/activate
            # 
            # # Install leanblueprint if not present
            # if ! python -c "import leanblueprint" 2>/dev/null; then
            #   echo "📦 Installing leanblueprint..."
            #   pip install --quiet leanblueprint
            # fi
            
            echo "Available commands:"
            echo "  lake build              - Build the Lean project"
            echo "  lake clean              - Clean build artifacts"
            echo "  python scripts/blueprint.py build  - Build blueprint docs"
            echo "  python scripts/blueprint.py serve  - Serve blueprint locally"
            echo ""
            echo "✓ Lean version: $(lean --version 2>/dev/null | head -1 || echo 'not found (install elan)')"
            echo "✓ Python version: $(python --version)"
            # echo "✓ Lake is available"
            # echo "✓ Leanblueprint is installed"
            echo ""
          '';
        };

        # Package the Lean project
        packages.default = pkgs.stdenv.mkDerivation {
          pname = "actus-spec-lean";
          version = "0.1.0";
          
          src = ./.;
          
          nativeBuildInputs = [ lean ];
          
          buildPhase = ''
            export HOME=$TMPDIR
            lake build
          '';
          
          installPhase = ''
            mkdir -p $out/lib $out/bin
            cp -r .lake/build/lib/* $out/lib/ 2>/dev/null || true
            cp -r build $out/ 2>/dev/null || true
          '';
          
          meta = with pkgs.lib; {
            description = "ACTUS formal specification in Lean 4";
            homepage = "https://github.com/actus-spec-lean";
            license = licenses.asl20;
            platforms = platforms.unix;
          };
        };

        # Blueprint documentation package
        packages.blueprint = pkgs.stdenv.mkDerivation {
          pname = "actus-spec-blueprint";
          version = "0.1.0";
          
          src = ./.;
          
          nativeBuildInputs = [
            pythonEnv
            pkgs.graphviz
            lean
          ];
          
          buildPhase = ''
            export HOME=$TMPDIR
            
            # Build Lean project first (needed for dependencies)
            lake build
            
            # Build blueprint
            cd blueprint
            python ../scripts/blueprint.py build || {
              # Fallback if leanblueprint isn't working
              echo "Blueprint build skipped (leanblueprint may not be installed)"
              mkdir -p web
            }
          '';
          
          installPhase = ''
            mkdir -p $out/share/doc/actus-spec
            cp -r blueprint/web/* $out/share/doc/actus-spec/ 2>/dev/null || true
            cp -r blueprint/src $out/share/doc/actus-spec/ 2>/dev/null || true
            cp README.md $out/share/doc/actus-spec/
          '';
          
          meta = with pkgs.lib; {
            description = "Blueprint documentation for ACTUS specification";
            homepage = "https://github.com/actus-spec-lean";
            license = licenses.asl20;
            platforms = platforms.unix;
          };
        };

        # Convenience: build everything
        packages.all = pkgs.symlinkJoin {
          name = "actus-spec-all";
          paths = [
            self.packages.${system}.default
            self.packages.${system}.blueprint
          ];
        };

        # Application for running locally
        apps.default = {
          type = "app";
          program = "${pkgs.writeShellScript "actus-serve" ''
            cd ${self.packages.${system}.blueprint}/share/doc/actus-spec
            ${pkgs.python3}/bin/python -m http.server 8000
          ''}";
        };

      }
    );
}
