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

        # The `plastex` console script nixpkgs ships is a binary wrapper whose
        # PYTHONPATH is pinned to plasTeX's own closure, so it cannot import the
        # sibling plugins (leanblueprint, plastexdepgraph, plastexshowmore) that
        # live alongside it in pythonEnv.  The result is that `\lean`, `\uses`
        # and `\dochome` are silently dropped and the blueprint shows no links
        # to the API docs.  This shim runs plasTeX through pythonEnv's python,
        # which sees the whole environment, so the plugins load and every
        # blueprint item links to its Lean declaration in the generated docs.
        plastex = pkgs.writeShellScriptBin "plastex" ''
          exec ${pythonEnv}/bin/python -c 'import sys; sys.argv = ["plastex"] + sys.argv[1:]; from plasTeX.client import plastex; sys.exit(plastex())' "$@"
        '';

        # Toolchain needed to compile the blueprint: the fixed `plastex` shim
        # (must precede pythonEnv on PATH to shadow the broken wrapper),
        # leanblueprint/plasTeX (pythonEnv), graphviz for the dependency graph,
        # and a TeX system for the PDF.  Reused by both the build and serve apps.
        blueprintRuntime = [
          plastex
          pythonEnv
          pkgs.graphviz
          pkgs.texlive.combined.scheme-medium
        ];

        # `nix run .#build` — compile the blueprint (web HTML + dependency
        # graph, then PDF) from the current working tree, so it picks up local
        # edits.  Run from the repository root.
        blueprint-build = pkgs.writeShellApplication {
          name = "blueprint-build";
          runtimeInputs = blueprintRuntime;
          text = ''
            if [ ! -d blueprint ]; then
              echo "error: no ./blueprint here — run from the repository root" >&2
              exit 1
            fi
            cd blueprint || exit 1

            # Call plastex/latexmk directly (the fixed shim is first on PATH)
            # rather than via `leanblueprint web|pdf`, whose plastex subprocess
            # does not pick up the shim.
            echo "==> blueprint: compiling web (HTML + dependency graph)…"
            rm -rf web && mkdir -p web
            ( cd src && plastex -c plastex.cfg web.tex )

            echo "==> blueprint: compiling PDF…"
            if ( cd src && latexmk -xelatex -interaction=nonstopmode -halt-on-error \
                   -auxdir=../print -outdir=../print print.tex ); then
              echo "==> blueprint: PDF ready → blueprint/print/print.pdf"
            else
              echo "warning: PDF compile failed (web is still built)." >&2
            fi

            echo "==> blueprint: web → blueprint/web/index.html"
          '';
        };

        # `nix run .#serve` — serve the blueprint locally at :8000 from the
        # working tree.  Compiles the web version first if it is missing, or
        # always when called as `nix run .#serve -- --rebuild`.
        blueprint-serve = pkgs.writeShellApplication {
          name = "blueprint-serve";
          runtimeInputs = blueprintRuntime;
          text = ''
            if [ ! -d blueprint ]; then
              echo "error: no ./blueprint here — run from the repository root" >&2
              exit 1
            fi
            cd blueprint || exit 1

            if [ "''${1:-}" = "--rebuild" ] || [ ! -f web/index.html ]; then
              echo "==> blueprint: compiling web…"
              rm -rf web && mkdir -p web
              ( cd src && plastex -c plastex.cfg web.tex )
            fi

            echo "==> Serving blueprint at http://localhost:8000  (Ctrl-C to stop)"
            cd web || exit 1
            exec python -m http.server 8000
          '';
        };

      in {
        # Development shell
        devShells.default = pkgs.mkShell {
          buildInputs = [
            # NOTE: Lean/Lake are intentionally NOT provided by nix here.  They
            # come from elan, which reads ./lean-toolchain and fetches the exact
            # upstream release (currently v4.30.0) matching Mathlib's prebuilt
            # cache (`lake exe cache get`).  A nix-pinned Lean tends to mismatch
            # that toolchain and shadow elan, breaking `lake build`.

            # Fixed `plastex` shim (see the `let` block) — must precede
            # pythonEnv so `leanblueprint web` and `plastex` use the
            # plugin-aware one, otherwise the blueprint loses its Lean links.
            plastex

            # Convenience commands, identical to `nix run .#build|serve`
            blueprint-build
            blueprint-serve

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

            # Force the plugin-aware `plastex` shim ahead of the nixpkgs binary
            # wrapper on PATH.  mkShell does not guarantee buildInputs order, and
            # the wrapped `plastex` cannot see the leanblueprint plugins, so
            # without this `leanblueprint web` produces a blueprint with no links
            # to the Lean docs.  Subprocesses (incl. `leanblueprint web`) inherit
            # this PATH, so the shim is used everywhere.
            export PATH="${plastex}/bin:$PATH"

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
            echo "  blueprint-build         - in-shell build (web + pdf)"
            echo "  blueprint-serve         - in-shell serve at http://localhost:8000"
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

        apps = {
          blueprint-build = {
            type = "app";
            program = "${blueprint-build}/bin/blueprint-build";
          };
          blueprint-serve = {
            type = "app";
            program = "${blueprint-serve}/bin/blueprint-serve";
          };
          default = {
            type = "app";
            program = "${blueprint-serve}/bin/blueprint-serve";
          };
        };

      }
    );
}
