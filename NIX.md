# Nix Support for ACTUS Lean 4

This project provides complete Nix integration for reproducible builds and development environments.

## Overview

The Nix configuration provides:

- ✅ **Reproducible environments** - Same setup on any machine
- ✅ **Automatic dependency management** - Lean, Python, build tools
- ✅ **Multiple entry points** - Development shell, builds, serving docs
- ✅ **Both flakes and traditional Nix** - Choose your preferred workflow

## Files

- `flake.nix` - Modern Nix flakes configuration
- `flake.lock` - Locked dependency versions
- `shell.nix` - Traditional Nix development shell
- `default.nix` - Traditional Nix build
- `.gitignore` - Excludes build artifacts

## Usage

### Development Shell

The development shell provides everything needed to work on the project:

#### With Flakes

```bash
nix develop
```

#### Without Flakes

```bash
nix-shell
```

**What you get:**
- Lean 4.14.0 (via elan)
- Lake (Lean build tool)
- Python 3 with pip
- Leanblueprint (auto-installed in `.venv`)
- Git, curl, wget
- Graphviz (for dependency graphs)
- Pandoc (for documentation)

**Optional additions:**
- Uncomment `texlive` lines in `shell.nix` for PDF generation

### Building the Project

#### With Flakes

```bash
# Build Lean code
nix build

# Build blueprint documentation
nix build .#blueprint

# Build everything
nix build .#all
```

#### Without Flakes

```bash
nix-build
```

Outputs will be in `./result/`

### Running the Blueprint Server

#### With Flakes

```bash
nix run
```

This serves the blueprint documentation at `http://localhost:8000`

## How It Works

### Flakes Workflow

1. `nix develop` reads `flake.nix`
2. Fetches Lean 4.14.0 from the official repository
3. Sets up Python environment
4. Creates `.venv` and installs leanblueprint
5. Drops you into a shell with everything ready

### Traditional Workflow

1. `nix-shell` reads `shell.nix`
2. Uses elan to manage Lean versions
3. Reads `lean-toolchain` to install Lean 4.14.0
4. Same Python setup as flakes

### Build Process

1. Sets up temporary HOME for Lean
2. Runs `lake build`
3. Copies build artifacts to Nix store
4. Makes them available via `./result/`

## Customization

### Adding Dependencies

Edit the `buildInputs` in `flake.nix` or `shell.nix`:

```nix
buildInputs = [
  pkgs.elan
  pythonEnv
  pkgs.yourPackage  # Add here
];
```

### Enabling LaTeX

Uncomment in `shell.nix`:

```nix
pkgs.texlive.combined.scheme-medium
```

### Python Packages

Add to `pythonEnv`:

```nix
pythonEnv = pkgs.python3.withPackages (ps: with ps; [
  pip
  yourPackage  # Add here
]);
```

## Troubleshooting

### "Lean version mismatch"

The `lean-toolchain` file pins Lean to v4.14.0. If you see version mismatches:

```bash
# In development shell
elan default $(cat lean-toolchain)
lake clean
lake build
```

### "leanblueprint not found"

The blueprint is installed in `.venv`. Make sure you're in the development shell:

```bash
source .venv/bin/activate
python -c "import leanblueprint"  # Should work
```

### "Flakes not enabled"

Enable flakes in your Nix configuration:

```bash
# ~/.config/nix/nix.conf
experimental-features = nix-command flakes
```

Or use one-time:

```bash
nix --extra-experimental-features 'nix-command flakes' develop
```

### "Hash mismatch" errors

The flake.lock includes placeholder hashes. To update:

```bash
nix flake update
```

This fetches the latest versions and updates hashes.

## CI/CD Integration

### GitHub Actions

```yaml
name: Build
on: [push]
jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - uses: cachix/install-nix-action@v20
        with:
          extra_nix_config: |
            experimental-features = nix-command flakes
      - run: nix build
      - run: nix build .#blueprint
```

### GitLab CI

```yaml
build:
  image: nixos/nix:latest
  script:
    - nix --extra-experimental-features 'nix-command flakes' build
```

## Docker Integration

Build a Docker image from the Nix closure:

```bash
nix build
docker load < $(nix-build docker.nix)
```

(Requires creating `docker.nix` - see Nix manual)

## Advanced: Nix Packages

The flake exports multiple packages:

- `default` - The Lean project
- `blueprint` - Blueprint documentation
- `all` - Everything together

Access them:

```bash
nix build .#default
nix build .#blueprint
nix build .#all
```

## References

- [Nix Manual](https://nixos.org/manual/nix/stable/)
- [Nix Flakes](https://nixos.wiki/wiki/Flakes)
- [Lean 4 Manual](https://leanprover.github.io/lean4/doc/)
- [Leanblueprint](https://github.com/PatrickMassot/leanblueprint)
