# ACTUS Lean 4 - Nix Quick Start

This project includes comprehensive Nix support for reproducible development and builds.

## 🚀 Quick Start

### Modern Nix (with flakes)

```bash
# Clone/extract the project
cd actus-lean

# Enter development shell (auto-downloads all dependencies)
nix develop

# Build the Lean project
lake build

# Build blueprint documentation
python scripts/blueprint.py build

# Serve docs at http://localhost:8000
python scripts/blueprint.py serve
```

### Traditional Nix

```bash
# Enter development shell
nix-shell

# Then same commands as above
lake build
python scripts/blueprint.py build
python scripts/blueprint.py serve
```

## 📦 What's Included

The Nix environment provides:

- ✅ **Lean 4.14.0** (via elan, automatically installed)
- ✅ **Lake** (Lean build tool, comes with Lean)
- ✅ **Python 3** with pip and dependencies
- ✅ **Leanblueprint** (auto-installed in `.venv`)
- ✅ **Git, curl, wget** (development tools)
- ✅ **Graphviz** (for dependency graph visualization)
- ✅ **Pandoc** (for documentation conversion)

## 🏗️ Build Commands

### With Flakes

```bash
# Build the Lean project
nix build

# Build blueprint documentation
nix build .#blueprint

# Build everything
nix build .#all

# Run the blueprint server
nix run
```

### Traditional Nix

```bash
# Build the project
nix-build

# Output in ./result/
ls -la result/
```

## 📁 Nix Files

- **flake.nix** - Modern Nix configuration (recommended)
- **flake.lock** - Locked dependency versions for reproducibility
- **shell.nix** - Development environment (traditional Nix)
- **default.nix** - Build configuration (traditional Nix)
- **NIX.md** - Comprehensive Nix documentation

## 🔍 Key Features

### Reproducible Environments

Same setup on every machine - no "works on my machine" issues.

### Automatic Dependency Management

All dependencies (Lean, Python packages, tools) are declared and managed by Nix.

### Virtual Environment Integration

Python packages are installed in a local `.venv` that persists across shell sessions.

### CI/CD Ready

Use in GitHub Actions, GitLab CI, or any CI system with Nix support.

## 💡 Tips

### First Time Setup

The first `nix develop` or `nix-shell` will:
1. Download Lean 4.14.0 (~500MB)
2. Set up Python environment
3. Install leanblueprint in `.venv`

This takes a few minutes but is cached for future use.

### Enabling Flakes

If you get "experimental features" errors, enable flakes:

```bash
# One-time command
nix --extra-experimental-features 'nix-command flakes' develop

# Or permanently in ~/.config/nix/nix.conf
experimental-features = nix-command flakes
```

### Updating Dependencies

```bash
# Update to latest versions
nix flake update

# Or pin specific versions in flake.lock
```

### Optional LaTeX Support

For PDF generation, uncomment the texlive line in `shell.nix`:

```nix
# Uncomment this line:
pkgs.texlive.combined.scheme-medium
```

## 📚 Documentation

- **NIX.md** - Detailed Nix documentation
- **README.md** - General project documentation  
- **PROJECT.md** - Project overview and structure
- **blueprint/README.md** - Blueprint-specific docs

## 🐛 Troubleshooting

### Lean Version Mismatch

```bash
# In the development shell:
elan default $(cat lean-toolchain)
lake clean
lake build
```

### leanblueprint Not Found

Make sure you're in the development shell and the venv is activated:

```bash
source .venv/bin/activate
python -c "import leanblueprint"
```

### Cache Issues

```bash
# Clean everything and rebuild
lake clean
rm -rf .venv .lake
nix develop  # Re-enter shell
```

## 🎯 Next Steps

1. Enter the development shell: `nix develop` or `nix-shell`
2. Build the project: `lake build`
3. Explore the code in `Actus/`
4. Build the docs: `python scripts/blueprint.py build`
5. Read NIX.md for advanced Nix features

Enjoy reproducible Lean development! 🎉
