#!/usr/bin/env python3
"""
ACTUS Blueprint Build Script

This script helps build the blueprint documentation for the ACTUS project.
It uses leanblueprint to generate dependency graphs and documentation.

Usage:
  python scripts/blueprint.py build   # Build the blueprint
  python scripts/blueprint.py serve   # Serve locally for preview
  python scripts/blueprint.py clean   # Clean generated files
"""

import sys
import os
import subprocess
from pathlib import Path

PROJECT_ROOT = Path(__file__).parent.parent
BLUEPRINT_DIR = PROJECT_ROOT / "blueprint"

def run_command(cmd, cwd=None):
    """Run a shell command and return its output."""
    print(f"Running: {' '.join(cmd)}")
    result = subprocess.run(cmd, cwd=cwd or PROJECT_ROOT, capture_output=True, text=True)
    if result.returncode != 0:
        print(f"Error: {result.stderr}")
        sys.exit(1)
    return result.stdout

def build_blueprint():
    """Build the blueprint documentation."""
    print("Building blueprint...")
    
    # Check if leanblueprint is installed
    try:
        subprocess.run(["leanblueprint", "--version"], check=True, capture_output=True)
    except (subprocess.CalledProcessError, FileNotFoundError):
        print("Error: leanblueprint not found. Install it with:")
        print("  pip install leanblueprint")
        sys.exit(1)
    
    # Build the blueprint
    run_command(["leanblueprint", "build"], cwd=BLUEPRINT_DIR)
    print("Blueprint built successfully!")
    print(f"Output in: {BLUEPRINT_DIR / 'web'}")

def serve_blueprint():
    """Serve the blueprint locally."""
    print("Serving blueprint at http://localhost:8000")
    run_command(["python", "-m", "http.server"], cwd=BLUEPRINT_DIR / "web")

def clean_blueprint():
    """Clean generated blueprint files."""
    print("Cleaning blueprint...")
    import shutil
    web_dir = BLUEPRINT_DIR / "web"
    if web_dir.exists():
        shutil.rmtree(web_dir)
        print("Cleaned web directory")

def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)
    
    command = sys.argv[1]
    
    if command == "build":
        build_blueprint()
    elif command == "serve":
        serve_blueprint()
    elif command == "clean":
        clean_blueprint()
    else:
        print(f"Unknown command: {command}")
        print(__doc__)
        sys.exit(1)

if __name__ == "__main__":
    main()
