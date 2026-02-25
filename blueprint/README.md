# ACTUS Blueprint Documentation

This directory contains the blueprint documentation for the ACTUS Lean 4 formalization.

## What is a Blueprint?

A blueprint is a mathematical documentation system for Lean projects that:

1. **Combines prose and formalization**: Write mathematical explanations in LaTeX/Markdown alongside Lean code
2. **Generates dependency graphs**: Automatically visualizes how definitions depend on each other
3. **Tracks progress**: Shows which parts are formalized vs. planned
4. **Links to source**: Every definition links to its Lean implementation
5. **Creates beautiful output**: Generates both web and PDF documentation

## Structure

```
blueprint/
├── web.toml              # Web version configuration
├── print.toml            # PDF version configuration
├── src/
│   ├── content.md        # Main blueprint content (includes chapters)
│   ├── chapter1.md       # Introduction and architecture
│   ├── chapter2.md       # Core concepts
│   ├── chapter3.md       # PAM contract
│   ├── macros.tex        # LaTeX macros
│   └── deps.lean         # Lean declarations for dependency tracking
└── .gitignore            # Ignore generated files
```

## Building the Blueprint

### Prerequisites

```bash
pip install leanblueprint
```

### Build

```bash
# From project root:
python scripts/blueprint.py build

# Or from blueprint directory:
leanblueprint build
```

### View

```bash
# Serve locally:
python scripts/blueprint.py serve
# Then open http://localhost:8000

# Or directly:
cd blueprint/web && python -m http.server
```

## Blueprint Syntax

In the markdown files, you can reference Lean declarations:

```latex
\begin{definition}
\label{my-definition}
\lean{Actus.Protocol.EventType}
\leanok
Description of the definition.
\end{definition}
```

- `\lean{...}` - Links to the Lean declaration
- `\leanok` - Marks this as formalized (green in the dependency graph)
- `\uses{label1, label2}` - Shows dependencies on other definitions

## Customization

### Adding New Chapters

1. Create `src/chapterN.md`
2. Add `\input{chapterN}` to `content.md`
3. Rebuild

### Adding Macros

Add LaTeX commands to `src/macros.tex` for consistent notation.

### Tracking New Definitions

Add `#check` declarations to `src/deps.lean` for new Lean definitions you want in the dependency graph.

## Output

After building, you'll find:

- `web/` - HTML documentation with interactive dependency graphs
- `print/` - LaTeX source for PDF generation (if configured)

## More Information

- [Leanblueprint documentation](https://github.com/PatrickMassot/leanblueprint)
- [Example blueprints](https://leanprover-community.github.io/sphere-eversion/)
