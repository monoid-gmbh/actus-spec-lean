# Vendored ACTUS Data Dictionary

`actus-dictionary.json` is a pinned snapshot of the ACTUS Data Dictionary,
used to generate the **Data Dictionary** glossary in the blueprint
(`../src/glossary.tex`, produced by `../../scripts/gen_glossary.py`).

- **Source:** <https://github.com/actusfrf/actus-dictionary> (`master`),
  file `actus-dictionary.json`.
- **Version:** 1.4 (2023-12-08).
- **License:** CC-BY-SA-4.0, © ACTUS Financial Research Foundation.

The file is committed verbatim from upstream. Note that upstream contains a
small data-entry bug — two description fields are delimited with “smart”
double quotes (U+201C/U+201D) instead of ASCII `"`, which is invalid JSON;
the generator normalises these on read (it does not modify this file).

To regenerate the glossary after updating this snapshot:

```
python scripts/gen_glossary.py
```
