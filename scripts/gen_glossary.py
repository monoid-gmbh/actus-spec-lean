#!/usr/bin/env python3
"""Generate the blueprint's Data Dictionary glossary from the vendored ACTUS
Data Dictionary snapshot.

Reads  blueprint/dictionary/actus-dictionary.json  and writes
  blueprint/src/glossary.tex   -- the Data Dictionary section (3 tables).
Each row anchors its acronym with \\hypertarget{<prefix>:<acronym>}{...}:
  term:<ACRONYM>   state:<Titlecased>   ct:<ACRONYM>

It then rewrites, in blueprint/src/content.tex, every *text-mode* \\attr{CODE}
(i.e. not inside $...$) whose CODE is a contract term into \\attrl{CODE}, so the
prose acronyms link to their glossary entry.  Formula (math-mode) \\attr is left
untouched (a link there would break MathJax in the web build).

Run:  python scripts/gen_glossary.py
"""
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DICT = ROOT / "blueprint" / "dictionary" / "actus-dictionary.json"
GLOSS = ROOT / "blueprint" / "src" / "glossary.tex"
CONTENT = ROOT / "blueprint" / "src" / "content.tex"


def load():
    raw = DICT.read_text(encoding="utf-8").replace("“", '"').replace("”", '"')
    return json.loads(raw)


def esc(s):
    """Escape a plain-text string for LaTeX."""
    s = s or ""
    s = s.replace("\\", r"\textbackslash{}")
    for a, b in [("&", r"\&"), ("%", r"\%"), ("$", r"\$"), ("#", r"\#"),
                 ("_", r"\_"), ("{", r"\{"), ("}", r"\}"),
                 ("~", r"\textasciitilde{}"), ("^", r"\textasciicircum{}")]:
        s = s.replace(a, b)
    return re.sub(r"\s+", " ", s).strip()


def table(rows):
    """rows: list of (display_acronym, label, name, description)."""
    out = [r"\begin{dicttable}"]
    for disp, label, name, desc in rows:
        # \hypertarget anchors the row in both plasTeX (html id) and xelatex,
        # which \label inside a table cell does not.
        out.append("\t\\hypertarget{%s}{\\texttt{%s}} & %s & %s \\\\ \\hline"
                   % (label, esc(disp), esc(name), esc(desc)))
    out.append(r"\end{dicttable}")
    return "\n".join(out)


def main():
    d = load()
    terms, states, tax = d["terms"], d["states"], d["taxonomy"]

    term_rows, term_keys = [], []
    for v in sorted(terms.values(), key=lambda t: t["acronym"]):
        a = v["acronym"]
        term_rows.append((a, "term:%s" % a, v.get("name", ""), v.get("description", "")))
        term_keys.append(a)

    state_rows, state_keys = [], []
    for v in sorted(states.values(), key=lambda t: t["acronym"]):
        disp = v["acronym"].capitalize()          # blueprint \svar form (IPAC -> Ipac)
        state_rows.append((disp, "state:%s" % disp, v.get("name", ""), v.get("description", "")))
        state_keys.append(disp)

    ct_rows, ct_keys = [], []
    for v in sorted(tax.values(), key=lambda t: t.get("acronym") or ""):
        a = v.get("acronym")
        if not a:
            continue
        ct_rows.append((a, "ct:%s" % a, v.get("name", ""), v.get("description", "")))
        ct_keys.append(a)

    body = []
    body.append(r"\section{Data Dictionary}\label{sec:dict}")
    body.append(
        "The tables below reproduce the \\emph{ACTUS Data Dictionary} (ACTUS "
        "Financial Research Foundation, v1.4, CC-BY-SA-4.0), the normative "
        "glossary of the standard.  They explain every contract-term, "
        "state-variable and contract-type acronym used throughout this "
        "document; the lifecycle event types (\\texttt{IED}, \\texttt{IP}, "
        "\\texttt{PR}, \\dots) are not part of the dictionary and so are not "
        "listed here.  Acronyms in \\texttt{typewriter} font elsewhere in the "
        "blueprint link to their entry below.")
    body.append(r"\subsection{Contract Terms}")
    body.append(table(term_rows))
    body.append(r"\subsection{State Variables}")
    body.append(table(state_rows))
    body.append(r"\subsection{Contract Types}")
    body.append(table(ct_rows))
    GLOSS.write_text("\n\n".join(body) + "\n", encoding="utf-8")

    n_links = link_prose_attr(set(term_keys))

    print("glossary.tex: %d terms, %d states, %d contract types"
          % (len(term_rows), len(state_rows), len(ct_rows)))
    print("content.tex: linked %d prose \\attr occurrences to the glossary" % n_links)


def link_prose_attr(termset):
    """Rewrite text-mode \\attr{CODE} -> \\attrl{CODE} in content.tex for every
    CODE that is a contract term.  Math-mode \\attr (inside $...$) is left as is.
    Idempotent: \\attrl is not matched by the \\attr{ pattern."""
    s = CONTENT.read_text(encoding="utf-8")
    attr = re.compile(r"\\attr\{([A-Za-z0-9]+)\}")
    out, i, n, math, esc, changed = [], 0, len(s), False, False, 0
    while i < n:
        c = s[i]
        if esc:
            out.append(c); esc = False; i += 1; continue
        if c == "\\":
            if s.startswith(r"\[", i) or s.startswith(r"\(", i):
                math = True; out.append(s[i:i + 2]); i += 2; continue
            if s.startswith(r"\]", i) or s.startswith(r"\)", i):
                math = False; out.append(s[i:i + 2]); i += 2; continue
            m = attr.match(s, i)
            if m and not math and m.group(1) in termset:
                out.append(r"\attrl{%s}" % m.group(1)); i = m.end(); changed += 1
                continue
            out.append(c); esc = True; i += 1; continue
        if c == "$":
            math = not math
        out.append(c); i += 1
    CONTENT.write_text("".join(out), encoding="utf-8")
    return changed


if __name__ == "__main__":
    main()
