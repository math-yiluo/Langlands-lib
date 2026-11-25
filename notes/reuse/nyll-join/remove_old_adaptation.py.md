# `remove_old_adaptation.py`

This page holds the script `remove_old_adaptation.py` as it is, in the code block below. To use it, save the content of the block under that name.

```python
#!/usr/bin/env python3
"""Point the last users of the old adaptation `Langlands/NYLL/` at the copy `Nyll/`, then
remove `Langlands/NYLL/`.

Usage: remove_old_adaptation.py ROOT [--dry-run]

ROOT is the root of a Library tree (the directory that contains `Langlands/` and, for the
check of step 3, the copy `Nyll/`).

The old adaptation split NYLL's source files into modules under the name space
`Langlands.NYLL`; the copy keeps NYLL's own modules and name spaces. The last uses of the
adaptation in the Library are of two layers of the copy's open zone, and this script knows
exactly those:

* the finite-module completeness lemma of
  `Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/HenselianFinite.lean`:
  `NYLL.ValuationTheory.DiscreteValuationField.isAdicComplete_of_moduleFinite.{u, v} R M I`
  (ring and module explicit) becomes
  `ValuationTheory.DiscreteValuationField.isAdicComplete_of_moduleFinite.{u, v} (R := R) (M := M) I`
  (the copy has them implicit; the universe order is the same);
* the linear-term calculus of Lubin–Tate formal modules
  (`Nyll/ClassFieldTheory/LubinTate/FormalModule/LinearTerm.lean` and
  `StandardFormalGroup.lean`): `open Langlands.NYLL.LubinTate.SameUniformizer` becomes
  `open LubinTate.SameUniformizer`; the names (`linearForm`, `HasLinearTerm`,
  `constantCoeff_linearForm`, `HasLinearTerm.constantCoeff_eq_zero`,
  `HasLinearTerm.coeff_eq_linearForm`, `HasLinearTerm.coeff_single`) are the same, and the
  copy states them directly where the adaptation had `…Statement` definitions.

Import lines `import Langlands.NYLL.X` are mapped to the module of the copy that holds X's
source (table `IMPORTS`); duplicate import lines are dropped. Pages (`.md`) get the same
renames of module paths and names.

Afterwards the script checks the tree: no file outside `Langlands/NYLL/` may import a
module `Langlands.NYLL.…`, open its name space, or write a name `NYLL.X` or
`Langlands.NYLL.X` whose first component `X` is declared by the adaptation. If anything is
left, it lists it and stops without deleting. Otherwise it deletes `Langlands/NYLL/`.

Prints one line per changed file (`path<TAB>what`) and the result of the check.
"""

import os
import re
import shutil
import sys

# Module prefixes of the old adaptation -> module of the copy that holds the source.
IMPORTS = [
    ("Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.HenselianFinite.",
     "Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.HenselianFinite"),
    ("Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup.",
     "Nyll.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup"),
    ("Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.LinearTerm.",
     "Nyll.ClassFieldTheory.LubinTate.FormalModule.LinearTerm"),
]

OPENS = [
    ("Langlands.NYLL.LubinTate.SameUniformizer", "LubinTate.SameUniformizer"),
]

LEMMA_OLD = re.compile(
    r"(?<![\w.'])(?:Langlands\.)?NYLL\.ValuationTheory\.DiscreteValuationField\."
    r"isAdicComplete_of_moduleFinite(\.\{[^}]*\})?")
LEMMA_NEW = "ValuationTheory.DiscreteValuationField.isAdicComplete_of_moduleFinite"

# Page text: module paths and names of the adaptation -> those of the copy.
PAGE_RENAMES = [
    ("`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.HenselianFinite.CompletenessProofs`",
     "`Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.HenselianFinite`"),
    ("`NYLL.ValuationTheory.DiscreteValuationField.isAdicComplete_of_moduleFinite`",
     "`ValuationTheory.DiscreteValuationField.isAdicComplete_of_moduleFinite`"),
]


def files(root, ext):
    for d, _, fs in os.walk(os.path.join(root, "Langlands")):
        for f in fs:
            if f.endswith(ext):
                yield os.path.join(d, f)


def rel(root, p):
    return os.path.relpath(p, root).replace(os.sep, "/")


def parse_arg(text, i):
    """Return (argument text, end index) of one explicit argument starting at or after i."""
    n = len(text)
    while i < n and text[i] in " \t\n":
        i += 1
    start = i
    if i < n and text[i] == "(":
        depth = 0
        while i < n:
            if text[i] == "(":
                depth += 1
            elif text[i] == ")":
                depth -= 1
                if depth == 0:
                    i += 1
                    break
            i += 1
        return text[start:i], start, i
    while i < n and not text[i].isspace() and text[i] not in "()":
        i += 1
    return text[start:i], start, i


def strip_parens(a):
    if a.startswith("(") and a.endswith(")"):
        return a[1:-1]
    return a


def rewrite_lemma(text):
    out, pos, count = [], 0, 0
    for m in LEMMA_OLD.finditer(text):
        if m.start() < pos:
            continue
        univ = m.group(1) or ""
        r_arg, s1, e1 = parse_arg(text, m.end())
        m_arg, s2, e2 = parse_arg(text, e1)
        if not r_arg or not m_arg or r_arg.startswith("(R :=") or r_arg == "_":
            continue
        # keep the original spacing and line breaks between the name and the arguments
        out.append(text[pos:m.start()])
        out.append(f"{LEMMA_NEW}{univ}{text[m.end():s1]}(R := {strip_parens(r_arg)})"
                   f"{text[e1:s2]}(M := {strip_parens(m_arg)})")
        pos = e2
        count += 1
    out.append(text[pos:])
    return "".join(out), count


def rewrite_imports(text):
    lines, seen, count, out = text.split("\n"), set(), 0, []
    for line in lines:
        m = re.match(r"^(public\s+)?import\s+(Langlands\.NYLL\.\S+)\s*$", line)
        if m:
            for prefix, target in IMPORTS:
                if m.group(2).startswith(prefix):
                    line = (m.group(1) or "") + "import " + target
                    count += 1
                    break
        m2 = re.match(r"^(?:public\s+)?import\s+(\S+)\s*$", line)
        if m2:
            if m2.group(1) in seen:
                count += 1
                continue
            seen.add(m2.group(1))
        out.append(line)
    return "\n".join(out), count


def rewrite_opens(text):
    count = 0
    for old, new in OPENS:
        pat = re.compile(r"(?m)^(\s*open\b[^\n]*?)(?<![\w.])" + re.escape(old) + r"(?![\w.])")
        text, n = pat.subn(lambda m: m.group(1) + new, text)
        count += n
    return text, count


DECL = re.compile(r"^\s*(?:(?:@\[[^\]]*\]\s*)|(?:private|protected|noncomputable)\s+)*"
                  r"(?:theorem|lemma|def|abbrev|structure|class|inductive|instance)\s+([^\W\d][\w.']*)")


def adaptation_first_components(root):
    """First components (below `Langlands.NYLL`) of the names the adaptation declares."""
    comps = set()
    base = os.path.join(root, "Langlands", "NYLL")
    for d, _, fs in os.walk(base):
        for f in fs:
            if not f.endswith(".lean"):
                continue
            ns = []
            for line in open(os.path.join(d, f), encoding="utf-8"):
                m = re.match(r"^\s*namespace\s+(\S+)", line)
                if m:
                    ns.append(m.group(1).split("."))
                    continue
                m = re.match(r"^\s*end\s+(\S+)\s*$", line)
                if m and ns and ".".join(ns[-1]).endswith(m.group(1)):
                    ns.pop()
                    continue
                m = DECL.match(line)
                if m:
                    full = [c for part in ns for c in part] + m.group(1).split(".")
                    if full[:2] == ["Langlands", "NYLL"] and len(full) > 2:
                        comps.add(full[2])
    return comps


def check(root, comps):
    problems = []
    tok = re.compile(r"(?<![\w.'])(?:Langlands\.)?NYLL\.([^\W\d][\w']*)")
    for p in files(root, ".lean"):
        r = rel(root, p)
        if r.startswith("Langlands/NYLL/"):
            continue
        text = open(p, encoding="utf-8").read()
        for i, line in enumerate(text.split("\n"), 1):
            if re.match(r"^\s*(public\s+)?import\s+Langlands\.NYLL\.", line):
                problems.append(f"{r}:{i}: imports the adaptation: {line.strip()}")
            elif re.match(r"^\s*open\b.*\bLanglands\.NYLL\b", line):
                problems.append(f"{r}:{i}: opens the adaptation: {line.strip()}")
            else:
                code = line.split("--", 1)[0]
                for m in tok.finditer(code):
                    if m.group(1) in comps:
                        problems.append(f"{r}:{i}: name of the adaptation: {m.group(0)}")
    return problems


def main():
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    root = os.path.abspath(sys.argv[1])
    dry = "--dry-run" in sys.argv[2:]
    adapt = os.path.join(root, "Langlands", "NYLL")
    comps = adaptation_first_components(root) if os.path.isdir(adapt) else set()
    for p in list(files(root, ".lean")) + list(files(root, ".md")):
        r = rel(root, p)
        if r.startswith("Langlands/NYLL/"):
            continue
        text = open(p, encoding="utf-8").read()
        new, what = text, []
        if p.endswith(".lean"):
            new, n = rewrite_imports(new)
            if n:
                what.append(f"imports re-pointed at the copy ({n})")
            new, n = rewrite_opens(new)
            if n:
                what.append(f"open of the adaptation's name space re-pointed ({n})")
            new, n = rewrite_lemma(new)
            if n:
                what.append(f"isAdicComplete_of_moduleFinite of the copy, named arguments ({n})")
        else:
            n = 0
            for old, rep in PAGE_RENAMES:
                n += new.count(old)
                new = new.replace(old, rep)
            if n:
                what.append(f"page: module path and name of the adaptation replaced by the copy's ({n})")
        if new != text:
            if not dry:
                open(p, "w", encoding="utf-8").write(new)
            print(f"{r}\t{'; '.join(what)}")
    problems = check(root, comps) if not dry else []
    if problems:
        print("CHECK FAILED: uses of the adaptation remain; nothing deleted")
        for line in problems:
            print("  " + line)
        sys.exit(1)
    if os.path.isdir(adapt):
        n_files = sum(len(fs) for _, _, fs in os.walk(adapt))
        if not dry:
            shutil.rmtree(adapt)
        print(f"Langlands/NYLL/\tdeleted ({n_files} files){' [dry run]' if dry else ''}")
    else:
        print("Langlands/NYLL/\talready absent")
    print("CHECK PASSED: no file imports, opens or names the old adaptation")


if __name__ == "__main__":
    main()
```
