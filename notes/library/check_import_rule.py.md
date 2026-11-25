# `check_import_rule.py`

This page holds the script `check_import_rule.py` as it is, in the code block below. To use it, save the content of the block under that name.

```python
#!/usr/bin/env python3
"""Check the import rule of the Library's roots.

The repository has the Library (`Langlands/`) and copies of outside libraries that stay libraries of their
own: `Nyll/`, `FontaineWintenberger/`, `StacksCore/`, `StacksFrontier/`, and the dependency
`WeilConjectures`. A file of the Library reaches a copy only through a bridge: a file in one of the bridge
directories below, which states and proves, in the Library's notions, what is taken from the copy. The open
zone of `Nyll/` (`ValuedFieldTheory/Valuation`, `ValuedFieldTheory/LocalField`,
`ClassFieldTheory/LubinTate/FormalModule`) may be imported anywhere. A copy never imports
the Library.

usage: python3 check_import_rule.py <root of the repository> [--list]
exit status 0 when the rule holds, 1 when it does not; --list prints every direct import of a copy."""
import os
import re
import sys

root = sys.argv[1]
show = "--list" in sys.argv[2:]

COPIES = {
    "Nyll": "Nyll",
    "FontaineWintenberger": "FontaineWintenberger",
    "StacksCore": "Stacks",
    "StacksFrontier": "Stacks",
    "WeilConjectures": "WeilConjectures",
}
# modules of a copy that any Library file may import
OPEN = [
    r"^Nyll\.ValuedFieldTheory\.(Valuation|LocalField)(\.|$)",
    r"^Nyll\.ClassFieldTheory\.LubinTate\.FormalModule(\.|$)",
]
# directories of the Library whose files may import a copy directly
BRIDGES = {
    "Nyll": ["Langlands/ClassFieldTheory/"],
    "FontaineWintenberger": ["Langlands/LocalFactor/Ramification/Wintenberger/"],
    "Stacks": ["Langlands/AlgebraicGeometry/DvrAffineReducedFibre/",
               "Langlands/CommutativeAlgebra/CompleteLocalNormalizationFinitenessProof.lean"],
    "WeilConjectures": [],
}
IMPORT = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z0-9_.'«»]+)", re.M)


def lean_files(top):
    for d, dirs, names in os.walk(os.path.join(root, top)):
        dirs[:] = [x for x in dirs if x != ".lake"]
        for n in names:
            if n.endswith(".lean"):
                yield os.path.relpath(os.path.join(d, n), root).replace(os.sep, "/")


def imports(rel):
    text = open(os.path.join(root, rel), encoding="utf-8", errors="replace").read()
    head = text.split("\n/-", 1)[0] if text.lstrip().startswith("import") else text
    return IMPORT.findall(head) or IMPORT.findall(text[:20000])


direct = []          # (library file, copy, imported module)
violations = []
for rel in lean_files("Langlands"):
    for m in imports(rel):
        top = m.split(".")[0]
        if top not in COPIES:
            continue
        copy = COPIES[top]
        direct.append((rel, copy, m))
        if any(re.search(p, m) for p in OPEN):
            continue
        if not any(rel.startswith(b) for b in BRIDGES[copy]):
            violations.append((rel, copy, m))
back = []
for top in ("Nyll", "FontaineWintenberger", "StacksCore", "StacksFrontier"):
    if not os.path.isdir(os.path.join(root, top)):
        continue
    for rel in lean_files(top):
        for m in imports(rel):
            if m.split(".")[0] == "Langlands":
                back.append((rel, m))

by = {}
for rel, copy, m in direct:
    key = (copy, "/".join(rel.split("/")[:3]))
    by.setdefault(key, set()).add(rel)
print("Library files that import a copy directly: %d" % len(set(r for r, _, _ in direct)))
for (copy, d), files in sorted(by.items()):
    print("  %-22s %-50s %d files" % (copy, d, len(files)))
if show:
    for rel, copy, m in sorted(direct):
        print("    %s  <-  %s" % (rel, m))
print("imports outside the bridge directories and the open zone: %d" % len(violations))
for rel, copy, m in sorted(violations):
    print("  %s imports %s" % (rel, m))
print("files of a copy that import the Library: %d" % len(back))
for rel, m in sorted(back)[:40]:
    print("  %s imports %s" % (rel, m))
sys.exit(1 if violations or back else 0)
```
