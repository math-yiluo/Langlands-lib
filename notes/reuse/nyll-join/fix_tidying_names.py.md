# `fix_tidying_names.py`

This page holds the script `fix_tidying_names.py` as it is, in the code block below. To use it, save the content of the block under that name.

```python
#!/usr/bin/env python3
"""Repair what the tidying of names left wrong, on a whole Library tree.

Usage: fix_tidying_names.py ROOT [--dry-run]

ROOT is the root of a Library tree (the directory that contains `Langlands/`).

The tidying renamed the name space `Langlands.LocalClassField.NYLL` to
`Langlands.LocalClassField.UniverseZero` by replacing the full name only, and moved
`Langlands/ClassField/Global/` to `Langlands/ClassFieldTheory/Global/` and the files of
`Langlands/ClassFieldTheory/Local/NYLL/` to `…/Local/{UniverseZero,Supplied,General}/`.
It left three kinds of text wrong; this script repairs them:

1. Partially qualified names `NYLL.x` (Lean files and pages) that were resolved, from
   inside `Langlands.LocalClassField` or under `open LocalClassField`, to
   `Langlands.LocalClassField.NYLL.x`. They become `UniverseZero.x`. A token `NYLL.x` is
   rewritten only when the first component of `x` is declared in the name space
   `Langlands.LocalClassField.UniverseZero` of the tree and is not also a first component
   of the old adaptation's name space `Langlands.NYLL` (such a conflict is reported and
   left alone). Files under `Langlands/NYLL/` are not touched.
2. Relative links of pages whose target no longer exists because the target moved:
   `…/ClassField/Global/X` and `…/ClassFieldTheory/Local/NYLL/X`. The link is rewritten
   to the file's new place when that file exists.
3. Nothing else: names written in full were already renamed by the tidying.

Prints one line per changed file: `path<TAB>kind<TAB>count`.
"""

import os
import re
import sys

UZ_NS = "Langlands.LocalClassField.UniverseZero"
OLD_ADAPT_NS = "Langlands.NYLL"

DECL_KW = (r"(?:theorem|lemma|def|abbrev|structure|class|inductive|instance|opaque|"
           r"irreducible_def|class\s+inductive)")
MODIFIERS = r"(?:(?:@\[[^\]]*\]\s*)|(?:private|protected|noncomputable|partial|nonrec)\s+)*"
DECL_RE = re.compile(r"^\s*" + MODIFIERS + DECL_KW + r"\s+([^\W\d][\w.'!?₀-₉]*)")
NS_RE = re.compile(r"^\s*namespace\s+([\w.'₀-₉]+)")
SEC_RE = re.compile(r"^\s*section(?:\s+([\w.'₀-₉]+))?\s*$")
END_RE = re.compile(r"^\s*end(?:\s+([\w.'₀-₉]+))?\s*$")


def lean_files(root):
    for d, _, fs in os.walk(os.path.join(root, "Langlands")):
        for f in fs:
            if f.endswith(".lean"):
                yield os.path.join(d, f)


def md_files(root):
    for d, _, fs in os.walk(os.path.join(root, "Langlands")):
        for f in fs:
            if f.endswith(".md"):
                yield os.path.join(d, f)


def strip_comments(text):
    """Remove block and line comments (not nested-exact, good enough for declaration scans)."""
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            if text[i] == "\n":
                out.append("\n")
            i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def declared_first_components(path, namespace):
    """First components (relative to `namespace`) of names declared inside `namespace`."""
    with open(path, encoding="utf-8") as fh:
        text = strip_comments(fh.read())
    stack = []  # entries: ("ns", [components]) or ("sec", name)
    found = set()
    for line in text.splitlines():
        m = NS_RE.match(line)
        if m:
            stack.append(("ns", m.group(1).split(".")))
            continue
        m = SEC_RE.match(line)
        if m:
            stack.append(("sec", m.group(1)))
            continue
        m = END_RE.match(line)
        if m:
            if stack:
                stack.pop()
            continue
        m = DECL_RE.match(line)
        if m:
            current = [c for kind, comps in stack if kind == "ns" for c in comps]
            name = m.group(1)
            if name.startswith("_root_."):
                continue
            full = current + name.split(".")
            target = namespace.split(".")
            if full[: len(target)] == target and len(full) > len(target):
                found.add(full[len(target)])
    return found


def collect(root, namespace, only_under=None):
    names = set()
    for p in lean_files(root):
        rel = os.path.relpath(p, root)
        if only_under is not None and not rel.startswith(only_under):
            continue
        with open(p, encoding="utf-8") as fh:
            head = fh.read()
        if "namespace " + namespace not in head and not (only_under is not None):
            continue
        names |= declared_first_components(p, namespace)
    return names


TOKEN_RE = re.compile(r"(?<![\w.'!?])NYLL\.([^\W\d][\w'!?₀-₉]*)")


def rename_tokens(text, names):
    count = 0

    def sub(m):
        nonlocal count
        if m.group(1) in names:
            count += 1
            return "UniverseZero." + m.group(1)
        return m.group(0)

    return TOKEN_RE.sub(sub, text), count


LINK_RE = re.compile(r"(\]\()([^)\s#]+)((?:#[^)\s]*)?\))")


def fix_links(path, text, root):
    base = os.path.dirname(path)
    count = 0

    def sub(m):
        nonlocal count
        target = m.group(2)
        if "://" in target or target.startswith("/"):
            return m.group(0)
        absolute = os.path.normpath(os.path.join(base, target))
        if os.path.exists(absolute):
            return m.group(0)
        rel = os.path.relpath(absolute, root).replace(os.sep, "/")
        new_rel = None
        if rel.startswith("Langlands/ClassField/Global/"):
            new_rel = "Langlands/ClassFieldTheory/Global/" + rel[len("Langlands/ClassField/Global/"):]
        elif rel.startswith("Langlands/ClassFieldTheory/Local/NYLL/"):
            tail = rel[len("Langlands/ClassFieldTheory/Local/NYLL/"):]
            for sub_dir in ("UniverseZero", "Supplied", "General"):
                cand = "Langlands/ClassFieldTheory/Local/" + sub_dir + "/" + tail
                if os.path.exists(os.path.join(root, cand)):
                    new_rel = cand
                    break
        if new_rel is None or not os.path.exists(os.path.join(root, new_rel)):
            return m.group(0)
        count += 1
        new_target = os.path.relpath(os.path.join(root, new_rel), base).replace(os.sep, "/")
        return m.group(1) + new_target + m.group(3)

    return LINK_RE.sub(sub, text), count


def main():
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    root = os.path.abspath(sys.argv[1])
    dry = "--dry-run" in sys.argv[2:]
    uz = collect(root, UZ_NS)
    old = collect(root, OLD_ADAPT_NS, only_under="Langlands/NYLL/") if os.path.isdir(
        os.path.join(root, "Langlands", "NYLL")) else set()
    conflicts = uz & old
    for c in sorted(conflicts):
        print(f"CONFLICT\t{c}\tdeclared in both {UZ_NS} and {OLD_ADAPT_NS}; not renamed",
              file=sys.stderr)
    names = uz - conflicts
    print(f"# {len(names)} first components declared in {UZ_NS}", file=sys.stderr)
    for p in list(lean_files(root)) + list(md_files(root)):
        rel = os.path.relpath(p, root)
        if rel.startswith("Langlands/NYLL/"):
            continue
        with open(p, encoding="utf-8") as fh:
            text = fh.read()
        new, n_tok = rename_tokens(text, names)
        n_link = 0
        if p.endswith(".md"):
            new, n_link = fix_links(p, new, root)
        if new != text:
            if not dry:
                with open(p, "w", encoding="utf-8") as fh:
                    fh.write(new)
            if n_tok:
                print(f"{rel}\tname NYLL.->UniverseZero.\t{n_tok}")
            if n_link:
                print(f"{rel}\tpage link to moved file\t{n_link}")


if __name__ == "__main__":
    main()
```
