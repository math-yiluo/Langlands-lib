# Reproducing the Library atlas

This is the executable source audit for [the module atlas](module-atlas.md),
written by Worker 34. It uses Python 3 and only its standard library. It does
not run Lean, alter the Library, or infer mathematical acceptance.

## Invocation and expected result

Save the Python block below as `atlas_inventory.py` outside the immutable
Library tree, then run:

```bash
python atlas_inventory.py /home/taskhub/pilot/library/fe68653a42ed5ae0a2d7f5cef0697a68e8acc978/files --output atlas-inventory.json
```

Any local checkout of this exact `files/` tree gives the same module, pair and
edge results. `base_commit` is taken from the parent directory name; retain the
published commit separately when using a differently named checkout.
The JSON file contains every module's imports, project importers and source
SHA-256 values. Standard output omits that large module dictionary but includes
the counts, full isolated list and topic counts.

Expected: 315 modules, 315 nonempty pairs, 386 edges, 143 modules without a
project importer, 69 Mathlib-only modules, 21 isolated modules, and zero
missing/empty pairs, unpaired `Langlands/` Markdown files, unresolved
`Langlands.*` imports or import-free modules. The canonical graph digest is
`90ff121be580f0f36d9edb56f8b93a60288b5ef03397b260cea17b0060b66627`.
It hashes the UTF-8 concatenation of sorted, distinct project edges, each
formatted as `importer`, a tab, `dependency`, and a newline.

## Parsing boundary

The scanner masks nested `/- ... -/` comments, `--` comments and ordinary
quoted strings, preserving newlines. It supports the current snapshot's
one-line import declarations, multiple module names on a line, and
`public`/`private`/`meta` modifiers. Blank or comment-only lines and the
`prelude`/`module` header commands are permitted. Module names in this snapshot
use the ASCII identifier syntax checked below.

This is a deliberately bounded source scanner, not the Lean parser. An import
split over code lines, a quoted/unusual module identifier, an unexpected header
line or an import after the first body command raises an error instead of being
silently counted. For example, `import` followed on the next line by a module
name is rejected; so is a continuation module on the next line after a complete
import. If future Lean header syntax changes, extend and validate the scanner
before trusting a new inventory. Imports mentioned inside strings or comments
do not count. The body is otherwise not parsed or checked.

The run on the named snapshot completed without unsupported-syntax errors.
The source/pair hashes make later byte changes visible; the graph digest alone
does not certify unchanged mathematical contents.

## Complete audit program

```python
"""Reproduce the Library source import inventory; no Lean compilation."""
import argparse
import hashlib
import json
import re
from collections import Counter
from pathlib import Path


def mask_comments_and_strings(text):
    """Keep newlines while masking nested Lean comments and string literals."""
    out = list(text)
    i, depth, string, line = 0, 0, False, False
    while i < len(text):
        pair = text[i:i + 2]
        if line:
            if text[i] == "\n":
                line = False
            else:
                out[i] = " "
        elif depth:
            if pair == "/-":
                out[i:i + 2] = "  "
                depth += 1
                i += 1
            elif pair == "-/":
                out[i:i + 2] = "  "
                depth -= 1
                i += 1
            elif text[i] != "\n":
                out[i] = " "
        elif string:
            if text[i] == "\\" and i + 1 < len(text):
                out[i] = " "
                if text[i + 1] != "\n":
                    out[i + 1] = " "
                i += 1
            elif text[i] == '"':
                out[i] = " "
                string = False
            elif text[i] != "\n":
                out[i] = " "
        elif pair == "--":
            out[i:i + 2] = "  "
            line = True
            i += 1
        elif pair == "/-":
            out[i:i + 2] = "  "
            depth = 1
            i += 1
        elif text[i] == '"':
            out[i] = " "
            string = True
        i += 1
    if depth or string:
        raise ValueError("Unterminated block comment or string")
    return "".join(out)


IMPORT = re.compile(r"(?:(?:public|private|meta)[ \t]+)*import[ \t]+(.+)")
MODULE = re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*")
COMMANDS = {
    "abbrev", "attribute", "axiom", "class", "def", "end", "example",
    "export", "inductive", "infix", "infixl", "infixr", "instance",
    "lemma", "local", "macro", "mutual", "namespace", "noncomputable",
    "notation", "open", "opaque", "private", "protected", "section",
    "set_option", "structure", "syntax", "theorem", "universe", "variable",
}


def read_imports(text, relative):
    """Read the snapshot's line-based headers; reject unsupported header syntax."""
    imports = []
    body = False
    for number, line in enumerate(mask_comments_and_strings(text).splitlines(), 1):
        line = line.strip()
        if not line:
            continue
        match = IMPORT.fullmatch(line)
        if match:
            if body:
                raise ValueError(f"Import after body in {relative}:{number}")
            fields = match.group(1).split()
            if not fields or not all(MODULE.fullmatch(field) for field in fields):
                raise ValueError(f"Unsupported import in {relative}:{number}")
            imports.extend(fields)
        elif not body:
            if line in {"prelude", "module"}:
                continue
            first = line.split()[0]
            if first not in COMMANDS and not first.startswith(("@[", "#")):
                raise ValueError(f"Unsupported header in {relative}:{number}: {line}")
            body = True
    return sorted(set(imports))


def inventory(root):
    entries = {}
    for path in sorted(root.rglob("*.lean")):
        relative = path.relative_to(root)
        name = ".".join(relative.with_suffix("").parts)
        text = path.read_text(encoding="utf-8-sig")
        imports = read_imports(text, relative)
        md = path.with_suffix(".md")
        entries[name] = {
            "path": relative.as_posix(),
            "imports": imports,
            "paired": md.is_file() and bool(md.read_text(encoding="utf-8-sig").strip()),
            "lean_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "markdown_sha256": hashlib.sha256(md.read_bytes()).hexdigest() if md.is_file() else None,
        }
    incoming = {name: [] for name in entries}
    for name, row in entries.items():
        row["project_imports"] = [dep for dep in row["imports"] if dep in entries]
        for dep in row["project_imports"]:
            incoming[dep].append(name)
    for name, row in entries.items():
        row["project_importers"] = sorted(incoming[name])
    isolated = [
        name for name, row in entries.items()
        if row["imports"] and all(dep == "Mathlib" or dep.startswith("Mathlib.") for dep in row["imports"])
        and not incoming[name]
    ]
    edges = sorted((name, dep) for name, row in entries.items() for dep in row["project_imports"])
    return {
        "base_commit": root.parent.name,
        "root": str(root),
        "module_count": len(entries),
        "nonempty_pair_count": sum(row["paired"] for row in entries.values()),
        "missing_or_empty_pairs": [name for name, row in entries.items() if not row["paired"]],
        "unpaired_langlands_markdown": sorted(
            str(path.relative_to(root)) for path in (root / "Langlands").rglob("*.md")
            if not path.with_suffix(".lean").is_file()
        ),
        "project_edge_count": sum(len(row["project_imports"]) for row in entries.values()),
        "project_edges_sha256": hashlib.sha256(
            "".join(f"{name}\t{dep}\n" for name, dep in edges).encode()
        ).hexdigest(),
        "no_project_importer_count": sum(not incoming[name] for name in entries),
        "mathlib_only_count": sum(bool(row["imports"]) and all(dep == "Mathlib" or dep.startswith("Mathlib.") for dep in row["imports"]) for row in entries.values()),
        "no_import_count": sum(not row["imports"] for row in entries.values()),
        "unresolved_project_imports": sorted({dep for row in entries.values() for dep in row["imports"] if dep.startswith("Langlands.") and dep not in entries}),
        "isolated_count": len(isolated),
        "isolated": isolated,
        "topic_counts": dict(sorted(Counter(".".join(name.split(".")[:2]) for name in entries).items())),
        "modules": entries,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("root", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = inventory(args.root.resolve())
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in result.items() if k != "modules"}, indent=2))
```
