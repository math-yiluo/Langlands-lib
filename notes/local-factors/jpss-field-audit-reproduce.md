# Reproducing the JPSS local-field module audit

Companion to [the module audit](jpss-field-audit.md), at Library commit
`26a5c21c0dd926a6ba1106b5c4a08f30fdea612c`.

Copy the Python 3 code below to `audit.py` and run:

```sh
python3 audit.py /path/to/pinned/Library/files /path/to/jpss-field-audit.md > audit.json
```

The script reads files only and uses the Python standard library. It traverses
all `Langlands.*` imports in the three old proof closures and emits the complete
module sets, source marker locations, table classifications and parametric lists.
Import counts are syntactic project-module counts, not kernel declaration
counts. The main note's module tables supply the human source classification;
the script checks their coverage against the markers and keeps the seven
L-dependency relays separate. It reproduces counts, not the semantic judgment
of which argument a port needs.

The scan removes nested block comments, line comments and ordinary quoted
strings, preserving line numbers, and omits imports from marker matching. Its
marker names are defined explicitly in `PATTERNS`. `canonicalNormalized...`
induction definitions do not match the canonical-norm family. Generic
`IsScalarTower` uses and complex `CharZero.eq_neg_self_iff` do not match the
field-structure families. The broad `moduleTopology` marker intentionally
retains five complex endomorphism-topology uses, identified in the main note.

```python
"""Read-only JPSS source audit. Run with the pinned Library root and the main note path as arguments."""
from collections import Counter
from pathlib import Path
import json
import re
import sys

ROOTS = {
    "fe": "Langlands.Representation.RankinSelberg.UnequalRankFunctionalEquationProof",
    "gamma": "Langlands.Representation.RankinSelberg.GammaMultiplicativityProof",
    "L": "Langlands.Representation.RankinSelberg.LFactorMultiplicativityProof",
}

PATTERNS = {
    "PadicField": r"\bPadicField\b",
    "Padic_base": r"\bPadic\s+(?:p\b|\()",
    "canonical_norm": (
        r"\b(?:canonicalNorm|canonicalNormedField|canonicalNormedAlgebra|"
        r"topology_eq_canonicalNormTopology|normalizedAbs_eq_canonicalNorm_pow_degree|"
        r"normalizedAbs_eq_canonicalNorm_pow|normalizedAbs_eq_norm_pow)\b"
    ),
    "canonical_module": r"\btopology_eq_canonicalModule\b",
    "spectral": r"\b(?:spectralNorm\w*|isNonarchimedean_spectralNorm)\b",
    "base_module_structure": r"\b(?:moduleTopology|valuativeExtension|ValuativeExtension)\b",
    "ramification": (
        r"\b(?:ramificationIndex|residueDegree|extensionDegree_pos|ord_algebraMap|"
        r"normalizedAbs_algebraMap\w*)\b"
    ),
    "field_CharZero": r"\bCharZero\s+(?:F(?:\.Carrier)?|K)\b",
}


def strip_comments(text):
    """Erase comments and ordinary strings, preserving every source newline."""
    out, depth, quoted, i = [], 0, False, 0
    while i < len(text):
        if not depth and quoted:
            if text[i] == "\\":
                if i + 1 < len(text) and text[i + 1] == "\n":
                    out.append("\n")
                i += 2
            elif text[i] == '"':
                quoted = False
                i += 1
            else:
                if text[i] == "\n":
                    out.append("\n")
                i += 1
        elif text[i:i + 2] == "/-":
            out.append(" ")
            depth += 1
            i += 2
        elif depth and text[i:i + 2] == "-/":
            depth -= 1
            i += 2
        elif depth:
            if text[i] == "\n":
                out.append("\n")
            i += 1
        elif text[i:i + 2] == "--":
            out.append(" ")
            j = text.find("\n", i)
            i = len(text) if j == -1 else j
        elif text[i] == '"':
            out.append(" ")
            quoted = True
            i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def collect(base):
    cache = {}

    def read(module):
        if module not in cache:
            path = base / (module.replace(".", "/") + ".lean")
            cache[module] = strip_comments(path.read_text()) if path.is_file() else None
        return cache[module]

    def closure(root):
        seen, todo = set(), [root]
        while todo:
            module = todo.pop()
            if module in seen:
                continue
            text = read(module)
            if text is None:
                raise FileNotFoundError(module)
            seen.add(module)
            for match in re.finditer(
                r"^[ \t]*(?:public[ \t]+)?(?:meta[ \t]+)?import[ \t]+([^\n]+)", text, re.M
            ):
                todo.extend(
                    name for name in match[1].split() if name.startswith("Langlands.")
                )
        return seen

    closures = {name: closure(root) for name, root in ROOTS.items()}
    union = set().union(*closures.values())
    texts = {
        module: re.sub(
            r"^[ \t]*(?:public[ \t]+)?(?:meta[ \t]+)?import[^\n]*", "", read(module), flags=re.M
        )
        for module in sorted(union)
    }
    return closures, texts


if __name__ == "__main__":
    base = Path(sys.argv[1]) if len(sys.argv) > 1 else Path.cwd()
    closures, texts = collect(base)
    hits = {
        module: {
            name: [
                [i, line.strip()]
                for i, line in enumerate(text.splitlines(), 1)
                if re.search(pattern, line)
            ]
            for name, pattern in PATTERNS.items()
            if re.search(pattern, text)
        }
        for module, text in texts.items()
    }
    result = {
        "roots": ROOTS,
        "closure": {name: sorted(values) for name, values in closures.items()},
        "closure_sizes": {name: len(values) for name, values in closures.items()},
        "union_size": len(texts),
        "marker_counts": {
            name: sum(name in values for values in hits.values())
            for name in PATTERNS
        },
        "hits": hits,
    }
    # The main note is the human-reviewed classification input.
    note = Path(sys.argv[2]).read_text()
    category = None
    classified = {}
    headings = {
        "The eight foundation modules": "foundation",
        "The twelve modules needing a different argument": "argument",
        "The forty-one canonical-structure and transport modules": "setup",
        "The twelve ancillary arithmetic imports": "ancillary",
        "The five unrelated complex module-topology hits": "complex",
        "The seven L-factor dependency relays": "relay",
    }
    for line in note.splitlines():
        if line.startswith("### "):
            category = headings.get(line[4:])
        elif line.startswith("## "):
            category = None
        match = re.match(r"\| `(Langlands\.[^`]+)` \|", line)
        if match and category is not None:
            assert match[1] not in classified, match[1]
            classified[match[1]] = category
    direct = {m for m, h in hits.items() if set(h) - {"PadicField"}}
    relays = {m for m, c in classified.items() if c == "relay"}
    assert direct == set(classified) - relays
    assert set(classified) <= set(texts)
    padic = {m for m, h in hits.items() if "PadicField" in h}
    remainder = sorted(padic - set(classified))
    result["classification"] = classified
    result["category_counts"] = dict(Counter(classified.values()))
    result["parametric_PadicField_modules"] = remainder
    result["parametric_directory_counts"] = dict(sorted(Counter(
        m.rsplit(".", 1)[0] for m in remainder).items()))
    result["PadicField_partition"] = {
        "all": len(padic), "classified": len(padic & set(classified)),
        "remainder": len(remainder)}
    print(json.dumps(result, indent=2))
```
