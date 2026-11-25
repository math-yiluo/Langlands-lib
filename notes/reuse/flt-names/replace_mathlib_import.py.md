# `replace_mathlib_import.py`

This page holds the script `replace_mathlib_import.py` as it is, in the code block below. To use it, save the content of the block under that name.

```python
#!/usr/bin/env python3
"""Replace `import Mathlib` by `import Langlands.MathlibBase` in every Lean file of a tree.

Usage: notes/reuse/flt-names/replace_mathlib_import.py <tree> [--apply]

Without --apply nothing is written: the script reports what it would change.  In the import header of
every `.lean` file of <tree> (leading comments, `module`/`prelude`, import lines; `.lake/` is skipped) a
line that is exactly `import Mathlib` (trailing blanks or a `--` comment allowed) becomes
`import Langlands.MathlibBase`; nothing else in the file changes.  `Langlands/MathlibBase.lean` itself is
never touched (make it with notes/reuse/flt-names/make_mathlib_base.py).

Report: the number of files changed, by directory (the first two path components below the tree, three
for `Langlands/AnthropicFLT`), and the list of files that import directly one of the three Mathlib modules
that clash with weil-conjectures (see Langlands/MathlibBase.lean).  Lines `public import Mathlib` (in a
`module` file) are listed and not changed, since an ordinary module cannot be imported publicly there.
"""
import os
import re
import sys
from collections import Counter

EXCLUDED = ('Mathlib.CategoryTheory.GuitartExact.Prod', 'Mathlib.RingTheory.Depth.Basic',
            'Mathlib.RepresentationTheory.Stabilizer')
tree = sys.argv[1]
apply = '--apply' in sys.argv[2:]
plain = re.compile(r'^(\s*)import(\s+)Mathlib(\s*(?:--.*)?)$')
public = re.compile(r'^\s*public\s+(?:meta\s+)?import\s+Mathlib\s*(?:--.*)?$')
anyimp = re.compile(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(.*?)\s*(?:--.*)?$')


def header_end(lines):
    """index of the first line after the import header"""
    depth = 0
    for i, line in enumerate(lines):
        s = line.strip()
        if depth:
            depth += s.count('/-') - s.count('-/')
            continue
        if not s or s.startswith('--'):
            continue
        if s.startswith('/-') and not s.startswith('/-!') and not s.startswith('/--'):
            depth = s.count('/-') - s.count('-/')
            continue
        if s in ('module', 'prelude') or s.startswith('module ') or anyimp.match(line):
            continue
        return i
    return len(lines)


changed = Counter()
direct = []
public_lines = []
nfiles = 0
for root, dirs, files in os.walk(tree):
    dirs[:] = sorted(d for d in dirs if not d.startswith('.'))  # .lake, .git, .tmp, …
    for f in sorted(files):
        if not f.endswith('.lean'):
            continue
        p = os.path.join(root, f)
        rel = os.path.relpath(p, tree)
        if rel == os.path.join('Langlands', 'MathlibBase.lean'):
            continue
        nfiles += 1
        text = open(p, encoding='utf-8').read()
        lines = text.split('\n')
        end = header_end(lines)
        hit = False
        for i in range(end):
            m = anyimp.match(lines[i])
            if m:
                for mod in m.group(1).split():
                    if mod in EXCLUDED:
                        direct.append((rel, i + 1, mod))
            if public.match(lines[i]):
                public_lines.append((rel, i + 1))
                continue
            mm = plain.match(lines[i])
            if mm:
                lines[i] = f'{mm.group(1)}import{mm.group(2)}Langlands.MathlibBase{mm.group(3)}'
                hit = True
        if hit:
            parts = rel.split(os.sep)
            key = os.sep.join(parts[:3] if parts[:2] == ['Langlands', 'AnthropicFLT'] else parts[:2])
            if len(parts) <= 2:
                key = parts[0] if len(parts) > 1 else '.'
            changed[key] += 1
            if apply:
                open(p, 'w', encoding='utf-8').write('\n'.join(lines))

print(f'{"changed" if apply else "would change"} {sum(changed.values())} of {nfiles} Lean files in {tree}')
for k, v in sorted(changed.items()):
    print(f'{v:6d}  {k}')
print(f'files that import one of {", ".join(EXCLUDED)} directly: {len(direct)}')
for rel, ln, mod in direct:
    print(f'  {rel}:{ln}: {mod}')
if public_lines:
    print(f'`public import Mathlib` lines left unchanged: {len(public_lines)}')
    for rel, ln in public_lines:
        print(f'  {rel}:{ln}')
if not os.path.exists(os.path.join(tree, 'Langlands', 'MathlibBase.lean')):
    print('note: the tree has no Langlands/MathlibBase.lean yet (notes/reuse/flt-names/make_mathlib_base.py makes it)')
```
