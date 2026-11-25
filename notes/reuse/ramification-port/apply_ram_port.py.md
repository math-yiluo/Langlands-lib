# `apply_ram_port.py`

This page holds the script `apply_ram_port.py` as it is, in the code block below. To use it, save the content of the block under that name.

```python
#!/usr/bin/env python3
"""Moves the users of the ramification block of the FLT extract to the ported modules.

Usage: tools/apply_ram_port.py <tree> [--apply] [--report FILE]

<tree> is a Library checkout (the directory that contains `Langlands/`).  The script performs on
it the edits that the port made to Library files outside the block, and nothing else:

1. `import Langlands.AnthropicFLT.<block module>` becomes the import of the new module that holds
   that module's declarations (IMPORTS below, from RAM-NAMES.tsv);
2. every old full name of a block declaration (RAM-NAMES.tsv: `IsLocalRing.herbrandPhi`,
   `FixedPoints.maximalIdeal_subring_eq_comap`, …) becomes its new name, written relative to
   `Langlands.Ramification` when the occurrence lies inside a `namespace Langlands.Ramification…`
   (or `Ramification.…` inside another `namespace Langlands…`), and in full elsewhere; this applies
   to Lean code, comments and the paired Markdown pages;
3. a mention of an old module name `Langlands.AnthropicFLT.<block module>` in text becomes the new
   module name.
EXTRA holds per-file replacements for edits that the rules do not produce (none are needed).

The new files of the port and the extract itself are not touched.  Without --apply nothing is
written.  The report lists, per file, the imports and names replaced, and then every file of the
tree that still imports a block module or mentions an old name (in Lean code or text).
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
WS = os.path.dirname(HERE)
R = 'Langlands.Ramification'
NEWPREFIX = 'Langlands.LocalFactor.Ramification.'


def load_table():
    rows = []
    with open(os.path.join(WS, 'RAM-NAMES.tsv'), encoding='utf-8') as f:
        next(f)
        for line in f:
            old, new, om, nm = line.rstrip('\n').split('\t')
            rows.append((old, new, om, nm))
    return rows


ROWS = load_table()
BLOCK_MODULES = sorted({om for _, _, om, _ in ROWS} | {
    # modules of the block that declare only private or auto-generated names
    line.split('\t')[1].replace('/', '.')[:-5]
    for line in open(os.path.join(WS, '..', 'ref', 'RAM-BLOCK.tsv') if os.path.exists(
        os.path.join(WS, '..', 'ref', 'RAM-BLOCK.tsv')) else '/srv/ll-ram/ref/RAM-BLOCK.tsv',
        encoding='utf-8').read().split('\n')[1:] if line})
NEW_MODULES = sorted({nm for _, _, _, nm in ROWS if nm.startswith(NEWPREFIX)} |
                     {NEWPREFIX + 'SeparableResidueField'})

# old module -> new module that holds its (ported) declarations
IMPORTS = {}
for om in BLOCK_MODULES:
    nms = {nm for _, new, o, nm in ROWS if o == om and nm.startswith(NEWPREFIX)}
    nms.discard(NEWPREFIX + 'Filtration')
    if not nms:
        nms = {nm for _, new, o, nm in ROWS if o == om and nm.startswith('Mathlib.')}
    if len(nms) == 1:
        IMPORTS[om] = nms.pop()
    elif om.endswith('Def_Compat_Mathlib430'):
        IMPORTS[om] = 'Mathlib.NumberTheory.RamificationInertia.Galois'
    elif nms:
        IMPORTS[om] = sorted(nms)[0]
# the statement modules' solution modules and the statement modules map alike
for om in BLOCK_MODULES:
    if om not in IMPORTS:
        twin = om.replace('.P2M.Sol.S_', '.Theorems.Thm_') if '.P2M.Sol.S_' in om else \
            om.replace('.Theorems.Thm_', '.P2M.Sol.S_')
        if twin in IMPORTS:
            IMPORTS[om] = IMPORTS[twin]

NAMES = {old: new for old, new, _, _ in ROWS
         if new != '—' and not old.startswith('P2MW.') and not old.startswith('_')}
NAME_RE = re.compile(r"(?<![\w.'])(" + '|'.join(re.escape(o) for o in
                                                 sorted(NAMES, key=len, reverse=True)) + r")(?![\w'])")
MOD_RE = re.compile(r"(?<![\w.])(" + '|'.join(re.escape(m) for m in
                                              sorted(IMPORTS, key=len, reverse=True)) + r")(?![\w.])")

# per-file extra replacements: path relative to the tree -> [(old text, new text)]
EXTRA = {}
# Imports a user needs once the block's modules, which imported `Langlands.MathlibBase`, are no
# longer in its import closure: Mathlib modules of instances or lemmas the user's own proofs use.
EXTRA_IMPORTS = {
    'Langlands/LocalFactor/Ramification/Herbrand/QuotientProof.lean': [
        'Mathlib.FieldTheory.Finite.GaloisField'],
    # downstream of a user: `Finset.mulActionFinset` was reached only through the block
    'Langlands/LocalFactor/DeligneHenniartTopLayerOrbits.lean': [
        'Mathlib.Algebra.Group.Action.Pointwise.Finset'],
}


def namespace_at(text):
    """List of (offset, current namespace) changes for a Lean text."""
    out = [(0, '')]
    stack = []
    for m in re.finditer(r'(?m)^(namespace (\S+)|(?:noncomputable )?section(?: (\S+))?\s*$|end(?: (\S+))?\s*$)', text):
        if m.group(2):
            stack.append(('ns', m.group(2).split('.')))
        elif m.group(0).lstrip().startswith(('section', 'noncomputable')):
            stack.append(('sec', [m.group(3)] if m.group(3) else []))
        else:
            want = m.group(4).split('.') if m.group(4) else None
            got = []
            while stack:
                k, comps = stack.pop()
                got = comps + got
                if want is None or len(got) >= len(want):
                    break
        ns = '.'.join(c for k, cs in stack if k == 'ns' for c in cs)
        out.append((m.end(), ns))
    return out


def spell(new, ns):
    if ns == R or ns.startswith(R + '.'):
        return new[len(R) + 1:] if new.startswith(R + '.') else new
    if (ns == 'Langlands' or ns.startswith('Langlands.')) and new.startswith('Langlands.'):
        return new[len('Langlands.'):]
    return new


def transform(path, text, is_lean):
    log = []
    # 1. imports
    def imp(m):
        new = IMPORTS[m.group(1)]
        log.append(f'import {m.group(1)} -> {new}')
        return 'import ' + new
    if is_lean:
        text = re.sub(r'(?m)^import (' + '|'.join(re.escape(m) for m in IMPORTS) + r')[ \t]*$', imp, text)
        # an import that now appears twice is kept once
        seen, lines = set(), []
        for l in text.split('\n'):
            if l.startswith('import '):
                if l in seen:
                    log.append(f'duplicate {l} removed')
                    continue
                seen.add(l)
            lines.append(l)
        text = '\n'.join(lines)
        for extra in EXTRA_IMPORTS.get(path, []):
            line = 'import ' + extra
            if line not in text.split('\n'):
                imps = [i for i, l in enumerate(text.split('\n')) if l.startswith('import ')]
                ls = text.split('\n')
                ls.insert(imps[-1] + 1, line)
                text = '\n'.join(ls)
                log.append(f'import {extra} added')
    # 2. names
    marks = namespace_at(text) if is_lean else [(0, '')]
    def ns_of(pos):
        cur = ''
        for off, ns in marks:
            if off <= pos:
                cur = ns
            else:
                break
        return cur
    def nm(m):
        new = NAMES[m.group(1)]
        s = spell(new, ns_of(m.start())) if is_lean else new
        log.append(f'{m.group(1)} -> {s}')
        return s
    text = NAME_RE.sub(nm, text)
    # 3. module names in text
    def mod(m):
        log.append(f'module {m.group(1)} -> {IMPORTS[m.group(1)]}')
        return IMPORTS[m.group(1)]
    text = MOD_RE.sub(mod, text)
    for a, b in EXTRA.get(path, []):
        if a in text:
            text = text.replace(a, b)
            log.append(f'extra: {a!r} -> {b!r}')
    return text, log


def excluded(rel):
    if rel.startswith('Langlands/AnthropicFLT/'):
        return True
    mod = rel[:-len(os.path.splitext(rel)[1])].replace('/', '.')
    return mod in NEW_MODULES


def main():
    args = sys.argv[1:]
    if not args:
        print(__doc__)
        sys.exit(2)
    tree = args[0]
    apply = '--apply' in args
    report_path = args[args.index('--report') + 1] if '--report' in args else None
    changed, out = [], []
    for dp, dn, fns in os.walk(os.path.join(tree, 'Langlands')):
        dn.sort()
        for fn in sorted(fns):
            if not fn.endswith(('.lean', '.md')):
                continue
            p = os.path.join(dp, fn)
            rel = os.path.relpath(p, tree)
            if excluded(rel):
                continue
            text = open(p, encoding='utf-8').read()
            new, log = transform(rel, text, fn.endswith('.lean'))
            if new != text:
                changed.append((rel, log))
                if apply:
                    open(p, 'w', encoding='utf-8').write(new)
    out.append(f'# apply_ram_port report for {os.path.abspath(tree)}' + (' (applied)' if apply else ' (dry run)'))
    out.append('')
    out.append(f'{len(changed)} files changed.')
    out.append('')
    for rel, log in changed:
        counts = {}
        for l in log:
            counts[l] = counts.get(l, 0) + 1
        out.append(f'## {rel}')
        for l, c in sorted(counts.items()):
            out.append(f'- {l}' + (f' (×{c})' if c > 1 else ''))
        out.append('')
    # remaining mentions (after the edits, or as they would be after them)
    out.append('## Remaining mentions of the block')
    out.append('')
    rem = 0
    for dp, dn, fns in os.walk(os.path.join(tree, 'Langlands')):
        dn.sort()
        for fn in sorted(fns):
            if not fn.endswith(('.lean', '.md')):
                continue
            p = os.path.join(dp, fn)
            rel = os.path.relpath(p, tree)
            if excluded(rel):
                continue
            text = open(p, encoding='utf-8').read()
            if not apply:
                text, _ = transform(rel, text, fn.endswith('.lean'))
            imps = [m for m in re.findall(r'(?m)^import (Langlands\.AnthropicFLT\.\S+)', text) if m in BLOCK_MODULES]
            mentions = sorted(set(NAME_RE.findall(text)))
            mods = sorted(set(MOD_RE.findall(text)))
            if imps or mentions or mods:
                rem += 1
                out.append(f'- {rel}: imports {imps}, names {mentions}, modules {mods}')
    out.append(f'{rem} files still mention the block.')
    txt = '\n'.join(out) + '\n'
    if report_path:
        open(report_path, 'w', encoding='utf-8').write(txt)
    print(txt)


if __name__ == '__main__':
    main()
```
