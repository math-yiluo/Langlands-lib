# `stx-clash.py`

This page holds the script `stx-clash.py` as it is, in the code block below. To use it, save the content of the block under that name.

```python
#!/usr/bin/env python3
"""Find the declarations of the extract whose full names clash with another library.

    python3 tools/stx-clash.py [--work .tmp/names] [--out tools/clashes.tsv]

Run from the workspace root after the extract is built. It dumps (with `tools/StxNames.lean`)

* the constants of the extract's modules (generated constants and instance names included;
  private names do not clash and are skipped),
* the constants of the whole environment of `import Mathlib` (Mathlib with its dependencies),
* the constants of the compiled Library modules (the five roots of `STX-LIBRARY-ROOTS.txt`
  and their closure, `Langlands` and `Nyll`),

and compares the extract's names with those, with `/srv/ll-stx/ref/weil-names.txt` (the
declarations of weil-conjectures), and with a scan of the declaration heads of every Lean file
of `/srv/ll-stx/ref/head/Langlands` (namespaces followed; only names a declaration command
writes, so the scan gives a lower bound for the modules not compiled here).

The extract's names are read from the built extract, that is after the renames. Output: one
line per shared name, `name, module, kind, clashes with, class`; the class is `TO RENAME`, or
`generated lemma of a declaration outside the extract` for an equation or congruence lemma
that Lean realized in a module of the extract for a Mathlib declaration (its name is fixed by
that declaration, and Lean's import accepts the same theorem from several modules).
"""

import argparse
import os
import re
import subprocess
import sys

WS = os.path.abspath(os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(__file__))


def dump(out, mods, roots):
    modfile = out + '.mods'
    with open(modfile, 'w') as f:
        f.write('\n'.join(mods) + '\n')
    subprocess.run(['lake', 'env', 'lean', '--run', os.path.join(WS, 'tools', 'StxNames.lean'),
                    out, modfile, roots], cwd=WS, check=True)


def read_names(path):
    out = {}
    with open(path, encoding='utf-8') as f:
        for line in f:
            name, mod, kind, priv = line.rstrip('\n').split('\t')
            out[name] = (mod, kind, priv == '1')
    return out


DECL_RE = re.compile(
    r'^(?:@\[[^\]]*\]\s*)*'
    r'((?:(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped|local|public|meta)\s+)*)'
    r'(theorem|lemma|def|abbrev|instance|structure|class(?:\s+inductive)?|inductive|opaque|axiom|'
    r'irreducible_def|alias)\s+(?:\([^)]*\)\s+)?([^\s:({\[⟨]+)')


def strip_comments(text):
    """Text with comments blanked (strings kept), by a small Lean lexer."""
    out = []
    i = 0
    n = len(text)
    pat = re.compile(r'--|/-|"')
    while True:
        m = pat.search(text, i)
        if not m:
            out.append(text[i:])
            break
        s = m.start()
        out.append(text[i:s])
        if m.group() == '--':
            e = text.find('\n', s)
            e = n if e < 0 else e
            i = e
        elif m.group() == '/-':
            depth, j = 1, s + 2
            while depth > 0:
                a = text.find('/-', j)
                b = text.find('-/', j)
                if b < 0:
                    j = n
                    break
                if 0 <= a < b:
                    depth, j = depth + 1, a + 2
                else:
                    depth, j = depth - 1, b + 2
            out.append('\n' * text.count('\n', s, j))
            i = j
        else:
            j = s + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == '\\' else 1
            out.append(text[s:j + 1])
            i = j + 1
    return ''.join(out)


def scan_library(root):
    """Full names written by declaration commands of the Lean files below `root`."""
    names = {}
    for d, _, files in os.walk(root):
        for fn in files:
            if not fn.endswith('.lean'):
                continue
            path = os.path.join(d, fn)
            with open(path, encoding='utf-8', errors='replace') as f:
                text = strip_comments(f.read())
            stack = []
            for line in text.split('\n'):
                if not line or line[0].isspace():
                    continue
                m = re.match(r'(?:noncomputable\s+|public\s+|@\[[^\]]*\]\s*)*(namespace|section|end)\b\s*(\S*)', line)
                if m:
                    kw, arg = m.groups()
                    if kw == 'namespace':
                        stack.append(arg.split('.'))
                    elif kw == 'section':
                        stack.append([])
                    elif stack:
                        stack.pop()
                    continue
                m = DECL_RE.match(line)
                if not m:
                    continue
                mods, kw, name = m.groups()
                if 'private' in mods.split():
                    continue
                if kw == 'instance' and (name.startswith(':') or name in ('where', ':=')):
                    continue
                if kw == 'alias' and name.startswith('⟨'):
                    continue
                name = name.rstrip(',')
                if name.startswith('_root_.'):
                    full = name[len('_root_.'):]
                else:
                    ns = [c for part in stack for c in part]
                    full = '.'.join(ns + [name])
                names.setdefault(full, os.path.relpath(path, os.path.dirname(root)))
    return names


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--work', default=os.path.join(WS, '.tmp', 'names'))
    ap.add_argument('--out', default=os.path.join(WS, 'tools', 'clashes.tsv'))
    ap.add_argument('--reuse', action='store_true', help='reuse the dumps of Mathlib and the Library')
    args = ap.parse_args()
    os.makedirs(args.work, exist_ok=True)
    mods = []
    for root in ('StacksCore', 'StacksFrontier'):
        for d, _, files in os.walk(os.path.join(WS, root)):
            for fn in files:
                if fn.endswith('.lean'):
                    rel = os.path.relpath(os.path.join(d, fn), WS)[:-len('.lean')]
                    mods.append(rel.replace(os.sep, '.'))
    mods.sort()
    ext_path = os.path.join(args.work, 'extract.tsv')
    dump(ext_path, mods, 'StacksCore,StacksFrontier')
    ml_path = os.path.join(args.work, 'mathlib.tsv')
    lib_path = os.path.join(args.work, 'lib.tsv')
    scan_path = os.path.join(args.work, 'library-scan.tsv')
    if not (args.reuse and os.path.exists(ml_path)):
        dump(ml_path, ['Mathlib'], '*')
    if not (args.reuse and os.path.exists(lib_path)):
        with open(os.path.join(WS, 'STX-LIBRARY-ROOTS.txt')) as f:
            roots = [x.strip() for x in f if x.strip()]
        dump(lib_path, roots, 'Langlands,Nyll')
    if not (args.reuse and os.path.exists(scan_path)):
        scan = scan_library('/srv/ll-stx/ref/head/Langlands')
        with open(scan_path, 'w', encoding='utf-8') as f:
            for k in sorted(scan):
                f.write(f'{k}\t{scan[k]}\n')
    scan = {}
    with open(scan_path, encoding='utf-8') as f:
        for line in f:
            k, v = line.rstrip('\n').split('\t')
            scan[k] = v
    ext = read_names(ext_path)
    ml = read_names(ml_path)
    lib = read_names(lib_path)
    with open('/srv/ll-stx/ref/weil-names.txt', encoding='utf-8') as f:
        weil = set(x.rstrip('\n') for x in f)
    rows = []
    counts = {'weil-conjectures': 0, 'Mathlib': 0, 'Library (compiled)': 0, 'Library (scan)': 0}
    for name in sorted(ext):
        mod, kind, priv = ext[name]
        if priv:
            continue
        hits = []
        if name in weil:
            hits.append('weil-conjectures')
        if name in ml:
            hits.append(f'Mathlib ({ml[name][1]} in {ml[name][0]})')
        if name in lib:
            hits.append(f'Library ({lib[name][1]} in {lib[name][0]})')
        elif name in scan:
            hits.append(f'Library scan ({scan[name]})')
        if hits:
            # A lemma Lean generates for a declaration outside the extract (`X.eq_1`,
            # `X.congr_simp` of a Mathlib definition, realized in a module of the extract): its
            # name is fixed by `X`, and Lean's import accepts the same theorem (same name, type and
            # universe parameters) from several modules (`subsumesInfo`), so it cannot clash.
            m = re.search(r'\.(eq_\d+|eq_def|congr_simp)$', name)
            if m and kind == 'theorem' and name[:m.start()] in ml and name[:m.start()] not in ext:
                cls = 'generated lemma of a declaration outside the extract'
            else:
                cls = 'TO RENAME'
            rows.append((name, mod, kind, '; '.join(hits), cls))
            for h in hits:
                for k in counts:
                    if h.startswith(k.split(' ')[0]) and (k != 'Library (scan)' or 'scan' in h) and \
                            (k != 'Library (compiled)' or 'scan' not in h):
                        counts[k] += 1
    with open(args.out, 'w', encoding='utf-8') as f:
        f.write('name\tmodule\tkind\tclashes with\tclass\n')
        for r in rows:
            f.write('\t'.join(r) + '\n')
    public = sum(1 for v in ext.values() if not v[2])
    print(f'extract constants {len(ext)}, not private {public}; same names {len(rows)}, '
          f'of which to rename {sum(1 for r in rows if r[4] == "TO RENAME")}')
    for k, v in counts.items():
        print(f'  with {k}: {v}')
    print(f'library scan: {len(scan)} names; weil-conjectures: {len(weil)} names')


if __name__ == '__main__':
    main()
```
