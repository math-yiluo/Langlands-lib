# `stx-checks.py`

This page holds the script `stx-checks.py` as it is, in the code block below. To use it, save the content of the block under that name.

```python
#!/usr/bin/env python3
"""Checks of the extract (step 5 of the brief).

    python3 tools/stx-checks.py [--repro]

Run from the workspace root after the extract is built. Writes `tools/checks.txt`:

* the words of rule 4.3 (`sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`,
  `extern`) counted in the files of the extract and in their source files, once in the whole
  text and once in the code (comments and strings left out), and the code occurrences listed;
* the counts of the extract beside those of its sources, of the cone and of the whole copy
  (modules, lines, declaration commands kept and left out);
* the root check: `tools/StxRootCheck.lean` on the whole copy (renames applied) and on the
  extract; the serialized types, universe parameters and axioms must be identical;
* with `--repro`: the tool is run twice more; the hashes of everything it writes are compared,
  and `git status --porcelain` must show no change.
"""

import argparse
import collections
import glob
import hashlib
import importlib.util
import os
import re
import subprocess
import sys

sys.dont_write_bytecode = True   # importing the extractor below leaves no __pycache__
WS = os.path.abspath(os.path.join(os.path.dirname(__file__), '..'))
SOURCE = '/srv/ll-stx/full'
WORDS = ['sorry', 'admit', 'axiom', 'native_decide', 'unsafe', 'implemented_by', 'extern']

spec = importlib.util.spec_from_file_location('stx', os.path.join(WS, 'tools', 'stx-extract.py'))
stx = importlib.util.module_from_spec(spec)
spec.loader.exec_module(stx)


def lean_files(root):
    out = []
    for top in ('StacksCore', 'StacksFrontier'):
        out += glob.glob(os.path.join(root, top, '**', '*.lean'), recursive=True)
    return sorted(os.path.relpath(p, root) for p in out)


def word_counts(path):
    with open(path, encoding='utf-8') as f:
        text = f.read()
    t = stx.Text(text)
    code = t.code_text(0, len(text))
    # strings are code for code_text; blank them too
    for s, e, kind in t.spans:
        if kind == 'string':
            code = code[:s] + ' ' * (e - s) + code[e:]
    raw = collections.Counter()
    cod = collections.Counter()
    hits = []
    for w in WORDS:
        pat = re.compile(r'(?<![\w.])' + re.escape(w) + r'(?![\w])')
        raw[w] = len(pat.findall(text))
        for m in pat.finditer(code):
            cod[w] += 1
            line = text.count('\n', 0, m.start()) + 1
            hits.append((w, line, text.split('\n')[line - 1].strip()[:100]))
    return raw, cod, hits, text.count('\n')


def tree_hash():
    h = {}
    paths = lean_files(WS) + ['STX-MANIFEST.tsv', 'tools/extract-stats.txt', 'tools/extract-commands.tsv',
                             'tools/extract-warnings.txt', 'tools/renames-applied.tsv',
                             'tools/extract-imports.tsv']
    for p in paths:
        with open(os.path.join(WS, p), 'rb') as f:
            h[p] = hashlib.sha256(f.read()).hexdigest()
    return h


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--repro', action='store_true')
    args = ap.parse_args()
    if not os.path.exists(os.path.join(WS, '.tmp', 'stx-work', 'summary.txt')):
        # the cone's work data is not kept: make it by running the tool
        subprocess.run([sys.executable, os.path.join(WS, 'tools', 'stx-extract.py')], cwd=WS, check=True,
                       stdout=subprocess.DEVNULL)
    out = []
    files = lean_files(WS)
    # 1. words
    tot = {k: collections.Counter() for k in ('extract raw', 'extract code', 'sources raw', 'sources code')}
    code_hits = []
    src_code_hits = []
    ext_lines = src_lines = 0
    for p in files:
        raw, cod, hits, n = word_counts(os.path.join(WS, p))
        tot['extract raw'].update(raw)
        tot['extract code'].update(cod)
        code_hits += [(p,) + h for h in hits]
        ext_lines += n
        raw, cod, hits, n = word_counts(os.path.join(SOURCE, p))
        tot['sources raw'].update(raw)
        tot['sources code'].update(cod)
        src_code_hits += [(p,) + h for h in hits]
        src_lines += n
    out.append('## Words of rule 4.3 (whole text / code only, comments and strings left out)')
    out.append('word\textract text\textract code\tsources text\tsources code')
    for w in WORDS:
        out.append(f'{w}\t{tot["extract raw"][w]}\t{tot["extract code"][w]}\t'
                   f'{tot["sources raw"][w]}\t{tot["sources code"][w]}')
    out.append('code occurrences in the extract:')
    for h in code_hits:
        out.append('  ' + '\t'.join(str(x) for x in h))
    out.append('code occurrences in the sources of the extract:')
    for h in src_code_hits:
        out.append('  ' + '\t'.join(str(x) for x in h))
    # 2. counts
    whole = lean_files(SOURCE)
    whole_lines = 0
    for p in whole:
        with open(os.path.join(SOURCE, p), encoding='utf-8') as f:
            whole_lines += f.read().count('\n')
    with open(os.path.join(SOURCE, 'StacksCore.lean'), encoding='utf-8') as f:
        whole_lines += f.read().count('\n')
    stats = {}
    with open(os.path.join(WS, 'tools', 'extract-stats.txt')) as f:
        for line in f:
            k, v = line.rstrip('\n').split('\t')
            stats[k] = int(v)
    cone = {}
    with open(os.path.join(WS, '.tmp', 'stx-work', 'summary.txt')) as f:
        for line in f:
            k, v = line.rstrip('\n').split('\t')
            cone[k] = v
    closure_cmds = 0
    with open(os.path.join(WS, '.tmp', 'stx-work', 'commands.tsv')) as f:
        for _ in f:
            closure_cmds += 1
    manifest = collections.Counter()
    with open(os.path.join(WS, 'STX-MANIFEST.tsv')) as f:
        next(f)
        for line in f:
            manifest[line.split('\t')[2]] += 1
    out.append('')
    out.append('## Counts')
    out.append(f'whole copy: {len(whole) + 1} Lean files (with the root StacksCore.lean), {whole_lines} lines')
    out.append(f'import closure of the roots: {cone["copy modules loaded"]} modules, '
               f'{closure_cmds} declaration commands (Lean declaration ranges)')
    out.append(f'cone: {cone["cone modules"]} modules ({cone["of them in StacksFrontier"]} StacksFrontier), '
               f'{cone["cone constants"]} constants, {cone["of them named"]} named '
               f'({cone["of those theorems"]} theorems), {cone["kept commands"]} declaration commands')
    out.append(f'extract: {len(files)} files, {ext_lines} lines; sources of these files: {src_lines} lines')
    out.append(f'extract declaration commands kept {stats["decl commands kept"]}, left out '
               f'{stats["decl commands dropped"]} (in the files of the extract); other commands left out '
               f'{stats["other commands dropped"]}')
    out.append(f'manifest: {manifest["kept"]} declarations kept, {manifest["dropped"]} left out')
    out.append(f'fraction of the whole copy: {len(files) / (len(whole) + 1):.1%} of the files, '
               f'{ext_lines / whole_lines:.1%} of the lines')
    # constants of the whole copy and of the extract (tools/StxNames.lean)
    work = os.path.join(WS, '.tmp', 'check')
    os.makedirs(work, exist_ok=True)
    lpw = [os.path.join(SOURCE, '.lake', 'build', 'lib', 'lean')]
    lpw += sorted(glob.glob(os.path.join(WS, '.lake', 'packages', '*', '.lake', 'build', 'lib', 'lean')))
    whole_mods = sorted(p[:-5].replace('/', '.') for p in whole) + ['StacksCore']
    ext_mods = sorted(p[:-5].replace('/', '.') for p in files)
    for name, mods_, envx in (('whole', whole_mods, dict(os.environ, LEAN_PATH=':'.join(lpw))),
                              ('extract', ext_mods, None)):
        with open(os.path.join(work, name + '-mods.txt'), 'w') as f:
            f.write('\n'.join(mods_) + '\n')
        cmd = ['lean', '--run', os.path.join(WS, 'tools', 'StxNames.lean'), os.path.join(work, name + '.tsv'),
               os.path.join(work, name + '-mods.txt'), 'StacksCore,StacksFrontier']
        if envx is None:
            cmd = ['lake', 'env'] + cmd
        subprocess.run(cmd, cwd=WS, env=envx, check=True)
    gen = re.compile(r'\.(eq_\d+|eq_def|congr_simp|rec|recOn|casesOn|below|brecOn|noConfusion|'
                     r'noConfusionType|mk\._flat_ctor|injEq|inj|sizeOf_spec|ext_iff|binductionOn|ibelow)$')
    for name in ('whole', 'extract'):
        tot = named = priv = 0
        with open(os.path.join(work, name + '.tsv'), encoding='utf-8') as f:
            for line in f:
                n, _, _, p_ = line.rstrip('\n').split('\t')
                tot += 1
                priv += p_ == '1'
                user = re.sub(r'^_private\.(?:[^.]+\.)*?0\.', '', n)
                if not any(c.startswith('_') for c in user.split('.')) and not gen.search(user):
                    named += 1
        out.append(f'constants of the {"whole copy" if name == "whole" else "extract"}: {tot}, of which '
                   f'{priv} private; declared names (no auxiliary or generated suffix) {named}')
    big = collections.Counter()
    for p in files:
        parts = p.split('/')
        big['/'.join(parts[:3])] += 1
    out.append('files of the extract by directory (first three levels):')
    for k, v in sorted(big.items(), key=lambda kv: -kv[1]):
        out.append(f'  {v:4d}  {k}')
    # 3. the roots: types up to the renames, and axioms (tools/StxRootCheck.lean on both sides)
    out.append('')
    out.append('## Roots (rule 4.4): type in the extract = type in the whole copy up to the renames')
    lp = [os.path.join(SOURCE, '.lake', 'build', 'lib', 'lean')]
    lp += sorted(glob.glob(os.path.join(WS, '.lake', 'packages', '*', '.lake', 'build', 'lib', 'lean')))
    work = os.path.join(WS, '.tmp', 'check')
    os.makedirs(work, exist_ok=True)
    script = os.path.join(WS, 'tools', 'StxRootCheck.lean')
    roots = os.path.join(WS, 'tools', 'roots.tsv')
    ren = os.path.join(WS, 'tools', 'renames-applied.tsv')
    subprocess.run(['lean', '--run', script, 'full', os.path.join(work, 'full.tsv'), roots, ren],
                   env=dict(os.environ, LEAN_PATH=':'.join(lp)), check=True)
    subprocess.run(['lake', 'env', 'lean', '--run', script, 'extract', os.path.join(work, 'extract.tsv'),
                    roots, ren], cwd=WS, check=True)
    with open(os.path.join(work, 'full.tsv'), encoding='utf-8') as f:
        full = [l.rstrip('\n').split('\t') for l in f]
    with open(os.path.join(work, 'extract.tsv'), encoding='utf-8') as f:
        ext = [l.rstrip('\n').split('\t') for l in f]
    for a, b in zip(full, ext):
        out.append(f'{a[0]}: universe parameters {a[1]} / {b[1]}; axioms whole copy {a[2]}, extract {b[2]}; '
                   f'serialized type {len(a[3])} characters; ' + ('IDENTICAL' if a == b else 'DIFFERENT'))
    # 4. reproducibility
    if args.repro:
        out.append('')
        out.append('## Reproducibility')
        before = tree_hash()
        for k in (1, 2):
            subprocess.run([sys.executable, os.path.join(WS, 'tools', 'stx-extract.py')], cwd=WS, check=True,
                           stdout=subprocess.DEVNULL)
            after = tree_hash()
            diff = [p for p in set(before) | set(after) if before.get(p) != after.get(p)]
            out.append(f'run {k}: {len(after)} files hashed, {len(diff)} differ from the committed state'
                       + (': ' + ', '.join(sorted(diff)[:10]) if diff else ''))
        st = subprocess.run(['git', 'status', '--porcelain'], cwd=WS, capture_output=True, text=True).stdout
        changed = [l for l in st.splitlines() if not l.endswith('tools/checks.txt')]
        out.append(f'git status after the runs: {len(changed)} changed paths' +
                   (': ' + '; '.join(changed[:10]) if changed else ''))
    with open(os.path.join(WS, 'tools', 'checks.txt'), 'w', encoding='utf-8') as f:
        f.write('\n'.join(out) + '\n')
    print('\n'.join(out[:60]))


if __name__ == '__main__':
    main()
```
