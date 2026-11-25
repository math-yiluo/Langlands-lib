# `stx-coimport.py`

This page holds the script `stx-coimport.py` as it is, in the code block below. To use it, save the content of the block under that name.

```python
#!/usr/bin/env python3
"""Co-import tests of the extract (and of the bridge modules) with weil-conjectures.

    python3 tools/stx-coimport.py [--weil /srv/ll-stx/weil]

Run from the workspace root after the extract and the bridge modules are built. Lean is run
without Lake, with the compiled outputs of the workspace, of weil-conjectures and of the packages
on `LEAN_PATH` (both projects use the same Mathlib and packages). Writes `tools/coimport.txt`:

1. **extract + weil-conjectures**: a file importing every module of `StacksCore/` and
   `StacksFrontier/` and `WeilConjectures` must be accepted;
2. **modules loaded by the extract**: a file importing every module of the extract reports how
   many modules it loads, and whether any module of `tools/forbidden-imports.tsv` is among them;
3. **bridges + weil-conjectures**: a file importing the four bridge modules and
   `WeilConjectures`; whatever the result, the Library and `Nyll` modules in the import closure
   of the bridge modules that import `Mathlib` or a forbidden module by name are listed.

The test files are written to `.tmp/coimport/`. Exit status 1 if test 1, 2 or 4 fails.
"""

import argparse
import glob
import os
import re
import subprocess
import sys
import time

WS = os.path.abspath(os.path.join(os.path.dirname(__file__), '..'))
BRIDGES = [
    'Langlands.AlgebraicGeometry.DvrAffineReducedFibre.SchemeReducedFibreProof',
    'Langlands.CommutativeAlgebra.CompleteLocalNormalizationFinitenessProof',
    'Langlands.AlgebraicGeometry.DvrAffineReducedFibreProof',
    'Langlands.AlgebraicGeometry.DvrStableNormalizationProof',
]
IMPORT_RE = re.compile(r'^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)')


def forbidden_modules():
    out = []
    with open(os.path.join(WS, 'tools', 'forbidden-imports.tsv'), encoding='utf-8') as f:
        for line in f:
            if line.strip() and not line.startswith('#'):
                out.append(line.split('\t')[0].strip())
    return out


def run_lean(path, lean_path):
    t0 = time.time()
    r = subprocess.run(['lean', path], env=dict(os.environ, LEAN_PATH=lean_path),
                       capture_output=True, text=True)
    return r.returncode, (r.stdout + r.stderr).strip(), time.time() - t0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--weil', default='/srv/ll-stx/weil')
    args = ap.parse_args()
    work = os.path.join(WS, '.tmp', 'coimport')
    os.makedirs(work, exist_ok=True)
    lp = [os.path.join(WS, '.lake', 'build', 'lib', 'lean'),
          os.path.join(args.weil, '.lake', 'build', 'lib', 'lean')]
    lp += sorted(glob.glob(os.path.join(WS, '.lake', 'packages', '*', '.lake', 'build', 'lib', 'lean')))
    lean_path = ':'.join(lp)
    files = sorted(glob.glob(os.path.join(WS, 'StacksCore', '**', '*.lean'), recursive=True) +
                   glob.glob(os.path.join(WS, 'StacksFrontier', '**', '*.lean'), recursive=True))
    mods = [os.path.relpath(f, WS)[:-5].replace(os.sep, '.') for f in files]
    forbidden = forbidden_modules()
    out = []
    failed = False

    # 1. extract + weil-conjectures
    p1 = os.path.join(work, 'ExtractWeil.lean')
    with open(p1, 'w') as f:
        f.write(''.join(f'import {m}\n' for m in mods))
        f.write('import WeilConjectures\n')
        f.write('\nopen Lean in\nrun_cmd do\n  let env ← getEnv\n  let names := env.header.moduleNames\n')
        f.write('  IO.println s!"modules loaded {names.size}, of weil-conjectures '
                '{(names.filter (·.getRoot == `WeilConjectures)).size}, of the extract '
                '{(names.filter fun m => m.getRoot == `StacksFrontier || m.getRoot == `StacksCore).size}"\n')
        f.write('  IO.println s!"StacksIsNagataRing (extract): {env.contains `StacksIsNagataRing}, '
                'IsNagataRing (weil-conjectures): {env.contains `IsNagataRing}"\n')
    rc, msg, dt = run_lean(p1, lean_path)
    out.append(f'## 1. All {len(mods)} modules of the extract and WeilConjectures')
    out.append(f'{"ACCEPTED" if rc == 0 else "REFUSED"} (exit {rc}, {dt:.0f} s)' + (f'\n{msg[:3000]}' if msg else ''))
    failed |= rc != 0

    # 2. the modules the extract loads
    p2 = os.path.join(work, 'ExtractModules.lean')
    with open(p2, 'w') as f:
        f.write(''.join(f'import {m}\n' for m in mods))
        f.write('\nopen Lean in\nrun_cmd do\n  let names := (← getEnv).header.moduleNames\n')
        f.write('  IO.println s!"modules loaded {names.size}"\n')
        for m in forbidden + ['Mathlib']:
            f.write(f'  IO.println s!"{m} loaded: {{names.contains `{m}}}"\n')
    rc, msg, dt = run_lean(p2, lean_path)
    out.append('')
    out.append(f'## 2. Modules loaded by a file importing all modules of the extract')
    out.append(msg)
    if rc != 0 or 'loaded: true' in msg:
        failed = True
        out.append('FAILED')

    # 3. bridges + weil-conjectures: each bridge module alone, then the four together
    def closure_offenders(roots):
        seen, stack, bad = set(), list(roots), []
        while stack:
            m = stack.pop()
            if m in seen:
                continue
            seen.add(m)
            path = os.path.join(WS, *m.split('.')) + '.lean'
            if not os.path.exists(path):
                continue
            with open(path, encoding='utf-8') as fh:
                for line in fh:
                    mm = IMPORT_RE.match(line)
                    if not mm:
                        continue
                    imp = mm.group(1)
                    if imp == 'Mathlib' or imp in forbidden:
                        bad.append((m, imp))
                    if imp.split('.')[0] in ('Langlands', 'Nyll', 'StacksCore', 'StacksFrontier'):
                        stack.append(imp)
        lib = sorted(x for x in seen if x.split('.')[0] in ('Langlands', 'Nyll'))
        return lib, sorted(set(bad))

    out.append('')
    out.append('## 3. The bridge modules and WeilConjectures')
    for k, roots in enumerate([[b_] for b_ in BRIDGES] + [BRIDGES]):
        p3 = os.path.join(work, f'BridgesWeil{k}.lean')
        with open(p3, 'w') as f:
            f.write(''.join(f'import {m}\n' for m in roots))
            f.write('import WeilConjectures\n')
        rc, msg, dt = run_lean(p3, lean_path)
        lib, bad = closure_offenders(roots)
        what = 'the four bridge modules' if len(roots) > 1 else roots[0]
        out.append(f'{what}: {"ACCEPTED" if rc == 0 else "REFUSED"} (exit {rc}); Library and Nyll modules '
                   f'in its import closure {len(lib)}, of them importing `Mathlib` or a forbidden module by '
                   f'name {len(set(m for m, _ in bad))}' + (f'\n  {msg.splitlines()[0][:400]}' if rc else ''))
    out.append('The Library and Nyll modules in the import closure of the four bridge modules that import '
               '`Mathlib` or a forbidden module by name:')
    for m, imp in bad:
        out.append(f'  {m}\timport {imp}')
    # 4. extract + all of Mathlib + the Library roots (the shared generated lemma names of the
    # extract with Mathlib and the Library are identical theorems, which Lean accepts)
    p4 = os.path.join(work, 'ExtractMathlibLibrary.lean')
    with open(os.path.join(WS, 'STX-LIBRARY-ROOTS.txt')) as fh:
        lib_roots = [x.strip() for x in fh if x.strip()]
    with open(p4, 'w') as f:
        f.write('import Mathlib\n')
        f.write(''.join(f'import {m}\n' for m in mods))
        f.write(''.join(f'import {m}\n' for m in lib_roots))
    rc, msg, dt = run_lean(p4, lean_path)
    out.append('')
    out.append('## 4. All modules of the extract, `import Mathlib` and the five Library roots')
    out.append(f'{"ACCEPTED" if rc == 0 else "REFUSED"} (exit {rc}, {dt:.0f} s)' + (f'\n{msg[:2000]}' if msg else ''))
    failed |= rc != 0
    with open(os.path.join(WS, 'tools', 'coimport.txt'), 'w', encoding='utf-8') as f:
        f.write('\n'.join(out) + '\n')
    print('\n'.join(out))
    return 1 if failed else 0


if __name__ == '__main__':
    sys.exit(main())
```
