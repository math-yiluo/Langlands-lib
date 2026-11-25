# `stx-timebuild.py`

This page holds the script `stx-timebuild.py` as it is, in the code block below. To use it, save the content of the block under that name.

```python
#!/usr/bin/env python3
"""Time a full build of the extract from nothing, without touching `.lake/`.

    taskset -c 0-11 python3 tools/stx-timebuild.py [--jobs 12] [--out .tmp/fullbuild]

Every module of `StacksCore/` and `StacksFrontier/` is compiled with `lean` (as `lake build`
does: `-o` olean, `-i` ilean, `-c` C file) into the scratch directory `--out`, in an order that
respects the imports, with at most `--jobs` compilers at a time; Mathlib and the other packages
are read from their compiled outputs in `.lake/packages`. The wall time of the whole build and the
time of every module are written to `OUT/times.tsv` and printed.
"""

import argparse
import glob
import os
import re
import subprocess
import sys
import time
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait

WS = os.path.abspath(os.path.join(os.path.dirname(__file__), '..'))
IMPORT_RE = re.compile(r'^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--jobs', type=int, default=12)
    ap.add_argument('--out', default=os.path.join(WS, '.tmp', 'fullbuild'))
    ap.add_argument('--src', default=WS, help='directory holding StacksCore/ and StacksFrontier/ '
                    '(default: the workspace; another tree, e.g. one exported by `git archive`, '
                    'to compare)')
    args = ap.parse_args()
    files = sorted(glob.glob(os.path.join(args.src, 'StacksCore', '**', '*.lean'), recursive=True) +
                   glob.glob(os.path.join(args.src, 'StacksFrontier', '**', '*.lean'), recursive=True))
    mods = {os.path.relpath(f, args.src)[:-5].replace(os.sep, '.'): f for f in files}
    deps = {}
    for m, f in mods.items():
        ds = set()
        with open(f, encoding='utf-8') as fh:
            for line in fh:
                mm = IMPORT_RE.match(line)
                if mm and mm.group(1) in mods:
                    ds.add(mm.group(1))
        deps[m] = ds
    os.makedirs(args.out, exist_ok=True)
    lp = [args.out] + sorted(glob.glob(os.path.join(WS, '.lake', 'packages', '*', '.lake', 'build', 'lib', 'lean')))
    env = dict(os.environ, LEAN_PATH=':'.join(lp))

    def build(m):
        base = os.path.join(args.out, *m.split('.'))
        os.makedirs(os.path.dirname(base), exist_ok=True)
        t0 = time.time()
        # `--root`: the module name is the file's path relative to the tree (private names and
        # `import all` depend on it)
        r = subprocess.run(['lean', f'--root={args.src}', mods[m], '-o', base + '.olean',
                            '-i', base + '.ilean', '-c', base + '.c'], env=env,
                           capture_output=True, text=True)
        return m, time.time() - t0, r.returncode, (r.stdout + r.stderr)[-2000:]

    done, failed, times = set(), [], {}
    pending = set(mods)
    start = time.time()
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        running = {}
        while pending or running:
            ready = sorted(m for m in pending if deps[m] <= done)
            for m in ready:
                if len(running) >= args.jobs:
                    break
                pending.discard(m)
                running[pool.submit(build, m)] = m
            if not running:
                print('blocked:', sorted(pending)[:5], file=sys.stderr)
                break
            fin, _ = wait(running, return_when=FIRST_COMPLETED)
            for fut in fin:
                m, dt, rc, log = fut.result()
                del running[fut]
                times[m] = dt
                if rc == 0:
                    done.add(m)
                else:
                    failed.append(m)
                    print(f'FAILED {m}\n{log}', file=sys.stderr)
    wall = time.time() - start
    with open(os.path.join(args.out, 'times.tsv'), 'w') as f:
        for m in sorted(times, key=lambda k: -times[k]):
            f.write(f'{m}\t{times[m]:.1f}\n')
    print(f'modules {len(mods)}, built {len(done)}, failed {len(failed)}; jobs {args.jobs}; '
          f'wall {wall:.0f} s; sum of module times {sum(times.values()):.0f} s')
    for m in sorted(times, key=lambda k: -times[k])[:10]:
        print(f'  {times[m]:7.1f} s  {m}')
    return 1 if failed else 0


if __name__ == '__main__':
    sys.exit(main())
```
