# Hasse–Arf evidence: reproduction procedure

Supporting evidence for the [audit note](../anthropic-hasse-arf-audit.md). These records are development evidence, not mathematical acceptance.

Save the Python block below as `.private/hasse-arf-reproduce.py`, then run it from a project worker workspace containing the public evidence directory and the unchanged host Library files. Use Python 3.9 or later and the ordinary `patch` command. Pass the registered source directory explicitly; use a fresh private destination.

```sh
python .private/hasse-arf-reproduce.py --source "/home/taskhub/pilot/literature/Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2"
```

The script reconstructs only under `.private/drafts`, verifies every original module and adapted Lean hash, preserves notices, and prints three `lean_check` calls. Invoke those operations through TaskHub in the approved environment, collecting each terminal result. The original request is expected to fail; the patched root and adapter are expected to pass. Build time, warnings emitted from caches, service scratch paths and source-workspace fingerprints may differ. The stable comparisons are source bytes, stated module/declaration names, types, universes, logical assumptions and results.

The archived reports record the actual historical checks; rerunning is a new development check, never retroactive independent acceptance. The script does not reconstruct historical failure variants automatically: their exact `.lean.txt` blocks are included in checks 05–07 if needed. No shell Lean/Lake invocation, Mathlib download, or project package change is involved.

The author ran this reconstruction procedure on 25 October 2026: all 53 original files, 8,170 original lines, all adapted Lean hashes and the bridge pair matched. This was a byte-level reconstruction check; the Lean results remain those linked in checks 01–09.

<!-- evidence-file: reproduce.py -->

## reproduce.py

SHA256 of the exact UTF-8 block: `044bba4fe3c7c7b42c2ed521e9f823fc614192eaa46c57dcc85c087c3c21a4bd`.

````python
"""Reconstruct the private audit experiment; never invoke Lean or Lake."""
import argparse
import hashlib
import json
import re
import shutil
import subprocess
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--evidence', type=Path,
                    default=Path('notes/reuse/anthropic-hasse-arf-evidence'))
parser.add_argument('--source', type=Path, required=True,
                    help='registered source tree at the exact pinned commit')
parser.add_argument('--output', type=Path,
                    default=Path('.private/drafts/hasse-arf-reproduced'))
args = parser.parse_args()

def block(page, name):
    text = (args.evidence / page).read_text()
    marker = f'<!-- evidence-file: {name} -->\n'
    section = text.split(marker, 1)[1]
    match = re.search(r'^````[^\n]*\n(.*?)^````\n', section, re.M | re.S)
    if not match:
        raise ValueError(f'Missing block {name}')
    return match[1]

def sha(data):
    return hashlib.sha256(data).hexdigest()

expected = json.loads(block('inventory.md', 'closure.json'))
adapted_hashes = json.loads(block('inventory.md', 'adapted-hashes.json'))
seen, order, external = {}, [], set()
def visit(module):
    if module in seen:
        return
    path = args.source / (module.replace('.', '/') + '.lean')
    if not path.is_file():
        external.add(module)
        return
    data = path.read_bytes()
    text = data.decode('utf-8')
    imports = []
    for line in text.splitlines():
        match = re.match(r'\s*(?:(?:public|private|meta)\s+)*import\s+(.+)', line)
        if match:
            imports.extend(match[1].split('--')[0].split())
    seen[module] = dict(module=module, path=str(path.relative_to(args.source)),
                        sha256=sha(data), lines=len(text.splitlines()), imports=imports)
    for dep in imports:
        visit(dep)
    order.append(module)
visit(expected['root'])
actual = [seen[m] for m in order]
assert actual == expected['files'], 'Source import closure or bytes differ'
assert sorted(external) == expected['external_imports'], 'Import boundary differs'
assert len(actual) == 53 and sum(x['lines'] for x in actual) == 8170
assert not args.output.exists(), 'Choose a fresh private output directory'
assert args.output.resolve().is_relative_to(Path('.private/drafts').resolve())
original, adapted = args.output / 'original', args.output / 'adapted'
for dest in [original, adapted]:
    dest.mkdir(parents=True)
    for entry in actual:
        p = dest / entry['path']
        p.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(args.source / entry['path'], p)
        p.with_suffix('.md').write_text(
            '# Private source audit copy\n\n'
            f'Pinned original: `{entry["path"]}`, SHA256 `{entry["sha256"]}`. '
            'Anthropic FLT commit 6e837e75355538c7f80bab5b956861e86c4eacc2; '
            'copyright 2026 Anthropic, PBC, Apache-2.0. '
            'Preserve LICENSE, NOTICE and ATTRIBUTION.md, including the original '
            'Mathlib notices. The adapted tree applies exactly the retained '
            'two-file compatibility patch. This is an unaccepted private experiment.\n')
    for name in ['LICENSE', 'NOTICE', 'ATTRIBUTION.md']:
        shutil.copyfile(args.source / name, dest / name)
patch = block('compatibility.md', 'patch01.diff')
subprocess.run(['patch', '--batch', '-p1', '-d', str(adapted)],
               input=patch, text=True, check=True)
for entry in adapted_hashes:
    assert sha((adapted / entry['path']).read_bytes()) == entry['sha256'], entry['path']
for name in ['HasseArfAudit.lean', 'HasseArfAudit.md']:
    data = block('bridge.md', name)
    (adapted / name).write_text(data)
expected_bridge = json.loads(block('bridge.md', 'bridge-hashes.json'))
for entry in expected_bridge:
    assert sha((adapted / entry['path']).read_bytes()) == entry['sha256']
print('Verified 53 original modules / 8170 lines; exact adapted Lean hashes and bridge match.')
root_decl = 'IsDiscreteValuationRing.hasseArfChain_lowerRamificationGroup_of_isMulCommutative'
for directory, module, decl in [(original, expected['root'], root_decl),
                                (adapted, expected['root'], root_decl),
                                (adapted, 'HasseArfAudit', 'HasseArfAudit.integrality')]:
    print(json.dumps({'operation': 'lean_check', 'arguments': {
        'environment_artifact': '3b864ddf-f0af-4c18-8903-c6f813a0ce0f',
        'directory': str(directory), 'modules': [module], 'declaration': decl}}, indent=2))
````
