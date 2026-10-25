# Reproducing the private audit

Run the following Python from a worker workspace containing this evidence bundle and the registered source directory. Change only the source location if the retained literature is elsewhere, and select a fresh private prefix. It independently recomputes the import closure and original hashes, constructs four private stages, applies the exact patches with zero fuzz, verifies all final Lean hashes and preserves source notices and paired English Markdown. It extracts the small audit modules from the evidence text. It does not run Lean.

The author executed this reconstruction and verified all bytes; repeating the same hash-verified compilation was unnecessary. The official successful service reports in this bundle checked the matching final source bytes. Invoke the printed `lean_check` operations through TaskHub in the approved environment, and collect every terminal result. The current Library must supply the unchanged target and LocalDegree interfaces identified in library.md; a later pin may need a separately recorded adaptation.

```python
from pathlib import Path
import hashlib, json, re, shutil, subprocess

# Run from a project worker workspace; never runs Lean or Lake.
evidence = Path('notes/reuse/anthropic-chebotarev-evidence')
source = Path('/home/taskhub/pilot/literature/Anthropic - Fermat\'s Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2')
prefix = Path('.private/drafts/chebotarev-repro')

def blocks(path, language):
    return re.findall(r'```' + re.escape(language) + r'\n(.*?)\n```', path.read_text(), re.S)
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
inventory, expected = [json.loads(x) for x in blocks(evidence/'inventory.md', 'json')]
seen, order, external = {}, [], set()
def visit(module):
    if module == 'Lean' or module == 'Mathlib' or module.startswith('Lean.') or module.startswith('Mathlib.'):
        external.add(module)
        return
    if module in seen:
        return
    path = module.replace('.', '/') + '.lean'
    text = (source/path).read_text()
    imports = re.findall(r'^import\s+(\S+)', text, re.M)
    seen[module] = dict(path=path, sha256=sha(source/path), lines=len(text.splitlines()), imports=imports)
    for dep in imports:
        visit(dep)
    order.append(module)
visit(inventory['root'])
assert seen == inventory['modules']
assert order == inventory['order']
assert sorted(external) == inventory['external']
assert len(order) == 41 and sum(x['lines'] for x in seen.values()) == 18672

baseline = Path(str(prefix)+'-baseline')
assert not baseline.exists(), 'Choose a fresh prefix; existing drafts are not overwritten.'
baseline.mkdir(parents=True)
for module in order:
    item = seen[module]
    target = baseline/item['path']
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source/item['path'], target)
    target.with_suffix('.md').write_text(
        '# Private external source reproduction\n\n'
        'Source: anthropic-flt-complete-lean-source-6e837e75; exact original path '+item['path']+
        ', SHA256 '+item['sha256']+'. Original Anthropic Apache-2.0 notices are retained. '
        'The later stages apply the exact compatibility, universe and cleanup patches in the audit evidence. '
        'This is unaccepted experimental source, not published mathematics.\n')
for notice in ['LICENSE','NOTICE','ATTRIBUTION.md']:
    shutil.copy2(source/notice, baseline/notice)

bridge_text = (evidence/'bridges.md').read_text()
def bridge_pair(module):
    part = bridge_text.split('## '+module+'.lean\n',1)[1].split('\n## ',1)[0]
    lean = re.search(r'```lean\n(.*?)\n```',part,re.S).group(1)+'\n'
    markdown = re.search(r'```markdown\n(.*?)\n```',part,re.S).group(1)+'\n'
    return lean, markdown
for suffix, text in zip(['.lean','.md'], bridge_pair('AuditRoot')):
    (baseline/('AuditRoot'+suffix)).write_text(text)

previous = baseline
for stage, patch_name in [('patched','compatibility'),('universes','universes'),('cleaned','cleaned')]:
    destination = Path(str(prefix)+'-'+stage)
    assert not destination.exists(), 'Choose a fresh prefix.'
    shutil.copytree(previous, destination)
    patch_path = destination/'.audit.patch'
    patch_path.write_text(blocks(evidence/(patch_name+'.md'),'diff')[0]+'\n')
    subprocess.run(['patch','--batch','--fuzz=0','-p0','-i',str(patch_path.resolve())],
                   cwd=destination,check=True,stdout=subprocess.DEVNULL)
    patch_path.unlink()
    for path in expected:
        assert sha(destination/path) == expected[path][stage], (stage,path)
    previous = destination
for module in ['AuditBridges','AuditRelative','AuditRealization','AuditInspection']:
    for suffix, text in zip(['.lean','.md'],bridge_pair(module)):
        (previous/(module+suffix)).write_text(text)
for module in ['AuditRoot','AuditBridges','AuditRelative','AuditRealization','AuditInspection']:
    part=bridge_text.split('## '+module+'.lean\n',1)[1].split('\n## ',1)[0]
    expected_hash=re.search(r'SHA256 `([0-9a-f]{64})`',part).group(1)
    assert sha(previous/(module+'.lean'))==expected_hash
print('Verified original closure and all cumulative Lean hashes. Final private draft:', previous)
print('Use taskhub_call lean_check, NOT shell Lean/Lake, with these arguments:')
for module, declaration in [
    ('AuditInspection','NumberField.exists_prime_isArithFrobAt_of_isGalois'),
    ('AuditRealization','ChebotarevAudit.realization'),
    ('AuditBridges','ChebotarevAudit.localDegree_ne_one'),
    ('AuditRelative','ChebotarevAudit.relative_frobenius')]:
    print(json.dumps(dict(environment_artifact='3b864ddf-f0af-4c18-8903-c6f813a0ce0f',
                         directory=str(previous),modules=[module],declaration=declaration)))
```
