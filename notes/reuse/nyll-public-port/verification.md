# NYLL partition: generation and verification record

Worker 25, 25 October 2026. [Main plan](../nyll-public-port-plan.md) ·
[Inventory](index.md).

## Evidence limits

This inventory is generated from pinned original files, not from Lean's
elaborated environment. It counts source declaration commands and records their
source namespace spellings. It is not an exact dependency analysis, a list of
all generated kernel declarations or semantic acceptance of any unit.

The extractor removes nested comments and string contents while retaining line
positions, then recognizes declaration commands and namespace/section boundaries.
For instances it consumes an optional priority annotation before reading the
optional source name, including a name on the following line; an ordinary
anonymous-instance binder is not a priority annotation.
It found 7,340 commands: 5,370 theorem, 37 lemma, 1,469 def, 116 abbrev,
46 structure, 3 class and 299 instance. Among the commands, 555 are private and
68 are local. No unmatched namespace/section boundary was reported. The source
spelling of a private declaration is not its mangled kernel identifier. Generated
structure fields, recursors and automatic instances belong to their parent
unit and are not separate source commands.

The private catalogue also retains signature snippets for navigation. Those
snippets omit section-variable context and may stop at a dependent let; they
are deliberately not published as exact theorem types. Full source reading and
a declaration inspection are required for every actual target. The row labels
for Prop-like definitions are lexical hints, explicitly marked with a question
mark in the inventory.

No Lean module was edited or checked in this partition task. The existing terminal
feasibility records remain the build evidence; this planning work neither
reruns nor strengthens those results. The three new children have their own
future compilation and review obligations.

## Source reading supporting the specific decisions

The following precise reading extents support the manually written boundary
and reuse decisions. They are not a claim that all 7,340 declarations were
semantically audited. Other rows remain B0/B1 unless explicitly marked otherwise.
All paths are under the original `Nyll/` tree; exact full paths are in the
linked module inventory.

| Source | Reading extent used here | Resulting distinction |
| --- | --- | --- |
| M005, `GaloisCohomology/GroupTheory/QuotientTower` | Entire file, 62 lines | Quotient type equivalences; no normality assumption. |
| M103, valuation `DiscreteValuationField/Basic` | Lines 37–100, plus initial instance boundary | Chosen field/value-group data and canonical residue aliases; later DVR theorems excluded. |
| M111, `NonarchimedeanLocalField/ValuedTopology` | Entire file, 68 lines | Precise supplied-valued topology target and future neighborhood-comparison proof. |
| M003, `GaloisCohomology/Cyclic/TateComparison` | Entire file, 138 lines | Three proof-bearing homological isomorphism definitions. |
| M007, `ProfiniteIntegers/TopologicalGeneration` | Lines 1–110 | Predicate, subgroup, map and density boundaries. |
| M092, `LocalField/NormUnits` | Entire file | Source norm has no finite-dimensional premise. |
| M258, `LocalReciprocity/NormResidue` | Entire file | Actual named continuous Artin map and comparison/surjectivity/kernel interface. |
| M128, `NonarchimedeanLocalField/Basic` | Lines 1–72 | Normalized unit-valued exponent definition `v`; sign comparison remains open. |
| M129, `NonarchimedeanLocalField/Norm` | Lines 1–110 | Distinct scalar inclusion and unit norm, including norm of an included scalar. |
| M131, `NonarchimedeanLocalField/PrincipalUnits` | Lines 1–98 | Actual integer-unit subgroup and zero-step equality with top. |
| M134, `NonarchimedeanLocalField/ValuationExactSequence` | Lines 1–68 | Distinct multiplicative/additive valuation data; the source `valuationMap_apply` compares with `v`. |
| M161, `NonarchimedeanLocalField/FiniteUnramified` | Lines 1–135 | Prop class is actual ideal ramification index one and needs finite integer-module structure. |
| M262, `LocalReciprocity/GeneralTowerNaturality` | Lines 440–484 with root signature context from retained diagnostics | Same-family automorphism conjugation and tower restriction. |
| M269, `LocalReciprocity/UnramifiedNormalization` | Lines 1–36 and 489–600; full selected signatures retained in feasibility evidence | Exact Type 0, supplied valuation-extension and unramified hypotheses; arithmetic versus host geometric convention. |
| M288, `FixedFieldIntrinsicReciprocity/NormRestriction` | Lines 665–781 with retained full root signature | Four-field norm square and host transfer specialization boundary. |
| M328, ramification `LocalField/ResidueInertia` | Entire file, 113 lines | Actual residue kernel; integral closure and finite integer modules remain hypotheses. |
| M355/M359, Lubin–Tate `FiniteLevel/CompletedEvaluation` and `LevelAutomorphisms` | Lines 28–50 and 25–43 respectively | Both priority-annotated private/local instances have explicit source names in namespace `LubinTate`. |
| M420, `Filtered/FiniteAbelian` | Lines 1–123 | General filtered proof uses standard domination and descent. No shorter zero-depth closure claimed. |
| M421–M422, `Small` and `ShrinkTransport` | Both entire files; lines 210–253 reread for generic transport | Smallness precedes transported data; two generic extension lemmas preserve broader universes/rings. |

Library bodies were read for `Norms`, `FiniteArtin`, `RelativeIntegers`,
`ResidueNormalization`, `CanonicalTransport` and `ExtensionValuationTransport`;
the relevant statement body was read in `InertiaFixedFieldUnramifiedStatement`.
The route also uses declaration searches in `ExtensionFieldTransport` and
normalization definitions. Their names and qualifications appear in the main
reuse table. The initial three child searches included current tasks and exact
Library/approved-Mathlib declaration searches. These searches do not establish
that no semantic alternative exists.

## Reproduction

The scripts below are the inventory implementation used for this note. They use
only the Python standard library and native source files; they never execute
Lean, install a repository or alter shared sources. Save them at the indicated
private paths in a disposable writable workspace, then run them in this order:

```text
python .private/nyll-partition/prepare_inputs.py
python .private/nyll-partition/catalogue.py
python .private/nyll-partition/render_plan.py
```

The first script extracts the six JSON payloads from the immutable feasibility
evidence and verifies their advertised SHA-256 values. It unifies their exact
source records without running the earlier feasibility preparation scripts.
The second script reads and hash-checks the originals and constructs the source
inventory. The third renders the 21 source appendices and the index, checks
backward import edges, visits every selected root, compares all six module sets
with their manifests, and checks prospective data/proof/target name uniqueness.
It does not overwrite the manually written plan or routing record.

## Instance source-name audit

The source headers of all 27 commands previously labeled anonymous were reread.
M355.001 and M359.001 explicitly name their instances after `(priority := 50)`;
the other 25 have an immediate binder or result-type colon and no source name.
The corrected catalogue retains all unit IDs, start lines, scopes, adapted
`PortInternal` names and scheduling edges. This is a source-spelling check,
not a semantic classification of the instances.

| Source unit | Source line | Source spelling after header inspection |
| --- | ---: | --- |
| `M008.002` | 32 | `(anonymous instance)` |
| `M008.009` | 71 | `(anonymous instance)` |
| `M008.010` | 76 | `(anonymous instance)` |
| `M008.011` | 81 | `(anonymous instance)` |
| `M008.012` | 86 | `(anonymous instance)` |
| `M008.013` | 91 | `(anonymous instance)` |
| `M008.014` | 96 | `(anonymous instance)` |
| `M008.016` | 105 | `(anonymous instance)` |
| `M010.024` | 191 | `(anonymous instance)` |
| `M010.114` | 1048 | `(anonymous instance)` |
| `M010.125` | 1147 | `(anonymous instance)` |
| `M010.139` | 1297 | `(anonymous instance)` |
| `M032.006` | 87 | `(anonymous instance)` |
| `M032.007` | 92 | `(anonymous instance)` |
| `M032.008` | 97 | `(anonymous instance)` |
| `M032.012` | 137 | `(anonymous instance)` |
| `M032.013` | 142 | `(anonymous instance)` |
| `M032.014` | 147 | `(anonymous instance)` |
| `M032.015` | 154 | `(anonymous instance)` |
| `M162.001` | 43 | `(anonymous instance)` |
| `M162.008` | 204 | `(anonymous instance)` |
| `M162.010` | 246 | `(anonymous instance)` |
| `M296.014` | 146 | `(anonymous instance)` |
| `M299.002` | 48 | `(anonymous instance)` |
| `M299.004` | 61 | `(anonymous instance)` |
| `M355.001` | 45 | `LubinTate.standardLubinTateLevelCoefficientUniformSpace` |
| `M359.001` | 38 | `LubinTate.standardLubinTateLevelAutomorphismCoefficientUniformSpace` |

### `.private/nyll-partition/prepare_inputs.py`

SHA-256: `5445160ca130d8c5570d1cfe429b734ac254c3a683493b77bfc8907546c6d572`.

```python
"""Reconstruct only inventory inputs from the immutable feasibility evidence."""
from pathlib import Path
import hashlib
import json
import re

EVIDENCE = Path('/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files')
CLOSURES = Path('.private/nyll-feasibility/closures')
HERE = Path('.private/nyll-partition')
CLOSURES.mkdir(parents=True, exist_ok=True)
HERE.mkdir(parents=True, exist_ok=True)
files = {}
for label in ['NormResidue', 'GeneralTowerNaturality', 'UnramifiedNormalization',
              'NormRestriction', 'FiniteAbelian', 'ShrinkTransport']:
    text = (EVIDENCE / 'closures' / (label + '.json.md')).read_text()
    expected = re.search(r'Original payload SHA-256: `([a-f0-9]{64})`', text)[1]
    payload = text.split('````json\n', 1)[1].rsplit('\n````', 1)[0] + '\n'
    assert hashlib.sha256(payload.encode()).hexdigest() == expected
    manifest = json.loads(payload)
    for name, data in manifest['files'].items():
        assert name not in files or files[name] == data
        files[name] = data
    (CLOSURES / (label + '.json')).write_text(payload)
assert len(files) == 422
(HERE / 'files.json').write_text(json.dumps(files, indent=2) + '\n')
print('Verified immutable manifest payloads; reconstructed', len(files), 'source records')

```

### `.private/nyll-partition/catalogue.py`

SHA-256: `691f28b5d434e0e1dadc948ca90133fa1a9f49ced622a54e33d5e504fb1df483`.

```python
from pathlib import Path
import json,re,hashlib,collections
SRC=Path('/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source')
FILES=json.loads(Path('.private/nyll-partition/files.json').read_text())
ORDER=['NormResidue','GeneralTowerNaturality','UnramifiedNormalization','NormRestriction','FiniteAbelian','ShrinkTransport']

def strip_comments(s):
    out=list(s);i=0;depth=0;string=False
    while i<len(s):
        if depth:
            if s.startswith('/-',i):out[i:i+2]='  ';depth+=1;i+=2
            elif s.startswith('-/',i):out[i:i+2]='  ';depth-=1;i+=2
            else:
                if s[i]!='\n':out[i]=' '
                i+=1
        elif string:
            if s[i]=='\\':
                out[i]=' ';i+=1
                if i<len(s):out[i]=' ';i+=1
            elif s[i]=='"':out[i]=' ';string=False;i+=1
            else:
                if s[i]!='\n':out[i]=' '
                i+=1
        elif s.startswith('/-',i):out[i:i+2]='  ';depth=1;i+=2
        elif s.startswith('--',i):
            while i<len(s) and s[i]!='\n':out[i]=' ';i+=1
        elif s[i]=='"':out[i]=' ';string=True;i+=1
        else:i+=1
    assert not depth and not string
    return ''.join(out)

# Command-boundary inventory, not an elaborated Lean dependency graph.
DECL=re.compile(r'(?m)^\s*(?:@\[[^\]]*\]\s*)*(?:(?:noncomputable|private|protected|unsafe|partial|nonrec|local|scoped)\s+)*(def|abbrev|theorem|lemma|structure|class|instance|inductive)\b\s*')
SCOPE=re.compile(r'(?m)^[ \t]*(namespace[ \t]+\S+|(?:noncomputable[ \t]+)?section(?:[ \t]+\w+)?|end(?:[ \t]+\S+)?)[ \t]*$')
seen=set();mods=[];issues=[]
for phase in ORDER:
    man=json.loads((Path('.private/nyll-feasibility/closures')/(phase+'.json')).read_text())
    for m in man['dependency_order']:
        if m in seen:continue
        f=FILES[m];seen.add(m)
        text=(SRC/f['path']).read_text();assert hashlib.sha256(text.encode()).hexdigest()==f['sha256']
        code=strip_comments(text);lines=code.splitlines();raw=text.splitlines()
        declarations=list(DECL.finditer(code));scopes=list(SCOPE.finditer(code));events=sorted([(x.start(),0,x) for x in scopes]+[(x.start(),1,x) for x in declarations]);stack=[];ds=[]
        for start,typ,x in events:
            if typ==0:
                cmd=x.group(1).split()
                if cmd[0]=='namespace':stack.append(('namespace',cmd[1]))
                elif cmd[0]=='end':
                    if not stack:issues.append((m,'unmatched end',code.count('\n',0,x.start())+1))
                    else:
                        k,n=stack.pop()
                        if len(cmd)>1 and n!=cmd[1]:issues.append((m,'end name mismatch',n,cmd[1]))
                else:stack.append(('section',cmd[-1] if cmd[-1]!='section' else ''))
            else:
                # Leading whitespace in regex can include previous blank lines.
                kwpos=x.end()-len(x.group(1))
                kind=x.group(1);km=re.search(r'\b'+kind+r'\b',code[x.start():x.end()]);kwpos=x.start()+km.start()
                line=code.count('\n',0,kwpos)+1
                rest=code[x.end():]
                # An instance priority precedes its optional name, even across lines.
                # Consume only a priority annotation, never an anonymous binder.
                if kind=='instance' and re.match(r'\(\s*priority\s*:=',rest):
                    depth=0
                    for end,ch in enumerate(rest):
                        if ch=='(':depth+=1
                        elif ch==')':
                            depth-=1
                            if depth==0:
                                rest=rest[end+1:].lstrip()
                                break
                    else:
                        raise ValueError((m,line,'unclosed instance priority'))
                named=re.match(r'((?:«[^»]+»|[^\s\[\]{}():=])+)',rest)
                name=named.group(1) if named else None
                if kind!='instance' and not name:issues.append((m,'missing name',line,kind))
                prefix='.'.join(n for k,n in stack if k=='namespace')
                if name and name.startswith('_root_.'):fq=name[7:]
                elif name:fq='.'.join(p for p in [prefix,name] if p)
                else:fq=None
                local=bool(re.search(r'\blocal\b',code[x.start():kwpos]))
                private=bool(re.search(r'\bprivate\b',code[x.start():kwpos]))
                # A top-level source name is precise even when Lean mangles private names.
                ds.append(dict(kind=kind,name=name,namespace=prefix,qualified=fq,line=line,private=private,local=local,header=raw[line-1].strip(),offset=kwpos))
        if any(k=='namespace' for k,n in stack):issues.append((m,'unclosed namespace',stack))
        for j,d in enumerate(ds):
            # This is an inspection slice ending before next declaration, including intervening scopes.
            d['slice_end']=(ds[j+1]['line']-1 if j+1<len(ds) else len(raw))
            # only the initial type/signature; ":=" may occur in dependent lets so keep limits explicit.
            snippet=code[d['offset']:(ds[j+1]['offset'] if j+1<len(ds) else len(code))]
            d['signature']=snippet.split(':=')[0].strip()[:5000]
            d['prop_definition']=d['kind'] in ['def','abbrev'] and bool(re.search(r':\s*Prop\b',d['signature']))
            d['has_by']=bool(re.search(r'\bby\b',snippet))
            del d['offset']
        mods.append(dict(module=m,id=f'M{len(mods)+1:03}',phase=phase,**f,declarations=ds))
assert len(mods)==422
for m in mods:
    for i,d in enumerate(m['declarations'],1):d['id']=m['id']+f'.{i:03}'
Path('.private/nyll-partition/catalogue.json').write_text(json.dumps(mods,ensure_ascii=False,indent=2)+'\n')
Path('.private/nyll-partition/issues.json').write_text(json.dumps(issues,ensure_ascii=False,indent=2)+'\n')
print('Modules',len(mods),'declarations',sum(len(m['declarations']) for m in mods),'scope issues',len(issues))
print('Phases',collections.Counter(m['phase'] for m in mods))
print('Kinds',collections.Counter(d['kind'] for m in mods for d in m['declarations']))
print('No declarations',[(m['id'],m['module']) for m in mods if not m['declarations']])
print('Issues',issues[:30])

```

### `.private/nyll-partition/render_plan.py`

SHA-256: `d218eb7e2783c8d2ffd5cfd18aecea4f032df516d325b9edfd3ecc4347ba15c0`.

```python
"""Render the source-unit routing inventory, without treating it as Lean analysis."""
from pathlib import Path
import collections
import hashlib
import json

HERE = Path(".private/nyll-partition")
OUT = Path("notes/reuse/nyll-public-port")
CAT = json.loads((HERE / "catalogue.json").read_text())
BY_NAME = {m["module"]: m for m in CAT}
SRC = Path("/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source")
PHASES = ["NormResidue", "GeneralTowerNaturality", "UnramifiedNormalization",
          "NormRestriction", "FiniteAbelian", "ShrinkTransport"]
PATCH = {
    23: "P1", 191: "P2", 247: "P3", 271: "P4", 327: "P5",
    379: "P6", 385: "P7", 386: "P8", 387: "P9",
}
OUT.mkdir(parents=True, exist_ok=True)


def family(m):
    s = m["module"]
    if m["phase"] == "ShrinkTransport":
        return "U"
    if ".LubinTate." in s or ".LubinTateApplication." in s:
        return "L"
    if ".GaloisCohomology." in s or ".ClassFormation." in s:
        return "C"
    if ".AbstractClassFieldTheory." in s:
        return "A"
    if ".Ramification." in s:
        return "R"
    if ".Valuation.Hensel" in s or ".Valuation.AbsoluteValue." in s or ".Valuation.UniqueRing" in s:
        return "H"
    if ".Valuation.DiscreteValuationField." in s or ".Valuation." in s:
        return "V"
    if ".LocalField." in s:
        return "F"
    if ".LocalClassFieldTheory." in s:
        return "N"
    return "G"


def portname(d):
    if d["private"] or d["local"] or not d["qualified"]:
        a, b = d["id"].split(".")
        return f"Langlands.NYLL.PortInternal.{a}.d{b}"
    return "Langlands.NYLL." + d["qualified"]


def route(d):
    k = d["id"]
    if k.startswith("M005."):
        return "Q1:D"
    if k in {f"M103.{i:03}" for i in [2, 3, 7, 8, 10]}:
        return "Q2:D"
    if k in {f"M103.{i:03}" for i in [4, 5, 6, 9]}:
        return "Q2:R"
    if k == "M111.001":
        return "Q3:S→P"
    if k in {"M128.001", "M134.001", "M134.002", "M131.001", "M161.001"}:
        return "B2:D"
    if k in {"M092.002", "M093.001", "M093.002"}:
        return "B3:D/R"
    if d["kind"] in {"theorem", "lemma"}:
        return "B0:S→P"
    if d["prop_definition"]:
        return "B1:Prop?"
    if d["kind"] in {"structure", "class"}:
        return "B1:bundle?"
    if d["kind"] == "instance":
        return "B1:instance?"
    return "B1:data?"


pages = []
for phase in PHASES:
    ms = [m for m in CAT if m["phase"] == phase]
    for i in range(0, len(ms), 24):
        group = ms[i:i + 24]
        name = f"{group[0]['id'].lower()}-{group[-1]['id'].lower()}.md"
        pages.append((name, group))
PAGE_OF = {m["id"]: name for name, ms in pages for m in ms}


def module_link(m):
    return f"[{m['id']}]({PAGE_OF[m['id']]}#{m['id'].lower()})"


unit_count = 0
for name, ms in pages:
    out = [
        f"# NYLL source-unit routes: {ms[0]['id']}–{ms[-1]['id']}",
        "",
        "[Plan](../nyll-public-port-plan.md) · [Inventory index](index.md)",
        "",
        "This is a proposed declaration-level work partition, not a list of accepted Lean declarations.",
        "Read the plan's naming, phase, dependency, blocker and attribution rules before using a row.",
        "`S→P` means publish a Prop target, then a separate proof; `D` means a definition unit.",
        "A question mark requires classification from the full source before task publication.",
        "The source spelling column is not an elaborated type or a private kernel identifier.",
        "All rows inherit their module's family, imports, patch and Worker 25 routing responsibility.",
        "No replacement is established for a row unless the plan's explicit reuse table says so.",
        "",
    ]
    for m in ms:
        n = int(m["id"][1:])
        deps = [BY_NAME[i] for i in m["imports"] if i in BY_NAME]
        ext = [i for i in m["imports"] if i not in BY_NAME]
        assert all(not i.startswith("Nyll.") for i in ext), m["id"]
        assert all(int(i["id"][1:]) < n for i in deps), m["id"]
        data = (SRC / m["path"]).read_bytes()
        assert hashlib.sha256(data).hexdigest() == m["sha256"]
        ds = m["declarations"]
        assert ds
        out += [
            f"## {m['id']}", "",
            f"Original: [`{m['path']}`](<{SRC / m['path']}>).",
            f"SHA-256: `{m['sha256']}`. Phase: `{m['phase']}`.",
            f"Family: `{family(m)}`. Patch: `{PATCH.get(n, 'none in patch10')}`.",
            "",
            "Incoming NYLL module-completion dependencies: " +
            (", ".join(module_link(x) + "`.END`" for x in deps) if deps else "none") + ".",
            "Incoming external imports: " + (", ".join(f"`{x}`" for x in ext) if ext else "none") + ".",
            "",
            f"Proposed support module stem: `Langlands/NYLL/{m['path'][5:-5]}`.",
            "Each row is its own candidate boundary unless a named Q-unit groups it.",
            "Suggested files below this stem are `Uxxx/Definitions.lean`,",
            "`Uxxx/Statements.lean`, and `Uxxx/Proofs.lean`, only for phases needed by that row.",
            "The three published child contracts override this suggested layout.",
            "",
            "| Source unit | Original start line and spelling | Kind / scope | Phase and blocker | Prospective declaration | Incoming within module |",
            "| --- | --- | --- | --- | --- | --- |",
        ]
        for i, d in enumerate(ds):
            source = d["qualified"] or "(anonymous instance)"
            scope = "/private" if d["private"] else "/local" if d["local"] else ""
            pn = portname(d)
            if d["id"] == "M111.001":
                pn = "Langlands.NYLL.LocalFieldTheory.ValuedTopologyStatement"
            if route(d) == "Q2:R":
                pn = "(canonical instance reuse; no new declaration)"
            inc = "module imports" if i == 0 else ds[i - 1]["id"] + ".END"
            out.append(f"| `{d['id']}` | {d['line']}: `{source}` | {d['kind']}{scope} | {route(d)} | `{pn}` | `{inc}` |")
            unit_count += 1
        out += ["", f"`{m['id']}.END` means resolution of `{ds[-1]['id']}.END` and its preceding dependency chain.",
                "It is a scheduling marker, never a Lean constant or acceptance artifact.", ""]
    (OUT / name).write_text("\n".join(out) + "\n")

index = [
    "# NYLL public-port inventory index", "",
    "[Main plan](../nyll-public-port-plan.md).",
    "",
    "The complete inventory contains 422 modules and 7,340 source declaration commands.",
    "It records a conservative dependency-first schedule. Module and source-order edges",
    "are scheduling prerequisites, not a minimized graph of Lean constants.",
    "Every row inherits the main plan's license, naming, review and unresolved-mathematics rules.",
    "",
    "| Appendix | First-root phase | Modules | Source commands |",
    "| --- | --- | ---: | ---: |",
]
for name, ms in pages:
    index.append(f"| [{ms[0]['id']}–{ms[-1]['id']}]({name}) | {ms[0]['phase']} | {len(ms)} | {sum(len(m['declarations']) for m in ms)} |")
index += ["", "## Family and module index", "",
          "| Module | Family | Original module | Commands |",
          "| --- | --- | --- | ---: |"]
for m in CAT:
    index.append(f"| {module_link(m)} | {family(m)} | `{m['module']}` | {len(m['declarations'])} |")
(OUT / "index.md").write_text("\n".join(index) + "\n")

# Validate that every retained module is reached by at least one original root.
roots = {}
union = set()
counts = {}
for phase in PHASES:
    manifest = json.loads((Path(".private/nyll-feasibility/closures") / (phase + ".json")).read_text())
    root = manifest["root"]
    reached = set()
    def visit(mod):
        if mod in reached:
            return
        reached.add(mod)
        for dep in BY_NAME[mod]["imports"]:
            if dep in BY_NAME:
                visit(dep)
    visit(root)
    assert reached == set(manifest["dependency_order"]), phase
    roots[phase] = BY_NAME[root]["id"]
    counts[phase] = {"closure_modules": len(reached), "increment": len(reached - union)}
    union |= reached
assert len(union) == 422 and unit_count == 7340
assert len({d["id"] for m in CAT for d in m["declarations"]}) == unit_count
public_names = [portname(d) for m in CAT for d in m["declarations"]]
assert len(set(public_names)) == len(public_names)
target_names = [
    ("Langlands.NYLL.LocalFieldTheory.ValuedTopologyStatement"
     if d["id"] == "M111.001" else portname(d) + "Statement")
    for m in CAT for d in m["declarations"] if d["kind"] in {"theorem", "lemma"}
]
assert len(set(target_names)) == len(target_names)
assert not set(target_names).intersection(public_names)
summary = {
    "modules": len(CAT), "source_commands": unit_count, "appendix_files": len(pages),
    "roots": roots, "counts": counts,
    "all_original_source_hashes_verified": True,
    "nyll_import_edges_point_backward": True,
    "all_six_root_module_sets_equal_retained_manifests": True,
    "proposed_names_unique": True,
    "proposed_target_names_unique_and_disjoint": True,
    "phase_command_counts": {
        p: sum(len(m["declarations"]) for m in CAT if m["phase"] == p)
        for p in PHASES
    },
    "family_counts": dict(collections.Counter(family(m) for m in CAT)),
    "kind_counts": dict(collections.Counter(d["kind"] for m in CAT for d in m["declarations"])),
    "private_source_commands": sum(d["private"] for m in CAT for d in m["declarations"]),
    "local_source_commands": sum(d["local"] for m in CAT for d in m["declarations"]),
}
(HERE / "validation.json").write_text(json.dumps(summary, indent=2) + "\n")
print(json.dumps(summary, indent=2))

```

## Terminal native verification result

This is an inventory check result, not a Lean-service or mathematical-review receipt.

```json
{
  "modules": 422,
  "source_commands": 7340,
  "appendix_files": 21,
  "roots": {
    "NormResidue": "M258",
    "GeneralTowerNaturality": "M262",
    "UnramifiedNormalization": "M269",
    "NormRestriction": "M288",
    "FiniteAbelian": "M420",
    "ShrinkTransport": "M422"
  },
  "counts": {
    "NormResidue": {
      "closure_modules": 258,
      "increment": 258
    },
    "GeneralTowerNaturality": {
      "closure_modules": 262,
      "increment": 4
    },
    "UnramifiedNormalization": {
      "closure_modules": 265,
      "increment": 7
    },
    "NormRestriction": {
      "closure_modules": 280,
      "increment": 19
    },
    "FiniteAbelian": {
      "closure_modules": 402,
      "increment": 132
    },
    "ShrinkTransport": {
      "closure_modules": 33,
      "increment": 2
    }
  },
  "all_original_source_hashes_verified": true,
  "nyll_import_edges_point_backward": true,
  "all_six_root_module_sets_equal_retained_manifests": true,
  "proposed_names_unique": true,
  "proposed_target_names_unique_and_disjoint": true,
  "phase_command_counts": {
    "NormResidue": 5384,
    "GeneralTowerNaturality": 32,
    "UnramifiedNormalization": 117,
    "NormRestriction": 155,
    "FiniteAbelian": 1640,
    "ShrinkTransport": 12
  },
  "family_counts": {
    "G": 1,
    "C": 42,
    "A": 76,
    "R": 57,
    "N": 71,
    "F": 60,
    "V": 21,
    "H": 47,
    "L": 45,
    "U": 2
  },
  "kind_counts": {
    "theorem": 5370,
    "def": 1469,
    "instance": 299,
    "abbrev": 116,
    "structure": 46,
    "lemma": 37,
    "class": 3
  },
  "private_source_commands": 555,
  "local_source_commands": 68
}
```

## Generated file fingerprints

These SHA-256 values cover the rendered inventory and index, before submission.
The main plan and routing record are ordinary reviewed prose, not generated rows.

| File | SHA-256 |
| --- | --- |
| [m001-m024.md](m001-m024.md) | `81f3fe9f1dc9744febf763ba443fa437c7240ab484e195c4031f864ac42a9a13` |
| [m025-m048.md](m025-m048.md) | `a6af52cb5b66f124a06d5a5338c2d82c18ec35f7fc695a958d652abf5bb92873` |
| [m049-m072.md](m049-m072.md) | `212533e1385eacd24b57585a97ce3829cbc779f5e33c1b415e7afe7c3ab15714` |
| [m073-m096.md](m073-m096.md) | `97d738aabff7abe1df8770dbeb9daa1b2b85f671a12d7b072e2faebfbe178761` |
| [m097-m120.md](m097-m120.md) | `7bf6c2c610d43fb91109509e6acc9dca7ff31f1940c70aaf795ab03102c66719` |
| [m121-m144.md](m121-m144.md) | `a65cff4fdf4b1046a306956975034e20c09e05193d96ab925b0182f21cadde19` |
| [m145-m168.md](m145-m168.md) | `10fc25413902aa8f622a2ba66e36ed1e5f0770e4857dd6e734435464196d09a8` |
| [m169-m192.md](m169-m192.md) | `8c05674eb2f32a4492fe6fea0c5cac65d9dc81d5ef15f52730a3280a2cb9b804` |
| [m193-m216.md](m193-m216.md) | `f6b3f17ef0e239e65b0c17717cc383de3225931f58a7543cafa5ee759974d0ce` |
| [m217-m240.md](m217-m240.md) | `cc03583d44ca12722501edb0e50f9fed13e82a5ae9e0d9d28ea842d17628a95d` |
| [m241-m258.md](m241-m258.md) | `92121d0db55c4fb5e2dbc4b88306ea6adf2e3bf272983a26c8622dc189f50f8d` |
| [m259-m262.md](m259-m262.md) | `e96c2877cd6824d595a823b38a173711c19b13e7d08cbdbbca71377d882cbc98` |
| [m263-m269.md](m263-m269.md) | `c731c88eebd9acf032c17cad957ce481b6b9398dba762dbb8827c2c0966b6ec4` |
| [m270-m288.md](m270-m288.md) | `c68167326dde45f032c60b004b31db31d432292c07205c532a0943479a59dad9` |
| [m289-m312.md](m289-m312.md) | `440ca2f8cd0a8431a5253dd0ccc535ac1e4226ab2317eec7bdfe3464b87d1a2a` |
| [m313-m336.md](m313-m336.md) | `700594030de9210e21c9dbd4d230da0621a828a2322db1b3f32ce7915b9ec751` |
| [m337-m360.md](m337-m360.md) | `4649b5f91a5e999de978aec520cc37e88fe137de601abf286e299989bf0248b2` |
| [m361-m384.md](m361-m384.md) | `18ab1211928a15d9070adaa116476e554b6ff3c83ecfd0b455f5dd9951176ff1` |
| [m385-m408.md](m385-m408.md) | `489d1a5bfc543082ecb6b6a83ec50218803c7fe230dd5ac506fc02fcde73f2a6` |
| [m409-m420.md](m409-m420.md) | `08dd2f337f43a5f7b25f76f937bef5920cac949789425d4ef4b1d77accdd6de7` |
| [m421-m422.md](m421-m422.md) | `05d737d066db4166e8945a092c8173cac3c2f50c056a053cd82e3bb6d4a5ee75` |
| [index.md](index.md) | `583caf00f28eae612a93b066c45c822373887ea5903ecb59d3a8a2b34908ae9d` |
