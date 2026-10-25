# Local-flatness audit: reproducible evidence

Worker 362, 25 October 2026. Companion to [the audit](../anthropic-local-flatness-audit.md). Scripts and snippets here document private development experiments; they are not published Lean modules.

## Closure traversal script

```python
from pathlib import Path
import re, json, hashlib
src=next(Path('/home/taskhub/pilot/literature').glob('Anthropic*complete Lean*'))
roots=['Module_flat_of_comap_maximalIdeal_rTensor_injective','IsLocalRing_flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map','IsLocalRing_flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map_univ']
def visit(mod, found):
 if mod in found: return
 f=src/(mod.replace('.','/')+'.lean')
 if not f.exists(): return
 txt=f.read_text(); imports=re.findall(r'^import\s+([\w.]+)',txt,re.M)
 found[mod]={'path':str(f.relative_to(src)),'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'lines':len(txt.splitlines()),'imports':imports}
 for imp in imports: visit(imp,found)
closures={}
for root in roots:
 found={}; visit('Theorems.Thm_'+root,found); closures[root]=found
 print(root, len(found), sum(x['lines'] for x in found.values()))
 for m,data in found.items():print(data)
Path('.private/flatness-audit/closure.json').write_text(json.dumps(closures,indent=2)+'\n')
```

## Original closure manifest

```json
{
  "Module_flat_of_comap_maximalIdeal_rTensor_injective": {
    "Theorems.Thm_Module_flat_of_comap_maximalIdeal_rTensor_injective": {
      "path": "Theorems/Thm_Module_flat_of_comap_maximalIdeal_rTensor_injective.lean",
      "sha256": "d56f7b966f32adeab7ab2afebf281ff7508a75470d4785a7a73acb1c8f95c939",
      "lines": 13,
      "imports": [
        "Mathlib",
        "P2M.Util",
        "P2M.Sol.S_Module_flat_of_comap_maximalIdeal_rTensor_injective"
      ]
    },
    "P2M.Util": {
      "path": "P2M/Util.lean",
      "sha256": "66f62069b83c0cf97531f88e5bd2c249e471df011ad873b0bd034eb959b1d8da",
      "lines": 127,
      "imports": [
        "Lean"
      ]
    },
    "P2M.Sol.S_Module_flat_of_comap_maximalIdeal_rTensor_injective": {
      "path": "P2M/Sol/S_Module_flat_of_comap_maximalIdeal_rTensor_injective.lean",
      "sha256": "31fec1ed578c9cab7b3ef8c860b3116bbee9b5be48743c755be8500973594959",
      "lines": 711,
      "imports": [
        "Mathlib",
        "P2M.Util"
      ]
    }
  },
  "IsLocalRing_flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map": {
    "Theorems.Thm_IsLocalRing_flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map": {
      "path": "Theorems/Thm_IsLocalRing_flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map.lean",
      "sha256": "017aa06cf9830d5e841756b0b736aee3854b54200df10eabff7761c0d7548432",
      "lines": 18,
      "imports": [
        "Mathlib",
        "P2M.Util",
        "P2M.Sol.S_IsLocalRing_flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map"
      ]
    },
    "P2M.Util": {
      "path": "P2M/Util.lean",
      "sha256": "66f62069b83c0cf97531f88e5bd2c249e471df011ad873b0bd034eb959b1d8da",
      "lines": 127,
      "imports": [
        "Lean"
      ]
    },
    "P2M.Sol.S_IsLocalRing_flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map": {
      "path": "P2M/Sol/S_IsLocalRing_flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map.lean",
      "sha256": "518b8c92fe7012465b983a6edb0969c69c52ef5ac6f1474ab5e57aec71a4b849",
      "lines": 636,
      "imports": [
        "Mathlib",
        "Theorems.Thm_Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero",
        "P2M.Util"
      ]
    },
    "Theorems.Thm_Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero": {
      "path": "Theorems/Thm_Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero.lean",
      "sha256": "874f0dc05ee06930ca4cca3982c910cf9367a8c755401bf441a425a8a476f971",
      "lines": 15,
      "imports": [
        "Mathlib",
        "P2M.Util",
        "P2M.Sol.S_Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero"
      ]
    },
    "P2M.Sol.S_Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero": {
      "path": "P2M/Sol/S_Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero.lean",
      "sha256": "b78045b06eb8c7b4c1d175b803d85007d99a98e7fe9eb89883f177ce6386a72e",
      "lines": 694,
      "imports": [
        "Mathlib",
        "P2M.Util"
      ]
    }
  },
  "IsLocalRing_flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map_univ": {
    "Theorems.Thm_IsLocalRing_flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map_univ": {
      "path": "Theorems/Thm_IsLocalRing_flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map_univ.lean",
      "sha256": "069236448d413acd9cb8b780f99e1337ba24d0a13a7dd99ab744d42ef3f179c8",
      "lines": 20,
      "imports": [
        "Mathlib",
        "P2M.Util",
        "P2M.Sol.S_IsLocalRing_flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map_univ"
      ]
    },
    "P2M.Util": {
      "path": "P2M/Util.lean",
      "sha256": "66f62069b83c0cf97531f88e5bd2c249e471df011ad873b0bd034eb959b1d8da",
      "lines": 127,
      "imports": [
        "Lean"
      ]
    },
    "P2M.Sol.S_IsLocalRing_flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map_univ": {
      "path": "P2M/Sol/S_IsLocalRing_flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map_univ.lean",
      "sha256": "8ce39f988131a4b74a918f362a400e42d251c044cea9719b644fd086e183079a",
      "lines": 638,
      "imports": [
        "Mathlib",
        "Theorems.Thm_Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero_univ",
        "P2M.Util"
      ]
    },
    "Theorems.Thm_Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero_univ": {
      "path": "Theorems/Thm_Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero_univ.lean",
      "sha256": "b644e8c04350c88af9fbb1994fdf0b1afe0b00607b016adca8f17237d0038633",
      "lines": 17,
      "imports": [
        "Mathlib",
        "P2M.Util",
        "P2M.Sol.S_Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero_univ"
      ]
    },
    "P2M.Sol.S_Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero_univ": {
      "path": "P2M/Sol/S_Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero_univ.lean",
      "sha256": "ec882a9149e1beadeab53e606c25f432f19347c0ebe8c4e2e9c4cefe14375fc7",
      "lines": 696,
      "imports": [
        "Mathlib",
        "P2M.Util"
      ]
    }
  }
}
```

## Original wrapper: Theorems.Thm_Module_flat_of_comap_maximalIdeal_rTensor_injective

```lean
import Mathlib
import P2M.Util
import P2M.Sol.S_Module_flat_of_comap_maximalIdeal_rTensor_injective

open TensorProduct

theorem Module.flat_of_comap_maximalIdeal_rTensor_injective
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] [Module.Finite S M]
    (p : Ideal R) (hp : (IsLocalRing.maximalIdeal S).comap (algebraMap R S) = p)
    (h : Function.Injective (p.subtype.rTensor M)) :
    Module.Flat R M := by p2m_exact_reverting @_root_.P2MW.S_Module_flat_of_comap_maximalIdeal_rTensor_injective.solution
```

## Original wrapper: Theorems.Thm_IsLocalRing_flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map

```lean
import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map

theorem IsLocalRing.flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map
    {R S S' : Type} [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing S']
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S S')]
    [IsNoetherianRing S] [IsNoetherianRing S'] :
    letI : Algebra (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))
        (S' ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S')) :=
      Ideal.Quotient.algebraQuotientOfLEComap (Ideal.map_le_iff_le_comap.mp (le_of_eq
        (by rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R S S'])))
    Module.Flat R S' →
    Module.Flat (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))
        (S' ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S')) →
    Module.Flat S S' := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map.solution
```

## Original wrapper: Theorems.Thm_Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero

```lean
import Mathlib
import P2M.Util
import P2M.Sol.S_Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero

open CategoryTheory CategoryTheory.Limits

theorem Module.flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero
    {R : Type} [CommRing R] {S : Type} [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [IsNoetherianRing R] [IsNoetherianRing S]
    {M : Type} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Finite S M]
    (hκ : IsZero (((Tor (ModuleCat.{0} R) 1).obj
      (ModuleCat.of R (IsLocalRing.ResidueField R))).obj (ModuleCat.of R M))) :
    Module.Flat R M := by p2m_exact_reverting @_root_.P2MW.S_Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero.solution
```

## Original wrapper: Theorems.Thm_IsLocalRing_flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map_univ

```lean
import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map_univ

universe u

theorem IsLocalRing.flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map_univ
    {R S S' : Type u} [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing S']
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S S')]
    [IsNoetherianRing S] [IsNoetherianRing S'] :
    letI : Algebra (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))
        (S' ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S')) :=
      Ideal.Quotient.algebraQuotientOfLEComap (Ideal.map_le_iff_le_comap.mp (le_of_eq
        (by rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R S S'])))
    Module.Flat R S' →
    Module.Flat (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))
        (S' ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S')) →
    Module.Flat S S' := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map_univ.solution
```

## Original wrapper: Theorems.Thm_Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero_univ

```lean
import Mathlib
import P2M.Util
import P2M.Sol.S_Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero_univ

universe u

open CategoryTheory CategoryTheory.Limits

theorem Module.flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero_univ
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [IsNoetherianRing R] [IsNoetherianRing S]
    {M : Type u} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Finite S M]
    (hκ : IsZero (((Tor (ModuleCat.{u} R) 1).obj
      (ModuleCat.of R (IsLocalRing.ResidueField R))).obj (ModuleCat.of R M))) :
    Module.Flat R M := by p2m_exact_reverting @_root_.P2MW.S_Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero_univ.solution
```

## Original-to-adapted names

Each implementation namespace `P2MW.S_<suffix>` is replaced, including all nested names. The solution is used directly in place of the wrapper. No external theorem wrapper is imported.

| Source suffix | Adapted implementation namespace/module |
| --- | --- |
| `Module_flat_of_comap_maximalIdeal_rTensor_injective` | `FlatnessAudit.Primary` in `Primary.lean` |
| `Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero` | `FlatnessAudit.TorZero` in `TorZero.lean` |
| `Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero_univ` | `FlatnessAudit.TorUniv` in `TorUniv.lean` |
| `IsLocalRing_flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map` | `FlatnessAudit.TowerZero` in `TowerZero.lean` |
| `IsLocalRing_flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map_univ` | `FlatnessAudit.TowerUniv` in `TowerUniv.lean` |

Primary helpers retain the nested `LocalFlatnessCriterionAtPrime` namespace and its `FreeCover` namespace. Tor helpers retain `MK00Port`; tower helpers retain `LocalCritPort`.

## Initial adaptation script: adapt.py

```python
from pathlib import Path
import re,shutil,difflib
src=next(Path('/home/taskhub/pilot/literature').glob('Anthropic*complete Lean*'))
out=Path('.private/drafts/anthropic-flatness'); out.mkdir(parents=True,exist_ok=True)
for f in ['LICENSE','NOTICE','ATTRIBUTION.md']:shutil.copyfile(src/f,out/f)
name='Module_flat_of_comap_maximalIdeal_rTensor_injective'
orig=(src/f'P2M/Sol/S_{name}.lean').read_text()
s=orig.replace('import P2M.Util\n','').replace('P2MW.S_'+name,'FlatnessAudit.Primary')
s=re.sub(r'^p2m_reactivate "([^"]*)"$',lambda m:'open scoped '+m[1],s,flags=re.M)
header='/-\nCopyright 2026 Anthropic, PBC. Apache-2.0; see LICENSE and NOTICE.\nAdapted by Worker 362 for a private feasibility audit, 2026-10-25.\nChanged namespace; removed P2M.Util; replaced scope reactivation with open scoped.\nOriginal: P2M/Sol/S_'+name+'.lean at 6e837e75355538c7f80bab5b956861e86c4eacc2.\n-/\n'
(out/'Primary.lean').write_text(header+s)
(out/'Primary.md').write_text('# Private primary flatness experiment\n\nAdapted from the registered Anthropic FLT source at commit 6e837e75355538c7f80bab5b956861e86c4eacc2, P2M/Sol/S_Module_flat_of_comap_maximalIdeal_rTensor_injective.lean. Copyright 2026 Anthropic, PBC; Apache-2.0. See LICENSE, NOTICE and ATTRIBUTION.md. No matching per-file third-party row was found in ATTRIBUTION.md. The proof uses a free cover to transfer tensor injectivity, extends a Tor-vanishing surrogate to powers, and applies Artin–Rees and Krull intersection. Localization and semisimplicity supply the residue-prime splitting. Only pipeline scope machinery and namespace are adapted at this stage; no hypotheses are changed. This is an unreviewed private experiment, not a Library proof.\n')
Path('.private/flatness-audit/primary-initial.patch').write_text(''.join(difflib.unified_diff(orig.splitlines(True),(header+s).splitlines(True),fromfile='upstream/'+name,tofile='Primary.lean')))
```

## Initial adaptation script: adapt-tower.py

```python
from pathlib import Path
import difflib
src=next(Path('/home/taskhub/pilot/literature').glob('Anthropic*complete Lean*'))
out=Path('.private/drafts/anthropic-flatness')
tor='Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero'
tower='IsLocalRing_flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map'
for suffix,label in [('', 'Zero'),('_univ','Univ')]:
 for root,kind in [(tor,'Tor'),(tower,'Tower')]:
  module=kind+label; name=root+suffix
  orig=(src/f'P2M/Sol/S_{name}.lean').read_text()
  s=orig.replace('import P2M.Util\n','').replace('P2MW.S_'+name, 'FlatnessAudit.'+module)
  s=s.replace('import Theorems.Thm_'+tor+suffix, 'import Tor'+label)
  s=s.replace('Module.flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero'+suffix,'FlatnessAudit.Tor'+label+'.solution')
  header='/-\nCopyright 2026 Anthropic, PBC. Apache-2.0; see LICENSE and NOTICE.\nAdapted by Worker 362 for a private feasibility audit, 2026-10-25.\nChanged namespace; removed unused P2M.Util; redirected the Tor criterion import and call where present.\nOriginal: P2M/Sol/S_'+name+'.lean at 6e837e75355538c7f80bab5b956861e86c4eacc2.\n-/\n'
  (out/(module+'.lean')).write_text(header+s)
  (out/(module+'.md')).write_text('# Private '+module+' experiment\n\nAdapted from the registered Anthropic source at commit 6e837e75355538c7f80bab5b956861e86c4eacc2, `P2M/Sol/S_'+name+'.lean`. Copyright 2026 Anthropic, PBC; Apache-2.0; see LICENSE, NOTICE and ATTRIBUTION.md. No matching third-party per-file row occurs in ATTRIBUTION.md. Only namespace, unused utility import and calls to the adapted dependency change. Universe restrictions and all hypotheses are preserved. '+('This proof uses categorical Tor exactness, finite-length devissage and an Artin–Rees/Krull-intersection argument.' if kind=='Tor' else 'This proof combines an ideal tensor factorization, quotient base change and Tor exactness with the imported local Tor criterion, applied to the module S\' itself.')+'\n\nThis is private feasibility evidence, not a published mathematical result.\n')
  Path('.private/flatness-audit/'+module+'-initial.patch').write_text(''.join(difflib.unified_diff(orig.splitlines(True),(header+s).splitlines(True),fromfile='upstream/'+name,tofile=module+'.lean')))
inspect=''.join('import '+m+'\n' for m in ['TorZero','TowerZero','TorUniv','TowerUniv'])+'\n'
for m in ['TorZero','TowerZero','TorUniv','TowerUniv']:
 inspect+='set_option pp.universes true in\n#check @FlatnessAudit.'+m+'.solution\n#print axioms FlatnessAudit.'+m+'.solution\n'
(out/'InspectTower.lean').write_text(inspect)
(out/'InspectTower.md').write_text('# Private tower inspection\n\nFull unapplied declaration and axiom checks for both original-universe and shared-universe local Tor and tower solutions. No claim of a general finite-module tower theorem is made.\n')
```

The scripts use the registered local source location. Reproduction runs them only in a private draft directory in an authorized project workspace. The initial scripts regenerate the initial versions and would overwrite the later failed compatibility experiment. They also copy the complete notices for retention.

## Retained patch: TorUniv-compat.patch

```diff
--- TorUniv.lean.initial
+++ TorUniv.lean
@@ -294,7 +294,6 @@
   rw [hM, hF, hG]
   simp only [Category.assoc]
 
-  refine Eq.trans (whisker_eq _ (whisker_eq _ (hbr _))) ?_
   refine Eq.trans (whisker_eq _ ((Category.assoc _ _ _).symm)) ?_
   refine Eq.trans (whisker_eq _ (eq_whisker hι _)) ?_
   refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
```

## Retained patch: TorUniv-initial.patch

```diff
--- upstream/Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero_univ
+++ TorUniv.lean
@@ -1,6 +1,11 @@
+/-
+Copyright 2026 Anthropic, PBC. Apache-2.0; see LICENSE and NOTICE.
+Adapted by Worker 362 for a private feasibility audit, 2026-10-25.
+Changed namespace; removed unused P2M.Util; redirected the Tor criterion import and call where present.
+Original: P2M/Sol/S_Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero_univ.lean at 6e837e75355538c7f80bab5b956861e86c4eacc2.
+-/
 import Mathlib
-import P2M.Util
-namespace P2MW.S_Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero_univ
+namespace FlatnessAudit.TorUniv
 
 universe u
```

## Retained patch: TorZero-compat.patch

```diff
--- TorZero.lean.initial
+++ TorZero.lean
@@ -292,7 +292,6 @@
   rw [hM, hF, hG]
   simp only [Category.assoc]
 
-  refine Eq.trans (whisker_eq _ (whisker_eq _ (hbr _))) ?_
   refine Eq.trans (whisker_eq _ ((Category.assoc _ _ _).symm)) ?_
   refine Eq.trans (whisker_eq _ (eq_whisker hι _)) ?_
   refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
```

## Retained patch: TorZero-initial.patch

```diff
--- upstream/Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero
+++ TorZero.lean
@@ -1,6 +1,11 @@
+/-
+Copyright 2026 Anthropic, PBC. Apache-2.0; see LICENSE and NOTICE.
+Adapted by Worker 362 for a private feasibility audit, 2026-10-25.
+Changed namespace; removed unused P2M.Util; redirected the Tor criterion import and call where present.
+Original: P2M/Sol/S_Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero.lean at 6e837e75355538c7f80bab5b956861e86c4eacc2.
+-/
 import Mathlib
-import P2M.Util
-namespace P2MW.S_Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero
+namespace FlatnessAudit.TorZero
 
 set_option autoImplicit false
 set_option maxHeartbeats 3200000
```

## Retained patch: TowerUniv-compat.patch

```diff
--- TowerUniv.lean.initial
+++ TowerUniv.lean
@@ -272,7 +272,6 @@
   rw [hM, hF, hG]
   simp only [Category.assoc]
 
-  refine Eq.trans (whisker_eq _ (whisker_eq _ (hbr _))) ?_
   refine Eq.trans (whisker_eq _ ((Category.assoc _ _ _).symm)) ?_
   refine Eq.trans (whisker_eq _ (eq_whisker hι _)) ?_
   refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
```

## Retained patch: TowerUniv-initial.patch

```diff
--- upstream/IsLocalRing_flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map_univ
+++ TowerUniv.lean
@@ -1,7 +1,12 @@
+/-
+Copyright 2026 Anthropic, PBC. Apache-2.0; see LICENSE and NOTICE.
+Adapted by Worker 362 for a private feasibility audit, 2026-10-25.
+Changed namespace; removed unused P2M.Util; redirected the Tor criterion import and call where present.
+Original: P2M/Sol/S_IsLocalRing_flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map_univ.lean at 6e837e75355538c7f80bab5b956861e86c4eacc2.
+-/
 import Mathlib
-import Theorems.Thm_Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero_univ
-import P2M.Util
-namespace P2MW.S_IsLocalRing_flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map_univ
+import TorUniv
+namespace FlatnessAudit.TowerUniv
 
 universe u
 
@@ -605,7 +610,7 @@
     (hloc : IsLocalHom (algebraMap R S)) (hfin : Module.Finite S M)
     (hκ : Igw157LcTor1ResidueVanishing R M) : Module.Flat R M := by
   haveI := hR; haveI := hS; haveI := hloc; haveI := hfin
-  exact Module.flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero_univ
+  exact FlatnessAudit.TorUniv.solution
     (S := S) hκ
 
 end LocalCritPort
```

## Retained patch: TowerZero-compat.patch

```diff
--- TowerZero.lean.initial
+++ TowerZero.lean
@@ -270,7 +270,6 @@
   rw [hM, hF, hG]
   simp only [Category.assoc]
 
-  refine Eq.trans (whisker_eq _ (whisker_eq _ (hbr _))) ?_
   refine Eq.trans (whisker_eq _ ((Category.assoc _ _ _).symm)) ?_
   refine Eq.trans (whisker_eq _ (eq_whisker hι _)) ?_
   refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
```

## Retained patch: TowerZero-initial.patch

```diff
--- upstream/IsLocalRing_flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map
+++ TowerZero.lean
@@ -1,7 +1,12 @@
+/-
+Copyright 2026 Anthropic, PBC. Apache-2.0; see LICENSE and NOTICE.
+Adapted by Worker 362 for a private feasibility audit, 2026-10-25.
+Changed namespace; removed unused P2M.Util; redirected the Tor criterion import and call where present.
+Original: P2M/Sol/S_IsLocalRing_flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map.lean at 6e837e75355538c7f80bab5b956861e86c4eacc2.
+-/
 import Mathlib
-import Theorems.Thm_Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero
-import P2M.Util
-namespace P2MW.S_IsLocalRing_flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map
+import TorZero
+namespace FlatnessAudit.TowerZero
 
 set_option autoImplicit false
 set_option maxHeartbeats 3200000
@@ -603,7 +608,7 @@
     (hloc : IsLocalHom (algebraMap R S)) (hfin : Module.Finite S M)
     (hκ : Igw157LcTor1ResidueVanishing R M) : Module.Flat R M := by
   haveI := hR; haveI := hS; haveI := hloc; haveI := hfin
-  exact Module.flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero
+  exact FlatnessAudit.TorZero.solution
     (S := S) hκ
 
 end LocalCritPort
```

## Retained patch: primary-initial.patch

```diff
--- upstream/Module_flat_of_comap_maximalIdeal_rTensor_injective
+++ Primary.lean
@@ -1,6 +1,11 @@
+/-
+Copyright 2026 Anthropic, PBC. Apache-2.0; see LICENSE and NOTICE.
+Adapted by Worker 362 for a private feasibility audit, 2026-10-25.
+Changed namespace; removed P2M.Util; replaced scope reactivation with open scoped.
+Original: P2M/Sol/S_Module_flat_of_comap_maximalIdeal_rTensor_injective.lean at 6e837e75355538c7f80bab5b956861e86c4eacc2.
+-/
 import Mathlib
-import P2M.Util
-namespace P2MW.S_Module_flat_of_comap_maximalIdeal_rTensor_injective
+namespace FlatnessAudit.Primary
 
 open TensorProduct LinearMap
 
@@ -22,7 +27,7 @@
 def equiv : FreeCover R X ≃ₗ[R] (X →₀ R) := LinearEquiv.refl R _
 
 end FreeCover
-p2m_reactivate "P2MW.S_Module_flat_of_comap_maximalIdeal_rTensor_injective.LocalFlatnessCriterionAtPrime.FreeCover"
+open scoped FlatnessAudit.Primary.LocalFlatnessCriterionAtPrime.FreeCover
 
 section KernelTransfer
 
@@ -378,7 +383,7 @@
       (torVanish_of_torsion I hsplit hI hN'')
 
 end KernelTransfer
-p2m_reactivate "P2MW.S_Module_flat_of_comap_maximalIdeal_rTensor_injective.LocalFlatnessCriterionAtPrime.FreeCover"
+open scoped FlatnessAudit.Primary.LocalFlatnessCriterionAtPrime.FreeCover
 
 section Tail
 
@@ -571,7 +576,7 @@
   exact (Submodule.mem_bot S).mp this
 
 end Tail
-p2m_reactivate "P2MW.S_Module_flat_of_comap_maximalIdeal_rTensor_injective.LocalFlatnessCriterionAtPrime.FreeCover"
+open scoped FlatnessAudit.Primary.LocalFlatnessCriterionAtPrime.FreeCover
 
 section Split
 
@@ -669,7 +674,7 @@
   rw [hinj (c₂.injective hxy)]
 
 end Split
-p2m_reactivate "P2MW.S_Module_flat_of_comap_maximalIdeal_rTensor_injective.LocalFlatnessCriterionAtPrime.FreeCover"
+open scoped FlatnessAudit.Primary.LocalFlatnessCriterionAtPrime.FreeCover
 
 theorem flat_of_comap_maximalIdeal_lTensor_injective
     {R : Type u} {S : Type*} {M : Type v} [CommRing R] [CommRing S] [Algebra R S]
@@ -694,10 +699,10 @@
     _ ≤ (⊥ : Ideal S).jacobson := IsLocalRing.maximalIdeal_le_jacobson _
 
 end LocalFlatnessCriterionAtPrime
-p2m_reactivate "P2MW.S_Module_flat_of_comap_maximalIdeal_rTensor_injective.LocalFlatnessCriterionAtPrime.FreeCover P2MW.S_Module_flat_of_comap_maximalIdeal_rTensor_injective.LocalFlatnessCriterionAtPrime"
+open scoped FlatnessAudit.Primary.LocalFlatnessCriterionAtPrime.FreeCover FlatnessAudit.Primary.LocalFlatnessCriterionAtPrime
 
 end
-p2m_reactivate "P2MW.S_Module_flat_of_comap_maximalIdeal_rTensor_injective.LocalFlatnessCriterionAtPrime.FreeCover P2MW.S_Module_flat_of_comap_maximalIdeal_rTensor_injective.LocalFlatnessCriterionAtPrime"
+open scoped FlatnessAudit.Primary.LocalFlatnessCriterionAtPrime.FreeCover FlatnessAudit.Primary.LocalFlatnessCriterionAtPrime
 
 theorem solution
     {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
```

The `*-compat.patch` files are failed experiments, not recommended fixes. Apply them after the corresponding initial adaptation only to reproduce check `9b300eab-7016-4613-9f4f-5f365725f4c4`; the original tower check uses only the initial edits.

## Inspection module: InspectPrimary

```lean
import Primary
import Langlands.Algebra.LocalFlatnessCriterionStatement

universe u v w

namespace FlatnessAudit

theorem exact00MK : Langlands.Algebra.LocalFlatnessCriterionStatement.{u,v,w} := by
  intro R S M _ _ _ _ _ _ _ _ _ _ _ _ _ h
  exact Primary.solution (S := S) (IsLocalRing.maximalIdeal R)
    (IsLocalRing.maximalIdeal_comap (algebraMap R S)) h

end FlatnessAudit

set_option pp.universes true in
#check @FlatnessAudit.Primary.solution
set_option pp.universes true in
#check @FlatnessAudit.exact00MK
#print axioms FlatnessAudit.Primary.solution
#print axioms FlatnessAudit.exact00MK
```

## Inspection module: InspectTower

```lean
import TorZero
import TowerZero
import TorUniv
import TowerUniv

set_option pp.universes true in
#check @FlatnessAudit.TorZero.solution
#print axioms FlatnessAudit.TorZero.solution
set_option pp.universes true in
#check @FlatnessAudit.TowerZero.solution
#print axioms FlatnessAudit.TowerZero.solution
set_option pp.universes true in
#check @FlatnessAudit.TorUniv.solution
#print axioms FlatnessAudit.TorUniv.solution
set_option pp.universes true in
#check @FlatnessAudit.TowerUniv.solution
#print axioms FlatnessAudit.TowerUniv.solution
```

## lean_check arguments: Primary checks

```json
{
  "environment_artifact": "3b864ddf-f0af-4c18-8903-c6f813a0ce0f",
  "directory": ".private/drafts/anthropic-flatness",
  "modules": [
    "Primary",
    "InspectPrimary"
  ],
  "declaration": "FlatnessAudit.exact00MK"
}
```

## lean_check arguments: Initial tower check

```json
{
  "environment_artifact": "3b864ddf-f0af-4c18-8903-c6f813a0ce0f",
  "directory": ".private/drafts/anthropic-flatness",
  "modules": [
    "TorZero",
    "TowerZero",
    "TorUniv",
    "TowerUniv",
    "InspectTower"
  ]
}
```

## lean_check arguments: Failed compatibility check

```json
{
  "environment_artifact": "3b864ddf-f0af-4c18-8903-c6f813a0ce0f",
  "directory": ".private/drafts/anthropic-flatness",
  "modules": [
    "Primary",
    "InspectPrimary",
    "TorZero",
    "TowerZero",
    "TorUniv",
    "TowerUniv",
    "InspectTower"
  ],
  "declaration": "FlatnessAudit.exact00MK"
}
```

Call these via TaskHub `lean_check`, never through shell Lean/Lake. The primary recheck uses the primary arguments above. Collect each terminal result. Draft Markdown companions explain provenance and the implemented proof; the evidence scripts show their initial construction.

## Full unapplied primary declaration and axiom output

```text
info: source/InspectPrimary.lean:16:0: @FlatnessAudit.Primary.solution.{u_1, u_2,
    u_3} : ∀ {R : Type u_1} {S : Type u_2} {M : Type u_3} [inst : CommRing.{u_1} R] [inst_1 : CommRing.{u_2} S]
  [inst_2 : Algebra.{u_1, u_2} R S] [IsNoetherianRing.{u_1} R] [IsNoetherianRing.{u_2} S] [inst_5 : IsLocalRing.{u_2} S]
  [inst_6 : AddCommGroup.{u_3} M] [inst_7 : Module.{u_1, u_3} R M] [inst_8 : Module.{u_2, u_3} S M]
  [IsScalarTower.{u_1, u_2, u_3} R S M] [Module.Finite.{u_2, u_3} S M] (p : Ideal.{u_1} R),
  Eq.{u_1 + 1} (Ideal.comap.{u_1, u_2, max u_1 u_2} (algebraMap.{u_1, u_2} R S) (IsLocalRing.maximalIdeal.{u_2} S)) p →
    Function.Injective.{max (u_1 + 1) (u_3 + 1), max (u_1 + 1) (u_3 + 1)}
        ⇑(LinearMap.rTensor.{u_1, u_3, u_1, u_1} M (Submodule.subtype.{u_1, u_1} p)) →
      Module.Flat.{u_1, u_3} R M
info: source/InspectPrimary.lean:18:0: FlatnessAudit.exact00MK.{u_1, u_2, u_3} : Langlands.Algebra.LocalFlatnessCriterionStatement.{u_1, u_2, u_3}
info: source/InspectPrimary.lean:19:0: 'FlatnessAudit.Primary.solution' depends on axioms: [propext, Classical.choice, Quot.sound]
info: source/InspectPrimary.lean:20:0: 'FlatnessAudit.exact00MK' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (4 jobs).
```

## Primary full structured declaration inspection

```json
{
  "module": "InspectPrimary",
  "declaration": "FlatnessAudit.exact00MK",
  "ok": true,
  "metadata": {
    "axiom_modules": {
      "Classical.choice": "Init.Prelude",
      "Quot.sound": "Init.Prelude",
      "propext": "Init.Core"
    },
    "axioms": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "declaration": "FlatnessAudit.exact00MK",
    "kind": "theorem",
    "level_parameters": [
      "u",
      "v",
      "w"
    ],
    "module": "InspectPrimary",
    "protocol": "task-based-lean-inspect@3",
    "statement_module": "",
    "statement_returns_prop": false,
    "statement_target_encoding": null,
    "target_matches": false,
    "type_encoding": "repr",
    "type_sha256": "adcf9218353ac4b3fe7c4f0e52c3acad4a782ea135d626fb96246f3ad1aeda06",
    "type_bytes": 134,
    "expression_transport": "private files; exact UTF-8 fingerprints retained"
  },
  "process": {
    "argv": [
      "/home/taskhub/src/Task-based-auto-formalize/.tools/codex-0.160.0/node_modules/@openai/codex-linux-x64/vendor/x86_64-unknown-linux-musl/bin/codex",
      "-c",
      "permissions.lean.extends=\":workspace\"",
      "-c",
      "permissions.lean.filesystem={\":slash_tmp\" = \"read\", \"/run/user/1000\" = \"deny\", \"/home/taskhub/.local/share/task-based-auto-formalize/codex/auth.json\" = \"deny\", \"/home/taskhub/.local/share/task-based-auto-formalize/claude/.credentials.json\" = \"deny\", \"/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/4/.lake/build/lib/lean\" = \"write\", \"/home/taskhub/pilot/.task-based/lean-service/scratch/40934fb0b0f4453ea42d322a1d19c9bf\" = \"write\"}",
      "sandbox",
      "-P",
      "lean",
      "-C",
      "/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/4/.lake/build/lib/lean",
      "--",
      "/home/taskhub/.elan/toolchains/leanprover--lean4---v4.34.0/bin/lean",
      "--run",
      "/home/taskhub/src/Task-based-auto-formalize/src/task_based_auto_formalize/lean_tools/Inspect.lean",
      "/home/taskhub/.elan/toolchains/leanprover--lean4---v4.34.0",
      "InspectPrimary",
      "FlatnessAudit.exact00MK",
      "--output",
      "/home/taskhub/pilot/.task-based/lean-service/scratch/40934fb0b0f4453ea42d322a1d19c9bf/inspect-e1ede2b1844e47bcbcdf98d898ef6256/result.json"
    ],
    "returncode": 0,
    "stdout": "",
    "stderr": "",
    "duration_seconds": 26.511756329011405,
    "timed_out": false,
    "output_limited": false,
    "error": null,
    "tree_quiet": true
  },
  "proof_accepted": false,
  "validation_method": "lake-build"
}
```

No analogous successful tower output exists. The inspection module was requested, but dependency compilation failed.

## Cancelled transport-timeout recheck: terminal service state

```json
{
  "id": "befc6e0bd63b43feae9c02a990e02e16",
  "state": "done",
  "outcome": "cancelled",
  "definitive": 0,
  "submitted_at": 1792936394.5663567,
  "started_at": null,
  "finished_at": 1792936530.2889192
}
```

The call returned `ReadTimeout`; a read-only query of the service record subsequently found `state: done`, `outcome: cancelled`, and no start time. No result or axiom inspection is attributed to that cancelled job. The two subsequent calls have complete terminal reports.

## Current private experiment file hashes

These identify the final files after the failed compatibility edit. The report-specific module hashes identify each earlier checked version.

| File | SHA256 |
| --- | --- |
| `InspectPrimary.lean` | `e1a1777dae0cd650f298f4467edd21024dacc876dd871a1c8ce8b7009fafdcd1` |
| `InspectTower.lean` | `511a935f5778053e56e84be1fa5ecb6141e430b574191acb0fe6d623ad21ba45` |
| `Primary.lean` | `d32767d091be9342362593ccb38ef19c75ec3fc4d4f177fcc74d1331edcc9e4e` |
| `TorUniv.lean` | `9550bc4dff1f09ec14558ca09cc4049b4525c27dddefd7c3c330c5c3302bcb22` |
| `TorZero.lean` | `99a5b87ac66803e9496669bdde0002c159236bf342e35cfbd50756f85e9304a7` |
| `TowerUniv.lean` | `ec473e70e317c63bd5ddd640f3b02dbb67cb61ca0df8ca7f1f855119819fe75c` |
| `TowerZero.lean` | `bbdca40c70b9f77b08641af9862c0cf9518f3b6faa089a87f3e23ebd24d81a60` |

## Retained source notices

All three files were read and copied intact to the private experiment directory. No applicable per-file attribution row was found; the source table’s explicit coverage limits remain relevant.

| File | SHA256 |
| --- | --- |
| `LICENSE` | `746bc52848eabf8765635fe532e0680756a10b18e7b3fb26e7433ab4edf34034` |
| `NOTICE` | `42b1821f19a6aaa25e6811d22ab8f2fdc6433d4a37bc810b1cfafa5b6dd6b0b6` |
| `ATTRIBUTION.md` | `698fb76c8d80b2ed78ebd48b271f2ee5815b3654fb8ec5c699b21b16ce0d9698` |
