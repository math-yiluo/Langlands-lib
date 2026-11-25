# `apply_brauer_port.py`

This page holds the script `apply_brauer_port.py` as it is, in the code block below. To use it, save the content of the block under that name.

```python
#!/usr/bin/env python3
"""Apply, to a Library tree, the edits that the Brauer port made outside the Brauer block, and
report the files that still mention an old name or import an old module.

Usage: apply_brauer_port.py TREE [--apply] [--names BRAUER-NAMES.tsv]

TREE is a Library tree (the directory holding `Langlands/`). Without `--apply` nothing is written:
the edits are computed in memory and the report describes the tree as it would be after them.

Edits. The port changed four Library files outside the block,
`Langlands/Representation/Finite/{BrauerLatticeProof,DegreeZeroBrauerProof,DegreeZeroBrauerSupport,
DegreeZeroMonomial}.lean`, and their pages `….md`. The edits are stored below as exact text hunks
(old text, new text); each hunk is applied if its old text occurs exactly once, reported as
"already applied" if its new text occurs and the old does not, and as "NOT FOUND" otherwise. A file
that does not exist is reported and skipped (the tree in `ref/tree` has Lean files but no pages).

Report. Every `.lean` and `.md` file of the tree is searched, after the edits, for
- an old module of the block (`Langlands.AnthropicFLT.…` dotted, or its path
  `AnthropicFLT/…`), and whether it is imported;
- an old declaration name of the block (first column of BRAUER-NAMES.tsv), as a whole token;
- the FLT proof name spaces `P2MW.S_…` of the block and the partial references
  `SolomonProof.x`, `MonomialProof.x`, `BrauerProof.x` with `x` a short name of the block.
Only the `Langlands/` directory of the tree is searched. The files of the old block itself (the
seven modules and their pages, which the port removes) are listed apart, all of them that exist;
so are the port's new files, whose headers and pages name the FLT declarations they were made from.
The third list, other files that still mention an old name or module, is the one that should be
empty once the port is complete.
"""
import argparse
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
FIN = 'Langlands/Representation/Finite/'

OLD_MODULES = [
    'Definitions.Def_ClassFunction_Induced',
    'Theorems.Thm_ClassFunction_exists_one_eq_sum_zsmul_induced_one_of_hyperelementary',
    'P2M.Sol.S_ClassFunction_exists_one_eq_sum_zsmul_induced_one_of_hyperelementary',
    'Theorems.Thm_ClassFunction_exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem',
    'P2M.Sol.S_ClassFunction_exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem',
    'Theorems.Thm_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter',
    'P2M.Sol.S_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter',
]
OLD_NS = [
    'P2MW.S_ClassFunction_exists_one_eq_sum_zsmul_induced_one_of_hyperelementary',
    'P2MW.S_ClassFunction_exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem',
    'P2MW.S_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter',
]
MON_NS = OLD_NS[1]
BRA_NS = OLD_NS[2]

# ---------------------------------------------------------------------------------------------
# The edits, file by file: lists of (old text, new text).
# ---------------------------------------------------------------------------------------------

EDITS = {}

EDITS[FIN + 'BrauerLatticeProof.lean'] = [
    ("""import Langlands.AnthropicFLT.Theorems.Thm_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter
""", """import Langlands.Representation.Finite.BrauerTrace
"""),
    ("""The Brauer trace expansion is the ported Anthropic theorem
`BrauerInduction.exists_trace_eq_sum_zsmul_induced_linearCharacter`, stated for matrix
representations of finite groups in `Type`; this module transports it to finite groups in an
arbitrary universe and identifies its normalized sums with actual induced characters.""",
     """The Brauer trace expansion is
`Langlands.FiniteRep.BrauerTrace.exists_trace_eq_sum_zsmul_induced_linearCharacter`, stated for
matrix representations of finite groups in any universe; this module identifies its normalized sums
with actual induced characters."""),
    ("""  obtain ⟨K, _, _, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv.{uG, 0} G
  obtain ⟨m, H, ψ, a, h⟩ := BrauerInduction.exists_trace_eq_sum_zsmul_induced_linearCharacter
    ((matrixModel V.ρ).comp e.symm.toMonoidHom)
  have hV : V.character = ∑ i : Fin m, a i • inducedCharacter (pullbackDatum e (H i) (ψ i)) := by
    funext g
    have hg := h (e g)
    rw [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulEquiv.symm_apply_apply, matrixModel_trace] at hg
    rw [Finset.sum_apply]
    change Representation.character V.ρ g = _
    rw [hg]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, inducedCharacter_pullbackDatum, zsmul_eq_mul]
""", """  obtain ⟨m, H, ψ, a, h⟩ :=
    BrauerTrace.exists_trace_eq_sum_zsmul_induced_linearCharacter (matrixModel V.ρ)
  have hV : V.character =
      ∑ i : Fin m, a i • inducedCharacter (pullbackDatum (MulEquiv.refl G) (H i) (ψ i)) := by
    funext g
    have hg := h g
    rw [matrixModel_trace] at hg
    rw [Finset.sum_apply]
    change Representation.character V.ρ g = _
    rw [hg]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, inducedCharacter_pullbackDatum, zsmul_eq_mul]
    rfl
"""),
]

EDITS[FIN + 'DegreeZeroBrauerSupport.lean'] = [
    ("""import Langlands.AnthropicFLT.Definitions.Def_ClassFunction_Induced
""", """import Langlands.Representation.Finite.ClassFunctionInduction
"""),
    ("""    { toFun := fun f => ClassFunction.induced S (extend S f)
      map_zero' := by
        funext g
        simp [extend, ClassFunction.induced_apply]""",
     """    { toFun := fun f => inducedClassFunction S (extend S f)
      map_zero' := by
        funext g
        simp [extend, inducedClassFunction_apply]"""),
    ("""        rw [he, ClassFunction.induced_add] }""", """        rw [he, inducedClassFunction_add] }"""),
    ("""  change ClassFunction.induced S (extend S f) g = _
  rw [ClassFunction.induced_apply]""", """  change inducedClassFunction S (extend S f) g = _
  rw [inducedClassFunction_apply]"""),
    ("""  change ClassFunction.induced S
    (fun g => if hg : g ∈ S then ClassFunction.induced T (extend T f) ⟨g, hg⟩ else 0) = _
  rw [ClassFunction.induced_induced]
  apply ClassFunction.induced_congr""", """  change inducedClassFunction S
    (fun g => if hg : g ∈ S then inducedClassFunction T (extend T f) ⟨g, hg⟩ else 0) = _
  rw [inducedClassFunction_inducedClassFunction]
  apply inducedClassFunction_congr"""),
]

EDITS[FIN + 'DegreeZeroMonomial.lean'] = [
    ("""import Langlands.AnthropicFLT.P2M.Sol.S_ClassFunction_exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem
""", """import Langlands.Representation.Finite.MonomialTrace
"""),
    ("""open P2MW.S_ClassFunction_exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem.MonomialProof
""", """open Langlands.FiniteRep.WeightSpaces Langlands.FiniteRep.MonomialTrace
"""),
    ("""  ClassFunction.induced e.1 (extChar e.1 e.2)""", """  inducedClassFunction e.1 (extChar e.1 e.2)"""),
    ("""    change ClassFunction.induced ⊤ (extChar ⊤ (weightHom σ T hχ)) g = _
    rw [ClassFunction.induced_top_of_conj_invariant _ hcf]""",
     """    change inducedClassFunction ⊤ (extChar ⊤ (weightHom σ T hχ)) g = _
    rw [inducedClassFunction_top_of_conj_invariant _ hcf]"""),
    ("""  rw [← induced_lsum_eq]""", """  rw [← inducedClassFunction_lsum_eq]"""),
    ("""      LinearMap.trace ℂ W (σ g) = ClassFunction.induced H₁ Φ g by""",
     """      LinearMap.trace ℂ W (σ g) = inducedClassFunction H₁ Φ g by"""),
    ("""  rw [ClassFunction.induced_apply]
  have hint := isInternal_wt σ B hcommB""", """  rw [inducedClassFunction_apply]
  have hint := isInternal_wt σ B hcommB"""),
]

EDITS[FIN + 'DegreeZeroBrauerProof.lean'] = [
    ("""import Langlands.AnthropicFLT.P2M.Sol.S_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter
""", """import Langlands.Representation.Finite.SolomonInduction
"""),
    ("""  open P2MW.S_ClassFunction_exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem.MonomialProof in""",
     """  open Langlands.FiniteRep.MonomialTrace in"""),
    ("""      ClassFunction.induced S (fun _ => (1 : ℂ)) g * augment K V.character g := by
  rw [ind_apply, ClassFunction.induced_apply]""",
     """      inducedClassFunction S (fun _ => (1 : ℂ)) g * augment K V.character g := by
  rw [ind_apply, inducedClassFunction_apply]"""),
    ("""    obtain ⟨k, H, a, hH, h1⟩ :=
      P2MW.S_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter.BrauerProof.solomon_complex
        (G := K)""", """    obtain ⟨k, H, a, hH, h1⟩ :=
      Solomon.exists_one_eq_sum_zsmul_inducedClassFunction_one_complex (G := K)"""),
]

# Pages.

EDITS[FIN + 'BrauerLatticeProof.md'] = [
    ("""- `Langlands.AnthropicFLT.Theorems.Thm_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter`, the
  port of the Anthropic FLT theorem `BrauerInduction.exists_trace_eq_sum_zsmul_induced_linearCharacter` (ported in
  the same contribution; see that module's Markdown for source, licence and changes). For a finite group `K : Type`
  and `ρ : K →* GL (Fin n) ℂ` it gives subgroups `H i`, unit characters `ψ i : H i →* ℂˣ` and integers `a i` with
  `trace (ρ g) = ∑ i, (a i : ℂ) * ((Nat.card (H i))⁻¹ * ∑ y : K, [y⁻¹ g y ∈ H i] ψ i (y⁻¹ g y))`.

The external theorem concerns a group in universe `0`, matrix representations, and a normalized conjugation sum.
The target concerns groups in an arbitrary universe, `FDRep` representation classes, and characters of actual
induced representations. This file bridges those three differences.""",
     """- `Langlands.Representation.Finite.BrauerTrace`, for
  `Langlands.FiniteRep.BrauerTrace.exists_trace_eq_sum_zsmul_induced_linearCharacter`, Brauer's theorem in trace
  form (the Library's port of the Anthropic FLT proof; see that module's Markdown for source, licence and changes).
  For a finite group `K` in any universe and `ρ : K →* GL (Fin n) ℂ` it gives subgroups `H i`, unit characters
  `ψ i : H i →* ℂˣ` and integers `a i` with
  `trace (ρ g) = ∑ i, (a i : ℂ) * ((Nat.card (H i))⁻¹ * ∑ y : K, [y⁻¹ g y ∈ H i] ψ i (y⁻¹ g y))`.

That theorem concerns matrix representations and a normalized conjugation sum. The target concerns `FDRep`
representation classes and characters of actual induced representations. This file bridges these two
differences; both are stated for groups in an arbitrary universe."""),
    ("""- `character_mem_inducedCharacterLattice V`: for every `V : FDRep ℂ G`, the character `V.character` lies in
  `inducedCharacterLattice`. Mathlib's `Finite.exists_type_univ_nonempty_mulEquiv` gives a finite group `K : Type` and
  `e : G ≃* K`. Apply the external theorem to `(matrixModel V.ρ).comp e.symm`, obtaining `H i`, `ψ i` and `a i`.
  Evaluating at `e g` and using `matrixModel_trace` gives `V.character g` on the left. By
  `inducedCharacter_pullbackDatum`, the `i`-th summand on the right is `a i • inducedCharacter (pullbackDatum e (H i) (ψ i)) g`.
  Hence `V.character = ∑ i, a i • inducedCharacter (pullbackDatum e (H i) (ψ i))`, a finite `ℤ`-combination of
  generators of the lattice.""",
     """- `character_mem_inducedCharacterLattice V`: for every `V : FDRep ℂ G`, the character `V.character` lies in
  `inducedCharacterLattice`. Apply Brauer's theorem in trace form to `matrixModel V.ρ`, obtaining `H i`, `ψ i` and
  `a i`; `matrixModel_trace` gives `V.character g` on the left. By `inducedCharacter_pullbackDatum` for the identity
  `MulEquiv.refl G`, the `i`-th summand on the right is
  `a i • inducedCharacter (pullbackDatum (MulEquiv.refl G) (H i) (ψ i)) g`. Hence
  `V.character = ∑ i, a i • inducedCharacter (pullbackDatum (MulEquiv.refl G) (H i) (ψ i))`, a finite
  `ℤ`-combination of generators of the lattice."""),
]

EDITS[FIN + 'DegreeZeroBrauerSupport.md'] = [
    ("""`extend S f` extends a complex function on a subgroup by zero. `ind S` is the
integer-linear normalized conjugation sum, using the published
`ClassFunction.induced` convention. `ind_apply` states its explicit dependent
sum, and `ind_character` identifies it with the trace character of the actual
finite-dimensional induction `induceRep`. `virtualCharacter_induce` extends this
comparison to the genuine split representation group by writing each virtual
class as a difference of actual classes.""",
     """`extend S f` extends a complex function on a subgroup by zero. `ind S` is the
integer-linear normalized conjugation sum, using the published
`Langlands.FiniteRep.inducedClassFunction` convention (`ClassFunctionInduction`).
`ind_apply` states its explicit dependent sum, and `ind_character` identifies it
with the trace character of the actual finite-dimensional induction `induceRep`.
`virtualCharacter_induce` extends this comparison to the genuine split representation
group by writing each virtual class as a difference of actual classes."""),
]

EDITS[FIN + 'DegreeZeroMonomial.md'] = [
    ("""Apache-2.0); see the repository notices. The original helper lemmas are imported
from the published Library and remain unchanged.""",
     """Apache-2.0); see the repository notices. The original helper lemmas are imported
from the published Library (`MonomialTrace`, `WeightSpaces`) and remain unchanged."""),
    ("""contained in every subgroup of the list. Both the group and the representation
carrier are in `Type 0`, as in the imported engine. This helper does not claim""",
     """contained in every subgroup of the list. Both the group and the representation
carrier are in `Type 0` here (the imported `MonomialTrace.engine` allows any
universes). This helper does not claim"""),
    ("""The existing `lsum` and `ClassFunction.induced` conventions are unchanged.""",
     """The existing `lsum` and `inducedClassFunction` conventions are unchanged."""),
]

EDITS[FIN + 'DegreeZeroBrauerProof.md'] = [
    ("""This implementation uses the Solomon and retained-normal-subgroup monomial
route. Solomon's identity is imported by Lean name from the published
Anthropic FLT port; the retained-subgroup engine and induction adapters are""",
     """This implementation uses the Solomon and retained-normal-subgroup monomial
route. Solomon's identity is
`Langlands.FiniteRep.Solomon.exists_one_eq_sum_zsmul_inducedClassFunction_one_complex`
from `SolomonInduction`, the Library's port of the Anthropic FLT proof; the
retained-subgroup engine and induction adapters are"""),
]


# ---------------------------------------------------------------------------------------------

def load_names(path):
    olds = []
    with open(path, encoding='utf-8') as f:
        next(f)
        for line in f:
            olds.append(line.split('\t')[0])
    return olds


def token_re(name):
    return re.compile(r"(?<![\w.'!?])" + re.escape(name) + r"(?![\w'!?])")


PREFILTER = ('ClassFunction', 'BrauerInduction', 'P2MW', 'SolomonProof', 'MonomialProof',
             'BrauerProof', 'AnthropicFLT')

NEW_FILES = {FIN + m + ext for m in ['ClassFunctionInduction', 'SolomonInduction', 'WeightSpaces',
                                     'MonomialTrace', 'BrauerTrace'] for ext in ('.lean', '.md')}


def block_files():
    out = set()
    for m in OLD_MODULES:
        p = 'Langlands/AnthropicFLT/' + m.replace('.', '/')
        out.add(p + '.lean')
        out.add(p + '.md')
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('tree')
    ap.add_argument('--apply', action='store_true')
    ap.add_argument('--names', default=os.path.join(HERE, '..', 'BRAUER-NAMES.tsv'))
    a = ap.parse_args()
    tree = a.tree

    # 1. edits
    new_text = {}
    print(f'== Edits ({"applied" if a.apply else "dry run, nothing written"}) on {tree}')
    for rel, hunks in EDITS.items():
        p = os.path.join(tree, rel)
        if not os.path.exists(p):
            print(f'{rel}: absent, skipped')
            continue
        txt = open(p, encoding='utf-8').read()
        status = []
        for i, (old, new) in enumerate(hunks, 1):
            n_old, n_new = txt.count(old), txt.count(new) if new else 0
            if n_old == 1:
                txt = txt.replace(old, new)
                status.append(f'{i}:applied')
            elif n_old == 0 and n_new >= 1:
                status.append(f'{i}:already')
            else:
                status.append(f'{i}:NOT FOUND' if n_old == 0 else f'{i}:AMBIGUOUS({n_old})')
        new_text[rel] = txt
        print(f'{rel}: ' + ' '.join(status))
        if a.apply:
            with open(p, 'w', encoding='utf-8') as f:
                f.write(txt)

    # 2. report
    olds = load_names(a.names)
    shorts = set()
    for o in olds:
        for ns in OLD_NS:
            for sub in ('.SolomonProof.', '.MonomialProof.', '.BrauerProof.'):
                if o.startswith(ns + sub):
                    shorts.add((sub.strip('.'), o[len(ns + sub):]))
    name_res = [(o, token_re(o)) for o in olds]
    ns_res = [(n, re.compile(re.escape(n) + r"(?![\w'])")) for n in OLD_NS]
    partial_res = [(f'{s}.{x}', token_re(f'{s}.{x}')) for (s, x) in sorted(shorts)]
    mod_res = []
    for m in OLD_MODULES:
        mod_res.append((m, re.compile(re.escape('Langlands.AnthropicFLT.' + m) + r"(?![\w])")))
        mod_res.append((m, re.compile(re.escape('AnthropicFLT/' + m.replace('.', '/')) + r"(?![\w])")))
    import_res = [re.compile(r'^\s*import\s+' + re.escape('Langlands.AnthropicFLT.' + m) + r'\s*$', re.M)
                  for m in OLD_MODULES]
    blk = block_files()
    hits_other, hits_block, hits_new = [], [], []
    present_block = sorted(r for r in blk if os.path.exists(os.path.join(tree, r)))
    nfiles = 0
    for dp, dn, fn in os.walk(os.path.join(tree, 'Langlands')):
        dn[:] = [d for d in dn if not d.startswith('.')]
        for x in fn:
            if not (x.endswith('.lean') or x.endswith('.md')):
                continue
            p = os.path.join(dp, x)
            rel = os.path.relpath(p, tree)
            nfiles += 1
            txt = new_text.get(rel)
            if txt is None:
                txt = open(p, encoding='utf-8', errors='replace').read()
            # every pattern below contains one of these substrings; skip files with none
            if not any(k in txt for k in PREFILTER):
                continue
            found = []
            if any(r.search(txt) for r in import_res):
                found.append('imports an old module')
            mods = sorted({m for (m, r) in mod_res if r.search(txt)})
            if mods:
                found.append('mentions old module(s): ' + ', '.join(mods))
            nm = sorted({o for (o, r) in name_res if r.search(txt)})
            nsm = sorted({n for (n, r) in ns_res if r.search(txt)})
            pm = sorted({s for (s, r) in partial_res if r.search(txt)})
            if nm:
                found.append(f'{len(nm)} old name(s): ' + ', '.join(nm[:6]) + (' …' if len(nm) > 6 else ''))
            if nsm and not nm:
                found.append('old FLT name space(s): ' + ', '.join(nsm))
            if pm:
                found.append('partial old name(s): ' + ', '.join(pm[:6]) + (' …' if len(pm) > 6 else ''))
            if found:
                if rel in blk:
                    hits_block.append((rel, found))
                elif rel in NEW_FILES:
                    hits_new.append((rel, found))
                else:
                    hits_other.append((rel, found))
    print(f'\n== Report: {nfiles} Lean files and pages under Langlands/ searched')
    print(f'Files of the old block present (the port removes them): {len(present_block)}')
    found_block = dict(hits_block)
    for rel in present_block:
        print(f'  {rel}: ' + '; '.join(found_block.get(rel, ['(no textual mention)'])))
    print(f'New files of the port naming FLT declarations in their provenance text: {len(hits_new)}')
    for rel, f in sorted(hits_new):
        print(f'  {rel}: ' + '; '.join(f))
    print(f'Other files that still mention an old name or module: {len(hits_other)}')
    for rel, f in sorted(hits_other):
        print(f'  {rel}: ' + '; '.join(f))


if __name__ == '__main__':
    main()
```
