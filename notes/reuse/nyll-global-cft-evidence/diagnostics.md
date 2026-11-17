# Lean diagnostics of the NYLL global audit

Evidence for [the audit note](../nyll-global-cft-audit.md), section 4. All checks ran in the project's Lean service with `lean_check` on environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean `v4.34.0`, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`), from a private draft directory holding the adapted closure of [closure.md](closure.md). The diagnostic identifiers are those of the service's records.

## 1. Builds of the closure, by layers

A single check of the six roots from scratch exceeded the service's 30-minute limit per call: run `002b1572` stopped there after reporting one error (the one fixed by the edit to `IntegerRingComparison`), and run `e5e0ad89` stopped with no message. The closure was therefore built in layers: each call requests the maximal modules among those of import depth at most N, which builds all modules of depth at most N. The build cache of the service keeps the outputs of earlier calls, including the modules compiled by the stopped runs, and rebuilds a module whenever its source or an import changed. Every call below ended with return code 0, no error and no warning.

| Diagnostic | Modules of the closure covered | Requested (maximal) modules | Build time (s) |
|---|---|---|---|
| `56515156-ac3f-4041-bc3b-0f437432d846` | depth ≤ 15: 430 | 93 | 1006 |
| `8be82939-386c-4b96-8f9c-25d5ba662087` | depth ≤ 30: 591 | 70 | 312 |
| `99f0429f-3c4d-4ea1-a745-93f961757dec` | depth ≤ 59: 742 | 57 | 16 |
| `48da7e0d-1632-417f-8302-7e4eec4f694e` | depth ≤ 75: 839 | 43 | 20 |
| `82fbda58-3e54-4747-9bf5-35ea471173ba` | depth ≤ 95: 931 | 21 | 214 |
| `913786b0-382e-4a71-b6b4-d1fd193018ff` | all 957 (the six roots) | 6 | 791 |

The import depth of a module is 1 plus the largest depth of its imports inside the closure; the largest depth is 107. The edits were found from the errors of earlier calls (for example `de07aa77`, `366aee7c`, `3f446f6f`, `38edcaf8`, `1670d346` and `002b1572`); [edits.md](edits.md) gives the final state.

## 2. Declarations: signatures and axioms

Diagnostic `3c6e5461-795a-465e-affe-39d3a25b0652` (ok, 39 information messages, no error, no warning). Module `NyllGlobalDiag`:

```lean
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.MathlibGlobalReciprocity
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.MathlibFrobeniusHilbertComparison
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ArithmeticNormalization
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteIdeleArtin
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.MathlibTopologyComparison
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Topology

/-! Audit diagnostic (Task 7345): the NYLL fbd320cd declarations that supply
clauses of `Langlands.Global.FiniteAbelianClassFieldStatement`, compiled from the
adapted closure on the Library's pin. Signatures and axioms only. -/

-- Clause 1: arithmetic Artin map on idele classes, kernel, surjectivity, continuity.
#check @GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom
#check @GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_ker
#check @GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_surjective
#check @GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_continuous
#check @GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
#check @ClassFieldTheory.GlobalClassFieldComparison.arithmeticPrimeArtin_eq_arithmeticFrobeniusAt
#check @GlobalClassFieldTheory.Reciprocity.chosenFinitePlaceArtinMonoidHom_eq_one_of_integral_of_unramifiedAt
#check @ClassFieldTheory.GlobalClassFieldComparison.finiteAbelianGlobalReciprocity
-- Clause 2: open subgroups contain a congruence subgroup.
#check @RayClass.exists_congruenceSubgroup_le_of_isOpen
-- Clause 3: class field of a closed finite-index subgroup.
#check @ClassFieldTheory.GlobalClassFieldComparison.classFieldExistence_normSubgroup
#check @ClassFieldTheory.GlobalClassFieldComparison.classFieldExistence_degree
-- Bridge to Mathlib's idele class group (the Library's `IdeleClasses`).
#check @IdeleGroup.ideleClassGroupContinuousMulEquivMathlib

-- Further declarations used in the audit note (added in the coauthor review).
#check @GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_comp_finitePlaceIdeleClass
#check @GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin_eq_arithmeticChosenFinitePlaceArtin
#check @IdeleGroup.ideleClassGroupEquivMathlib_finitePlaceIdeleClass
#check @RayClass.congruenceSubgroupFiniteIndex
#check @RayClass.isClosed_and_finiteIndex_iff_exists_congruenceSubgroup_le
#check @GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassField
#check @GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_apply
#check @ClassFieldTheory.arithmeticFrobeniusAt

#print axioms GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_ker
#print axioms GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_surjective
#print axioms GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_continuous
#print axioms ClassFieldTheory.GlobalClassFieldComparison.arithmeticPrimeArtin_eq_arithmeticFrobeniusAt
#print axioms GlobalClassFieldTheory.Reciprocity.chosenFinitePlaceArtinMonoidHom_eq_one_of_integral_of_unramifiedAt
#print axioms ClassFieldTheory.GlobalClassFieldComparison.finiteAbelianGlobalReciprocity
#print axioms RayClass.exists_congruenceSubgroup_le_of_isOpen
#print axioms ClassFieldTheory.GlobalClassFieldComparison.classFieldExistence_normSubgroup
#print axioms ClassFieldTheory.GlobalClassFieldComparison.classFieldExistence_degree
#print axioms IdeleGroup.ideleClassGroupContinuousMulEquivMathlib
#print axioms GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_comp_finitePlaceIdeleClass
#print axioms GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin_eq_arithmeticChosenFinitePlaceArtin
#print axioms IdeleGroup.ideleClassGroupEquivMathlib_finitePlaceIdeleClass
#print axioms RayClass.congruenceSubgroupFiniteIndex
#print axioms RayClass.isClosed_and_finiteIndex_iff_exists_congruenceSubgroup_le
#print axioms GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassField
#print axioms GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom
#print axioms GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_apply
#print axioms ClassFieldTheory.arithmeticFrobeniusAt
```

Its messages, verbatim, by line:

```text
[line 13] GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom : (K L : Type) →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field L] →
        [NumberField L] →
          [inst_4 : Algebra K L] → [FiniteDimensional K L] → [IsAbelianGalois K L] → IdeleClassGroup K →* Gal(L/K)
[line 14] GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_ker : ∀ (K L : Type) [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field L] [inst_3 : NumberField L] [inst_4 : Algebra K L]
  [inst_5 : FiniteDimensional K L] [inst_6 : IsAbelianGalois K L],
  (GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom K L).ker = (ideleClassNorm K L).range
[line 15] GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_surjective : ∀ (K L : Type) [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field L] [inst_3 : NumberField L] [inst_4 : Algebra K L]
  [inst_5 : FiniteDimensional K L] [inst_6 : IsAbelianGalois K L],
  Function.Surjective ⇑(GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom K L)
[line 16] GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_continuous : ∀ (K L : Type) [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field L] [inst_3 : NumberField L] [inst_4 : Algebra K L]
  [inst_5 : FiniteDimensional K L] [inst_6 : IsAbelianGalois K L],
  Continuous ⇑(GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom K L)
[line 17] @GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin : {K L : Type} →
  [inst : Field K] →
    [NumberField K] →
      [inst_2 : Field L] →
        [NumberField L] →
          [inst_4 : Algebra K L] →
            [IsAbelianGalois K L] → IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → Gal(L/K)
[line 18] @ClassFieldTheory.GlobalClassFieldComparison.arithmeticPrimeArtin_eq_arithmeticFrobeniusAt : ∀ {K L : Type}
  [inst : Field K] [inst_1 : NumberField K] [inst_2 : Field L] [inst_3 : NumberField L] [inst_4 : Algebra K L]
  [inst_5 : IsAbelianGalois K L] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)),
  w.asIdeal.LiesOver v.asIdeal →
    Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K) w.asIdeal →
      GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin v =
        ClassFieldTheory.arithmeticFrobeniusAt w
[line 19] @GlobalClassFieldTheory.Reciprocity.chosenFinitePlaceArtinMonoidHom_eq_one_of_integral_of_unramifiedAt : ∀ {K L : Type}
  [inst : Field K] [inst_1 : NumberField K] [inst_2 : Field L] [inst_3 : NumberField L] [inst_4 : Algebra K L]
  [inst_5 : IsAbelianGalois K L] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  (a : IdeleGroup K),
  (IdeleGroup.finiteComponent v) a ∈ (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v).units →
    Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K)
        (finitePlaceExtensionCentre v (chosenFinitePlaceExtension v)).asIdeal →
      (GlobalClassFieldTheory.Reciprocity.chosenFinitePlaceArtinMonoidHom v) ((IdeleGroup.finiteComponent v) a) = 1
[line 20] ClassFieldTheory.GlobalClassFieldComparison.finiteAbelianGlobalReciprocity : ∀ (K L : Type) [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field L] [inst_3 : NumberField L] [inst_4 : Algebra K L] [FiniteDimensional K L]
  [IsAbelianGalois K L], Nonempty (IdeleClassGroup K ⧸ (ideleClassNorm K L).range ≃ₜ* Gal(L/K))
[line 22] @RayClass.exists_congruenceSubgroup_le_of_isOpen : ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  (H : Subgroup (IdeleClassGroup K)), IsOpen ↑H → ∃ m, m.congruenceSubgroup ≤ H
[line 24] ClassFieldTheory.GlobalClassFieldComparison.classFieldExistence_normSubgroup : ∀ (K : Type) [inst : Field K]
  [inst_1 : NumberField K] (H : Subgroup (IdeleClassGroup K)) (hclosed : IsClosed ↑H) [inst_2 : H.FiniteIndex],
  (ideleClassNorm K (GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassField H hclosed)).range = H
[line 25] ClassFieldTheory.GlobalClassFieldComparison.classFieldExistence_degree : ∀ (K : Type) [inst : Field K]
  [inst_1 : NumberField K] (H : Subgroup (IdeleClassGroup K)) (hclosed : IsClosed ↑H) [inst_2 : H.FiniteIndex],
  Module.finrank K (GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassField H hclosed) = H.index
[line 27] IdeleGroup.ideleClassGroupContinuousMulEquivMathlib : (K : Type u_1) →
  [inst : Field K] →
    [inst_1 : NumberField K] → IdeleClassGroup K ≃ₜ* NumberField.IdeleClassGroup (NumberField.RingOfIntegers K) K
[line 30] GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_comp_finitePlaceIdeleClass : ∀ (K L : Type)
  [inst : Field K] [inst_1 : NumberField K] [inst_2 : Field L] [inst_3 : NumberField L] [inst_4 : Algebra K L]
  [inst_5 : FiniteDimensional K L] [inst_6 : IsAbelianGalois K L]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
  (GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom K L).comp
      (IdeleGroup.finitePlaceIdeleClass v) =
    GlobalClassFieldTheory.Reciprocity.arithmeticChosenFinitePlaceArtinMonoidHom K L v
[line 31] @GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin_eq_arithmeticChosenFinitePlaceArtin : ∀
  {K L : Type} [inst : Field K] [inst_1 : NumberField K] [inst_2 : Field L] [inst_3 : NumberField L]
  [inst_4 : Algebra K L] [inst_5 : IsAbelianGalois K L]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
  GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin v =
    (GlobalClassFieldTheory.Reciprocity.arithmeticChosenFinitePlaceArtinMonoidHom K L v)
      (FiniteIdeleGroup.chosenLocalOrderSection v 1)
[line 32] IdeleGroup.ideleClassGroupEquivMathlib_finitePlaceIdeleClass : ∀ (K : Type u_1) [inst : Field K]
  [inst_1 : NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  (x : (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)ˣ),
  (IdeleGroup.ideleClassGroupEquivMathlib K) ((IdeleGroup.finitePlaceIdeleClass v) x) =
    (NumberField.IdeleClassGroup.ofAdicCompletion (NumberField.RingOfIntegers K) K v) x
[line 33] @RayClass.congruenceSubgroupFiniteIndex : ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  (m : RayClass.Modulus K), m.congruenceSubgroup.FiniteIndex
[line 34] @RayClass.isClosed_and_finiteIndex_iff_exists_congruenceSubgroup_le : ∀ {K : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] (H : Subgroup (IdeleClassGroup K)),
  IsClosed ↑H ∧ H.FiniteIndex ↔ ∃ m, m.congruenceSubgroup ≤ H
[line 35] @GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassField : {K : Type} →
  [inst : Field K] →
    [inst_1 : NumberField K] → (H : Subgroup (IdeleClassGroup K)) → IsClosed ↑H → [H.FiniteIndex] → Type
[line 36] GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_apply : ∀ (K L : Type) [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field L] [inst_3 : NumberField L] [inst_4 : Algebra K L]
  [inst_5 : FiniteDimensional K L] [inst_6 : IsAbelianGalois K L] (c : IdeleClassGroup K),
  (GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom K L) c =
    ((GlobalClassFieldTheory.Reciprocity.globalNormResidueMonoidHom K L) c)⁻¹
[line 37] @ClassFieldTheory.arithmeticFrobeniusAt : {K : Type u_1} →
  {L : Type u_2} →
    [inst : Field K] →
      [NumberField K] →
        [inst_2 : Field L] →
          [NumberField L] →
            [inst_4 : Algebra K L] →
              [IsAbelianGalois K L] → IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L) → Gal(L/K)
[line 39] 'GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_ker' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
[line 40] 'GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_surjective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
[line 41] 'GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
[line 42] 'ClassFieldTheory.GlobalClassFieldComparison.arithmeticPrimeArtin_eq_arithmeticFrobeniusAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
[line 43] 'GlobalClassFieldTheory.Reciprocity.chosenFinitePlaceArtinMonoidHom_eq_one_of_integral_of_unramifiedAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
[line 44] 'ClassFieldTheory.GlobalClassFieldComparison.finiteAbelianGlobalReciprocity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
[line 45] 'RayClass.exists_congruenceSubgroup_le_of_isOpen' depends on axioms: [propext, Classical.choice, Quot.sound]
[line 46] 'ClassFieldTheory.GlobalClassFieldComparison.classFieldExistence_normSubgroup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
[line 47] 'ClassFieldTheory.GlobalClassFieldComparison.classFieldExistence_degree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
[line 48] 'IdeleGroup.ideleClassGroupContinuousMulEquivMathlib' depends on axioms: [propext, Classical.choice, Quot.sound]
[line 49] 'GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_comp_finitePlaceIdeleClass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
[line 50] 'GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin_eq_arithmeticChosenFinitePlaceArtin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
[line 51] 'IdeleGroup.ideleClassGroupEquivMathlib_finitePlaceIdeleClass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
[line 52] 'RayClass.congruenceSubgroupFiniteIndex' depends on axioms: [propext, Classical.choice, Quot.sound]
[line 53] 'RayClass.isClosed_and_finiteIndex_iff_exists_congruenceSubgroup_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
[line 54] 'GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassField' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
[line 55] 'GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
[line 56] 'GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
[line 57] 'ClassFieldTheory.arithmeticFrobeniusAt' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every declaration checked, the nineteen of the `#print axioms` lines, depends only on `propext`, `Classical.choice` and `Quot.sound`. Since `#print axioms` follows the definitions a declaration mentions, this also covers the definitions in their statements. Together they are every NYLL declaration named in section 3 of the note except the wrapper `Theorems/GlobalClassFieldTheory/FiniteAbelianGlobalReciprocity.lean:31` and `ordinaryIdeleClassNormSubgroup_injective`, which the note names but which a proof of the clauses would not use.

Universes: the Artin map and its `_apply`, kernel, surjectivity, continuity and finite-place lemmas, the prime-Artin and Frobenius comparisons, the unit lemma, the quotient form `GlobalClassFieldComparison.finiteAbelianGlobalReciprocity` (a `Nonempty` homeomorphic isomorphism from the norm quotient of the idele class group to the Galois group), the class field `closedFiniteIndexClassField` and the two class-field theorems take `K L : Type` or `K : Type` (universe 0). `ClassFieldTheory.arithmeticFrobeniusAt`, the three `RayClass` declarations and the two bridge declarations `IdeleGroup.ideleClassGroupContinuousMulEquivMathlib` and `IdeleGroup.ideleClassGroupEquivMathlib_finitePlaceIdeleClass` are universe-polymorphic.

Earlier runs of the same module checked fewer declarations, with the same results for those: diagnostic `d004145b-cd7f-438f-890e-4718daafcf73` (the first ten `#print axioms` lines) and `fc43fa87-99f0-455f-9a14-b551e262024a` (the first sixteen). The last six were added in the coauthor review.

## 3. Coexistence with the Library and the bridge

### `NyllCoexistDiag`: diagnostic `63bbdfc1-cdab-4be0-96e7-c73ce19c42fd`

Checked at Library commit `fcb85a7ef43356fec01e6ccf1605f08568c08cb0`. It imports the class-field statement, four modules of the Library's NYLL port and the six NYLL roots, with the bridge checked against the Library's `IdeleClasses` and `finiteClassInclusion`. Result: ok, no error, no warning; 1 information message(s):

```text
[line 24] Langlands.Global.FiniteAbelianClassFieldStatement : Prop
```

Source (32 lines, SHA-256 `e115ee5c9392ae42525f1a766ce8e78be26843552f3751d9adbed6a99f67d5a5`):

```lean
import Langlands.Global.Arithmetic.ClassFieldStatement
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldNorm.U002.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U024.Definitions
import Langlands.ClassFieldTheory.Local.NYLL.ZeroRamificationHostProof
import Langlands.NYLL.ValuedFieldTheory.Ramification.LocalField.Unramified.Proof
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.MathlibGlobalReciprocity
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.MathlibFrobeniusHilbertComparison
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ArithmeticNormalization
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteIdeleArtin
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.MathlibTopologyComparison
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Topology

/-! Audit diagnostic (Task 7345): one module importing the Library's interface-F
statement, part of the Library's NYLL local port, and the adapted NYLL fbd320cd
global closure. Checks that the imports coexist and that NYLL's idele-class
comparison lands in the Library's `IdeleClasses`. -/

open Langlands.Global in
/-- NYLL's comparison equivalence targets the Library's `IdeleClasses K`. -/
noncomputable example (K : Type) [Field K] [NumberField K] :
    _root_.IdeleClassGroup K ≃ₜ* IdeleClasses K :=
  IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K

#check @Langlands.Global.FiniteAbelianClassFieldStatement

open Langlands.Global in
/-- The bridge sends NYLL's one-place idele class to the Library's `finiteClassInclusion`. -/
example (K : Type) [Field K] [NumberField K] (v : FinitePlace K)
    (x : (FiniteCompletion K v)ˣ) :
    IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K
        (IdeleGroup.finitePlaceIdeleClass v x) = finiteClassInclusion K v x :=
  IdeleGroup.ideleClassGroupEquivMathlib_finitePlaceIdeleClass K v x
```

### `NyllCoexistFullDiag`: diagnostic `0390f87b-26e0-4e6a-a671-a54868109762`

Checked at Library commit `fcb85a7ef43356fec01e6ccf1605f08568c08cb0`. It imports the class-field statement, all 1749 modules of the Library's NYLL port (through its 620 maximal modules) and the six NYLL roots. Result: ok, no error, no warning; 0 information message(s).

Source (636 lines, SHA-256 `74c1f7d9c387548068bad82c82ea80f5dd7f80faf5822ff79a033c377d90f81c`):

```lean
import Langlands.Global.Arithmetic.ClassFieldStatement
import Langlands.ClassFieldTheory.Local.NYLL.InertiaFromGeometricProof
import Langlands.ClassFieldTheory.Local.NYLL.NormTransferReductionProof
import Langlands.ClassFieldTheory.Local.NYLL.NormTransferUniverseTransportProof
import Langlands.ClassFieldTheory.Local.NYLL.RamifiedGeometricNormalizationTransferProof
import Langlands.ClassFieldTheory.Local.NYLL.ReciprocityUniverseTransportProof
import Langlands.ClassFieldTheory.Local.NYLL.RestrictionUniverseTransportProof
import Langlands.ClassFieldTheory.Local.NYLL.SuppliedUniformityProof
import Langlands.ClassFieldTheory.Local.NYLL.SuppliedUnramifiedProof
import Langlands.ClassFieldTheory.Local.NYLL.SuppliedValuationSignProof
import Langlands.ClassFieldTheory.Local.NYLL.ZeroRamificationHostProof
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Extension.NumericStatements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Residue.U128.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.U122.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteExtension.DegreeStatements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteExtension.NumericStatements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.GaloisSubextension.U061.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Supplement.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Supplement.U064.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U020.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Unramified.U046.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Unramified.U063.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Unramified.U075.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.FieldImageIndex.U002.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.MaximalUnramified.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.NaturalityStatements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.ResidueDegreeStatements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.ExtensionInertiaClosed.U022.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosure.U013.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosure.U014.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosure.U027.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosure.U038.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.NormalizedDegreeContinuous.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusLift.FrobeniusElements.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusLift.U001.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusLift.U008.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Indices.U007.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Indices.U012.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Indices.U013.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.U010.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.U004.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormConjugation.Mono.U001.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.AbsoluteConjugate.U008.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.AbsoluteConjugate.U010.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.ConjugateFixedElement.U004.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.RelativeNorm.U013.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.OneValue.U006.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.Prime.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.RelativeNorm.U004.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.MemNsmulImageIffStatement
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.ValuationData.Normalized.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.ValuationData.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.ValuationLaws.Conjugate.U003.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ClassFieldAxiom.U003.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ClassFieldAxiom.U004.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteFieldUnitMaps.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteFieldUnitMaps.U007.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteFieldUnitMaps.U010.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteIntermediateCompositum.Compositum.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteIntermediateCompositum.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteIntermediateFieldCompositum.U003.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.MaximalUnramified.U019.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.MaximalUnramified.U020.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.MaximalUnramifiedComparison.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.U013.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.U014.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.U016.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.U017.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusClosureCommutation.U002.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusDescent.FixedFieldLe.U004.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusDescent.InertiaQuotientImage.U002.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusDescent.JointInjectivity.U005.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusDescent.JointInjectivity.U006.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusDescent.JointInjectivity.U007.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField.ResidueDegree.U015.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField.ResidueDegree.U018.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField.U003.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField.U005.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField.U006.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField.U007.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField.U008.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField.U009.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusFixedFieldTower.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusPowerFixedField.DegreeZeroCommutes.U001.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusPowerFixedField.DegreeZeroCommutes.U002.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusPowerFixedField.DegreeZeroCommutes.U003.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusSemigroup.U003.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.InfiniteUnitDescent.FiniteStageUnit.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.InfiniteUnitNormSubgroup.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.InfiniteUnitNormSubgroup.Universal.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainFiniteReciprocity.FrobeniusEquality.U010.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainMultiplicativity.CorrectionSum.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainMultiplicativity.FrobeniusActionRemainder.U004.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainMultiplicativity.FrobeniusExponentMul.U001.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainNaturality.FrobeniusTower.U006.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainNaturality.NormMap.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainTransfer.IntermediateEquiv.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainTransfer.NormDoubleCoset.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.ExtensionSubgroup.U022.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.ExtensionSubgroup.U023.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.Main.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.QuotientLift.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.PrimeChoice.ChosenPrime.U002.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.PrimeChoice.ChosenPrime.U003.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.PrimeChoice.ChosenPrime.U005.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.PrimeChoice.PrimeDifference.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.ReciprocityDefinition.AbsoluteFinite.U002.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.ReciprocityIndependence.CompositumWith.Finiteness.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.ReciprocityIndependence.CompositumWith.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.ReciprocityIndependence.GaloisRefinement.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.ReciprocityIndependence.NormalCoreField.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.ReciprocityIndependence.QuotientGenerator.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.ReciprocityIndependence.UnramifiedGeneratorStatements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.TransferOrbitClosure.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UnitCohomologyAxiom.FieldExtension.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UnitCohomologyAxiom.TateZeroNormStatement
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UnitCohomologyAxiom.UnramifiedCyclic.AbsoluteFinite.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UnitCohomologyAxiom.ValuationAction.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UniversalNormDescent.ConjugateStableAction.U006.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UniversalNormDescent.ConjugateStableAction.U007.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UniversalNormDescent.RepNorm.U009.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UniversalNormDescent.RepNorm.U010.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UniversalNormDescent.RepNorm.U011.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UniversalNormDescent.RepNorm.U012.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UnramifiedNormQuotient.PrimeClass.U014.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UnramifiedNormQuotient.ValuationHom.U008.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Core.Inclusion.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Core.NormSubgroup.U014.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Core.Restriction.SameBase.U008.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Core.Restriction.U006.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Core.Restriction.U009.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Core.Restriction.U013.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Core.TotallyRamifiedValuation.U029.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Core.TotallyRamifiedValuation.U030.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.CyclicNormQuotient.ClassFieldAxiomCard.U012.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.CyclicNormQuotient.Kernel.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.CyclicNormQuotient.NormClass.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.CyclicNormQuotient.RelativeNorm.U004.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FieldRepresentation.Norm.U005.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianClassification.Restriction.U017.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianClassification.UnconditionalNorm.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.ExtProof
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.M296015Proof
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.U012.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.U020.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.AbstractExtension.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.InductionStatement
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.U012.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.U018.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.U020.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.U022.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.U030.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.U031.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.Unramified.U021.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.IntermediateExtension.ExtensionSubgroupLe.U003.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.IntermediateExtension.U002.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.IntermediateExtension.U006.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.IntermediateExtension.U009.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.IntermediateExtension.U011.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.IntermediateExtension.U012.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.IntermediateExtension.U023.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.IntermediateExtension.U034.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Main.U018.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Main.U020.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.NormTopology.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Reduction.DiagramChase.U032.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Reduction.DiagramChase.U033.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Reduction.DiagramChase.U034.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Reduction.InertiaImage.U024.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Sylow.CoprimeNsmul.U005.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamified.ActionValuation.U003.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamified.PrimeNormUnit.U002.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamified.Primitive.U004.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamifiedCase.FixedSource.FixedCombination.U001.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamifiedCase.FixedSource.GaloisGenerator.U005.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamifiedCase.FrobeniusLift.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamifiedCase.RestrictionCosets.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamifiedCase.RestrictionCosets.U008.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamifiedCase.RestrictionCosets.U009.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ValuationContinuity.U003.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ValuationContinuity.U009.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ValuationContinuity.UnramifiedExtension.ExtensionSubgroupStatement
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.CohomologyBridge.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.CohomologyBridge.QuotientHom.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.CohomologyBridge.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.FieldUnitsHerbrand.FinitenessStatements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.FilteredLiftingSequence.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Hilbert90.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.IntegerUnitsHerbrand.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Main.IntegerUnitsHerbrandStatement
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Main.TateCardStatement
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Main.TateH0FiniteStatement
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasis.CoordinateMapStatement
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasis.GaloisActionLawStatements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasis.GaloisLinearEquiv
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasis.LatticeMaps.U003.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasis.LatticeMaps.U024.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasis.LatticeMaps.U027.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasis.MulPowBijectiveStatement
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasis.MulPowLinearMap
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasis.ResidueInverseIndexStatement
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasis.U018.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasis.UniformizerGaloisStatement
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisCohomology.HerbrandSubsingletonStatement
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisFiniteQuotient.FiniteBoundaryStatements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisFiniteQuotient.FiniteQuotientStatement
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisFiniteQuotient.U003.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisGaloisAction.QuotientMapEquivarianceStatement
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisGaloisAction.StableQuotient
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisGaloisAction.SubgroupCompatibilityStatements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisGaloisAction.U012.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisGaloisAction.U017.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisGaloisAction.U018.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisGaloisAction.U019.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisGradedLifting.OneStepLiftingStatements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisGradedLifting.SuccQuotActionOnRepresentativesStatement
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisInfiniteProduct.ActionLimitStatements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisInfiniteProduct.ContinuousEquivStatement
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisInfiniteProduct.CorrectionProductComparisonStatement
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisInfiniteProduct.U003.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisInfiniteProduct.U011.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisInfiniteProduct.U016.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisRecursiveLifting.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.PrincipalUnitGraded.SuccessiveQuotientComparisonStatement
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation.U004.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation.U006.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation.U007.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation.U010.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation.U011.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation.U013.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.ValuationHerbrand.QuotientDefinedStatements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.ValuationHerbrand.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.ValueGroupCohomology.HerbrandStatements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.ValueGroupCohomology.U001.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.ValueGroupCohomology.U003.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Conductor.AntitoneProof
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.LocalAbsoluteData.U006.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.NormSubgroupOrderEmbedding.CompositumFixedField.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.NormSubgroupOrderEmbedding.FixedFieldAbelian.U004.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.NormSubgroupOrderEmbedding.Transport.U008.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.NormSubgroupOrderEmbedding.U014.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.OrderReversal.U002.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.OrderReversal.U003.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.OrderReversal.U004.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.StandardSubgroupIntersection.U003.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup.U002.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup.U004.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup.U007.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup.U009.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup.U014.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup.U021.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup.U024.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldNorm.U002.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldUnits.Action.U007.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldUnits.Action.U008.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldUnits.Action.U009.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldUnits.Relative.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.AbstractUnramified.DegreeProof
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.AbstractUnramified.ResidueDegreeProof
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Finiteness.Relative.U018.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Finiteness.U003.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Finiteness.U004.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Initial.U008.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.RelativeGalois.U020.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteExtensionClassFieldAxiom.Cardinality.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteGaloisRealization.Normality.U016.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueFinrankTransfer.U003.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueValuationComparison.U001.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteSubgroupResidueDegree.U006.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteSubgroupResidueDegree.U007.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteSubgroupResidueDegree.U011.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientNormResidue.U001.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientNormResidue.U004.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientPrimeNormTransport.U003.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientPrimeNormTransport.U004.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientPrimeNormTransport.U005.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientPrimeNormTransport.U007.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientPrimeNormTransport.U009.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientPrimeNormTransport.U010.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientPrimeWitness.U001.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.EmbeddedExtensionQuotient.U002.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.EmbeddedExtensionQuotient.U004.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.EmbeddedExtensionQuotient.U007.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.FixedFieldNormQuotient.U001.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.IntrinsicBaseEquivalence.U007.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.EmbeddedFrobeniusTransport.U002.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.EmbeddedFrobeniusTransport.U004.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.NormRestriction.U001.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldLocalData.U007.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldLocalData.U011.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldNormResidueNaturality.U004.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldNormResidueNaturality.U005.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldRelativeNorm.U008.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GaloisExtensionQuotient.Kernel.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GeneralTowerNaturality.U006.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GeneralTowerNaturality.U013.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntermediateFieldNormResidueNaturality.U006.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData.Base.U007.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalClassFieldAxiom.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U013.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U014.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U019.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U021.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U023.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U024.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.NormResidue.U004.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.NormResidueNaturality.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueActionIndex.U002.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueActionIndex.U004.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueActionIndex.U005.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAlgebraicClosureDegree.U009.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAlgebraicClosureDegree.U013.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAlgebraicClosureDegree.U014.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueDatum.U004.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm.BaseUnits.RelativeNorm.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TateTransport.GroupEquiv.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TateTransport.Initial.U001.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TateTransport.RepresentationIso.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TopologicalReciprocity.U004.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TopologicalReciprocity.U006.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TopologicalReciprocity.U008.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TopologicalReciprocity.U009.U009.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TopologicalReciprocity.U013.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedNormComparison.U003.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedNormComparison.U004.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedNormComparison.U006.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedNormComparison.U008.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedNormComparison.U009.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.UnramifiedConductor.U003.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.StandardSubgroupIndex.CanonicalIndexStatement
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.StandardSubgroupIndex.CanonicalValuationStatement
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.StandardSubgroupIndex.U005.Proof
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.ChangedPrimitiveEvaluation.ParameterDepthStatement
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.ChangedUniformizer.UniformizerUnit
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.ChangedUniformizer.UnitFactorFieldUnitCoeProof
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Iterate.NatDegreeProof
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.MonicProof
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.NatDegreeProof
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Primitive.CoeffZeroProof
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Primitive.SuccFactorProof
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.FiniteParameterFiltration.Cardinality
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.FiniteParameterFiltration.Membership
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.FiniteParameters.ChosenRepresentativeProof
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.FiniteParameters.ClassEqualityProof
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.ParameterCongruence.IterateMapStatement
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.ParameterCongruence.PolynomialMapProof
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.ParameterCongruence.PrimitiveStatements
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveDisplacement.U001.Proofs
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveDisplacement.U016.Proofs
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveDisplacement.U022.Proofs
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveDisplacement.U026.Proofs
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveEisenstein.EisensteinIrreducibleStatements
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveEisenstein.PrimitiveResidueProof
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveRoot.DerivativeNonzeroProof
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveRoot.FieldPolynomialDegreeProof
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveRoot.FieldPolynomialMonicProof
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveTorsion.MappedIterateDefinitions
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveUniformizer.IntegralClosureMonogeneityProof
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveUniformizer.PolynomialIdealProofs
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField.CompleteDVFProof
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField.FieldPrincipalUnitsComparisonProof
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField.IntegerEquivCoeStatements
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField.ResidueCardinalityProof
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField.ValuationProof
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField.ValuationUnitsToFieldUnitsCoeStatement
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.DefectMonomialResponse.Statements
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.LinearModel.ConstantCoeff
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.LinearModel.HasSubst
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.LinearModel.OneLeOrderInVariable
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.LinearModel.OneLeOrderLinear
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.LinearModel.TwoLeOrderSub
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.LowDegreeDefect.LinearFormDefect
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.MonomialSubst.D019Proof
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.OrderEstimates.D005.Proofs
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.OrderEstimates.D006.Proofs
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.OrderEstimates.D007.Proofs
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.OrderEstimates.D008.Proofs
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.OrderEstimates.D009.Proofs
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.OrderEstimates.D010.Proofs
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.PowAddMonomial.D021Proof
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.PowAddMonomial.D023Proof
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.U001.Proof
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.U002.D002Proof
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.U002.D003Proof
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.U002.D004Proof
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.IntertwinesIffDefect
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.IntertwinesX
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.LinearTerm.U002.Proofs
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient.CorrectionSpecProof
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient.UniformizerMulProof
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner.DefectCancellationStatements
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner.DefectPreservationStatements
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner.DefectReplacementStatements
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner.DegreeIndexList.MembershipProof
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner.DegreeIndexList.NodupProof
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner.LinearForm.Proof
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner.LinearTermCoefficientProof
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner.LowerCoefficientStatements
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner.ReplaceDegreeStatements
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner.Replacement.ListAbsentProof
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner.Replacement.ListLowerProof
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner.Replacement.StepSelfProof
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner.U045.Statements
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Reduction.MapDefectEqZero
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Reduction.MapInVariable
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Series.ExtProof
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup.LinearTerms.Basis
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup.LinearTerms.CoeffEqLinearForm
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup.LinearTerms.CoeffSingle
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup.LinearTerms.HasLinearTermX
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup.LinearTerms.HasLinearTermZero
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup.LinearTerms.Subst
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup.LinearTerms.WeightedSum
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup.SubstitutionClosure.U010.Proofs
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup.SubstitutionClosure.U012.Statements
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup.SubstitutionClosure.U013.Proofs
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.StandardSeries.ToPowerSeries
import Langlands.NYLL.GaloisCohomology.Cyclic.GaloisCohomology.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.GaloisCohomology.Statements
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandFiniteness.U006.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandFiniteness.U010.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandFiniteness.U014.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.HerbrandQuotients.RightRegularStatements
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.HerbrandQuotients.Statements
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.RightRegularStatements
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.U004.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Cardinality.ExactIdentity.U021.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Cardinality.ModuleCat.Statements
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Cardinality.RangeEquiv.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Cardinality.Statements
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Core.U002.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Core.U003.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Core.U004.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Core.U005.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.TateComparison.Statements
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U001.U001.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U001.U003.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U001.U004.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U001.U006.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U015.U017.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U015.U018.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U015.U019.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U015.U022.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U015.U027.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U015.U028.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U015.U054.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U029.U029.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U029.U032.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U029.U033.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U029.U034.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U029.U036.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U029.U038.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U029.U039.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U029.U040.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U029.U041.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U042.U042.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U042.U046.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U042.U048.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U042.U050.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U042.U053.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U042.U057.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U060.U060.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U060.U061.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U060.U062.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U060.U065.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U060.U085.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U069.U076.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U078.Statements
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U091.U091.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U091.U093.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U091.U100.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U091.U101.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U109.U115.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U109.U119.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U121.U122.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientTower.Maps.U002.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientTower.Maps.U004.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientTower.Maps.U011.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientTower.Maps.U012.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientTower.Maps.U013.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientTower.U023.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.TateH0.NormImage.Statements
import Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerAbelianAssembly.U002.U002.Proofs
import Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerAbelianCyclicFactors.U001.Proofs
import Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerAbelianCyclicFactors.U011.Statements
import Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerDelta.U002.Proofs
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U003.Proofs
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U012.Proofs
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore.U020.Proofs
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.TopologicalGeneration.U002.Proofs
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.TopologicalGeneration.U006.Proofs
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.TopologicalGeneration.U009.Proofs
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.TopologicalGeneration.U010.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.ExistsUniformizerProof
import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.ResidueCharacteristicFactPrimeProof
import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Norm.Basic.InverseStatement
import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.PolynomialRootProximity.RootProximityProof
import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Core.GradedPieceComparison
import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Core.RangeCardinalityStatement
import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Core.SubquotientFiniteStatement
import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Core.SuccessorCardinalityStatement
import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Filtration.ZeroLevel
import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.ResidueQuotient.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationAddVal.AddValIrreducibleProof
import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationAddVal.AddValRestrictionProof
import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationIdeal.MaximalIdealPowerImageProof
import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationIdeal.MaximalIdealPowerMembershipProof
import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationInvariants.IndexNonzeroProof
import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationInvariants.IndexPositiveProof
import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Units.Cardinality.ProductStatement
import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Units.Comparison
import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Units.QuotientMembership
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U002.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U003.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.Units.U007.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.Units.U018.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF.IntegerRingPropertiesProof
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionTopology.U009.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing.U001.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.FinitenessStatements
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.U014.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.UniformizerPowMap.U018.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.UniformizerPowMap.U019.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.UniformizerPowMap.U029.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.UniformizerPowMap.U030.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Norm.U004.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Norm.U009.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Norm.U020.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Norm.U021.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormContinuity.U002.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormContinuity.U003.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U041.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitActions.U001.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitActions.U002.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitActions.U003.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitActions.U004.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.CorrectionStatements
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.CorrectionUnit.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.SuccessorStatements
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.TopologyStatements
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.U046.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.U048.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.U053.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.U063.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.U068.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.U086.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.U019.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.U020.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueExtension.U007.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueExtension.U026.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueUnits.Statements
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ShrinkLocallyCompactProof
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ShrinkNontrivialProof
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ShrinkValuationLtStatement
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UniformizerPrincipalQuotient.UnitFactorStatements
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnitTopology.U002.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnitTopology.U003.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnramifiedFrobenius.CyclicProof
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnramifiedFrobenius.ResidueActionProof
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.U029.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuedTopologyStatement
import Langlands.NYLL.ValuedFieldTheory.LocalField.NormUnits.U003.Statements
import Langlands.NYLL.ValuedFieldTheory.Ramification.Filtration.Definitions
import Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.FiniteLevelValuationRestriction.U005.Proofs
import Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.FiniteLevelValuationRestriction.U006.Proofs
import Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.CompositumRestriction.IntermediateFieldProof
import Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.CompositumRestriction.JointRestrictionProof
import Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.CompositumRestriction.SubgroupEqualityProof
import Langlands.NYLL.ValuedFieldTheory.Ramification.Herbrand.Quotient.FiltrationData
import Langlands.NYLL.ValuedFieldTheory.Ramification.Herbrand.Tower.Definitions
import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.FiniteGaloisLevelIndependence.Proofs
import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.GaloisStabilizer.Proofs
import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.HerbrandFunction.LowerFiltrationProof
import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RamificationNumber.AdjoinProof
import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RamificationNumberFormula.Definitions
import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.IsLocalRingProof
import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.ResidueActionStatements
import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.SMulCommClassProof
import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.UniqueExtensionIntegralClosure.IntegralOrbitPolynomial
import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.UniqueExtensionIntegralClosure.Statements
import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ValuationKrasner.Proof
import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ValuationRestriction.Proof
import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ValuationSubring.DecompositionFieldIsGaloisProof
import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ValuationSubring.InertiaGroupNormalProof
import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ValuationSubring.ResidueActionKerProof
import Langlands.NYLL.ValuedFieldTheory.Ramification.LocalField.Core.AntitoneProof
import Langlands.NYLL.ValuedFieldTheory.Ramification.LocalField.Core.RestrictionProof
import Langlands.NYLL.ValuedFieldTheory.Ramification.LocalField.Unramified.Proof
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.AddVal.MaximalIdealProof
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.AdicPower.Statements
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Basic.ResidueSurjectivityStatement
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Basic.Statements
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension.IntegralClosureMap.Definitions
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension.U002.Proofs
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension.U005.Proofs
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension.U008.Proofs
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension.U010.Proofs
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension.U011.Proofs
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension.U012.Proofs
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension.U013.Proofs
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension.U014.Proofs
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension.U017.Proofs
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension.U029.Proofs
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension.U057.Proofs
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.ResidueSurjectivityStatement
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.U002.Proofs
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.U013.Proofs
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.U014.Proofs
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.U017.Proofs
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.U023.Proofs
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.U032.Proofs
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Extensions.Definitions
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Henselian.U001.Proofs
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Henselian.U002.Proofs
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Henselian.U003.Proofs
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Henselian.U004.Proofs
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Henselian.U013.Proofs
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Henselian.U015.Proofs
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ValuationExtension.U007.Proofs
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ValuationTransport.Statements
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.MathlibGlobalReciprocity
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.MathlibFrobeniusHilbertComparison
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ArithmeticNormalization
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteIdeleArtin
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.MathlibTopologyComparison
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Topology

/-! Audit diagnostic (Task 7345): the Library interface-F statement, all 1749
modules of the Library NYLL port (through its 620 maximal modules) and the adapted
NYLL fbd320cd global closure, imported together. -/

open Langlands.Global in
noncomputable example (K : Type) [Field K] [NumberField K] :
    _root_.IdeleClassGroup K ≃ₜ* IdeleClasses K :=
  IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K
```

Earlier runs of the same two modules at older Library commits gave the same results (`55576d99`, `d575a023`, `ed44ef05`).
