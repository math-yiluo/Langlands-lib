/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionOrdinaryModels
import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsOrdinaryLocalDetection
import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionUnitRestriction
import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionUnitCriterion
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! Source: Stacks Tags 099M, 09BL and 09BM; blueprint: lem-fix-qcqs-completion-unit-tree.
This is a separately stated component of the locality argument. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralOnSlice
private theorem emptyModule_isZero
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (S : Scheme.{t}) [IsEmpty S] (M : Mod l E S none) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  ext U x
  let : IsEmpty U.unop.left := ⟨fun x ↦ (inferInstance : IsEmpty S).false (U.unop.hom x)⟩
  have h := ProEt.isTerminalSectionsOfIsEmpty
    ((SheafOfModules.toSheaf _).obj M) U.unop
  have : Subsingleton (M.val.obj U) := AddCommGrpCat.subsingleton_of_isZero
    (IsZero.of_iso (isZero_zero AddCommGrpCat)
      (h.uniqueUpToIso (isZero_zero AddCommGrpCat).isTerminal))
  exact Subsingleton.elim _ _

private theorem emptyDerived_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (S : Scheme.{t}) [IsEmpty S] {H K : D l E S none} (f : H ⟶ K) : IsIso f := by
  apply (DerivedCategory.isIso_iff (Mod l E S none) f).mpr
  intro n
  exact (emptyModule_isZero l E S _).isIso (emptyModule_isZero l E S _) _

attribute [local irreducible] ordinaryPull ordinaryDerivedPull ordinaryComplexCounit
  ordinaryCoefficientMap tower completion completionComparison completionUnit

set_option linter.unusedVariables false in
/-- Detection of the specified completion unit along a finite open--closed tree.

Source: Stacks Tags 09AH, 09BM, 04TQ and Bhatt--Scholze Remark 6.5.10
(blueprint: lem-fix-qcqs-completion-unit-tree).
Proof: fix the original unit morphism. Induct on the number of vertex indices
strictly greater than the given vertex. A nonempty leaf uses cover conservativity;
an empty leaf uses the zero category. At an internal vertex both children have
larger indices, and open--closed conservativity combines their conclusions. At the
root, restriction along its isomorphism with the base reflects invertibility.
For completeness, compare the actual unit of each covering-domain pullback with
the image of the original unit, and apply the canonical-unit criterion at the
root and the covering domains. The induction also includes height-zero trees
and empty open or closed children. -/
theorem qcqsCompletionUnitTree
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{t}) [CompactSpace T] [QuasiSeparatedSpace T]
    (_hl : IsUnit (l : Γ(T, ⊤))) :
    (∀ (d : ℕ) (V : Fin d → Scheme.{t}) (toT : ∀ v : Fin d, V v ⟶ T)
      (root : Fin d) (parent left right : Fin d → Fin d)
      (leftEdge : ∀ v : Fin d, V (left v) ⟶ V v)
      (rightEdge : ∀ v : Fin d, V (right v) ⟶ V v) (leaf : Fin d → Prop),
      (∃ e : V root ≅ T, e.hom = toT root) → parent root = root →
      (∀ v, v ≠ root → (parent v).val < v.val) →
      (∀ v, CompactSpace (V v)) → (∀ v, QuasiSeparatedSpace (V v)) →
      (∀ v, IsImmersion (toT v)) →
      (∀ v, v ≠ root → left (parent v) = v ∨ right (parent v) = v) →
      (∀ v, leaf v ↔ ∀ z, z ≠ root → parent z ≠ v) →
      (∀ v, ¬ leaf v →
        left v ≠ right v ∧ v.val < (left v).val ∧ v.val < (right v).val ∧
        parent (left v) = v ∧ parent (right v) = v ∧
        leftEdge v ≫ toT v = toT (left v) ∧ rightEdge v ≫ toT v = toT (right v) ∧
        IsOpenImmersion (leftEdge v) ∧ QuasiCompact (leftEdge v) ∧
        IsClosedImmersion (rightEdge v) ∧
        Set.range (leftEdge v).base ∪ Set.range (rightEdge v).base = Set.univ ∧
        Disjoint (Set.range (leftEdge v).base) (Set.range (rightEdge v).base)) →
      ∀ (I : ∀ v : Fin d, Type w) (W : ∀ v : Fin d, I v → (V v).ProEt),
      (∀ (v : Fin d) (a : I v), leaf v → Nonempty (V v) → CompactSpace (W v a).left) →
      (∀ (v : Fin d) (a : I v), leaf v → Nonempty (V v) →
        QuasiSeparatedSpace (W v a).left) →
      (∀ v, leaf v → Nonempty (V v) →
        Presieve.ofArrows (fun a : I v ↦ W v a)
          (fun a ↦ (MorphismProperty.Over.homMk (W v a).hom (Category.comp_id _) :
            W v a ⟶ ProEt.mk (𝟙 (V v)))) ∈
          ProEt.precoverage (V v) (ProEt.mk (𝟙 (V v)))) →
      ∀ H : D l E T none,
        (IsIso ((completionUnit l E T none).app H) ↔
          ∀ v, leaf v → Nonempty (V v) → ∀ a : I v,
            IsIso ((ordinaryDerivedPull l E ((W v a).hom ≫ toT v)).map
              ((completionUnit l E T none).app H))) ∧
        (IsComplete l E T none H ↔
          ∀ v, leaf v → Nonempty (V v) → ∀ a : I v,
            IsComplete l E (W v a).left none
              ((ordinaryDerivedPull l E ((W v a).hom ≫ toT v)).obj H)))  := by
  classical
  intro d V toT root parent left right leftEdge rightEdge leaf hroot _ _ hqc hqs hi
    _ _ hsplit I W hWqc hWqs hcover H
  let (v : Fin d) : CompactSpace (V v) := hqc v
  let (v : Fin d) : QuasiSeparatedSpace (V v) := hqs v
  let P := fun v : Fin d ↦ IsIso ((ordinaryDerivedPull l E (toT v)).map
    ((completionUnit l E T none).app H))
  have hdetection := qcqsOrdinaryLocalDetection.{t, u, w} l E T
    ((completionUnit l E T none).app H)
  have hdetect : IsIso ((completionUnit l E T none).app H) ↔
      ∀ v, leaf v → Nonempty (V v) → ∀ a : I v,
        IsIso ((ordinaryDerivedPull l E ((W v a).hom ≫ toT v)).map
          ((completionUnit l E T none).app H)) := by
    constructor
    · intro h v hv hn a
      let := h
      infer_instance
    · intro h
      have hp : ∀ v : Fin d, P v := by
        intro v
        have descend : ∀ n : ℕ, ∀ z : Fin d, d - z.val = n → P z := by
          intro n
          induction n using Nat.strong_induction_on with
          | h n ih =>
            intro z hz
            let := hi z
            by_cases hzleaf : leaf z
            · by_cases hn : Nonempty (V z)
              · let := hn
                exact (hdetection.2.2 (V z) (toT z) (I z) (W z)
                  (fun a ↦ hWqc z a hzleaf hn) (fun a ↦ hWqs z a hzleaf hn)
                  (hcover z hzleaf hn)).mpr (h z hzleaf hn)
              · have : IsEmpty (V z) := ⟨fun x ↦ hn ⟨x⟩⟩
                exact emptyDerived_isIso l E (V z) _
            · obtain ⟨_, hleft, hright, _, _, hel, her, hj, hjqc, hc, hunion, hdis⟩ :=
                hsplit z hzleaf
              let := hj
              let := hjqc
              let := hc
              have hleft_lt := (left z).isLt
              have hright_lt := (right z).isLt
              have hl : P (left z) := ih (d - (left z).val) (by omega) _ rfl
              have hr : P (right z) := ih (d - (right z).val) (by omega) _ rfl
              apply (hdetection.2.1 (V z) (V (left z)) (V (right z))
                (toT z) (leftEdge z) (rightEdge z) hunion hdis).mpr
              constructor
              · erw [hel]
                exact hl
              · erw [her]
                exact hr
        exact descend _ v rfl
      obtain ⟨e, he⟩ := hroot
      have : IsIso (toT root) := he ▸ inferInstanceAs (IsIso e.hom)
      exact (hdetection.1 (V root) (toT root)).mp (hp root)
  refine ⟨hdetect, ?_⟩
  rw [← canonicalCompletionUnitCriterion l E T H, hdetect]
  constructor
  · intro h v hv hn a
    let : CompactSpace ((𝟭 Scheme).obj (W v a).left) := hWqc v a hv hn
    let : QuasiSeparatedSpace ((𝟭 Scheme).obj (W v a).left) := hWqs v a hv hn
    let : CompactSpace ((Functor.fromPUnit (V v)).obj (W v a).right) := hqc v
    let : QuasiSeparatedSpace ((Functor.fromPUnit (V v)).obj (W v a).right) := hqs v
    let := hi v
    exact (canonicalCompletionUnitCriterion l E (W v a).left _).mp
      ((ordinaryCompositeCompletionUnit_isIso l E (W v a).hom (toT v) H).mp
        (h v hv hn a))
  · intro h v hv hn a
    let : CompactSpace ((𝟭 Scheme).obj (W v a).left) := hWqc v a hv hn
    let : QuasiSeparatedSpace ((𝟭 Scheme).obj (W v a).left) := hWqs v a hv hn
    let : CompactSpace ((Functor.fromPUnit (V v)).obj (W v a).right) := hqc v
    let : QuasiSeparatedSpace ((Functor.fromPUnit (V v)).obj (W v a).right) := hqs v
    let := hi v
    exact (ordinaryCompositeCompletionUnit_isIso l E (W v a).hom (toT v) H).mpr
      ((canonicalCompletionUnitCriterion l E (W v a).left _).mpr (h v hv hn a))

end WeilConjectures.IntegralOnSlice
