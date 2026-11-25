/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement
import WeilConjectures.SixFunctors.SequenceModuleEvaluation.SequenceModulePullbackEvaluation

/-! # The ordinary scalar evaluation comparison

Source: Stacks 03D7, 06YY and 07A6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures
section Ordinary
attribute [local irreducible] SemilinearSections.systemRing
  SemilinearSections.ringPresheaf SemilinearSections.rings
set_option backward.defeqAttrib.useBackward true
universe c v r
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B F : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n, B (n + 1) ⟶ B n) (σ : ∀ n, F (n + 1) ⟶ F n)
  (α : ∀ n, B n ⟶ F n) (hα : ∀ n, α (n + 1) ≫ σ n = τ n ≫ α n)
  (A : SemilinearSections.ScalarSystems.{c, v, r} J B τ F σ α hα)

/-- Ordinary scalar extension commutes with sequence evaluation, respecting the
specified ordinary adjunction units.
Source: Stacks 03D7 and the sequence-site coextension construction
(blueprint: stage3-pur-ordinary-scalar-evaluation-unit).
Proof: take the inverse mate of the identity-on-sections restriction comparison.
The sequence-site coextension lemma makes this mate invertible. The mate unit
identity, followed by the image of its inverse, gives the displayed unit equation.
This works for every coefficient level, including n = 0. -/
theorem ordinaryScalarEvaluationUnit :
    ∃ ρ : ∀ n, A.scalar.model.E ⋙ SemilinearSections.evaluation J F σ n ≅
        SemilinearSections.evaluation J B τ n ⋙ (A.levels n).model.E,
      ∀ n M,
        (SemilinearSections.evaluation J B τ n).map
            (A.scalar.ordinaryAdjunction.unit.app M) ≫
          (SemilinearSections.restrictionEvaluation_existsUnique
            J B τ F σ α hα n).exists.choose.hom.app (A.scalar.model.E.obj M) ≫
          (SemilinearSections.res (α n)).map ((ρ n).hom.app M) =
        (A.levels n).ordinaryAdjunction.unit.app
          ((SemilinearSections.evaluation J B τ n).obj M) := by
  let δ n := (SemilinearSections.restrictionEvaluation_existsUnique
    J B τ F σ α hα n).exists.choose
  let m n := ((mateEquiv A.scalar.ordinaryAdjunction
    (A.levels n).ordinaryAdjunction).symm (δ n).hom)
  have hm n : IsIso (m n) := by
    let : ((𝟭 ℕ).prod (𝟭 C)).IsContinuous
        (coefficientSequenceTopology J) (coefficientSequenceTopology J) := by
      change (𝟭 (ℕ × C)).IsContinuous _ _
      infer_instance
    let a := (sheafCompose (coefficientSequenceTopology J)
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map
      (SemilinearSections.systemMap J B τ F σ α hα)
    let b := (sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map (α n)
    have hs : SheafOfModules.pushforward (F := (𝟭 ℕ).prod (𝟭 C)) a =
        SemilinearSections.res (SemilinearSections.systemMap J B τ F σ α hα) := by
      rfl
    have hl : SheafOfModules.pushforward (F := 𝟭 C) b =
        SemilinearSections.res (α n) := by
      rfl
    let as' : A.scalar.model.E ⊣ SheafOfModules.pushforward
        (F := (𝟭 ℕ).prod (𝟭 C)) a := by
      rw [hs]
      exact A.scalar.ordinaryAdjunction
    let al' : (A.levels n).model.E ⊣ SheafOfModules.pushforward (F := 𝟭 C) b := by
      rw [hl]
      exact (A.levels n).ordinaryAdjunction
    have hd := SequenceModuleEvaluation.sequenceModulePullbackEvaluation_isIso
      J J (𝟭 C)
      (SemilinearSections.ring _ (SemilinearSections.systemRing J B τ))
      (SemilinearSections.ring _ (SemilinearSections.systemRing J F σ)) n a
      (SemilinearSections.ring J (B n)) (SemilinearSections.ring J (F n))
      (SemilinearSections.evaluation_ring J B τ n)
      (SemilinearSections.evaluation_ring J F σ n) b
      A.scalar.model.E (A.levels n).model.E as' al'
      (by rw [hs, hl]; exact δ n)
    convert hd using 1 <;> rfl
  let ρ n := (asIso (m n)).symm
  refine ⟨ρ, ?_⟩
  intro n M
  have h := unit_mateEquiv_symm A.scalar.ordinaryAdjunction
    (A.levels n).ordinaryAdjunction (δ n).hom M
  dsimp only [ρ, Iso.symm_hom]
  rw [reassoc_of% h]
  change (A.levels n).ordinaryAdjunction.unit.app _ ≫
    (SemilinearSections.res (α n)).map ((asIso (m n)).hom.app M) ≫
      (SemilinearSections.res (α n)).map ((asIso (m n)).inv.app M) = _
  rw [← CategoryTheory.Functor.map_comp]
  rw [Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

end Ordinary
end WeilConjectures
