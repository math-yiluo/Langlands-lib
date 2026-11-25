/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorRawComposition

import WeilConjectures.PoincareDuality.Pod.Reindex.PodReindexRoosComposition
import Mathlib.Tactic.CategoryTheory.Slice

/-! # Pasting normalized Roos comparisons on arbitrary towers

Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 07A4 and 0941 (blueprint: lem-pod-reindex-roos-pasting).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
-- Preserve sharing of the dependent functor and representative aliases.
set_option cleanup.letToHave false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard integralCompletedTensor
  completedIntegralCoefficientSheafUnrestricted Scheme.residueField
  sfIntegralConstructible podReindexCalculus isoReductionCompletedMap
  integralOperationsTensorTowerFunctor
  integralOperationsRoos integralCompletedTensorComparison
attribute [local implicit_reducible] podGoodReindex integralOperationsTensorComplexFunctor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem roos_tensor_pasting
    {C D T : Type*} [Category C] [Category D] [Category T]
    (G : C ⥤ D) (R : T ⥤ D)
    {A B C' : C} {A' : D} {t₀ t₁ t₂ t₃ t₄ : T}
    (a : A' ⟶ G.obj A) (r : A ⟶ B) (s : B ⟶ C')
    (rG : G.obj B ⟶ R.obj t₁) (rW : G.obj C' ⟶ R.obj t₂)
    (rH : A' ⟶ R.obj t₀)
    (τ : t₀ ⟶ t₁) (tf : t₁ ⟶ t₂) (tg : t₂ ⟶ t₃)
    (tc : t₀ ⟶ t₄) (u : t₄ ⟶ t₃)
    (cf : A ⟶ C') (cg : G.obj C' ⟶ R.obj t₃) (cc : A' ⟶ R.obj t₄)
    (hcf : cf = r ≫ s) (hcg : cg = rW ≫ R.map tg) (hcc : cc = rH ≫ R.map tc)
    (hr : a ≫ G.map r ≫ rG = rH ≫ R.map τ)
    (hn : G.map s ≫ rW = rG ≫ R.map tf)
    (ht : τ ≫ tf ≫ tg = tc ≫ u) :
    a ≫ G.map cf ≫ cg = cc ≫ R.map u := by
  rw [hcf, hcg, hcc, G.map_comp]
  simp only [Category.assoc]
  slice_lhs 3 4 => exact hn
  simp only [Category.assoc]
  slice_lhs 1 3 => exact hr
  simp only [Category.assoc]
  slice_lhs 2 4 => rw [← R.map_comp, ← R.map_comp, ht, R.map_comp]

/-- Roos realization pastes a compatible square of arbitrary strict towers.
Source: blueprint Steps 1 and 5; Stacks 07A4 and 0941
(blueprint: lem-pod-reindex-roos-pasting).
Proof: use composition of the normalized Roos comparisons on C. RoosNaturality
moves the first tower map across the second comparison. The assumed tower
square and functoriality of Roos identify the remaining maps. Substitute the
three supplied equations for the named chain maps. Both cone coordinates are
retained by normalized Roos composition; no tensor or localization is used. -/
theorem podReindexRoosPasting
    (A : PodReindexFamily l E)
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (f : W ⟶ V) [IsIso h] [IsIso f]
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    [(isoReductionIntegralInverse l E f).Additive]
    [(isoReductionIntegralInverse l E h).Additive]
    [(isoReductionIntegralInverse l E (h ≫ f)).Additive]
    (hf : PodCompletionReindex.Laws l E f (A.completion f))
    (hh : PodCompletionReindex.Laws l E h (A.completion h))
    (hhf : PodCompletionReindex.Laws l E (h ≫ f) (A.completion (h ≫ f)))
    (C : ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E V) ℤ)
    (D : ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E W) ℤ)
    {K L : ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E Z) ℤ}
    (tf : (podReindexTower l E f).obj C ⟶ D)
    (tg : (podReindexTower l E h).obj D ⟶ K)
    (tc : (podReindexTower l E (h ≫ f)).obj C ⟶ L) (δ : L ⟶ K)
    :
    let α := NatIso.mapHomologicalComplex (A.composition h f) (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (isoReductionIntegralInverse l E f ⋙ isoReductionIntegralInverse l E h))
        (.up ℤ)).symm
    whiskerLeft C α.hom ≫ (podReindexTower l E h).map tf ≫ tg = tc ≫ δ →
      PodRoosCompositionEquation (isoReductionIntegralComplex l E h)
        integralOperationsRoosFunctor (α.hom.app (integralOperationsRoosFunctor.obj C))
        (((A.completion f).roos C).hom ≫ integralOperationsRoosFunctor.map tf)
        (((A.completion h).roos D).hom ≫ integralOperationsRoosFunctor.map tg)
        (((A.completion (h ≫ f)).roos C).hom ≫ integralOperationsRoosFunctor.map tc) δ := by
  intro α ht
  unfold PodRoosCompositionEquation PodCompositionEquation
  have hr := podReindexRoosComposition l E A h f hf hh hhf C
  have hn := hh.2.2.2.2.2.2.2.2.2.2.2.2.1 ((podReindexTower l E f).obj C) D tf
  exact roos_tensor_pasting (isoReductionIntegralComplex l E h)
    integralOperationsRoosFunctor
    (α.hom.app _) ((A.completion f).roos C).hom
    (integralOperationsRoosFunctor.map tf)
    ((A.completion h).roos ((podReindexTower l E f).obj C)).hom
    ((A.completion h).roos D).hom ((A.completion (h ≫ f)).roos C).hom
    (whiskerLeft C α.hom) ((podReindexTower l E h).map tf) tg tc δ
    _ _ _ rfl rfl rfl hr hn ht

end WeilConjectures
