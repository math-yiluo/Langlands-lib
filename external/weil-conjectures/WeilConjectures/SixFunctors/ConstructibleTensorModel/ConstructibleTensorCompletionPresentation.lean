/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels

/-! # Canonical ordinary tensor-completion presentation

Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 6.5.5
(blueprint: lem-fix-constructible-tensor-completion-presentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleTensorModel
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})

set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  IntegralOnSlice.abSheafify IntegralOnSlice.abLocallyBijective
attribute [-instance] IntegralAmbient.ambientCxCategory IntegralAmbient.ambientDCategory
attribute [local instance 3100] integralTowerHasDerivedCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local irreducible] IntegralOnSlice.duality IntegralOnSlice.roosUnit
  IntegralAmbient.tensorTowerIso IntegralAmbient.tensorOperationUnit

/-- Fix the coefficient size of the small-site model.
Source: Stacks 098K
(blueprint: lem-fix-constructible-tensor-completion-presentation). -/
instance (priority := 3100) tensorSiteSmall :
    EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0, u, u + 1} _

/-- The locally bijective criterion at that same coefficient universe.
Source: Stacks 03DA
(blueprint: lem-fix-constructible-tensor-completion-presentation). -/
instance (priority := 3100) tensorAbLocallyBijective :
    (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} W

/-- Signed total tensor over the completed coefficient sheaf.
Source: Stacks 06YL
(blueprint: lem-fix-constructible-tensor-completion-presentation). -/
abbrev totalTensor := coefficientTotalTensor.{u, u + 1, u} (ProEt.topology W)
  (completedIntegralCommRingSheafUnrestricted l E W)

/-- The ordinary tensor from the recorded K-flat duality model.
Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 6.5.5
(blueprint: lem-fix-constructible-tensor-completion-presentation). -/
@[irreducible] def ordinaryTensor :
    DerivedCategory (integralTowerModules l E W) ×
      DerivedCategory (integralTowerModules l E W) ⥤
        DerivedCategory (integralTowerModules l E W) :=
  (IntegralOnSlice.duality.{u, u} l E W none).closed.tensor

/-- The existing canonical completion, with its native derived-category type.
Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 6.5.5
(blueprint: lem-fix-constructible-tensor-completion-presentation). -/
@[irreducible] def tensorCompletionFunctor :
    DerivedCategory (integralTowerModules l E W) ⥤
      DerivedCategory (integralTowerModules l E W) := by
  with_unfolding_all exact IntegralOnSlice.completion l E W none

/-- The existing canonical unit, with its native derived-category type.
Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 6.5.5
(blueprint: lem-fix-constructible-tensor-completion-presentation). -/
@[irreducible] def tensorCompletionUnit :
    𝟭 (DerivedCategory (integralTowerModules l E W)) ⟶
      tensorCompletionFunctor l E W := by
  unfold tensorCompletionFunctor
  with_unfolding_all exact IntegralOnSlice.completionUnit l E W none

omit [Fact l.Prime] in
/-- Residue-field invertibility of the prime implies stalkwise invertibility.
Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 6.5.5
(blueprint: lem-fix-constructible-tensor-completion-presentation). -/
theorem tensorPrime_stalkUnit
    [∀ w : W, Invertible (l : W.residueField w)] (w : W) :
    IsUnit (l : W.presheaf.stalk w) := by
  have : IsLocalHom (W.residue w).hom := by
    unfold Scheme.residue
    change IsLocalHom (IsLocalRing.residue (W.presheaf.stalk w))
    infer_instance
  apply isUnit_of_map_unit (W.residue w).hom
  simpa only [map_natCast] using isUnit_of_invertible (l : W.residueField w)

/-- Restrict the recorded K-flat comparison to flat-term K-flat good complexes.
Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 6.5.5
(blueprint: lem-fix-constructible-tensor-completion-presentation). -/
@[irreducible] def tensorRepresentativeIso :
    ((integralOperationsGoodComplex l E W).ι.prod
      (integralOperationsGoodComplex l E W).ι) ⋙ totalTensor l E W ⋙
        DerivedCategory.Q ≅
      ((integralOperationsGoodLocalization l E W).prod
        (integralOperationsGoodLocalization l E W)) ⋙ ordinaryTensor l E W := by
  let K := (IntegralOnSlice.duality.{u, u} l E W none).models
  let G := integralOperationsGoodComplex l E W
  let H := ObjectProperty.lift (CochainComplex.IsKFlatIndependentCoefficients
    (J := AlgebraicGeometry.Scheme.ProEt.topology W)
    (R := completedIntegralCommRingSheafUnrestricted l E W) :
      ObjectProperty (CochainComplex (integralTowerModules l E W) ℤ)) G.ι
        (fun P ↦ P.property.1)
  unfold ordinaryTensor
  exact Functor.isoWhiskerLeft (H.prod H) K.comparison

/-- The existing normalized augmentation, with its native representative target.
Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 6.5.5
(blueprint: lem-fix-constructible-tensor-completion-presentation). -/
@[irreducible] def tensorCompletionUnitMap
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) :
    (totalTensor l E W).obj (P, Q) ⟶
      (integralOperationsTensorComplexFunctor l E W).obj (P, Q) := by
  with_unfolding_all exact IntegralAmbient.tensorOperationUnit l E W P Q

private theorem existsConjRight {A : Sort*} {P Q : A → Prop}
    (h : ∃ a, P a ∧ Q a) : ∃ a, Q a := by
  obtain ⟨a, _, ha⟩ := h
  exact ⟨a, ha⟩

/-- Completion of the recorded ordinary tensor identifies with the specified completed
tensor, compatibly with the canonical normalized augmentation.
Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 6.5.5
(blueprint: lem-fix-constructible-tensor-completion-presentation). -/
theorem tensorCompletionModel
    [∀ w : W, Invertible (l : W.residueField w)] :
    ∃ β : ordinaryTensor l E W ⋙ tensorCompletionFunctor l E W ≅
        integralCompletedTensor l E W,
      ∀ P Q : (integralOperationsGoodComplex l E W).FullSubcategory,
        (tensorCompletionUnit l E W).app
            ((ordinaryTensor l E W).obj
              (((integralOperationsGoodLocalization l E W).prod
                (integralOperationsGoodLocalization l E W)).obj (P, Q))) ≫
          β.hom.app (((integralOperationsGoodLocalization l E W).prod
            (integralOperationsGoodLocalization l E W)).obj (P, Q)) ≫
          (integralCompletedTensorComparison l E W).hom.app (P, Q) =
        (tensorRepresentativeIso l E W).inv.app (P, Q) ≫
          DerivedCategory.Q.map (tensorCompletionUnitMap l E W P.obj Q.obj) := by
  have hl := tensorPrime_stalkUnit l W
  obtain ⟨_, _, _, _, _, _, _, ht⟩ :=
    IntegralAmbient.integralAmbientOperationModels l E (𝟙 W) hl hl
  have ht' := existsConjRight (ht W (.inl rfl))
  dsimp only [IntegralAmbient.modelOrdinaryTensor, IntegralAmbient.modelCompletion,
    IntegralAmbient.modelCompletionUnit, IntegralAmbient.modelCompletedTensor,
    IntegralAmbient.modelGoodLocalization, IntegralAmbient.modelTensorComparison,
    IntegralAmbient.tensorRepresentative, IntegralAmbient.modelTensorUnitMap,
    IntegralAmbient.modelTensorModelComparison, IntegralAmbient.modelQ,
    IntegralAmbient.modelRoosUnit, IntegralAmbient.modelTensorTowerIso,
    IntegralAmbient.modelRoos, IntegralAmbient.modelTotalTensor,
    IntegralAmbient.modelRecordedTensorComplex, IntegralAmbient.modelRoosComplex,
    IntegralAmbient.modelTensorTowerMap, IntegralAmbient.modelCompletionComparison,
    IntegralAmbient.modelTensorGoodLift, IntegralAmbient.modelTensorOnGood,
    IntegralAmbient.modelCompletionOnGood, IntegralAmbient.modelQuotientTower,
    IntegralAmbient.modelRecordedTensorTower] at ht'
  rw [IntegralAmbient.ambientPackage_eq] at ht'
  dsimp only [IntegralAmbient.rawAmbientPackage] at ht'
  obtain ⟨β, hb⟩ := ht'
  let β' : ordinaryTensor l E W ⋙ tensorCompletionFunctor l E W ≅
      integralCompletedTensor l E W := by
    unfold ordinaryTensor tensorCompletionFunctor
    with_unfolding_all exact β
  refine ⟨β', ?_⟩
  intro P Q
  unfold β' tensorCompletionUnit tensorCompletionFunctor tensorRepresentativeIso
    tensorCompletionUnitMap
  with_unfolding_all exact hb P Q

end WeilConjectures.ConstructibleTensorModel
