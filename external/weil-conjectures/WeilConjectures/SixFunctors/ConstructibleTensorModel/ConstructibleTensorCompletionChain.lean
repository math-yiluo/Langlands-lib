/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleTensorModel.ConstructibleTensorCompletionPresentation
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices

/-! # The canonical tensor-completion chain map

Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 6.5.5
(blueprint: lem-fix-constructible-tensor-completion-chain).
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

/-- Compose a natural augmentation with a natural comparison of its target towers.
Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 6.5.5
(blueprint: lem-fix-constructible-tensor-completion-chain). -/
def completionChainOfTower
    {C B S : Type*} [Category* C] [Category* B] [Category* S]
    (F : B ⥤ C) (U : C ⥤ S) (V : B ⥤ S) (R : S ⥤ C)
    (η : 𝟭 C ⟶ U ⋙ R) (b : F ⋙ U ≅ V) : F ⟶ V ⋙ R where
  app X := η.app (F.obj X) ≫ R.map (b.hom.app X)
  naturality {X Y} f := by
    have hη := η.naturality (F.map f)
    have hb := b.hom.naturality f
    dsimp only [Functor.id_map, Functor.comp_map] at hη hb
    change F.map f ≫ η.app (F.obj Y) ≫ R.map (b.hom.app Y) =
      (η.app (F.obj X) ≫ R.map (b.hom.app X)) ≫ R.map (V.map f)
    rw [← Category.assoc, hη, Category.assoc, ← R.map_comp, hb,
      R.map_comp, ← Category.assoc]

/-- Naturality of the existing Roos unit, in the native cochain category.
Source: Bhatt--Scholze, Definition 3.4.10
(blueprint: lem-fix-constructible-tensor-completion-chain). -/
theorem tensorRoosUnit_natural
    {P Q : CochainComplex (integralTowerModules l E W) ℤ} (f : P ⟶ Q) :
    f ≫ IntegralOnSlice.roosUnit l E W none Q =
      IntegralOnSlice.roosUnit l E W none P ≫
        integralOperationsRoosFunctor.map ((IntegralOnSlice.tower l E W none).map f) := by
  with_unfolding_all
    exact WeilConjectures.IntegralOnSlice.sliceRoosUnit_natural l E W none f

/-- The actual Roos augmentation followed by the normalized tensor-tower comparison.
Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 6.5.5
(blueprint: lem-fix-constructible-tensor-completion-chain). -/
@[irreducible] def tensorCompletionChain : totalTensor l E W ⟶
    integralOperationsTensorComplexFunctor l E W := by
  let F := totalTensor l E W
  let U : CochainComplex (integralTowerModules l E W) ℤ ⥤
      (ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E W) ℤ) :=
    IntegralOnSlice.tower l E W none
  let R : (ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E W) ℤ) ⥤
      CochainComplex (integralTowerModules l E W) ℤ := integralOperationsRoosFunctor
  let η : 𝟭 (CochainComplex (integralTowerModules l E W) ℤ) ⟶ U ⋙ R :=
    { app := IntegralOnSlice.roosUnit l E W none
      naturality := fun _ _ f ↦ tensorRoosUnit_natural l E W f }
  exact completionChainOfTower F U (integralOperationsTensorTowerFunctor l E W) R η
    (IntegralAmbient.tensorTowerIso l E W)

/-- The component is the actual normalized tensor operation unit.
Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 6.5.5
(blueprint: lem-fix-constructible-tensor-completion-chain). -/
theorem tensorCompletionChain_app
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) :
    (tensorCompletionChain l E W).app (P, Q) = tensorCompletionUnitMap l E W P Q := by
  unfold tensorCompletionChain completionChainOfTower tensorCompletionUnitMap
    IntegralAmbient.tensorOperationUnit
  rfl

end WeilConjectures.ConstructibleTensorModel
