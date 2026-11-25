/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleTensorModel.ConstructibleTensorCompletionChain

/-! # Normalized ordinary-to-completed tensor comparison

Source: Bhatt--Scholze, Lemma 6.5.5, pp. 49--50
(blueprint: lem-fix-constructible-tensor-completion-comparison).
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

/-- Descend the canonical chain augmentation to ordinary derived tensor. The comparison
is invertible whenever the canonical completion unit is invertible.
Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 6.5.5
(blueprint: lem-fix-constructible-tensor-completion-comparison).

Proof: compose the canonical completion unit with the existing normalized isomorphism
from completion of ordinary tensor to completed tensor. Its representative equation
is the recorded normalization, after cancelling the representative isomorphism.
Invertibility follows by composition of the unit and that isomorphism. -/
theorem tensorCompletionComparison
    [∀ w : W, Invertible (l : W.residueField w)] :
    ∃ τ : ordinaryTensor l E W ⟶ integralCompletedTensor l E W,
      (∀ P Q : (integralOperationsGoodComplex l E W).FullSubcategory,
        (tensorRepresentativeIso l E W).hom.app (P, Q) ≫
          τ.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
          (integralCompletedTensorComparison l E W).hom.app (P, Q) =
        DerivedCategory.Q.map ((tensorCompletionChain l E W).app (P.obj, Q.obj))) ∧
      ∀ M N : DerivedCategory (integralTowerModules l E W),
        IsIso ((tensorCompletionUnit l E W).app ((ordinaryTensor l E W).obj (M, N))) →
          IsIso (τ.app (M, N)) := by
  obtain ⟨β, hβ⟩ := ConstructibleTensorModel.tensorCompletionModel l E W
  let τ : ordinaryTensor l E W ⟶ integralCompletedTensor l E W :=
    Functor.whiskerLeft (ordinaryTensor l E W)
      (tensorCompletionUnit l E W) ≫ β.hom
  refine ⟨τ, ?_, ?_⟩
  · intro P Q
    have ha := congrArg (fun k ↦ (tensorRepresentativeIso l E W).hom.app (P, Q) ≫ k)
      (hβ P Q)
    change (tensorRepresentativeIso l E W).hom.app (P, Q) ≫
      ((tensorCompletionUnit l E W).app _ ≫ β.hom.app _) ≫
        (integralCompletedTensorComparison l E W).hom.app (P, Q) = _
    have hr : (tensorRepresentativeIso l E W).hom.app (P, Q) ≫
        (tensorRepresentativeIso l E W).inv.app (P, Q) ≫
          DerivedCategory.Q.map (tensorCompletionUnitMap l E W P.obj Q.obj) =
        DerivedCategory.Q.map (tensorCompletionUnitMap l E W P.obj Q.obj) := by
      rw [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    simpa only [Category.assoc, integralOperationsGoodLocalization, Functor.prod_obj,
      Functor.comp_obj, ObjectProperty.ι_obj, tensorCompletionChain_app] using ha.trans hr
  · intro M N hu
    change IsIso ((tensorCompletionUnit l E W).app _ ≫ β.hom.app _)
    exact IsIso.comp_isIso' hu (by infer_instance)

end WeilConjectures.ConstructibleTensorModel
