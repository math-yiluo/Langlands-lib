/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleTensorModel.ConstructibleTensorCompletionPresentation
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SixFunctors.Supporting.DerivedCompleteUnrestricted
import WeilConjectures.SixFunctors.ConstructibleTensorModel.ConstructibleTensorCompletionConstructible
import WeilConjectures.SixFunctors.ConstructibleTensorModel.ConstructibleTensorCompletionComparison
import WeilConjectures.SixFunctors.ConstructibleTensorModel.ConstructibleTensorCompletionCoordinates

/-! # Constructible tensor completion in the native total-tensor presentation

Source: Bhatt--Scholze, Lemma 6.5.5, pp. 49--50
(blueprint: lem-fix-constructible-tensor-completion-assembly).
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

/-- The specified 1-s map of the strict finite tensor tower.
Source: Bhatt--Scholze, Definition 3.4.10
(blueprint: lem-fix-constructible-tensor-completion-assembly). -/
abbrev completionBoundary (P Q : CochainComplex (integralTowerModules l E W) ℤ) :=
  towerTransitionEndomorphism
    (K := fun n ↦ (integralOperationsTensorLevel l E W n).obj (P, Q))
    (integralOperationsTowerStep ((integralOperationsTensorTowerFunctor l E W).obj (P, Q)))

/-- Assemble the actual ordinary tensor, canonical normalized chain map and completed
comparison in the native coefficient-total-tensor presentation. The ordinary tensor
is complete, and its specified comparison is invertible, on constructible pairs.

Source: Bhatt--Scholze, Lemma 6.5.5, pp. 49--50; Definition 3.4.10
(blueprint: lem-fix-constructible-tensor-completion-assembly).

Proof: use the recorded representative model and canonical tower augmentation, with
both coordinate equations. The normalized ambient comparison identifies completion
of the ordinary tensor with completed tensor. Simultaneous projective charts give
local completeness by projectiveTensorChartComplete; finite open--closed locality
then gives global completeness and invertibility of the canonical unit. Compose this
unit with the recorded isomorphism. Its normalization follows by cancelling the
representative isomorphism. -/
theorem constructibleTensorCompletionNative [CompactSpace W] [QuasiSeparatedSpace W]
    [∀ w : W, Invertible (l : W.residueField w)] :
    ∃ (T : DerivedCategory (integralTowerModules l E W) ×
        DerivedCategory (integralTowerModules l E W) ⥤
          DerivedCategory (integralTowerModules l E W))
      (e : ((integralOperationsGoodComplex l E W).ι.prod
          (integralOperationsGoodComplex l E W).ι) ⋙ totalTensor l E W ⋙
          DerivedCategory.Q ≅
        ((integralOperationsGoodLocalization l E W).prod
          (integralOperationsGoodLocalization l E W)) ⋙ T)
      (chi : totalTensor l E W ⟶ integralOperationsTensorComplexFunctor l E W),
      (∀ (P Q : CochainComplex (integralTowerModules l E W) ℤ) (p q : ℤ) (n : ℕ)
        (U : W.ProEtᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        (((chi.app (P, Q) ≫ CochainComplex.mappingCocone.fst
          (completionBoundary l E W P Q) ≫
          Pi.π (fun n ↦ (integralOperationsTensorLevel l E W n).obj (P, Q)) n).f
            (p + q)).val.app U)
          (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology W)
            (completedIntegralCommRingSheafUnrestricted l E W) P Q p q (p + q) rfl U x y) =
        integralOperationsTotalTensorSection l E W n P Q p q U
          (unrestrictedIntegralTensorSection l E W n (P.X p) U 1 x)
          (unrestrictedIntegralTensorSection l E W n (Q.X q) U 1 y)) ∧
      (∀ (P Q : CochainComplex (integralTowerModules l E W) ℤ) (i j : ℤ)
        (h : i + -1 = j),
        (chi.app (P, Q)).f i ≫ (CochainComplex.mappingCocone.snd
          (completionBoundary l E W P Q)).v i j h = 0) ∧
      ∃ tau : T ⟶ integralCompletedTensor l E W,
        (∀ (P Q : (integralOperationsGoodComplex l E W).FullSubcategory),
          e.hom.app (P, Q) ≫ tau.app (DerivedCategory.Q.obj P.obj,
              DerivedCategory.Q.obj Q.obj) ≫
            (integralCompletedTensorComparison l E W).hom.app (P, Q) =
          DerivedCategory.Q.map (chi.app (P.obj, Q.obj))) ∧
        ∀ M N : DerivedCategory (integralTowerModules l E W),
          sfIntegralConstructible l E W M → sfIntegralConstructible l E W N →
          IsDerivedCompleteUnrestricted l E W (T.obj (M, N)) ∧ IsIso (tau.app (M, N)) := by
  obtain ⟨τ, hτ, hτiso⟩ := tensorCompletionComparison l E W
  refine ⟨ordinaryTensor l E W, tensorRepresentativeIso l E W,
    tensorCompletionChain l E W, tensorChain_first l E W, tensorChain_second l E W,
    τ, hτ, ?_⟩
  intro M N hM hN
  obtain ⟨hc, hu⟩ := tensorComplete_onConstructible l E W M N hM hN
  exact ⟨hc, hτiso M N hu⟩

end WeilConjectures.ConstructibleTensorModel
