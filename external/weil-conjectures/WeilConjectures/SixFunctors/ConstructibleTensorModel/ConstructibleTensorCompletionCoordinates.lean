/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleTensorModel.ConstructibleTensorCompletionChain

/-! # Coordinates of the canonical tensor-completion chain map

Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 6.5.5
(blueprint: lem-fix-constructible-tensor-completion-coordinates).
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

/-- Every first product coordinate is the prescribed quotient map on pure tensors.
Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 6.5.5
(blueprint: lem-fix-constructible-tensor-completion-coordinates). -/
theorem tensorChain_first
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (p q : ℤ) (n : ℕ)
    (U : W.ProEtᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    (((((tensorCompletionChain l E W).app (P, Q)) ≫ CochainComplex.mappingCocone.fst
      (towerTransitionEndomorphism
      (K := fun n ↦ (integralOperationsTensorLevel l E W n).obj (P, Q))
      (integralOperationsTowerStep ((integralOperationsTensorTowerFunctor l E W).obj (P, Q)))) ≫
      Pi.π (fun n ↦ (integralOperationsTensorLevel l E W n).obj (P, Q)) n).f
        (p + q)).val.app U) (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) P Q p q (p + q) rfl U x y) =
      integralOperationsTotalTensorSection l E W n P Q p q U
        (unrestrictedIntegralTensorSection l E W n (P.X p) U 1 x)
        (unrestrictedIntegralTensorSection l E W n (Q.X q) U 1 y) := by
  let K : ℕ → CochainComplex (integralTowerModules l E W) ℤ := fun n ↦
    ((IntegralOnSlice.tower l E W none).obj
      ((totalTensor l E W).obj (P, Q))).obj (op n)
  have : HasProduct K := inferInstance
  let a : ∀ n, (totalTensor l E W).obj (P, Q) ⟶ K n := fun n ↦
    ((IntegralOnSlice.augmentation l E W none).app
      ((totalTensor l E W).obj (P, Q))).app (op n)
  have hc := congrArg (fun f ↦ f ≫ Pi.π _ n)
    (IntegralAmbient.tensorOperationUnit_coordinates l E W P Q).1
  dsimp only [IntegralOnSlice.productAugmentation, integralOperationsRoos,
    integralOperationsRoosFunctor] at hc
  have hc' := hc.trans ((Category.assoc _ _ _).trans
    ((congrArg (fun k ↦ _ ≫ k) (Pi.map_π
      (fun n ↦ ((IntegralAmbient.tensorTowerIso l E W).hom.app (P, Q)).app (op n)) n)).trans
        (by
          with_unfolding_all
            exact Pi.lift_comp_π_assoc (f := K) a n
              (((IntegralAmbient.tensorTowerIso l E W).hom.app (P, Q)).app (op n)))))
  rw [tensorCompletionChain_app]
  unfold tensorCompletionUnitMap
  erw [hc']
  change (((((IntegralAmbient.tensorTowerIso l E W).hom.app (P, Q)).app
    (op n)).f (p + q)).val.app U)
      (((((IntegralOnSlice.augmentation l E W none).app
        ((totalTensor l E W).obj (P, Q))).app
          (op n)).f (p + q)).val.app U
            (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) P Q p q (p + q) rfl U x y)) = _
  unfold IntegralOnSlice.augmentation
  erw [(IntegralOnSlice.augmentation_existsUnique l E W none).exists.choose_spec]
  unfold IntegralAmbient.tensorTowerIso
  with_unfolding_all
    exact (IntegralAmbient.tensorTowerModel l E W).exists.choose_spec P Q n p q U 1 x y

/-- Every shifted mapping-fiber coordinate of the actual augmentation is zero.
Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 6.5.5
(blueprint: lem-fix-constructible-tensor-completion-coordinates). -/
theorem tensorChain_second
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (i j : ℤ)
    (h : i + -1 = j) :
    ((tensorCompletionChain l E W).app (P, Q)).f i ≫
      (CochainComplex.mappingCocone.snd
        (towerTransitionEndomorphism
      (K := fun n ↦ (integralOperationsTensorLevel l E W n).obj (P, Q))
      (integralOperationsTowerStep ((integralOperationsTensorTowerFunctor l E W).obj
        (P, Q))))).v i j h = 0 := by
  rw [tensorCompletionChain_app]
  unfold tensorCompletionUnitMap
  exact (IntegralAmbient.tensorOperationUnit_coordinates l E W P Q).2 i j h

end WeilConjectures.ConstructibleTensorModel
