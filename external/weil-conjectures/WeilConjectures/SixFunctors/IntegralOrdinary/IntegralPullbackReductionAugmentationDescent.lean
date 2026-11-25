/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOrdinary.IntegralOrdinaryPullbackComparison
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # Descent of the reduction/pullback augmentation equation

This is the localization step after the good-representative calculation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOfSpec false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralOrdinary
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- A normalized adjunct equation on the good localization descends to every
object of the derived category.
Source: Stacks 07A6 and 0941; the localization argument in
`fix-prop-projection-formula.proof.md`.
(blueprint: lem-sf-pullback-reduction-augmentation-descent).

Proof: the good-complex localization presents the derived category. Naturality
of the pullback comparison, the Roos realization, and the candidate natural
isomorphism transports the equation along localization morphisms. The
localization universal property and its faithfulness identify the two natural
transformations on all derived objects from their equal components on good
representatives.
-/
theorem pullbackReductionAugmentation_of_good {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : PurCompactSupport.pull (PurCompactSupport.completed l E) f ⋙
        (pullbackTensorCalculus l E X).reduction ≅
      (pullbackTensorCalculus l E Y).reduction ⋙ pullbackTensorSequenceDerived l E f)
    (ha : ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
      (pullComparison l E f).app (DerivedCategory.Q.obj P.obj) ≫
          (pullbackTensorIntegralPullbackModel l E f).hom.app (DerivedCategory.Q.obj P.obj) =
        (pullbackTensorCalculus l E X).adjunction.unit.app
            ((PurCompactSupport.pull (PurCompactSupport.completed l E) f).obj
              (DerivedCategory.Q.obj P.obj)) ≫
          (coefficientSequenceLimit l E X).map
            (a.hom.app (DerivedCategory.Q.obj P.obj))) :
    ∀ K : DerivedCategory (integralTowerModules l E Y),
      (pullComparison l E f).app K ≫
          (pullbackTensorIntegralPullbackModel l E f).hom.app K =
        (pullbackTensorCalculus l E X).adjunction.unit.app
            ((PurCompactSupport.pull (PurCompactSupport.completed l E) f).obj K) ≫
          (coefficientSequenceLimit l E X).map (a.hom.app K) := by
  let L := integralOperationsGoodLocalization l E Y
  let W := (HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ)).inverseImage
    (integralOperationsGoodComplex l E Y).ι
  have : L.IsLocalization W := integralOperationsGoodLocalization_isLocalization l E Y
  let b : PurCompactSupport.pull (PurCompactSupport.completed l E) f ⟶
      pullbackTensorReferencePullback l E f :=
    pullComparison l E f ≫ (pullbackTensorIntegralPullbackModel l E f).hom
  let c : PurCompactSupport.pull (PurCompactSupport.completed l E) f ⟶
      pullbackTensorReferencePullback l E f :=
    Functor.whiskerLeft (PurCompactSupport.pull (PurCompactSupport.completed l E) f)
        (pullbackTensorCalculus l E X).adjunction.unit ≫
      Functor.whiskerRight a.hom (coefficientSequenceLimit l E X)
  have h : b = c := Localization.natTrans_ext L W ha
  intro K
  exact congrArg (fun t ↦ t.app K) h

end WeilConjectures.IntegralOrdinary
