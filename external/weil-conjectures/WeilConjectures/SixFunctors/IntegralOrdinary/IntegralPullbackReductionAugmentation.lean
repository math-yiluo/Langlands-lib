/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOrdinary.IntegralOrdinaryPullbackComparison
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
import WeilConjectures.SixFunctors.IntegralOrdinary.IntegralPullbackReductionAugmentationGood
import WeilConjectures.SixFunctors.IntegralOrdinary.IntegralPullbackReductionAugmentationDescent

/-! # The coherent reduction mate of ordinary pullback

Source: Stacks 03D2, 07A6 and 0941. No tensor comparison occurs here.
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

/-- Ordinary inverse image commutes with coherent derived reduction. Its adjunct is
exactly the recorded forward pullback augmentation in the normalized limit model.

Source: Stacks 03D2, 07A6, 08TC and 0941.
(blueprint: lem-sf-pullback-reduction-augmentation).

Proof: on modules, the two composite scalar-extension/inverse-image left adjoints
have the same right adjoint. Its equality follows from directRing_eq and the
projection equations for the completed coefficient map. Uniqueness of left
adjoints gives their unit-preserving comparison. Derive on flat-term K-flat
representatives, using the unit-normalized reduction model and ordinary pullIso.
The quotient units have the same finite projections and the same transitions.
Their maps into the strict Roos complex have identical product components and
zero shifted component. Product and mapping-cocone extensionality identify the
whole chain maps. The reduction model and the prescribed limit/Roos comparison
therefore give the displayed adjunct equation, including the pullback-model
transport. Good-complex localization descends it to all derived inputs. The
reduction/limit Hom bijection determines every component of a from this equation,
so the natural isomorphism is unique. No tensor, constructibility, properness,
Noetherianness, or dimension hypothesis is used. -/
theorem pullbackReductionAugmentation_exists {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ a : PurCompactSupport.pull (PurCompactSupport.completed l E) f ⋙
        (pullbackTensorCalculus l E X).reduction ≅
      (pullbackTensorCalculus l E Y).reduction ⋙ pullbackTensorSequenceDerived l E f,
      ∀ K : DerivedCategory (integralTowerModules l E Y),
        (pullComparison l E f).app K ≫
            (pullbackTensorIntegralPullbackModel l E f).hom.app K =
          (pullbackTensorCalculus l E X).adjunction.unit.app
              ((PurCompactSupport.pull (PurCompactSupport.completed l E) f).obj K) ≫
            (coefficientSequenceLimit l E X).map (a.hom.app K) := by
  obtain ⟨a, ha⟩ := pullbackReductionAugmentation_good l E f
  exact ⟨a, pullbackReductionAugmentation_of_good l E f a ha⟩

/-- An adjunction determines the coherent inverse-image comparison from its adjunct.
Source: Stacks 07A6; the reduction/limit adjunction
(blueprint: lem-sf-pullback-reduction-augmentation). -/
theorem pullbackReductionAugmentation_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! a : PurCompactSupport.pull (PurCompactSupport.completed l E) f ⋙
        (pullbackTensorCalculus l E X).reduction ≅
      (pullbackTensorCalculus l E Y).reduction ⋙ pullbackTensorSequenceDerived l E f,
      ∀ K : DerivedCategory (integralTowerModules l E Y),
        (pullComparison l E f).app K ≫
            (pullbackTensorIntegralPullbackModel l E f).hom.app K =
          (pullbackTensorCalculus l E X).adjunction.unit.app
              ((PurCompactSupport.pull (PurCompactSupport.completed l E) f).obj K) ≫
            (coefficientSequenceLimit l E X).map (a.hom.app K) := by
  obtain ⟨a, ha⟩ := pullbackReductionAugmentation_exists l E f
  refine ⟨a, ha, ?_⟩
  intro b hb
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply ((pullbackTensorCalculus l E X).adjunction.homEquiv _ _).injective
  simpa only [Adjunction.homEquiv_unit] using (hb K).symm.trans (ha K)

/-- The unique unit-preserving coherent reduction/pullback comparison.
Source: Stacks 03D2 and 0941 (blueprint: lem-sf-pullback-reduction-augmentation). -/
def pullbackReductionComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (pullbackReductionAugmentation_existsUnique l E f).exists.choose

end WeilConjectures.IntegralOrdinary
