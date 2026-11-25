/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
public import WeilConjectures.SixFunctors.Tensor.TensorReductionStrictComparison
import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.CanonicalReductionTensorPullComplexComponentBridge

/-! # Degreewise ordinary reduction and total tensor pullback

Source: Stacks 07A4, 07A6 and 0941; proposition-six-operations-change-coefficients, first paragraph.
-/

@[expose] public section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization

attribute [local irreducible] pullbackTensorCalculus
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
  HasDerivedCategory.standard SheafOfModules.monoidalCategory

/-- The missing ordinary tensor identity, after taking one cochain degree.
Source: Stacks 07A4, 07A6 and 0941; proposition-six-operations-change-coefficients, first paragraph.
(blueprint: lem-sf-canonical-reduction-tensor-pull-complex-component).

Proof: expand the three strict-system maps in degree `n` and use the finite
component formula for `tensorReductionStrictMap`, the unit formula for
`pullbackTensorSequenceCochain`, and the pure-tensor formula for the ordinary
limit mate. Balancing and additivity extend the pure-tensor equality to each
summand; compatibility with quotient transitions is inherited from the same
finite component formula. -/
theorem canonicalReductionTensorPullComplex_component
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (a : OrdinaryLimitModel l E) {U V : Scheme.{u}} (f : U ⟶ V)
    (P Q : CochainComplex (integralTowerModules l E V) ℤ) (n : ℤ) :
    let F := (integralOrdinaryPull l E f).mapHomologicalComplex (.up ℤ)
    let R (W : Scheme.{u}) :=
      (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
    let S := (pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)
    let T := (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology V)
      (completedIntegralCommRingSheafUnrestricted l E V)).obj (P, Q)
    (a.reductionPullComplex l E f T ≫
        S.map (tensorReductionStrictMap l E V P Q) ≫
        (pullbackTensorSequenceCochain l E f).hom.app ((R V).obj P, (R V).obj Q)).f n =
      ((R U).map
          (proEtaleTensorPullbackTotalIso f ((PurCompactSupport.completed l E).ring V)
            ((PurCompactSupport.completed l E).ring U)
            ((PurCompactSupport.completed l E).pull f) P Q).inv ≫
        tensorReductionStrictMap l E U (F.obj P) (F.obj Q) ≫
        (coefficientTotalTensor.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology U))
          (coefficientSequenceCommRingSheaf l E U)).map
          (Prod.mkHom (a.reductionPullComplex l E f P)
            (a.reductionPullComplex l E f Q))).f n := by
  dsimp only
  apply canonicalReductionTensorPullComplex_component_bridge l E a f P Q n
  · intro m
    exact tensorReductionStrictMap_component l E V P Q m
  · intro m
    exact tensorReductionStrictMap_component l E U
      (((integralOrdinaryPull l E f).mapHomologicalComplex (.up ℤ)).obj P)
      (((integralOrdinaryPull l E f).mapHomologicalComplex (.up ℤ)).obj Q) m

end WeilConjectures.IntegralSystemRealization
