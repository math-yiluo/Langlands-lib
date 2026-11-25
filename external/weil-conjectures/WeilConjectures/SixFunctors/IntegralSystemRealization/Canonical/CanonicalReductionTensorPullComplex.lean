/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
public import WeilConjectures.SixFunctors.Tensor.TensorReductionStrictComparison
import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.CanonicalReductionTensorPullComplexComponent

/-! # Ordinary reduction and the total tensor pullback square

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

/-- The ordinary reduction/pullback mate preserves the signed total tensor map.
Source: Stacks 07A4, 07A6 and 0941; proposition-six-operations-change-coefficients, first paragraph.
(blueprint: lem-sf-canonical-reduction-tensor-pull-complex).

Proof: the limit comparison is identity on the projected sections by
OrdinaryLimitModel.projections. Transpose this identity through the ordinary
reduction/limit and geometric module adjunctions. The resulting mate sends an
iterated quotient and inverse-image unit to the same iterated unit. Precompose
both displayed maps in degree k with each tensor summand p+q=k. On an ordinary
pure tensor their values are (b tensor x) tensor (1 tensor y), with the same
inverse-image and quotient units on both factors. The finite-component formula
for tensorReductionStrictMap and the unit formula for pullbackTensorSequenceCochain
identify the other two sides. Balancing, additivity and the sheafification
universal property extend this equality to the summand. Inverse image and scalar
extension preserve coproducts, so the total summand injections determine the
whole degree map. These maps preserve both input degrees and therefore the
signed differential. The same finite-component formulas commute with every
adjacent quotient transition, proving equality of strict system complexes.
This is an ordinary cochain identity: no derived evaluation or localization is
used, and neither K-flatness nor flatness is required. Zero complexes and identity
scheme maps are included in the same generator calculation. -/
theorem canonicalReductionTensorPullComplex
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (a : OrdinaryLimitModel l E) {U V : Scheme.{u}} (f : U ⟶ V)
    (P Q : CochainComplex (integralTowerModules l E V) ℤ) :
    let F := (integralOrdinaryPull l E f).mapHomologicalComplex (.up ℤ)
    let R (W : Scheme.{u}) :=
      (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
    let S := (pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)
    let T := (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology V)
      (completedIntegralCommRingSheafUnrestricted l E V)).obj (P, Q)
    a.reductionPullComplex l E f T ≫
        S.map (tensorReductionStrictMap l E V P Q) ≫
        (pullbackTensorSequenceCochain l E f).hom.app ((R V).obj P, (R V).obj Q) =
      (R U).map
          (proEtaleTensorPullbackTotalIso f ((PurCompactSupport.completed l E).ring V)
            ((PurCompactSupport.completed l E).ring U)
            ((PurCompactSupport.completed l E).pull f) P Q).inv ≫
        tensorReductionStrictMap l E U (F.obj P) (F.obj Q) ≫
        (coefficientTotalTensor.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology U))
          (coefficientSequenceCommRingSheaf l E U)).map
          (Prod.mkHom (a.reductionPullComplex l E f P) (a.reductionPullComplex l E f Q)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact canonicalReductionTensorPullComplex_component l E a f P Q n

end WeilConjectures.IntegralSystemRealization
