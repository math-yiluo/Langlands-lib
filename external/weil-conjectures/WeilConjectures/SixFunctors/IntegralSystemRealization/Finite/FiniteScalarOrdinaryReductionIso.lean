/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
public import WeilConjectures.SixFunctors.Sf.SfIntegralReductionTowerSupplement
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge

/-! # Counit normalization of the finite scalar presentation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
attribute [local irreducible] HasDerivedCategory.standard Functor.mapDerivedCategory
  Functor.rightDerivedFunctor CategoryTheory.constantSheaf
  completedIntegralCommRingSheafUnrestricted
  pbcDerivedScalarAdjunction pbcComplexCounit pbcExtensionCounit
  Functor.leftAdjoint SheafOfModules.monoidalCategory
  PurCompactSupport.finiteReductionIso scalarReductionExistence scalarReductionDerivedExistence
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  PurCompactSupport.completed scalarReductionDerivedRestriction
  coefficientFiniteDerivedExtension coefficientFiniteDerivedRestriction
  unrestrictedIntegralReductionFunctor
attribute [local instance] coefficientFiniteExtensionAdditive

/-- The ordinary finite scalar presentation, fixed by its restriction adjunction.
Source: Stacks Tag 06YY
(blueprint: lem-sf-finite-scalar-ordinary-reduction-iso). -/
def finiteScalarOrdinaryReductionIso (W : Scheme.{u}) (n : ℕ) :
    pbcExtend (PurCompactSupport.projection l E (n + 1) (Nat.le_add_left 1 n) W) ≅
      scalarReductionExtension.{u, u} l E W n :=
  (pbcScalarAdjunction
    (PurCompactSupport.projection l E (n + 1) (Nat.le_add_left 1 n) W)).leftAdjointUniq
      (scalarReductionExtension_adjunction.{u, u} l E W n).choose

/-- Fold the scalar adjunction alias without unfolding its chosen left adjoint.
Source: Stacks Tag 06YY
(blueprint: lem-sf-finite-scalar-ordinary-reduction-iso). -/
theorem finiteScalarOrdinaryReductionIso_eq (W : Scheme.{u}) (n : ℕ) :
    (pbcScalarAdjunction
      (PurCompactSupport.projection l E (n + 1) (Nat.le_add_left 1 n) W)).leftAdjointUniq
        (pullbackTensorFiniteAdjunction l E W n) =
      finiteScalarOrdinaryReductionIso l E W n := by
  unfold finiteScalarOrdinaryReductionIso pullbackTensorFiniteAdjunction
  rfl

/-- The ordinary scalar presentation carries the scalar adjunction unit to its
finite scalar unit degreewise. Source: Stacks Tag 06YY
(blueprint: lem-sf-finite-scalar-ordinary-reduction-iso). -/
theorem finiteScalarOrdinaryReductionIso_unitComplex (W : Scheme.{u}) (n : ℕ)
    (P : CochainComplex (integralTowerModules l E W) ℤ) :
    let := sfExtensionAdditive l E W n
    ((pbcScalarAdjunction
        (PurCompactSupport.projection l E (n + 1) (Nat.le_add_left 1 n) W)).mapHomologicalComplex
      (.up ℤ)).homEquiv _ _
        ((NatTrans.mapHomologicalComplex (finiteScalarOrdinaryReductionIso l E W n).hom
          (.up ℤ)).app P) =
      (((scalarReductionExtension_adjunction.{u, u} l E W n).choose).mapHomologicalComplex
        (.up ℤ)).unit.app P := by
  let := sfExtensionAdditive l E W n
  let a := pbcScalarAdjunction
    (PurCompactSupport.projection l E (n + 1) (Nat.le_add_left 1 n) W)
  let b := (scalarReductionExtension_adjunction.{u, u} l E W n).choose
  apply HomologicalComplex.hom_ext
  intro i
  change a.homEquiv _ _ ((a.leftAdjointUniq b).hom.app (P.X i)) = b.unit.app (P.X i)
  exact Adjunction.homEquiv_leftAdjointUniq_hom_app a b (P.X i)

end WeilConjectures.IntegralSystemRealization
