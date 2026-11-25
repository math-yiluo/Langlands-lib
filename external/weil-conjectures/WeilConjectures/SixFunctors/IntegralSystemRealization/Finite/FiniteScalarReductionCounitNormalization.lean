/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Finite.FiniteScalarOrdinaryReductionIso
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitFiniteMateComparison
import WeilConjectures.SixFunctors.PurCompactSupport.ScalarComplexAdjunctionNormalization
import WeilConjectures.CategoryTheory.Normalized.NormalizedAdjunctionComposition

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

/-- The canonical finite scalar presentation carries the canonical counit on K-flat
complexes to the scalar reduction computation map.
Source: Stacks Tags 07A6 and 06YY
(blueprint: lem-sf-finite-scalar-reduction-counit-normalization).
Proof: transpose through the pbc scalar adjunction. The left-adjoint uniqueness
map transfers the first transpose to the finite scalar adjunction. Its K-flat unit
normalization gives the localized ordinary finite scalar unit. ScalarComplexTranspose
computes the other transpose. The ordinary left-adjoint uniqueness unit equation
identifies it with the same unit. Cancel the exact restriction computation map and
use injectivity of the pbc scalar Hom equivalence. -/
theorem finiteScalarReductionCounitNormalization (W : Scheme.{u}) (n : ℕ)
    (P : (integralOperationsGoodComplex l E W).FullSubcategory) :
    let := sfExtensionAdditive l E W n
    (PurCompactSupport.finiteReductionIso l E W n).hom.app (DerivedCategory.Q.obj P.obj) ≫
        (coefficientFiniteReductionModel.{u, u} l E W P.obj P.property.1 n).hom =
      pbcComplexCounit
          (PurCompactSupport.projection l E (n + 1) (Nat.le_add_left 1 n) W) P.obj ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (finiteScalarOrdinaryReductionIso l E W n).hom
            (.up ℤ)).app P.obj) := by
  let hP := P.property.1
  let P := P.obj
  let := sfExtensionAdditive l E W n
  let π := PurCompactSupport.projection l E (n + 1) (Nat.le_add_left 1 n) W
  let a := pbcScalarAdjunction π
  let b := (scalarReductionExtension_adjunction.{u, u} l E W n).choose
  let ad := pbcDerivedScalarAdjunction π
  let bd := (derivedScalarExtensionRestrictionAdjunction.{u, u} l E W n).choose
  let e := NatTrans.mapHomologicalComplex (finiteScalarOrdinaryReductionIso l E W n).hom
    (.up ℤ)
  have he := finiteScalarOrdinaryReductionIso_unitComplex l E W n P
  apply (ad.homEquiv _ _).injective
  unfold PurCompactSupport.finiteReductionIso
  change ad.homEquiv _ _
      ((ad.leftAdjointUniq bd).hom.app _ ≫
        (coefficientFiniteReductionModel l E W P hP n).hom) = _
  rw [leftAdjointUniq_homEquiv_comp, PurCompactSupport.scalarComplexTranspose, he]
  change bd.unit.app (DerivedCategory.Q.obj P) ≫
    (scalarReductionDerivedRestriction.{u, u} l E W n).map
      (coefficientFiniteReductionModel l E W P hP n).hom =
    DerivedCategory.Q.map ((b.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
      (scalarReductionRestriction.{u, u} l E W n).mapDerivedCategoryFactors.inv.app
        (((scalarReductionExtension.{u, u} l E W n).mapHomologicalComplex (.up ℤ)).obj P)
  apply (cancel_mono ((scalarReductionRestriction l E W n).mapDerivedCategoryFactors.hom.app
    (((scalarReductionExtension.{u, u} l E W n).mapHomologicalComplex (.up ℤ)).obj P))).1
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  exact CompletionUnit.finiteModel_unit l E W P hP n

end WeilConjectures.IntegralSystemRealization
