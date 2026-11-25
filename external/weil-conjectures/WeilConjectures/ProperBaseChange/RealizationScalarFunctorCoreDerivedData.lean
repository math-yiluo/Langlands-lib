/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarExtension
public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientBasicSupplement
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]
variable (T : Scheme.{u}) [IsNoetherian T]
  [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]

/-- Derived unit and complex-counit data for the completed scalar map. -/
structure RealizationScalarFunctorCoreDerivedData
    [HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1}]
    [(ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [EssentiallySmall.{u + 1} T.ProEt]
    (φ : pbcAdicCompletion T (pbcIntegralDatum l E) ⟶
      rationalCoefficientSheaf l T E) where
  unit : ∀ P : CochainComplex (pbcModules.{u} T
      (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ,
    (pbcDerivedScalarAdjunction φ).unit.app (DerivedCategory.Q.obj P) ≫
      (pbcDerivedRestrict φ).map (pbcComplexCounit φ P) ≫
      (pbcRestrict φ).mapDerivedCategoryFactors.hom.app
        ((pbcExtend φ).mapHomologicalComplex (.up ℤ) |>.obj P) =
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (pbcScalarAdjunction φ).unit (.up ℤ)).app P)
  computes : ∀ P : CochainComplex (pbcModules.{u} T
      (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ,
    IsIso (pbcComplexCounit φ P)

/-- The derived scalar extension construction supplies the two core identities.

Source: Stacks Tags 06YY and 0DVC, via the exact termwise extension and its
universal derived adjunction. The proof is the derived scalar extension
construction specialized to the integral-to-rational coefficient map.
-/
theorem realization_scalar_functor_core_derived_data
    [HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1}]
    [(ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [EssentiallySmall.{u + 1} T.ProEt]
    (φ : pbcAdicCompletion T (pbcIntegralDatum l E) ⟶
      rationalCoefficientSheaf l T E) :
    Nonempty (RealizationScalarFunctorCoreDerivedData l E T φ) := by
  sorry

end WeilConjectures
