/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ConstantGeometricStalkUnit.IntegralConstantPullbackChainUnit
public import WeilConjectures.SmoothPurity.ConstantGeometricStalkUnit.IntegralConstantRegularReductionModel
import all WeilConjectures.SmoothPurity.ConstantGeometricStalkUnit.IntegralConstantPullbackChainUnit
import all WeilConjectures.SmoothPurity.Supporting.ConstantWeilStructure
import all WeilConjectures.ZetaWeil.ConstantPullbackUnitQuasiIsomorphism.ConstantPullbackUnitQuasiIsomorphism
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
import all WeilConjectures.Algebra.Homology.DerivedCategory.ReductionDatum
import all WeilConjectures.SmoothPurity.ConstantGeometricStalkUnit.IntegralConstantRegularReductionModel
import WeilConjectures.SmoothPurity.ConstantScalarStrictUnit.ConstantScalarStrictUnit

/-! # The finite quotient of the normalized integral coefficient unit

Source: Stacks 099N(5) and the normalized strict Roos construction of the constant unit.
(blueprint: lem-pur-integral-constant-unit-reduction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
-- This proof module shares private model calculations through `import all`.
set_option linter.privateModule false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
attribute [local implicit_reducible] WeilConjectures.scalarReductionDerivedRestriction
  WeilConjectures.integralCoefficientSheaf WeilConjectures.integralCoefficientCommRingSheaf
  WeilConjectures.finiteConstantCoefficientObject
  WeilConjectures.constantWeilIntegralGood WeilConjectures.constantWeilIntegralObject
  WeilConjectures.completedIntegralCommRingSheafUnrestricted
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  WeilConjectures.integralOperationsGoodComplex
  WeilConjectures.integralOperationsPullbackOnGood
  WeilConjectures.integralOperationsGoodLocalization
  WeilConjectures.constantWeilIntegralComplex
namespace WeilConjectures.ConstantGeometricStalkUnit
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence
  unrestrictedIntegralReductionExistence HasDerivedCategory.standard limit
  finiteRegularIso finiteSingleRegularIso finiteRingUnit finiteChainUnit
attribute [local implicit_reducible] integralConstantReduction

/-- Reducing the normalized integral unit gives the finite multiplication map.

Source: Stacks 099N(5); normalized Roos-unit construction, finite quotient clause.
(blueprint: lem-pur-integral-constant-unit-reduction).

Proof: compute with the regular K-flat representative. The reduction comparison is
adjoint to the nth Roos projection. The strict unit's projection formula sends the
section one to the finite pullback generator. After the regular reduction isomorphism,
finite multiplication sends that generator to one. Adjunction and regular-module
extensionality identify the two maps before localization. The good-representative
comparison and the universal scalar-reduction counit give the displayed equation
on the canonical regular representative. This is a single-arrow quotient normalization;
it asserts neither composition of integral units nor a Frobenius square. -/
theorem integralUnit_reduction
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (n : ℕ) :
    (scalarReductionDerivedExtension l E X n).map (integralUnit l E f).hom ≫
        (integralConstantReduction l E D hl X n).hom =
      (integralPullbackReductionIso l E f (constantWeilIntegralObject l E D hl Y)
        (constantWeilIntegralGood l E Y) (Iso.refl _) n).hom ≫
        (proEtaleConstantRingDerivedPullback
          (Padic.coefficientExtensionRing l E (n + 1)) f).map
            (integralConstantReduction l E D hl Y n).hom ≫ (finiteRingUnit l E f n).hom := by
  let := integralChainUnit_isIso l E f
  let P := constantWeilIntegralGood l E Y
  let V := (unrestrictedIntegralFiniteComplex l E Y n).obj P.obj
  let F := proEtaleConstantRingPullback
    (Padic.coefficientExtensionRing l E (n + 1)) f
  let R := scalarReductionRestriction l E X n
  let b := integralPullbackFiniteComparison l E f
    (integralConstantCoefficientObject l E Y) P (Iso.refl _) n
  have hY : (coefficientFiniteReductionModel l E Y P.obj P.property.1 n).inv ≫
        (integralConstantReduction l E D hl Y n).hom =
      DerivedCategory.Q.map (WeilConjectures.finiteSingleRegularIso l E Y n).hom := by
    change _ ≫ constantCoefficientReductionMap l E Y n = _
    rw [← regular_reduction_model l E Y n]
    exact Iso.inv_hom_id_assoc _ _
  have hRhs :
      (integralPullbackReductionIso l E f (constantWeilIntegralObject l E D hl Y)
        P (Iso.refl _) n).hom ≫
        F.mapDerivedCategory.map (integralConstantReduction l E D hl Y n).hom ≫
        (finiteRingUnit l E f n).hom =
      b ≫ DerivedCategory.Q.map (finiteChainUnit l E f n) := by
    dsimp only [integralPullbackReductionIso, integralSystemPullbackReductionIso,
      Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_hom]
    simp only [Category.assoc, Iso.app_hom, Iso.app_inv, Iso.refl_hom]
    change b ≫ DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (integralFinitePullbackModel l E f n) (.up ℤ)).hom.app V) ≫
      F.mapDerivedCategoryFactors.inv.app V ≫
      F.mapDerivedCategory.map
        ((coefficientFiniteReductionModel l E Y P.obj P.property.1 n).inv ≫
          (scalarReductionDerivedExtension l E Y n).map (𝟙 _)) ≫
      F.mapDerivedCategory.map (integralConstantReduction l E D hl Y n).hom ≫
      (finiteRingUnit l E f n).hom = _
    erw [CategoryTheory.Functor.map_id, Category.comp_id,
      ← F.mapDerivedCategory.map_comp_assoc, hY]
    exact congrArg (fun t ↦ b ≫ t) (finite_chain_model l E f n)
  rw [hRhs]
  let adj := (derivedScalarExtensionRestrictionAdjunction l E X n).choose
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  change (integralUnit l E f).hom ≫
      (adj.homEquiv _ _) ((adj.homEquiv _ _).symm _) =
    (adj.homEquiv _ _) ((adj.homEquiv _ _).symm _) ≫
      R.mapDerivedCategory.map (DerivedCategory.Q.map (finiteChainUnit l E f n))
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  apply (cancel_mono (R.mapDerivedCategoryFactors.hom.app
    ((CochainComplex.singleFunctor _ 0).obj
      (SheafOfModules.unit (integralCoefficientSheaf l E X n))))).1
  simp only [Category.assoc]
  erw [← R.mapDerivedCategoryFactors_inv_naturality_assoc]
  erw [Iso.inv_hom_id_app]
  erw [Category.comp_id]
  erw [R.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app]
  change (integralUnit l E f).hom ≫
    DerivedCategory.Q.map
      ((CochainComplex.singleFunctor (scalarReductionSource l E X) 0).map
        (constantCoefficientProjection l E X n)) ≫ _ = _
  rw [← DerivedCategory.Q.map_comp]
  change (integralUnit l E f).hom ≫
    DerivedCategory.Q.map (ConstantScalarStrictUnit.projectionComplex l E X n) = _
  dsimp only [integralUnit, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc]
  change (integralDerivedPullbackComparison l E f).hom.app P ≫
      (asIso (DerivedCategory.Q.map (integralChainUnit l E f))).inv ≫ _ =
    (integralDerivedPullback l E f).map (𝟙 _) ≫
      (integralDerivedPullbackComparison l E f).hom.app P ≫
      integralOperationRoosProjection l E X (constantWeilPullbackTower l E f) n ≫
      DerivedCategory.Q.map
        ((R.mapHomologicalComplex (.up ℤ)).map (finiteChainUnit l E f n))
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  apply congrArg (fun t ↦ (integralDerivedPullbackComparison l E f).hom.app P ≫ t)
  apply (cancel_epi (asIso (DerivedCategory.Q.map (integralChainUnit l E f))).hom).1
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  simp only [asIso_hom]
  unfold integralOperationRoosProjection
  rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
  simpa only [Category.assoc] using!
    congrArg DerivedCategory.Q.map (chain_projection l E f n).symm

end WeilConjectures.ConstantGeometricStalkUnit
