/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.ZetaWeil.ConstantGeometricStalkUnit.CoefficientPullbackUnitCoordinates
import WeilConjectures.TraceFormula.Integral.IntegralPullbackComposition
import all WeilConjectures.SmoothPurity.Supporting.ConstantWeilStructure
import all WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import WeilConjectures.SmoothPurity.ConstantScalarStrictUnit.ConstantScalarStrictUnit
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor

/-! # The finite quotient of the normalized integral coefficient unit

Source: Stacks 099N(5) and the normalized strict Roos construction of the constant unit.
(blueprint: lem-pur-integral-constant-regular-reduction-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
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

/-- The canonical regular-module reduction, transposed from the coefficient projection.
Source: Bhatt--Scholze, Sections 3.5 and 6.5; constant coefficient constructibility.
(blueprint: lem-pur-integral-constant-regular-reduction-model). -/
def integralConstantReduction (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (X : Scheme.{u}) (n : ℕ) :
    (scalarReductionDerivedExtension l E X n).obj (integralConstantCoefficientObject l E X) ≅
      finiteConstantCoefficientObject l E X n :=
  letI := ((integralConstantCoefficient_constructible l E X D hl).2.2.2 n).1
  asIso (constantCoefficientReductionMap l E X n)

attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence
  unrestrictedIntegralReductionExistence HasDerivedCategory.standard limit
  finiteRegularIso finiteSingleRegularIso
  integralConstantReduction

private theorem regular_reduction_unit (W : Scheme.{u}) (n : ℕ) :
    unrestrictedTowerUnit l E W (constantWeilIntegralComplex l E W) n ≫
        ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).map
          (WeilConjectures.finiteSingleRegularIso l E W n).hom =
      ConstantScalarStrictUnit.projectionComplex l E W n := by
  let T : W.ProEt := ProEt.mk (𝟙 W)
  apply WeilConjectures.regular_hom_ext l E W T
    (MorphismProperty.Over.mkIdTerminal _ W)
  change ((WeilConjectures.finiteSingleRegularIso l E W n).hom.f 0).val.app (op T)
    (((unrestrictedTowerUnit l E W (constantWeilIntegralComplex l E W) n).f 0).val.app
      (op T) (constantWeilUnitSection l E W T)) = _
  rw [unrestrictedTowerUnit_condition]
  have ht : unrestrictedTowerTensorSection l E W n
      ((constantWeilIntegralComplex l E W).X 0) (op T) 1
        (constantWeilUnitSection l E W T) = constantWeilReducedUnitSection l E W n T := by
    unfold constantWeilReducedUnitSection constantWeilUnitSection
    rw [WeilConjectures.reduction_map_tensor]
    rfl
  rw [ht, WeilConjectures.finiteSingleRegularIso_one]
  change _ = ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
    (SheafOfModules.unit (integralCoefficientSheaf l E W n))).inv.val.app (op T))
      ((ConstantScalarStrictUnit.projectionModule l E W n).val.app (op T)
        (((HomologicalComplex.singleObjXSelf (.up ℤ) 0
          (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E W))).inv ≫
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0
            (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E W))).hom
              ).val.app (op T)
          (1 : (completedIntegralCoefficientSheafUnrestricted l E W).obj.obj (op T))))
  simp only [Iso.inv_hom_id, SheafOfModules.id_val, PresheafOfModules.id_app,
    ModuleCat.id_apply]
  congr 1
  change 1 = (completedIntegralCommRingProjectionUnrestricted l E W n).hom.app (op T) 1 * 1
  simp only [map_one, one_mul]

/-- The quotient model is the canonical reduction map.
Source: Stacks 099N(5), regular K-flat computation.
(blueprint: lem-pur-integral-constant-regular-reduction-model). -/
private theorem regular_reduction_model (W : Scheme.{u}) (n : ℕ) :
    (coefficientFiniteReductionModel l E W (constantWeilIntegralComplex l E W)
      (constantWeilIntegralComplex_good l E W).1 n).hom ≫
        DerivedCategory.Q.map (WeilConjectures.finiteSingleRegularIso l E W n).hom =
      constantCoefficientReductionMap l E W n := by
  let P := constantWeilIntegralComplex l E W
  let v := WeilConjectures.finiteSingleRegularIso l E W n
  let c := coefficientFiniteReductionModel l E W P
    (constantWeilIntegralComplex_good l E W).1 n
  have hc : sfReductionRepresentativeComparison l E W n P =
      (scalarReductionDerivedRestriction l E W n).map c.hom ≫
        (scalarReductionRestriction l E W n).mapDerivedCategoryFactors.hom.app
          ((unrestrictedIntegralFiniteComplex l E W n).obj P) := by
    change (scalarReductionDerivedRestriction l E W n).map
      ((scalarReductionCounit l E W n).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫ _ = _
    erw [Functor.mapDerivedCategoryFactorsh_hom_app]
    simp! [c, coefficientFiniteReductionModel, coefficientLocalizedCounitModel,
      DerivedCategory.quotientCompQhIso,
      HomologicalComplexUpToQuasiIso.quotientCompQhIso, Functor.mapHomotopyCategoryFactors,
      Category.assoc]
    change (scalarReductionDerivedRestriction l E W n).map
      ((scalarReductionCounit l E W n).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
        (scalarReductionRestriction l E W n).mapDerivedCategory.map (𝟙 _) ≫
        (scalarReductionRestriction l E W n).mapDerivedCategoryFactors.hom.app
          ((unrestrictedIntegralFiniteComplex l E W n).obj P) ≫ 𝟙 _ =
      (scalarReductionDerivedRestriction l E W n).map
        ((coefficientFiniteDerivedExtension l E W n).map (𝟙 _)) ≫
        (scalarReductionDerivedRestriction l E W n).map
          ((scalarReductionCounit l E W n).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
        (scalarReductionDerivedRestriction l E W n).map (𝟙 _) ≫
        (scalarReductionRestriction l E W n).mapDerivedCategoryFactors.hom.app
          ((unrestrictedIntegralFiniteComplex l E W n).obj P)
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp, Category.comp_id]
    erw [Category.id_comp]
  let adj := (derivedScalarExtensionRestrictionAdjunction l E W n).choose
  symm
  unfold constantCoefficientReductionMap
  apply (adj.homEquiv (integralConstantCoefficientObject l E W)
    (finiteConstantCoefficientObject l E W n)).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  apply (cancel_mono ((scalarReductionRestriction l E W n).mapDerivedCategoryFactors.hom.app
    (ConstantScalarStrictUnit.finiteRegularComplex l E W n))).1
  have hn := (scalarReductionRestriction l E W n).mapDerivedCategoryFactors_hom_naturality v.hom
  have hu := WeilConjectures.representative_unit l E W n P
    (constantWeilIntegralComplex_good l E W).1
  have hp :
      (DerivedCategory.singleFunctor (scalarReductionSource l E W) 0).map
          (constantCoefficientProjection l E W n) ≫
        ((scalarReductionRestriction l E W n).mapDerivedCategorySingleFunctor 0).inv.app
          (SheafOfModules.unit (integralCoefficientSheaf l E W n)) ≫
        (scalarReductionRestriction l E W n).mapDerivedCategoryFactors.hom.app
          (ConstantScalarStrictUnit.finiteRegularComplex l E W n) =
      DerivedCategory.Q.map (ConstantScalarStrictUnit.projectionComplex l E W n) := by
    erw [Functor.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app]
    change DerivedCategory.Q.map
      ((CochainComplex.singleFunctor (scalarReductionSource l E W) 0).map
        (constantCoefficientProjection l E W n)) ≫ _ = _
    rw [← DerivedCategory.Q.map_comp]
    rfl
  simp only [Category.assoc]
  calc
    _ = DerivedCategory.Q.map (ConstantScalarStrictUnit.projectionComplex l E W n) := hp
    _ = DerivedCategory.Q.map (unrestrictedTowerUnit l E W P n) ≫
        DerivedCategory.Q.map
          (((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).map
            v.hom) := by
      rw [← DerivedCategory.Q.map_comp]
      exact congrArg DerivedCategory.Q.map (regular_reduction_unit l E W n).symm
    _ = _ := by
      rw [← hu, hc]
      simp only [Functor.map_comp, Category.assoc]
      exact congrArg (fun a ↦ adj.unit.app _ ≫
        (scalarReductionDerivedRestriction l E W n).map c.hom ≫ a) hn.symm

end WeilConjectures.ConstantGeometricStalkUnit
