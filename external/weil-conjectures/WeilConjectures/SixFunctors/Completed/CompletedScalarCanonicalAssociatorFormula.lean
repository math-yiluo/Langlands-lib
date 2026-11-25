/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.CompletedLineTensor.CompletedLineTensorCoherence
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
import all WeilConjectures.SixFunctors.Completed.CompletedScalarTensorAssociatorCounit
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.SmoothPurity.PurStrictScalar.ConstantCompletedOrdinaryAssociativity

/-! # Ambient formula for the canonical completed scalar associator

Source: Bhatt--Scholze, Proposition 3.5.1; Stacks Tag 06YY.
(blueprint: lem-sf-completed-scalar-associator-ambient-formula).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
attribute [local irreducible] HasDerivedCategory.standard Padic
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  WeilConjectures.completedIntegralCommRingSheafUnrestricted
  WeilConjectures.completedCoefficientMap
  CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryFactors
  WeilConjectures.completedScalarComparison
  WeilConjectures.completedScalarChangeData
attribute [local irreducible] CategoryTheory.sheafCompose CategoryTheory.presheafToSheaf
  CategoryTheory.Functor.leftAdjoint SheafOfModules.changeOfRings
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
section
variable (l : ℕ) [Fact l.Prime]
  (E L M : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
  (i : E →ₐ[Padic l] L) (j : L →ₐ[Padic l] M) (T : Scheme.{u})
open CategoryTheory.Limits
private theorem ordinary_sheaf_eq :
    (CompletedLineTensor.associatorData l E T L i M j).sheaf =
      PurStrictScalar.ordinaryScalarAssociator _ _ _
        (PurCompactSupport.completedMap_composition l E L i M j T) := by
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply PurStrictScalar.successive_unit_ext
    (completedCoefficientMap l E L i T) (completedCoefficientMap l L M j T)
  intro U x
  have h := (CompletedLineTensor.associatorData_existsUnique l E T L i M j)
    |>.exists.choose_spec.1 N U 1 1 x
  have h' := PurStrictScalar.associator_unit
    (completedCoefficientMap l E L i T) (completedCoefficientMap l L M j T)
    (completedCoefficientMap l E M (j.comp i) T)
    (PurCompactSupport.completedMap_composition l E L i M j T) N U x
  simp only [map_one, mul_one] at h
  have hh := h
  change _ = pbcTensorSection (completedCoefficientMap l E M (j.comp i) T) N U 1 x at hh
  exact hh.trans h'.symm

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian in
private theorem ordinary_good_component
    (P : (integralOperationsGoodComplex l E T).FullSubcategory) :
    (PurCompactSupport.tensorComposition _ _ _
      (PurCompactSupport.completedMap_composition l E L i M j T)).hom.app
        (DerivedCategory.Q.obj P.obj) =
      (CompletedLineTensor.associatorData l E T L i M j).derived.hom.app
        (DerivedCategory.Q.obj P.obj) := by
  have hn := (CompletedLineTensor.associatorData_existsUnique l E T L i M j)
    |>.exists.choose_spec.2 P
  change (completedDerivedScalarExtension l L M j T).map
    (completedScalarCounit l E L i T P.obj) ≫
      completedScalarCounit l L M j T ((completedOrdinaryScalarComplex l E L i T).obj
        P.obj) ≫ DerivedCategory.Q.map
          ((CompletedLineTensor.scalarAssociatorComplex l E T L i M j
            (CompletedLineTensor.associatorData l E T L i M j).sheaf).hom.app P.obj) =
    (CompletedLineTensor.associatorData l E T L i M j).derived.hom.app
      (DerivedCategory.Q.obj P.obj) ≫ completedScalarCounit l E M (j.comp i) T P.obj at hn
  rw [ordinary_sheaf_eq l E L M i j T] at hn
  have hc := completed_associator_counit l E L M i j T P.obj
  have := scalar_counit_isIso l E M (j.comp i) T P.obj
  apply (cancel_mono (completedScalarCounit l E M (j.comp i) T P.obj)).mp
  exact hc.trans hn

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian in
private theorem ordinary_derived_eq :
    (PurCompactSupport.tensorComposition _ _ _
      (PurCompactSupport.completedMap_composition l E L i M j T)) =
      (CompletedLineTensor.associatorData l E T L i M j).derived := by
  apply Iso.ext
  let Q := integralOperationsGoodLocalization l E T
  let W := (HomologicalComplex.quasiIso (integralTowerModules l E T) (.up ℤ)).inverseImage
    (integralOperationsGoodComplex l E T).ι
  let : Q.IsLocalization W := integralOperationsGoodLocalization_isLocalization l E T
  apply Localization.natTrans_ext Q W
  intro P
  exact ordinary_good_component l E L M i j T P

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian in
/-- The canonical restricted integral associator is the specified comparison conjugate.
Source: Bhatt--Scholze, Proposition 3.5.1, and Stacks 06YY (lemma-derived-base-change).
(blueprint: lem-sf-completed-scalar-associator-ambient-formula).
Proof: first identify the ordinary sheaf associators on successive tensor units.
The tensor-associator counit formula and the associator-data normalization then
agree on every good complex. Their direct counit is invertible, so cancellation
and the good-complex localization identify the derived associators.
Finally canonical_restriction identifies the intrinsic associator with the
completed associator, whose definition is precisely the displayed conjugation. -/
theorem completedScalarCanonicalAssociatorFormula (K : sfIntegralConstructibleCategory l E T) :
    ((sfIntegralScalarComp l E L i T 0 (Fact.out : l.Prime).ne_zero M j).hom.app K).hom =
      (CompletedLineTensor.chi l L T M j _
        (CompletedLineTensor.extension_complete l E T L i K.obj
          (CompletedLineTensor.intrinsic_complete l E T K))).inv ≫
      (pbcDerivedExtend (completedCoefficientMap l L M j T)).map
        (CompletedLineTensor.chi l E T L i K.obj
          (CompletedLineTensor.intrinsic_complete l E T K)).inv ≫
      (PurCompactSupport.tensorComposition _ _ _
        (PurCompactSupport.completedMap_composition l E L i M j T)).hom.app K.obj ≫
      (CompletedLineTensor.chi l E T M (j.comp i) K.obj
        (CompletedLineTensor.intrinsic_complete l E T K)).hom := by
  rw [ordinary_derived_eq l E L M i j T]
  exact eq_of_heq ((CompletedLineTensor.canonical_restriction l E L i M j T 0
    (Fact.out : l.Prime).ne_zero).1 K)

end
end WeilConjectures
