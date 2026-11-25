/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarPullbackRoosCoordinates
import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarPullbackCompletionRoos
import WeilConjectures.TraceFormula.Coherent.CoherentPrimitiveReductionPresentation
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.SmoothPurity.IntegralCoherence.IntegralGoodQuotientPresentation

/-! # Fixed cochain coordinates for the scalar/pullback calculation

Source: Stacks 06YY, 07A4 and 0941. The coordinates are constructed from the
ordinary scalar/pullback chain map and a coherent quotient presentation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.ScalarExtensionTower

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] HasDerivedCategory.standard
  integralDerivedPullback integralOrdinaryScalar integralComparisonSequenceScalarModel
  integralComparisonSequenceScalarPullback coefficientSequenceLimit
  scalarCompletionIso

-- STATEMENT-DISPUTED: the former version allowed arbitrary q. Composing q with
-- negation negates the left side while fixing the right side. The missing hq is
-- supplied by every current caller and fixes the nested tensor-unit generators.
/-- Right Roos normalization with the specified quotient formula.
Source: Stacks 06YY, 07A4 and 0941; normalization of the scalar realization
and pullback model, before the explicit nested quotient identification.
(blueprint: stage3-pur-scalar-pullback-right-roos-normalized).

The proof compares the normalized scalar model with the pulled normalized model
on a coherent presentation, using the whole-system counit equation. The quotient
formula fixes the strict map used at the end of the normalization step.
-/
theorem scalarPullbackRightRoos_normalized (W : Bool → Scheme.{u})
    (ME : CompletedOperations.Models.{u, u} l E W)
    (ρ : IntegralComparisonRoosModel.{u, u} l L (W true))
    (SX : IntegralComparisonScalarModel.{u, u} l E L ι (W true) (ME.calculus true) ρ)
    (f : W true ⟶ W false)
    (_hX : IsUnit (l : Γ(W true, ⊤))) (_hY : IsUnit (l : Γ(W false, ⊤)))
    (P : (integralOperationsGoodComplex.{u, u} l E (W false)).FullSubcategory)
    (K : sfIntegralConstructibleCategory l E (W false))
    (eP : DerivedCategory.Q.obj P.obj ≅ K.obj)
    (C : CochainComplex (coefficientSequenceModules.{u, u} l E (W false)) ℤ)
    (eC : (ME.calculus false).reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation.{u, u} l E (W false) n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex.{u, u} l E (W false) n).obj P.obj)
    (hp : CoefficientReductionPresentation.{u, u} l E (W false)
      (ME.calculus false).toCoefficientDerivedSystemReduction P.obj P.property.1 C eC κ)
    (hc : IsIntegralComparisonPresentationCoherent.{u, u} l E (W false)
      (ME.calculus false) P.obj C eC κ)
    (q :
    (((coefficientSequenceRestriction.{u, u} l L (W true)).mapHomologicalComplex (.up ℤ)).obj
      ((((integralComparisonSequencePullback.{u, u} l L f).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel.{u, u} l E L ι (W false)).E.mapHomologicalComplex
          (.up ℤ)).obj C)))).asFunctor ≅
      (integralOperationsPullbackTowerFunctor.{u, u} l L f).obj
        (((integralOrdinaryScalar l E L ι (W false)).mapHomologicalComplex (.up ℤ)).obj P.obj))
    (hq : ScalarPullbackQuotientFormula l E L ι f P C κ q)
    (hF : IsSfDerivedComplete l E (W true)
      ((integralDerivedPullback.{u, u} l E f).obj K.obj)) :
    (SX.realization.hom.app ((integralDerivedPullback.{u, u} l E f).obj K.obj) ≫
      (coefficientSequenceLimit.{u, u} l L (W true)).map
        ((integralComparisonDerivedSequenceScalar.{u, u} l E L ι (W true)).map
          (pullbackReduction l E W ME f K.obj))) ≫
      scalarPullbackRoosCoordinate l E L ι f P C (ME.calculus false) ρ K.obj eP eC q =
    (scalarCompletionIso l E L ι (W true)
      ((integralDerivedPullback.{u, u} l E f).obj K.obj) hF).inv ≫
      (integralOrdinaryDerivedScalar l E L ι (W true)).map
        ((integralDerivedPullback.{u, u} l E f).map eP.inv) ≫
      (integralOrdinaryDerivedScalar l E L ι (W true)).map
        ((integralDerivedPullbackComparison.{u, u} l E f).hom.app P) ≫
      (integralOrdinaryScalar l E L ι (W true)).mapDerivedCategoryFactors.hom.app
        ((integralOperationsPullbackComplexFunctor.{u, u} l E f).obj P.obj) ≫
      DerivedCategory.Q.map (scalarPullbackChain l E L ι f P.obj) := by
  classical
  let X := W true
  let F := integralDerivedPullback.{u, u} l E f
  let O := integralOrdinaryDerivedScalar l E L ι X
  let A := integralComparisonDerivedSequenceScalar.{u, u} l E L ι X
  let T := coefficientSequenceLimit.{u, u} l L X
  let S := ME.calculus true
  let χ := scalarCompletion l E L ι X
  let G := integralOperationsGoodLocalization.{u, u} l E X
  let V := (HomologicalComplex.quasiIso (integralTowerModules l E X) (.up ℤ)).inverseImage
    (integralOperationsGoodComplex l E X).ι
  have : G.IsLocalization V := integralOperationsGoodLocalization_isLocalization l E X
  have : G.EssSurj := Localization.essSurj G V
  let R := G.objPreimage (F.obj K.obj)
  let eR : DerivedCategory.Q.obj R.obj ≅ F.obj K.obj := G.objObjPreimageIso _
  obtain ⟨D, eD, κD, hpD, hcD⟩ := coherentPrimitiveReductionPresentation l E S R
  obtain ⟨qD, hqD, hSX⟩ := SX.normalization R D eD κD hpD hcD
  have hkD : CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf.{u, u} l E X) D := by
    apply WeilConjectures.kflat_of_levels l E X
    intro n
    exact SheafOfModules.kFlat_iso_independent (integralCoefficientCommRingSheaf l E X n)
      (κD n).symm ((coefficientTensorModelPreservation l E X).1 R.obj R.property.1 n)
  have := (integralComparisonSequenceScalarModel.{u, u} l E L ι X).computes D hkD
  let εD := asIso ((integralComparisonSequenceScalarModel.{u, u} l E L ι X).ε.app D)
  let SD := ((integralComparisonSequenceScalarModel.{u, u} l E L ι X).E.mapHomologicalComplex
    (.up ℤ)).obj D
  let rD := T.mapIso (A.mapIso eD ≪≫ εD) ≪≫
    integralComparisonRoosBridge.{u, u} l L X ρ SD ≪≫
    DerivedCategory.Q.mapIso (integralOperationsRoosFunctor.mapIso qD)
  have hn : SX.realization.hom.app (DerivedCategory.Q.obj R.obj) ≫ rD.hom =
      (integralScalarExtensionComparison l E L ι X).hom.app R := by
    simpa only [rD, εD, T, A, SD, X, Iso.trans_hom, Functor.mapIso_hom,
      asIso_hom, Functor.map_comp, Category.assoc, integralScalarExtensionComparison,
      integralScalarExtensionComparisonOfUniverses] using hSX
  have hχ : χ.app (DerivedCategory.Q.obj R.obj) ≫
      (integralScalarExtensionComparison l E L ι X).hom.app R =
      (integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.hom.app R.obj ≫
        DerivedCategory.Q.map ((integralScalarCompletionChain l E L ι X).app R.obj) := by
    dsimp only [χ]
    unfold scalarCompletion
    exact (scalarCompletion_existsUnique l E L ι X).exists.choose_spec.1 R
  have hs : χ.app (DerivedCategory.Q.obj R.obj) ≫
      SX.realization.hom.app (DerivedCategory.Q.obj R.obj) =
      (integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.hom.app R.obj ≫
        DerivedCategory.Q.map ((integralScalarCompletionChain l E L ι X).app R.obj) ≫
        rD.inv := by
    apply (cancel_mono rD.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hn]
    exact hχ
  have hcore := scalarPullbackCompletionRoos l E L ι W ME ρ f P K.obj eP C eC κ hp hc q hq
    R eR D eD κD hpD hcD εD rfl qD hqD
  change _ ≫ _ ≫ rD.inv ≫ T.map (A.map (S.reduction.map eR.hom ≫
    pullbackReduction l E W ME f K.obj)) ≫ _ = _ at hcore
  let c := scalarPullbackRoosCoordinate l E L ι f P C (ME.calculus false) ρ K.obj eP eC q
  let b := T.map (A.map (pullbackReduction l E W ME f K.obj)) ≫ c
  have hSXnat := SX.realization.hom.naturality eR.hom
  dsimp only [Functor.comp_map] at hSXnat
  have hχnat := χ.naturality eR.hom
  have hpre : O.map eR.hom ≫ χ.app (F.obj K.obj) ≫
      SX.realization.hom.app (F.obj K.obj) ≫ b =
      O.map eR.hom ≫ O.map (F.map eP.inv) ≫
        O.map ((integralDerivedPullbackComparison.{u, u} l E f).hom.app P) ≫
        (integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.hom.app
          ((integralOperationsPullbackComplexFunctor.{u, u} l E f).obj P.obj) ≫
        DerivedCategory.Q.map (scalarPullbackChain l E L ι f P.obj) := by
    rw [← Category.assoc, ← Category.assoc, hχnat]
    simp only [Category.assoc]
    have hmap : (integralScalarExtension l E L ι X).map eR.hom =
        (integralScalarExtensionOfUniverses l E L ι X).map eR.hom := by
      unfold integralScalarExtension integralScalarExtensionOfUniverses
      rfl
    rw [hmap]
    erw [reassoc_of% hSXnat]
    rw [← Category.assoc, ← Category.assoc, hs]
    simpa only [b, c, Functor.map_comp, Category.assoc] using hcore
  have he : (scalarCompletionIso l E L ι X (F.obj K.obj) hF).hom =
      χ.app (F.obj K.obj) := by
    unfold scalarCompletionIso
    rfl
  have ht := (cancel_epi (O.map eR.hom)).1 hpre
  have hf := congrArg ((scalarCompletionIso l E L ι X (F.obj K.obj) hF).inv ≫ ·) ht
  rw [← he] at hf
  simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp,
    b, c, X, F, O, T, A] using hf

end WeilConjectures.ScalarExtensionTower
