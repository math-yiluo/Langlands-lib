/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarPullbackRoosCoordinates
import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarCompletionQuotientPresentation
import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarPullbackQuotientExt
import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarPullbackRoosCoordinateSystem

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
  integralDerivedPullback integralOrdinaryScalar
  scalarCompletion scalarCompletionIso scalarPullbackOrdinary
  integralComparisonSystemScalarPullback integralComparisonSequenceScalarPullback
  integralComparisonSequenceScalarModel coefficientSequenceLimit

private theorem scalarReduction_naturality (Y : Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E Y)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L Y)
    (ρ : IntegralComparisonRoosModel.{u, u} l L Y)
    (SY : IntegralComparisonScalarModel.{u, u} l E L ι Y SE ρ)
    {K K' : DerivedCategory (scalarReductionSource.{u, u} l E Y)} (g : K ⟶ K') :
    SL.reduction.map ((integralScalarExtension.{u} l E L ι Y).map g) ≫
        scalarReduction l E L ι Y SE SL ρ SY K' =
      scalarReduction l E L ι Y SE SL ρ SY K ≫
        (integralComparisonDerivedSequenceScalar.{u, u} l E L ι Y).map (SE.reduction.map g) := by
  have hmap : (integralScalarExtension l E L ι Y).map g =
      (integralScalarExtensionOfUniverses l E L ι Y).map g := by
    unfold integralScalarExtension integralScalarExtensionOfUniverses
    rfl
  rw [hmap]
  have hS := SY.realization.hom.naturality g
  dsimp only [Functor.comp_map] at hS
  unfold scalarReduction
  erw [← SL.reduction.map_comp_assoc, hS, SL.reduction.map_comp]
  simp only [Category.assoc]
  erw [SL.adjunction.counit.naturality]
  rfl

private theorem scalarCompletionIso_hom (Y : Scheme.{u})
    (K : DerivedCategory (integralTowerModules l E Y)) (hK : IsSfDerivedComplete l E Y K) :
    (scalarCompletionIso l E L ι Y K hK).hom = (scalarCompletion l E L ι Y).app K := by
  unfold scalarCompletionIso
  rfl

attribute [local irreducible] integralScalarExtension

/-- Compute the route using scalar normalization at Y and pullback normalization
with coefficients L. There is no scalar model at X or pullback model for E here.
Source: Stacks 07A4, 0941; the left route in realization step 8 of
lem-pur-scalar-extension-tower-coherence.
(blueprint: stage3-pur-scalar-pullback-left-roos).

Proof: precompose by scalarCompletionIso at the pulled E input. Its inverse in
scalarPullbackCompleted cancels. Naturality of the L-pullback realization moves
the remaining scalarCompletion at Y into the reduction diagram. Use the scalar
normalization of SY on the coherent presentation C, and the normalization of the
L-pullback on the ordinary scalar extension of P. The normalized completion chain
has the tensor-unit augmentation and zero shifted coordinate. The quotient
formula for q identifies its augmentation with the canonical scalarPullbackTower
map, level by level and with every transition. Applying the Roos functor gives
scalarPullbackChain on both coordinates. The normalization of
scalarPullbackOrdinary identifies its localization with the middle of the
conjugated completed comparison. Move eP through the natural transformations,
then cancel the source completion isomorphism. This proves the stated one-sided
coordinate formula. No realization with E after pullback is used. -/
theorem scalarPullbackLeftRoos (W : Bool → Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E (W false))
    (ML : CompletedOperations.Models.{u, u} l L W)
    (SY : IntegralComparisonScalarModel.{u, u} l E L ι (W false) SE (ML.roos false))
    (f : W true ⟶ W false)
    (_hX : IsUnit (l : Γ(W true, ⊤))) (_hY : IsUnit (l : Γ(W false, ⊤)))
    (P : (integralOperationsGoodComplex.{u, u} l E (W false)).FullSubcategory)
    (K : sfIntegralConstructibleCategory l E (W false))
    (eP : DerivedCategory.Q.obj P.obj ≅ K.obj)
    (C : CochainComplex (coefficientSequenceModules.{u, u} l E (W false)) ℤ)
    (eC : SE.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation.{u, u} l E (W false) n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex.{u, u} l E (W false) n).obj P.obj)
    (hp : CoefficientReductionPresentation.{u, u} l E (W false)
      SE.toCoefficientDerivedSystemReduction P.obj P.property.1 C eC κ)
    (hc : IsIntegralComparisonPresentationCoherent.{u, u} l E (W false) SE P.obj C eC κ)
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
    (((scalarPullbackCompleted l E L ι f K.obj K.property.1 hF).hom ≫
        (ML.pullback f).realization.hom.app
          ((integralScalarExtension.{u} l E L ι (W false)).obj K.obj) ≫
        (coefficientSequenceLimit.{u, u} l L (W true)).map
          ((integralComparisonDerivedSequencePullback.{u, u} l L f).map
            (scalarReduction l E L ι (W false) SE (ML.calculus false)
              (ML.roos false) SY K.obj))) ≫
      (coefficientSequenceLimit.{u, u} l L (W true)).map
        ((integralComparisonSystemScalarPullback.{u, u} l E L ι f).inv.app
          (SE.reduction.obj K.obj))) ≫
      scalarPullbackRoosCoordinate l E L ι f P C SE (ML.roos true) K.obj eP eC q =
    scalarPullbackRoosChain l E L ι f P K.obj eP hF := by
  classical
  -- Keep the schemes syntactically aligned with the presentation hypotheses to avoid
  -- unfolding coefficient functors when checking definitional equality.
  let T := coefficientSequenceLimit.{u, u} l L (W true)
  let B := integralComparisonDerivedSequencePullback.{u, u} l L f
  let A := integralComparisonDerivedSequenceScalar.{u, u} l E L ι (W false)
  let PS := ((integralOrdinaryScalar l E L ι (W false)).mapHomologicalComplex (.up ℤ)).obj P.obj
  let CS :=
    ((integralComparisonSequenceScalarModel.{u, u} l E L ι (W false)).E.mapHomologicalComplex
      (.up ℤ)).obj C
  let d := (integralOrdinaryScalar l E L ι (W false)).mapDerivedCategoryFactors.hom.app P.obj
  let t : A.obj (DerivedCategory.Q.obj C) ⟶ DerivedCategory.Q.obj CS :=
    (integralComparisonSequenceScalarModel.{u, u} l E L ι (W false)).ε.app C
  let b : B.obj (DerivedCategory.Q.obj CS) ⟶ DerivedCategory.Q.obj
      (((integralComparisonSequencePullback l L f).mapHomologicalComplex (.up ℤ)).obj CS) :=
    (integralComparisonSequencePullback.{u, u} l L f).mapDerivedCategoryFactors.hom.app CS
  let r := (integralComparisonRoosBridge.{u, u} l L (W true) (ML.roos true)
    (((integralComparisonSequencePullback.{u, u} l L f).mapHomologicalComplex (.up ℤ)).obj CS)).hom
  let z := DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom)
  obtain ⟨eS, κS, hpS, hcS, hκS, heS⟩ :=
    scalarCompletionQuotientPresentation l E L ι (W false) SE (ML.calculus false)
      (ML.roos false) SY P C eC κ hp hc
  let GP : (integralOperationsGoodComplex l L (W false)).FullSubcategory :=
    ⟨PS, scalarGood l E L ι (W false) P⟩
  obtain ⟨qL, hqL, hML⟩ := (ML.pullback f).normalization GP CS eS κS hpS hcS
  have hqL' : ScalarPullbackQuotientFormula l E L ι f P C κ qL := by
    intro n i U x
    let y := integralComparisonSequenceTensorSection.{u, u} l E L ι (W false) (C.X i)
      (op (n, U)) 1
      (integralComparisonSequenceSection.{u, u} l E (W false) (C.X i) n (op U)
        (((κ n).inv.f i).val.app (op U)
          (unrestrictedIntegralTensorSection.{u, u} l E (W false) n (P.obj.X i) (op U) 1 x)))
    exact (hqL n i U y).trans (congrArg
      (integralOperationsPullbackGenerator l L f n _ U) (hκS n i U x))
  have hqq : q = qL := scalarPullbackQuotient_ext l E L ι f P C κ q qL hq hqL'
  rw [← hqq] at hML
  let β := integralComparisonSystemScalarPullback.{u, u} l E L ι f
  let a := SE.reduction.map eP.inv ≫ eC.hom
  have hcoord : T.map (β.inv.app (SE.reduction.obj K.obj)) ≫
      scalarPullbackRoosCoordinate l E L ι f P C SE (ML.roos true) K.obj eP eC q =
      T.map (B.map (A.map a ≫ t) ≫ b) ≫ r ≫ z := by
    exact scalarPullbackRoosCoordinate_system l E L ι f P C SE (ML.roos true)
      K.obj eP eC q κ
  have hn : (integralDerivedPullback.{u, u} l L f).map
        ((scalarCompletion l E L ι (W false)).app (DerivedCategory.Q.obj P.obj)) ≫
      (ML.pullback f).realization.hom.app
        ((integralScalarExtension.{u} l E L ι (W false)).obj (DerivedCategory.Q.obj P.obj)) ≫
      T.map (B.map (scalarReduction l E L ι (W false) SE (ML.calculus false)
        (ML.roos false) SY (DerivedCategory.Q.obj P.obj) ≫ A.map eC.hom ≫ t)) ≫
      T.map b ≫ r ≫ z =
      (integralDerivedPullback.{u, u} l L f).map d ≫
        (integralDerivedPullbackComparison.{u, u} l L f).hom.app
          GP := by
    have hχ := (ML.pullback f).realization.hom.naturality
      ((scalarCompletion l E L ι (W false)).app (DerivedCategory.Q.obj P.obj))
    have hd := (ML.pullback f).realization.hom.naturality d
    dsimp only [Functor.comp_map] at hχ hd
    erw [← Category.assoc, ← Category.assoc, ← Category.assoc, ← Category.assoc, hχ]
    simp only [Category.assoc]
    change (ML.pullback f).realization.hom.app _ ≫
      T.map (B.map ((ML.calculus false).reduction.map
        ((scalarCompletion l E L ι (W false)).app (DerivedCategory.Q.obj P.obj)))) ≫
      T.map (B.map (scalarReduction l E L ι (W false) SE (ML.calculus false)
        (ML.roos false) SY (DerivedCategory.Q.obj P.obj) ≫ A.map eC.hom ≫ t)) ≫
      T.map b ≫ r ≫ z = _
    erw [← T.map_comp_assoc, ← B.map_comp]
    erw [← heS]
    simp only [Functor.map_comp, Category.assoc]
    erw [← reassoc_of% hd]
    exact congrArg ((integralDerivedPullback.{u, u} l L f).map d ≫ ·) hML
  let F := integralDerivedPullback.{u, u} l L f
  let O := integralOrdinaryDerivedScalar l E L ι (W false)
  let χ := scalarCompletion l E L ι (W false)
  let ν := (ML.pullback f).realization.hom
  let δ := scalarReduction l E L ι (W false) SE (ML.calculus false) (ML.roos false) SY K.obj
  have hδ := scalarReduction_naturality l E L ι (W false) SE (ML.calculus false)
    (ML.roos false) SY eP.inv
  have hδa : δ ≫ A.map a ≫ t =
      (ML.calculus false).reduction.map
          ((integralScalarExtension.{u} l E L ι (W false)).map eP.inv) ≫
        scalarReduction l E L ι (W false) SE (ML.calculus false) (ML.roos false) SY
          (DerivedCategory.Q.obj P.obj) ≫ A.map eC.hom ≫ t := by
    simpa only [δ, A, a, Functor.map_comp, Category.assoc] using
      congrArg (fun g ↦ g ≫ A.map eC.hom ≫ t) hδ.symm
  have hnK : F.map (χ.app K.obj) ≫
      ν.app ((integralScalarExtension.{u} l E L ι (W false)).obj K.obj) ≫
      T.map (B.map δ) ≫ T.map (B.map (A.map a ≫ t) ≫ b) ≫ r ≫ z =
      F.map (O.map eP.inv) ≫ F.map d ≫
        (integralDerivedPullbackComparison.{u, u} l L f).hom.app
          GP := by
    have hν := ν.naturality ((integralScalarExtension.{u} l E L ι (W false)).map eP.inv)
    have hχ := χ.naturality eP.inv
    dsimp only [Functor.comp_map] at hν
    erw [T.map_comp]
    simp only [Category.assoc]
    erw [← T.map_comp_assoc, ← B.map_comp, hδa]
    simp only [Functor.map_comp, Category.assoc]
    erw [← reassoc_of% hν]
    erw [← F.map_comp_assoc, ← hχ, F.map_comp]
    simp only [Category.assoc]
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (F.map (O.map eP.inv) ≫ ·) hn
  have hOrd : scalarPullbackOrdinaryNormalization l E L ι f
      (scalarPullbackOrdinary l E L ι f) := by
    unfold scalarPullbackOrdinary
    exact (scalarPullbackOrdinary_existsUnique l E L ι f).exists.choose_spec
  have hOrdP := hOrd P
  have hNat := (scalarPullbackOrdinary l E L ι f).hom.naturality eP.inv
  dsimp only [Functor.comp_map] at hNat
  simp only [Category.assoc]
  erw [hcoord]
  dsimp only [scalarPullbackCompleted, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Functor.mapIso_hom, scalarPullbackRoosChain]
  simp only [Category.assoc]
  erw [scalarCompletionIso_hom]
  change (scalarCompletionIso l E L ι (W true) _ hF).inv ≫
      (scalarPullbackOrdinary l E L ι f).hom.app K.obj ≫
      F.map (χ.app K.obj) ≫ ν.app _ ≫ T.map (B.map δ) ≫
      T.map (B.map (A.map a ≫ t) ≫ b) ≫ r ≫ z = _
  erw [hnK]
  erw [← reassoc_of% hNat]
  erw [← hOrdP]

end WeilConjectures.ScalarExtensionTower
