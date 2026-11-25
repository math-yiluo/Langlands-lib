/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarTowerTensorLimitStrictWitness
import WeilConjectures.TraceFormula.Coherent.CoherentPrimitiveReductionPresentation
import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarCompletionQuotientPresentation
import WeilConjectures.SmoothPurity.ScalarExtensionTower.IntegralScalarRoosCounitNormalization
import WeilConjectures.TraceFormula.Integral.IntegralScalarOrdinaryModelComparison
import all WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarTensorStrictQuotientTower
import all WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarTensorRoosQuotientChain
import all WeilConjectures.TraceFormula.Scalar.ScalarModelRoosZeroLiftCore

/-! # Good representative transport

The strict K-flat calculation is isolated from the later localization and
completed-limit assembly.
(blueprint: stage3-pur-scalar-tensor-limit-good-representatives)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [-instance] WeilConjectures.scalarReductionSourceDerived
  WeilConjectures.scalarReductionTargetDerived WeilConjectures.integralOperationsSiteSmall
attribute [local instance 3000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 50000] CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
  WeilConjectures.integralOperationsAbSheafify WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsCommHasDerivedCategory
  SheafOfModules.cochainModulesMonoidal SheafOfModules.cochainModulesSymmetric
  SheafOfModules.cochainModulesPreadditive
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures.ScalarExtensionTower

private local instance (W : Scheme.{u}) : EssentiallySmall.{u + 1} W.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _
private local instance (W : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology W) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} W
private local instance (W : Scheme.{u}) :
    (Scheme.ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} W

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible]
  integralCompletedTensor scalarReduction tensorReduction

attribute [local irreducible] HasDerivedCategory.standard
  integralComparisonSequenceScalarModel coefficientSequenceRestriction coefficientSequenceLimit
  integralOrdinaryScalar completedIntegralCommRingSheafUnrestricted
  comparisons Functor.leftAdjoint Functor.mapDerivedCategory SheafOfModules.monoidalCategory
  coefficientSequenceCommRingSheaf coefficientSequenceCommRingPresheaf
  integralOperationsRoos integralOperationsRoosMap scalarRoosMap scalarCompletion
  scalarTensorOrdinary coefficientTotalTensor integralOrdinaryTensorSection
  unrestrictedIntegralTensorSection integralTensorGenerator
  integralComparisonSequenceTensorSection integralComparisonRestrictedSection
  integralComparisonSequenceSection coefficientEvaluationSection
attribute [local implicit_reducible] tensor integralComparisonDerivedSequenceScalar
  integralOperationsTensorTowerFunctor integralOperationsTensorLevel
  integralScalarExtension integralScalarExtensionOfUniverses
  integralOperationsGoodLocalization integralOperationsRoosFunctor
  integralOperationsTensorComplexFunctor integralOperationsTensorOnGood

/-- The normalized scalar/tensor square on good representatives, before inverting
scalar completion. The bridge is the specified ordinary tensor comparison followed
by the two completion maps. It is not an arbitrary morphism.

Source: Stacks 07A4 and 0941; scalar/tensor normalization and localization
(blueprint: stage3-pur-scalar-tensor-limit-good-representatives).

Proof: take the actual whole-system quotient presentations of P and Q. The
normalizations of TE, TL and SY express the two maps through the same Roos
comparisons and the coherent reduction counits. Apply the strict equation hstrict
on flat-term K-flat resolutions of the quotient presentations. Tensor balancing
sends b tensor (x tensor y) to (b tensor x) tensor (1 tensor y), on both routes.
This agrees with scalarTensorOrdinary's specified chain normalization. The
scalarCompletion normalization inserts the quotient augmentation, with zero
shifted coordinate. Both routes therefore agree on each homogeneous tensor and
on both Roos coordinates. Naturality of the Roos comparison and localization
remove the resolutions and yield the displayed equality. No inverse completion
map, arbitrary bridge, or faithfulness of finite derived evaluations is used. -/
theorem scalarTowerTensorLimitSquare_on_good_representatives (W : Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L W)
    (ρE : IntegralComparisonRoosModel.{u, u} l E W)
    (ρL : IntegralComparisonRoosModel.{u, u} l L W)
    (SY : IntegralComparisonScalarModel.{u, u} l E L ι W SE ρL)
    (TE : TensorModel l E W SE ρE) (TL : TensorModel l L W SL ρL)
    (α : SE.systemClosed.tensor ⋙ integralComparisonDerivedSequenceScalar.{u, u} l E L ι W ≅
      (integralComparisonDerivedSequenceScalar.{u, u} l E L ι W).prod
        (integralComparisonDerivedSequenceScalar.{u, u} l E L ι W) ⋙ SL.systemClosed.tensor)
    (hstrict : DerivedSigmaModel l E L ι W SE SL α) :
    ∀ (P Q : (integralOperationsGoodComplex l E W).FullSubcategory),
      (scalarTensorOrdinary l E L ι W).hom.app
          ((integralOperationsGoodLocalization l E W).obj P,
            (integralOperationsGoodLocalization l E W).obj Q) ≫
        (integralCompletedTensor l L W).map (Prod.mkHom
          ((scalarCompletion l E L ι W).app
            ((integralOperationsGoodLocalization l E W).obj P))
          ((scalarCompletion l E L ι W).app
            ((integralOperationsGoodLocalization l E W).obj Q))) ≫
        TL.realization.hom.app
          ((integralScalarExtension.{u} l E L ι W).obj
              ((integralOperationsGoodLocalization l E W).obj P),
            (integralScalarExtension.{u} l E L ι W).obj
              ((integralOperationsGoodLocalization l E W).obj Q)) ≫
        (coefficientSequenceLimit.{u, u} l L W).map
          (SL.systemClosed.tensor.map (Prod.mkHom
            (scalarReduction l E L ι W SE SL ρL SY
              ((integralOperationsGoodLocalization l E W).obj P))
            (scalarReduction l E L ι W SE SL ρL SY
              ((integralOperationsGoodLocalization l E W).obj Q)))) =
      (scalarCompletion l E L ι W).app
          ((integralCompletedTensor l E W).obj
            ((integralOperationsGoodLocalization l E W).obj P,
              (integralOperationsGoodLocalization l E W).obj Q)) ≫
        SY.realization.hom.app
          ((integralCompletedTensor.{u, u} l E W).obj
            ((integralOperationsGoodLocalization l E W).obj P,
              (integralOperationsGoodLocalization l E W).obj Q)) ≫
        (coefficientSequenceLimit.{u, u} l L W).map
          ((integralComparisonDerivedSequenceScalar.{u, u} l E L ι W).map
            (tensorReduction l E W SE ρE TE
              ((integralOperationsGoodLocalization l E W).obj P)
              ((integralOperationsGoodLocalization l E W).obj Q)) ≫
          α.hom.app
            (SE.reduction.obj ((integralOperationsGoodLocalization l E W).obj P),
              SE.reduction.obj ((integralOperationsGoodLocalization l E W).obj Q))) := by
  classical
  intro P Q
  obtain ⟨C, eC, κC, hpC, hcC⟩ := coherentPrimitiveReductionPresentation l E SE P
  obtain ⟨D, eD, κD, hpD, hcD⟩ := coherentPrimitiveReductionPresentation l E SE Q
  have hC := presentation_good l E W P C κC
  have hD := presentation_good l E W Q D κD
  obtain ⟨hsC, hsD, hσ⟩ := hstrict C D hC hD
  obtain ⟨qE, hqE, hTE⟩ := TE.normalization P Q C D eC eD κC κD
    hC.1 hD.1 hpC hpD hcC hcD
  obtain ⟨eS, κS, hpS, hcS, hκS, heS⟩ :=
    scalarCompletionQuotientPresentation l E L ι W SE SL ρL SY P C eC κC hpC hcC
  obtain ⟨eT, κT, hpT, hcT, hκT, heT⟩ :=
    scalarCompletionQuotientPresentation l E L ι W SE SL ρL SY Q D eD κD hpD hcD
  let PS : (integralOperationsGoodComplex l L W).FullSubcategory :=
    ⟨_, scalarGood l E L ι W P⟩
  let QS : (integralOperationsGoodComplex l L W).FullSubcategory :=
    ⟨_, scalarGood l E L ι W Q⟩
  obtain ⟨qL, hqL, hTL⟩ := TL.normalization PS QS
    ((scalar l E L ι W).obj C) ((scalar l E L ι W).obj D) eS eT κS κT
    hsC.1 hsD.1 hpS hpT hcS hcT
  have hTE' := eq_of_heq hTE
  have hTL' := eq_of_heq hTL
  let A := integralComparisonDerivedSequenceScalar l E L ι W
  let T := coefficientSequenceLimit l L W
  let TE' := coefficientSequenceLimit l E W
  let B := SL.systemClosed.tensor
  let H := (tensor l E W).obj (C, D)
  let HL := (tensor l L W).obj ((scalar l E L ι W).obj C, (scalar l E L ι W).obj D)
  let εC := (integralComparisonSequenceScalarModel l E L ι W).ε.app C
  let εD := (integralComparisonSequenceScalarModel l E L ι W).ε.app D
  let εH := (integralComparisonSequenceScalarModel l E L ι W).ε.app H
  let mE := SE.systemTensorModel.iso _ _ _ C D hC.1 hD.1
  let mL := SL.systemTensorModel.iso _ _ _ _ _ hsC.1 hsD.1
  let x := SE.systemClosed.tensor.map (Prod.mkHom eC.hom eD.hom) ≫ mE.inv
  let y := B.map (Prod.mkHom (A.map eC.hom ≫ εC) (A.map eD.hom ≫ εD)) ≫ mL.inv
  let rL := (integralComparisonRoosBridge l L W ρL HL).hom
  let zL := DerivedCategory.Q.map (integralOperationsRoosFunctor.map qL.hom)
  let post := T.map y ≫ rL ≫ zL
  have hεC : IsIso εC :=
    (integralComparisonSequenceScalarModel l E L ι W).computes C hC.1
  have hεD : IsIso εD :=
    (integralComparisonSequenceScalarModel l E L ι W).computes D hD.1
  have hy : IsIso y := by
    have : IsIso (Prod.mkHom (A.map eC.hom ≫ εC) (A.map eD.hom ≫ εD)) :=
      (CategoryTheory.isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
    dsimp only [y]
    infer_instance
  have hp : IsIso post := by dsimp only [post, rL, zL]; infer_instance
  let dP := (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app P.obj
  let dQ := (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app Q.obj
  let χ := scalarCompletion l E L ι W
  let δP := scalarReduction l E L ι W SE SL ρL SY (DerivedCategory.Q.obj P.obj)
  let δQ := scalarReduction l E L ι W SE SL ρL SY (DerivedCategory.Q.obj Q.obj)
  have hpair :
      B.map (Prod.mkHom (SL.reduction.map (χ.app (DerivedCategory.Q.obj P.obj)))
        (SL.reduction.map (χ.app (DerivedCategory.Q.obj Q.obj)))) ≫
      B.map (Prod.mkHom δP δQ) ≫ y =
      B.map (Prod.mkHom (SL.reduction.map dP) (SL.reduction.map dQ)) ≫
      B.map (Prod.mkHom eS.hom eT.hom) ≫ mL.inv := by
    exact paired_tensor_word B
      (SL.reduction.map (χ.app (DerivedCategory.Q.obj P.obj)))
      (SL.reduction.map (χ.app (DerivedCategory.Q.obj Q.obj))) δP δQ
      (A.map eC.hom ≫ εC) (A.map eD.hom ≫ εD)
      (SL.reduction.map dP) (SL.reduction.map dQ) eS.hom eT.hom mL.inv heS heT
  have hleft :
      (scalarTensorOrdinary l E L ι W).hom.app
          (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
        (integralCompletedTensor l L W).map (Prod.mkHom
          (χ.app (DerivedCategory.Q.obj P.obj)) (χ.app (DerivedCategory.Q.obj Q.obj))) ≫
        TL.realization.hom.app
          ((integralScalarExtension l E L ι W).obj (DerivedCategory.Q.obj P.obj),
            (integralScalarExtension l E L ι W).obj (DerivedCategory.Q.obj Q.obj)) ≫
        T.map (B.map (Prod.mkHom δP δQ)) ≫ post =
      (integralOrdinaryDerivedScalar l E L ι W).map
          ((integralCompletedTensorComparison l E W).hom.app (P, Q)) ≫
        (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app
          ((integralOperationsTensorComplexFunctor l E W).obj (P.obj, Q.obj)) ≫
        DerivedCategory.Q.map (scalarTensorChain l E L ι W P.obj Q.obj) := by
    have hχ := TL.realization.hom.naturality (Prod.mkHom
      (χ.app (DerivedCategory.Q.obj P.obj)) (χ.app (DerivedCategory.Q.obj Q.obj)))
    have hd := TL.realization.hom.naturality (Prod.mkHom dP dQ)
    dsimp only [Functor.comp_map, Functor.prod_map] at hχ hd
    have hw := normalized_tensor_word T
      ((scalarTensorOrdinary l E L ι W).hom.app
        (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj))
      ((integralCompletedTensor l L W).map (Prod.mkHom
        (χ.app (DerivedCategory.Q.obj P.obj)) (χ.app (DerivedCategory.Q.obj Q.obj))))
      (TL.realization.hom.app _)
      (TL.realization.hom.app
        ((integralOrdinaryDerivedScalar l E L ι W).obj (DerivedCategory.Q.obj P.obj),
          (integralOrdinaryDerivedScalar l E L ι W).obj (DerivedCategory.Q.obj Q.obj)))
      ((integralCompletedTensor l L W).map (Prod.mkHom dP dQ))
      (TL.realization.hom.app (DerivedCategory.Q.obj PS.obj, DerivedCategory.Q.obj QS.obj))
      (B.map (Prod.mkHom (SL.reduction.map (χ.app (DerivedCategory.Q.obj P.obj)))
        (SL.reduction.map (χ.app (DerivedCategory.Q.obj Q.obj)))))
      (B.map (Prod.mkHom δP δQ)) y
      (B.map (Prod.mkHom (SL.reduction.map dP) (SL.reduction.map dQ)))
      (B.map (Prod.mkHom eS.hom eT.hom)) mL.inv rL zL
      ((integralCompletedTensorComparison l L W).hom.app (PS, QS)) hχ hpair hd hTL'
    have hOrd := scalar_tensor_normalization l E L ι W
    have hw' := hw.trans (hOrd P Q).symm
    simpa only [post, Category.assoc] using hw'
  have hsquare :
      α.hom.app (SE.reduction.obj (DerivedCategory.Q.obj P.obj),
          SE.reduction.obj (DerivedCategory.Q.obj Q.obj)) ≫ y =
        A.map x ≫ εH ≫ DerivedCategory.Q.map (((comparisons l).sigma E L ι W).hom.app
          (C, D)) := by
    exact tensor_comparison_transport A SE.systemClosed.tensor B α.hom
      eC.hom eD.hom εC εD εH _ mE mL hσ
  let CE := ((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj H
  let SH := (scalar l E L ι W).obj H
  let σ := ((comparisons l).sigma E L ι W).hom.app (C, D)
  let τ := HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
    (((coefficientSequenceRestriction l L W).mapHomologicalComplex (.up ℤ)).map σ)
  let a : CE.asFunctor ⋙ completedOrdinaryScalarComplex l E L ι W ⟶
      (((coefficientSequenceRestriction l L W).mapHomologicalComplex (.up ℤ)).obj
        SH).asFunctor :=
    { app n := ScalarRoosLiftProof.levelChange l E L ι W H n.unop
      naturality n m f := ScalarRoosLiftProof.levelChange_horizontal l E L ι W H f }
  obtain ⟨t, e, ht, he, hχmodel⟩ := integralScalarOrdinaryModelComparison l E L ι W
  have hCounit := integralScalarRoosCounitNormalization l E L ι W SE ρE ρL SY t e he
    hχmodel H a (fun n i U s v ↦
      ScalarRoosLiftProof.scalarComponent_tensor l E L ι W (H.X i) n U s v)
  have hchain :
      ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).map
          (integralOperationsRoosMap qE.inv) ≫
        (NatIso.mapHomologicalComplex t (.up ℤ)).hom.app (integralOperationsRoos CE.asFunctor) ≫
        scalarRoosMap (completedOrdinaryScalarExtension l E L ι W) CE.asFunctor ≫
        integralOperationsRoosMap a ≫ integralOperationsRoosMap τ ≫
        integralOperationsRoosMap qL.hom = scalarTensorChain l E L ι W P.obj Q.obj := by
    exact scalarTensorRoosQuotientChain l E L ι W P.obj Q.obj C D κC κD κS κT
      hκS hκT qE hqE qL hqL t ht a (fun n i U s v ↦
        ScalarRoosLiftProof.scalarComponent_tensor l E L ι W (H.X i) n U s v)
  have hright :
      χ.app ((integralCompletedTensor l E W).obj
          (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)) ≫
        SY.realization.hom.app ((integralCompletedTensor l E W).obj
          (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)) ≫
        T.map (A.map (tensorReduction l E W SE ρE TE
          (DerivedCategory.Q.obj P.obj) (DerivedCategory.Q.obj Q.obj)) ≫
          α.hom.app (SE.reduction.obj (DerivedCategory.Q.obj P.obj),
            SE.reduction.obj (DerivedCategory.Q.obj Q.obj))) ≫ post =
      (integralOrdinaryDerivedScalar l E L ι W).map
          ((integralCompletedTensorComparison l E W).hom.app (P, Q)) ≫
        (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app
          ((integralOperationsTensorComplexFunctor l E W).obj (P.obj, Q.obj)) ≫
        DerivedCategory.Q.map (scalarTensorChain l E L ι W P.obj Q.obj) := by
    exact normalized_scalar_tensor_right l E L ι W SE SL ρE ρL SY TE α P Q C D
      x y qE qL t a hsquare (by
        dsimp only [x]
        simp only [Functor.map_comp, Category.assoc]
        exact hTE') hCounit hchain
  apply (cancel_mono post).1
  simpa only [Category.assoc, integralOperationsGoodLocalization, Functor.comp_obj,
    ObjectProperty.ι_obj] using hleft.trans hright.symm

end WeilConjectures.ScalarExtensionTower
