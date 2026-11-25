/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerRealizationData
public import WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison
import all WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarTensorStrictQuotientTower

/-! # Roos transport of the strict scalar tensor quotient calculation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.ScalarExtensionTower

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
private local instance (W : Scheme.{u}) : EssentiallySmall.{u + 1} W.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _
private local instance (W : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology W) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} W
private local instance (W : Scheme.{u}) :
    (Scheme.ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} W

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] HasDerivedCategory.standard integralOrdinaryScalar
  integralComparisonSequenceScalarModel coefficientSequenceRestriction
  completedIntegralCommRingSheafUnrestricted integralOperationsRoos integralOperationsRoosMap
  scalarRoosMap integralOrdinaryTensorSection unrestrictedIntegralTensorSection comparisons
attribute [local implicit_reducible] tensor integralOperationsTensorTowerFunctor
  integralOperationsRoosFunctor NatIso.mapHomologicalComplex

/-- Apply Roos naturality to the strict quotient tensor calculation.
Source: Stacks 07A4 and 0941; naturality of the two-coordinate Roos construction.
(blueprint: lem-pur-scalar-tensor-roos-quotient-chain).

Proof: the strict quotient tower theorem identifies the composite of the inverse
E tensor quotient map, the ordinary scalar model, the scalar restriction map,
strict sigma and the L tensor quotient map with scalarTensorTower. Naturality of
scalarRoos with respect to the model isomorphism and the inverse quotient map
transports this equality through both Roos coordinates. Functoriality identifies
the resulting map with the defining scalarTensorChain. -/
theorem scalarTensorRoosQuotientChain (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ)
    (C D : Complex l E W)
    (κC : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E W n).obj P)
    (κD : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj D ≅
        (unrestrictedIntegralFiniteComplex l E W n).obj Q)
    (κSC : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ)).obj
        ((scalar l E L ι W).obj C) ≅
      (unrestrictedIntegralFiniteComplex l L W n).obj
        (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P))
    (κSD : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ)).obj
        ((scalar l E L ι W).obj D) ≅
      (unrestrictedIntegralFiniteComplex l L W n).obj
        (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj Q))
    (hκC : ∀ (n : ℕ) (i : ℤ) (U : W.ProEt) (x : (P.X i).val.obj (op U)),
      ((κSC n).hom.f i).val.app (op U)
        (coefficientEvaluationSection l L W (((scalar l E L ι W).obj C).X i) n (op U)
          (integralComparisonSequenceTensorSection l E L ι W (C.X i) (op (n, U)) 1
            (integralComparisonSequenceSection l E W (C.X i) n (op U)
              (((κC n).inv.f i).val.app (op U)
                (unrestrictedIntegralTensorSection l E W n (P.X i) (op U) 1 x))))) =
      unrestrictedIntegralTensorSection l L W n
        ((integralOrdinaryScalar l E L ι W).obj (P.X i)) (op U) 1
          (integralOrdinaryTensorSection l E L ι W (P.X i) (op U) 1 x))
    (hκD : ∀ (n : ℕ) (i : ℤ) (U : W.ProEt) (x : (Q.X i).val.obj (op U)),
      ((κSD n).hom.f i).val.app (op U)
        (coefficientEvaluationSection l L W (((scalar l E L ι W).obj D).X i) n (op U)
          (integralComparisonSequenceTensorSection l E L ι W (D.X i) (op (n, U)) 1
            (integralComparisonSequenceSection l E W (D.X i) n (op U)
              (((κD n).inv.f i).val.app (op U)
                (unrestrictedIntegralTensorSection l E W n (Q.X i) (op U) 1 x))))) =
      unrestrictedIntegralTensorSection l L W n
        ((integralOrdinaryScalar l E L ι W).obj (Q.X i)) (op U) 1
          (integralOrdinaryTensorSection l E L ι W (Q.X i) (op U) 1 x))
    (qE : (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj
        ((tensor l E W).obj (C, D))).asFunctor ≅
      (integralOperationsTensorTowerFunctor l E W).obj (P, Q))
    (hqE : ∀ (n : ℕ) (p r : ℤ) (U : W.ProEtᵒᵖ)
      (x : (C.X p).val.obj (op (n, U.unop)))
      (y : (D.X r).val.obj (op (n, U.unop))),
      ((qE.hom.app (op n)).f (p + r)).val.app U
        (integralComparisonRestrictedSection l E W
          (((tensor l E W).obj (C, D)).X (p + r)) n U
          (generator l E W C D p r (op (n, U.unop)) x y)) =
      integralTensorGenerator l E W P Q n p r U
        (((κC n).hom.f p).val.app U (coefficientEvaluationSection l E W (C.X p) n U x))
        (((κD n).hom.f r).val.app U (coefficientEvaluationSection l E W (D.X r) n U y)))
    (qL : (((coefficientSequenceRestriction l L W).mapHomologicalComplex (.up ℤ)).obj
        ((tensor l L W).obj ((scalar l E L ι W).obj C, (scalar l E L ι W).obj D))).asFunctor ≅
      (integralOperationsTensorTowerFunctor l L W).obj
        ((((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P),
          (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj Q)))
    (hqL : ∀ (n : ℕ) (p r : ℤ) (U : W.ProEtᵒᵖ)
      (x : (((scalar l E L ι W).obj C).X p).val.obj (op (n, U.unop)))
      (y : (((scalar l E L ι W).obj D).X r).val.obj (op (n, U.unop))),
      ((qL.hom.app (op n)).f (p + r)).val.app U
        (integralComparisonRestrictedSection l L W
          (((tensor l L W).obj ((scalar l E L ι W).obj C,
            (scalar l E L ι W).obj D)).X (p + r)) n U
          (generator l L W _ _ p r (op (n, U.unop)) x y)) =
      integralTensorGenerator l L W _ _ n p r U
        (((κSC n).hom.f p).val.app U (coefficientEvaluationSection l L W _ n U x))
        (((κSD n).hom.f r).val.app U (coefficientEvaluationSection l L W _ n U y)))
    (t : integralOrdinaryScalar l E L ι W ≅ completedOrdinaryScalarExtension l E L ι W)
    (ht : ∀ (N : integralTowerModules l E W) (U : W.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l L W).obj.obj U) (x : N.val.obj U),
      (t.hom.app N).val.app U (integralOrdinaryTensorSection l E L ι W N U s x) =
        completedScalarTensorSection l E L ι W N U s x)
    (a : (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj
        ((tensor l E W).obj (C, D))).asFunctor ⋙ completedOrdinaryScalarComplex l E L ι W ⟶
      (((coefficientSequenceRestriction l L W).mapHomologicalComplex (.up ℤ)).obj
        ((scalar l E L ι W).obj ((tensor l E W).obj (C, D)))).asFunctor)
    (ha : ∀ (n : ℕ) (i : ℤ) (U : W.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l L W).obj.obj U)
      (x : (((tensor l E W).obj (C, D)).X i).val.obj (op (n, U.unop))),
      ((a.app (op n)).f i).val.app U
        (completedScalarTensorSection l E L ι W
          (((coefficientSequenceRestriction l E W).obj
            (((tensor l E W).obj (C, D)).X i)).obj (op n)) U s
          (integralComparisonRestrictedSection l E W _ n U x)) =
      integralComparisonRestrictedSection l L W _ n U
        (integralComparisonSequenceTensorSection l E L ι W _ (op (n, U.unop))
          ((completedIntegralCommRingProjectionUnrestricted l L W n).hom.app U s) x)) :
    let H := (tensor l E W).obj (C, D)
    let CE := ((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj H
    let σ := ((comparisons l).sigma E L ι W).hom.app (C, D)
    let τ := HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
      (((coefficientSequenceRestriction l L W).mapHomologicalComplex (.up ℤ)).map σ)
    ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).map
        (integralOperationsRoosMap qE.inv) ≫
      (NatIso.mapHomologicalComplex t (.up ℤ)).hom.app (integralOperationsRoos CE.asFunctor) ≫
      scalarRoosMap (completedOrdinaryScalarExtension l E L ι W) CE.asFunctor ≫
      integralOperationsRoosMap a ≫ integralOperationsRoosMap τ ≫
      integralOperationsRoosMap qL.hom = scalarTensorChain l E L ι W P Q := by
  dsimp only
  let H := (tensor l E W).obj (C, D)
  let CE := ((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj H
  let σ := ((comparisons l).sigma E L ι W).hom.app (C, D)
  let τ := HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
    (((coefficientSequenceRestriction l L W).mapHomologicalComplex (.up ℤ)).map σ)
  let G := integralOrdinaryScalar l E L ι W
  let b := Functor.whiskerLeft CE.asFunctor (NatIso.mapHomologicalComplex t (.up ℤ)).hom
  let c := Functor.whiskerRight qE.inv (G.mapHomologicalComplex (.up ℤ))
  have hs := scalarTensorStrictQuotientTower l E L ι W P Q C D κC κD κSC κSD
    hκC hκD qE hqE qL hqL t ht a ha
  have hR := scalarRoos_iso_quotient G (completedOrdinaryScalarExtension l E L ι W)
    t CE.asFunctor ((integralOperationsTensorTowerFunctor l E W).obj (P, Q)) qE _
    (a ≫ τ ≫ qL.hom)
  change _ = scalarRoosMap G _ ≫ integralOperationsRoosMap
    (c ≫ b ≫ a ≫ τ ≫ qL.hom) at hR
  have hS := congrArg (fun f ↦ scalarRoosMap G _ ≫ integralOperationsRoosMap f) hs
  simpa only [scalarTensorChain, G, integralOperationsRoosMap_comp, Category.assoc] using
    hR.trans hS

attribute [local irreducible] integralCompletedTensor scalarReduction tensorReduction
  scalarCompletion scalarTensorOrdinary

/-- The prescribed tensorator satisfies its ordinary chain normalization. -/
private theorem scalar_tensor_normalization (W : Scheme.{u}) :
    scalarTensorOrdinaryNormalization l E L ι W (scalarTensorOrdinary l E L ι W) := by
  unfold scalarTensorOrdinary
  exact (scalarTensorOrdinary_existsUnique l E L ι W).exists.choose_spec

/-- Naturality of the reduction counit transports a tensor-model coordinate. -/
private theorem tensor_reduction_coordinate (W : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (ρ : IntegralComparisonRoosModel.{u, u} l E W) (T : TensorModel l E W S ρ)
    (M N : DerivedCategory (integralTowerModules.{u, u} l E W))
    (H : coefficientSequenceDerived l E W)
    (x : S.systemClosed.tensor.obj (S.reduction.obj M, S.reduction.obj N) ⟶ H) :
    S.reduction.map (T.realization.hom.app (M, N) ≫
        (coefficientSequenceLimit l E W).map x) ≫ S.adjunction.counit.app H =
      tensorReduction l E W S ρ T M N ≫ x := by
  have hn := S.adjunction.counit.naturality x
  change S.reduction.map ((coefficientSequenceLimit l E W).map x) ≫
      S.adjunction.counit.app H = S.adjunction.counit.app _ ≫ x at hn
  unfold tensorReduction
  simp only [Functor.map_comp, Category.assoc]
  rw [hn]
  rfl

attribute [local irreducible] coefficientSequenceLimit Functor.mapDerivedCategory
attribute [local implicit_reducible] integralScalarExtension integralScalarExtensionOfUniverses
  integralComparisonDerivedSequenceScalar

/-- The right scalar/tensor word in strict tensor-model coordinates. -/
private theorem normalized_scalar_tensor_right (W : Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L W)
    (ρE : IntegralComparisonRoosModel.{u, u} l E W)
    (ρL : IntegralComparisonRoosModel.{u, u} l L W)
    (SY : IntegralComparisonScalarModel.{u, u} l E L ι W SE ρL)
    (TE : TensorModel l E W SE ρE)
    (α : SE.systemClosed.tensor ⋙ integralComparisonDerivedSequenceScalar.{u, u} l E L ι W ≅
      (integralComparisonDerivedSequenceScalar.{u, u} l E L ι W).prod
        (integralComparisonDerivedSequenceScalar.{u, u} l E L ι W) ⋙ SL.systemClosed.tensor)
    (P Q : (integralOperationsGoodComplex l E W).FullSubcategory)
    (C D : Complex l E W)
    (x : SE.systemClosed.tensor.obj
        (SE.reduction.obj (DerivedCategory.Q.obj P.obj),
          SE.reduction.obj (DerivedCategory.Q.obj Q.obj)) ⟶
      DerivedCategory.Q.obj ((tensor l E W).obj (C, D)))
    (y : SL.systemClosed.tensor.obj
        ((integralComparisonDerivedSequenceScalar l E L ι W).obj
          (SE.reduction.obj (DerivedCategory.Q.obj P.obj)),
        (integralComparisonDerivedSequenceScalar l E L ι W).obj
          (SE.reduction.obj (DerivedCategory.Q.obj Q.obj))) ⟶
      DerivedCategory.Q.obj ((tensor l L W).obj
        ((scalar l E L ι W).obj C, (scalar l E L ι W).obj D)))
    (qE : (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj
        ((tensor l E W).obj (C, D))).asFunctor ≅
      (integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj))
    (qL : (((coefficientSequenceRestriction l L W).mapHomologicalComplex (.up ℤ)).obj
        ((tensor l L W).obj ((scalar l E L ι W).obj C, (scalar l E L ι W).obj D))).asFunctor ≅
      (integralOperationsTensorTowerFunctor l L W).obj
        ((((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P.obj),
          (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj Q.obj)))
    (t : integralOrdinaryScalar l E L ι W ≅ completedOrdinaryScalarExtension l E L ι W)
    (a : (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj
        ((tensor l E W).obj (C, D))).asFunctor ⋙ completedOrdinaryScalarComplex l E L ι W ⟶
      (((coefficientSequenceRestriction l L W).mapHomologicalComplex (.up ℤ)).obj
        ((scalar l E L ι W).obj ((tensor l E W).obj (C, D)))).asFunctor)
    (hsquare : α.hom.app
        (SE.reduction.obj (DerivedCategory.Q.obj P.obj),
          SE.reduction.obj (DerivedCategory.Q.obj Q.obj)) ≫ y =
      (integralComparisonDerivedSequenceScalar l E L ι W).map x ≫
        (integralComparisonSequenceScalarModel l E L ι W).ε.app
          ((tensor l E W).obj (C, D)) ≫
        DerivedCategory.Q.map (((comparisons l).sigma E L ι W).hom.app (C, D)))
    (hTEcomp : TE.realization.hom.app
        (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
      (coefficientSequenceLimit l E W).map x ≫
      (integralComparisonRoosBridge l E W ρE ((tensor l E W).obj (C, D))).hom ≫
      DerivedCategory.Q.map (integralOperationsRoosFunctor.map qE.hom) =
        (integralCompletedTensorComparison l E W).hom.app (P, Q))
    (hCounit :
    let Z := integralOperationsRoos
      (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj
          ((tensor l E W).obj (C, D))).asFunctor
    (integralOrdinaryDerivedScalar l E L ι W).map
        (integralComparisonRoosBridge l E W ρE ((tensor l E W).obj (C, D))).inv ≫
      (scalarCompletion l E L ι W).app
        ((coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj ((tensor l E W).obj (C, D)))) ≫
      SY.realization.hom.app
        ((coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj ((tensor l E W).obj (C, D)))) ≫
      (coefficientSequenceLimit l L W).map
        ((integralComparisonDerivedSequenceScalar l E L ι W).map
          (SE.adjunction.counit.app (DerivedCategory.Q.obj ((tensor l E W).obj (C, D))))) ≫
      (coefficientSequenceLimit l L W).map
        ((integralComparisonSequenceScalarModel l E L ι W).ε.app ((tensor l E W).obj (C, D))) ≫
      (integralComparisonRoosBridge l L W ρL _).hom =
    (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app Z ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex t (.up ℤ)).hom.app Z ≫
        scalarRoosMap (completedOrdinaryScalarExtension l E L ι W)
          (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj
          ((tensor l E W).obj (C, D))).asFunctor
          ≫ integralOperationsRoosMap a))
    (hchain :
    let H := (tensor l E W).obj (C, D)
    let CE := ((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj H
    let σ := ((comparisons l).sigma E L ι W).hom.app (C, D)
    let τ := HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
      (((coefficientSequenceRestriction l L W).mapHomologicalComplex (.up ℤ)).map σ)
    ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).map
        (integralOperationsRoosMap qE.inv) ≫
      (NatIso.mapHomologicalComplex t (.up ℤ)).hom.app (integralOperationsRoos CE.asFunctor) ≫
      scalarRoosMap (completedOrdinaryScalarExtension l E L ι W) CE.asFunctor ≫
      integralOperationsRoosMap a ≫ integralOperationsRoosMap τ ≫
      integralOperationsRoosMap qL.hom = scalarTensorChain l E L ι W P.obj Q.obj) :
  let A := integralComparisonDerivedSequenceScalar l E L ι W
  let T := coefficientSequenceLimit l L W
  let HL := (tensor l L W).obj ((scalar l E L ι W).obj C, (scalar l E L ι W).obj D)
  let χ := scalarCompletion l E L ι W
  let rL := (integralComparisonRoosBridge l L W ρL HL).hom
  let zL := DerivedCategory.Q.map (integralOperationsRoosFunctor.map qL.hom)
  let post := T.map y ≫ rL ≫ zL
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
  dsimp only
  let A := integralComparisonDerivedSequenceScalar l E L ι W
  let T := coefficientSequenceLimit l L W
  let TE' := coefficientSequenceLimit l E W
  let H := (tensor l E W).obj (C, D)
  let HL := (tensor l L W).obj ((scalar l E L ι W).obj C, (scalar l E L ι W).obj D)
  let εH := (integralComparisonSequenceScalarModel l E L ι W).ε.app H
  let χ := scalarCompletion l E L ι W
  let σ := ((comparisons l).sigma E L ι W).hom.app (C, D)
  let τ := HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
    (((coefficientSequenceRestriction l L W).mapHomologicalComplex (.up ℤ)).map σ)
  let rL := (integralComparisonRoosBridge l L W ρL HL).hom
  let zL := DerivedCategory.Q.map (integralOperationsRoosFunctor.map qL.hom)
  let post := T.map y ≫ rL ≫ zL
  let CE := ((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj H
  let SH := (scalar l E L ι W).obj H
  let γ := TE.realization.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
    TE'.map x
  let rE := integralComparisonRoosBridge l E W ρE H
  let zE := DerivedCategory.Q.mapIso (integralOperationsRoosFunctor.mapIso qE)
  have hγcomp : γ ≫ rE.hom ≫ zE.hom =
      (integralCompletedTensorComparison l E W).hom.app (P, Q) := by
    simpa only [γ, rE, zE, Functor.mapIso_hom, Category.assoc] using hTEcomp
  have hγ : γ = (integralCompletedTensorComparison l E W).hom.app (P, Q) ≫
      zE.inv ≫ rE.inv := by
    apply (cancel_mono (rE.hom ≫ zE.hom)).1
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.comp_id] using hγcomp
  have hAdj : SE.reduction.map γ ≫ SE.adjunction.counit.app (DerivedCategory.Q.obj H) =
      tensorReduction l E W SE ρE TE
        (DerivedCategory.Q.obj P.obj) (DerivedCategory.Q.obj Q.obj) ≫ x := by
    exact tensor_reduction_coordinate l E W SE ρE TE
      (DerivedCategory.Q.obj P.obj) (DerivedCategory.Q.obj Q.obj)
      (DerivedCategory.Q.obj H) x
  let O := integralOrdinaryDerivedScalar l E L ι W
  let dR := (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app
    (integralOperationsRoos CE.asFunctor)
  let start := DerivedCategory.Q.map
    (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).map
      (integralOperationsRoosMap qE.inv))
  let front := DerivedCategory.Q.map
    ((NatIso.mapHomologicalComplex t (.up ℤ)).hom.app (integralOperationsRoos CE.asFunctor) ≫
      scalarRoosMap (completedOrdinaryScalarExtension l E L ι W) CE.asFunctor ≫
      integralOperationsRoosMap a)
  have hsq := congrArg (fun f ↦ T.map f) hsquare
  simp only [Functor.map_comp] at hsq
  have ha := congrArg (fun f ↦ T.map (A.map f)) hAdj
  simp only [Functor.map_comp] at ha
  have hb : T.map (DerivedCategory.Q.map
      (((comparisons l).sigma E L ι W).hom.app (C, D))) ≫ rL =
    (integralComparisonRoosBridge l L W ρL SH).hom ≫
      DerivedCategory.Q.map (integralOperationsRoosMap τ) :=
    bridge_naturality l L W ρL σ
  have hn := SY.realization.hom.naturality γ
  dsimp only [Functor.comp_map] at hn
  have hχ := χ.naturality γ
  have hg := congrArg (fun f ↦ O.map f) hγ
  simp only [Functor.map_comp] at hg
  have hf := (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.naturality
    (integralOperationsRoosMap qE.inv)
  dsimp only [Functor.comp_map] at hf
  have ht' : start ≫ front ≫ DerivedCategory.Q.map (integralOperationsRoosMap τ) ≫ zL =
      DerivedCategory.Q.map (scalarTensorChain l E L ι W P.obj Q.obj) := by
    simpa only [start, front, zL, integralOperationsRoosFunctor,
      Functor.map_comp, Category.assoc] using
      congrArg (fun f ↦ DerivedCategory.Q.map f) hchain
  have hw := normalized_scalar_word
    (χ.app ((integralCompletedTensor l E W).obj
      (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)))
    (SY.realization.hom.app _)
    (T.map (A.map (tensorReduction l E W SE ρE TE
      (DerivedCategory.Q.obj P.obj) (DerivedCategory.Q.obj Q.obj))))
    (T.map (α.hom.app (SE.reduction.obj (DerivedCategory.Q.obj P.obj),
      SE.reduction.obj (DerivedCategory.Q.obj Q.obj))))
    (T.map y) rL zL (T.map (A.map x)) (T.map εH) (T.map (DerivedCategory.Q.map σ))
    (T.map (A.map (SE.reduction.map γ)))
    (T.map (A.map (SE.adjunction.counit.app (DerivedCategory.Q.obj H))))
    (integralComparisonRoosBridge l L W ρL SH).hom
    (DerivedCategory.Q.map (integralOperationsRoosMap τ))
    ((integralScalarExtension l E L ι W).map γ) (SY.realization.hom.app _)
    (O.map γ) (χ.app _)
    (O.map ((integralCompletedTensorComparison l E W).hom.app (P, Q)))
    (O.map zE.inv) (O.map rE.inv) dR front
    ((integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app
      ((integralOperationsTensorComplexFunctor l E W).obj (P.obj, Q.obj)))
    start (DerivedCategory.Q.map (scalarTensorChain l E L ι W P.obj Q.obj))
    hsq ha.symm hb hn.symm hχ.symm hg hCounit hf ht'
  simpa only [post, Functor.map_comp, Category.assoc] using hw

/-- Combine two reduction equations before applying the tensor functor. -/
private theorem paired_tensor_word {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟]
    (B : 𝒞 × 𝒞 ⥤ 𝒟) {x₁ x₂ y₁ y₂ z₁ z₂ w₁ w₂ u₁ u₂ : 𝒞} {v : 𝒟}
    (a₁ : x₁ ⟶ y₁) (a₂ : x₂ ⟶ y₂) (b₁ : y₁ ⟶ z₁) (b₂ : y₂ ⟶ z₂)
    (c₁ : z₁ ⟶ w₁) (c₂ : z₂ ⟶ w₂) (d₁ : x₁ ⟶ u₁) (d₂ : x₂ ⟶ u₂)
    (e₁ : u₁ ⟶ w₁) (e₂ : u₂ ⟶ w₂) (m : B.obj (w₁, w₂) ⟶ v)
    (h₁ : d₁ ≫ e₁ = a₁ ≫ b₁ ≫ c₁) (h₂ : d₂ ≫ e₂ = a₂ ≫ b₂ ≫ c₂) :
    B.map (Prod.mkHom a₁ a₂) ≫ B.map (Prod.mkHom b₁ b₂) ≫
        (B.map (Prod.mkHom c₁ c₂) ≫ m) =
      B.map (Prod.mkHom d₁ d₂) ≫ B.map (Prod.mkHom e₁ e₂) ≫ m := by
  simp only [← B.map_comp_assoc, CategoryTheory.prod_comp]
  rw [← h₁, ← h₂]

/-- The completed comparison is the ordinary comparison after cancelling its
source completion map. This is its defining normalization, without any
assertion about the system realization models. -/
private theorem scalarTensorCompleted_unitEquation (W : Scheme.{u})
    (M N : DerivedCategory (integralTowerModules.{u, u} l E W))
    (hM : IsSfDerivedComplete l E W M) (hN : IsSfDerivedComplete l E W N)
    (hT : IsSfDerivedComplete l E W ((integralCompletedTensor l E W).obj (M, N))) :
    (scalarCompletion l E L ι W).app
        ((integralCompletedTensor l E W).obj (M, N)) ≫
      (scalarTensorCompleted l E L ι W M N hM hN hT).hom =
    (scalarTensorOrdinary l E L ι W).hom.app (M, N) ≫
      (integralCompletedTensor l L W).map (Prod.mkHom
        ((scalarCompletion l E L ι W).app M)
        ((scalarCompletion l E L ι W).app N)) := by
  change (scalarCompletionIso l E L ι W _ hT).hom ≫
      ((scalarCompletionIso l E L ι W _ hT).inv ≫ _ ≫ _) = _
  rw [Iso.hom_inv_id_assoc]
  rfl

end WeilConjectures.ScalarExtensionTower
