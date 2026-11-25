/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
public import WeilConjectures.SixFunctors.Tensor.TensorReductionStrictComparison
import WeilConjectures.SixFunctors.Tensor.TensorReductionCanonicalFiniteTransport
import WeilConjectures.SixFunctors.Tensor.TensorReductionCanonicalPresentation

/-! # Canonical representative square for coherent reduction tensor

Source: Stacks 07A4, 07A6 and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option cleanup.letToHave false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  completedIntegralCommRingSheafUnrestricted completedIntegralCoefficientSheafUnrestricted
  coefficientTotalTensor CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory pullbackTensorCalculus
attribute [local irreducible] pullbackTensorReductionModel pullbackTensorSystemModel
attribute [local implicit_reducible] integralOperationsGoodLocalization
  integralOperationsGoodComplex
  coefficientIntegralTensorModelIso coefficientSystemTensorModelIso
  coefficientKFlatInclusion CoefficientTensorModels.iso
  scalarReductionSourceDerived scalarReductionTargetDerived coefficientSequenceHasDerived
  coefficientFiniteHasDerived coefficientConstantTowerDerived
  unrestrictedIntegralReductionFunctor integralCoefficientSheaf integralCoefficientCommRingSheaf
attribute [local implicit_reducible] pullbackTensorOrdinaryLimit pullbackTensorConstantLimit
  coefficientConstantTowerLimit coefficientSequenceLimit
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The finite-component predicate used to identify the strict assembled map. -/
def tensorReductionFiniteProperty (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ)
    (ψ : ((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj
      ((coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)) ⟶
      (coefficientTotalTensor.{u, u + 1, u}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)).obj
        (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj P,
          ((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj Q)) : Prop :=
  ∀ n : ℕ,
    ((SheafOfModules.systemSequenceEvaluation.{u + 1, u, u + 1}
      (coefficientSequenceCommRingSystem l E W) n).mapHomologicalComplex (.up ℤ)).map ψ =
      ((SheafOfModules.systemSequenceEvaluation.{u + 1, u, u + 1}
        (coefficientSequenceCommRingSystem l E W) n).mapHomologicalComplex (.up ℤ)).map
        (tensorReductionStrictMap l E W P Q)

private theorem map_pair_comp
    {C D H : Type*} [Category C] [Category D] [Category H]
    (T : C × D ⥤ H) {P Q R : C} {P' Q' R' : D}
    (a : P ⟶ Q) (b : P' ⟶ Q') (c : Q ⟶ R) (d : Q' ⟶ R') :
    T.map (Prod.mkHom (a ≫ c) (b ≫ d)) =
      T.map (Prod.mkHom a b) ≫ T.map (Prod.mkHom c d) :=
  T.map_comp (Prod.mkHom a b) (Prod.mkHom c d)

private theorem square_transport
    {A B : Type*} [Category A] [Category B]
    (L : A ⥤ B) (U : A × A ⥤ A) (F : B × B ⥤ B)
    {GP GQ GT C D Z : A} {RP RQ RT : B}
    (aC : GP ≅ C) (aD : GQ ≅ D) (aZ : GT ≅ Z)
    (eC : RP ≅ L.obj C) (eD : RQ ≅ L.obj D) (eZ : RT ≅ L.obj Z)
    (mP : RP ⟶ L.obj GP) (mQ : RQ ⟶ L.obj GQ) (mT : RT ⟶ L.obj GT)
    (mCD : L.obj (U.obj (C, D)) ⟶ F.obj (L.obj C, L.obj D))
    (mGP : L.obj (U.obj (GP, GQ)) ⟶ F.obj (L.obj GP, L.obj GQ))
    (y : RT ⟶ F.obj (RP, RQ)) (ψ : Z ⟶ U.obj (C, D))
    (hc : mP ≫ L.map aC.hom = eC.hom)
    (hd : mQ ≫ L.map aD.hom = eD.hom)
    (hz : mT ≫ L.map aZ.hom = eZ.hom)
    (hn : mCD ≫ F.map (Prod.mkHom (L.map aC.inv) (L.map aD.inv)) =
      L.map (U.map (Prod.mkHom aC.inv aD.inv)) ≫ mGP)
    (hs : y ≫ F.map (Prod.mkHom eC.hom eD.hom) =
      eZ.hom ≫ L.map ψ ≫ mCD) :
    y ≫ F.map (Prod.mkHom mP mQ) =
      mT ≫ L.map (aZ.hom ≫ ψ ≫ U.map (Prod.mkHom aC.inv aD.inv)) ≫ mGP := by
  have hep : eC.hom ≫ L.map aC.inv = mP := by
    rw [← hc, Category.assoc, ← L.map_comp, aC.hom_inv_id, L.map_id, Category.comp_id]
  have heq : eD.hom ≫ L.map aD.inv = mQ := by
    rw [← hd, Category.assoc, ← L.map_comp, aD.hom_inv_id, L.map_id, Category.comp_id]
  have h := congrArg (fun f ↦ f ≫
    F.map (Prod.mkHom (L.map aC.inv) (L.map aD.inv))) hs
  simp only [Category.assoc] at h
  rw [← map_pair_comp, hep, heq, hn, ← hz] at h
  simpa only [L.map_comp, Category.assoc] using h

attribute [local irreducible] coefficientSequenceRestriction scalarReductionExtension
  coefficientScalarTensorIso coefficientEvaluationTensorIso
attribute [local implicit_reducible] pullbackTensorReductionEvaluationComplex

/-- The normalized reduction tensor square admits a representative map before
selecting the uniquely assembled strict map.

Source: Stacks 07A4 and 07A6; transport of the simultaneous representative normalization.
(blueprint: lem-coef-tensor-reduction-canonical-square). -/
theorem tensorReductionCanonicalSquare_exists (W : Scheme.{u})
    (P Q : (integralOperationsGoodComplex l E W).FullSubcategory)
    (hT : integralOperationsGoodComplex l E W
      ((coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)).obj (P.obj, Q.obj))) :
    let S := pullbackTensorCalculus l E W
    let T := (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).obj (P.obj, Q.obj)
    let G := (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
    let B := (coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)).obj (G.obj P.obj, G.obj Q.obj)
    ∃ ψ : G.obj T ⟶ B,
      S.reduction.map ((S.integralTensorModel.iso (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W) S.integralClosed
          P.obj Q.obj P.property.1 Q.property.1).hom) ≫
        S.reductionTensor.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
        S.systemClosed.tensor.map
          (Prod.mkHom ((pullbackTensorReductionModel l E W).hom.app P)
            ((pullbackTensorReductionModel l E W).hom.app Q)) =
      (pullbackTensorReductionModel l E W).hom.app ⟨T, hT⟩ ≫
        DerivedCategory.Q.map ψ ≫
        (pullbackTensorSystemModel l E W _ _
          (pullbackTensorReductionGood l E W P)
          (pullbackTensorReductionGood l E W Q)).hom ∧
      tensorReductionFiniteProperty l E W P.obj Q.obj ψ := by
  dsimp only
  let S := pullbackTensorCalculus l E W
  let T : CochainComplex (integralTowerModules l E W) ℤ :=
    (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)).obj (P.obj, Q.obj)
  let G := (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
  let U : CochainComplex (coefficientSequenceModules l E W) ℤ ×
      CochainComplex (coefficientSequenceModules l E W) ℤ ⥤
      CochainComplex (coefficientSequenceModules l E W) ℤ :=
    coefficientTotalTensor.{u, u + 1, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W)
  have hn := S.reductionTensor_normalization P.obj Q.obj P.property.1 Q.property.1
    P.property.2 Q.property.2
  obtain ⟨C, D, Z, hC, hD, eC, eD, eZ, κC, κD, κZ, ψ,
    ⟨_hPC, _hPCt, hc⟩, ⟨_hPD, _hPDt, hd⟩, ⟨_hPZ, _hPZt, hz⟩, hfinite, hsquare⟩ := hn
  obtain ⟨aC, heC, haC⟩ := tensorReductionCanonicalPresentation l E W P C eC κC hc
  obtain ⟨aD, heD, haD⟩ := tensorReductionCanonicalPresentation l E W Q D eD κD hd
  obtain ⟨aZ, heZ, haZ⟩ := tensorReductionCanonicalPresentation l E W ⟨T, hT⟩ Z eZ κZ hz
  let φ : G.obj T ⟶ U.obj (G.obj P.obj, G.obj Q.obj) :=
    aZ.hom ≫ ψ ≫ U.map (Prod.mkHom aC.inv aD.inv)
  refine ⟨φ, ?_, ?_⟩
  · have hmodel :
        (coefficientSystemTensorModelIso l E W S.toCoefficientDerivedSystemTensors
          C D hC hD).hom ≫
          S.systemClosed.tensor.map
            (Prod.mkHom (DerivedCategory.Q.map aC.inv) (DerivedCategory.Q.map aD.inv)) =
        DerivedCategory.Q.map (U.map (Prod.mkHom aC.inv aD.inv)) ≫
          (pullbackTensorSystemModel l E W _ _
            (pullbackTensorReductionGood l E W P)
            (pullbackTensorReductionGood l E W Q)).hom := by
      have hn := (S.systemTensorModel.comparison.hom.naturality
        (Prod.mkHom
          (ObjectProperty.homMk (X := ⟨C, hC⟩)
            (Y := ⟨G.obj P.obj, pullbackTensorReductionGood l E W P⟩) aC.inv)
          (ObjectProperty.homMk (X := ⟨D, hD⟩)
            (Y := ⟨G.obj Q.obj, pullbackTensorReductionGood l E W Q⟩) aD.inv))).symm
      with_unfolding_all exact hn
    dsimp only [CoefficientTensorComparisonSquare] at hsquare
    rw [← Category.assoc] at hsquare
    have hs := square_transport DerivedCategory.Q U S.systemClosed.tensor
      aC aD aZ eC eD eZ
      ((pullbackTensorReductionModel l E W).hom.app P)
      ((pullbackTensorReductionModel l E W).hom.app Q)
      ((pullbackTensorReductionModel l E W).hom.app ⟨T, hT⟩)
      (coefficientSystemTensorModelIso l E W S.toCoefficientDerivedSystemTensors
        C D hC hD).hom
      (pullbackTensorSystemModel l E W _ _
        (pullbackTensorReductionGood l E W P)
        (pullbackTensorReductionGood l E W Q)).hom
      _ ψ heC heD heZ hmodel hsquare
    simp only [Category.assoc] at hs ⊢
    with_unfolding_all exact hs
  · exact tensorReductionCanonicalFiniteTransport l E W P.obj Q.obj C D Z aC aD aZ
      κC κD κZ ψ hfinite haC haD haZ

end WeilConjectures
