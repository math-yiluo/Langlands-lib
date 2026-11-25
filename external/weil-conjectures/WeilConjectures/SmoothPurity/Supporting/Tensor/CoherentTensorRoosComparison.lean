/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerCore
import WeilConjectures.SmoothPurity.Supporting.NaturalCoherentTensorLevel
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections

/-! # The natural coherent tensor Roos comparison -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.all false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures
attribute [local irreducible] Functor.leftAdjoint HasDerivedCategory.standard
  coefficientSequenceRestriction scalarReductionExtension
  completedIntegralCommRingSheafUnrestricted
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local irreducible] coefficientTotalTensor pullbackTensorCalculus

/-- Combine coherent reduction, the K-flat tensor model and a strict tower comparison.
Source: Stacks 06YU, 08TC, 0941
(blueprint: def-pur-coherent-tensor-roos-comparison).
The product reduction model is followed by the inverse K-flat tensor model,
exact scalar restriction and the full Roos comparison. Whiskering the supplied
strict tower isomorphism gives the last factor. This constructs the entire natural
isomorphism, without invoking detection by finite projections. -/
def pullbackTensorCoherentTensorRoosComparison (W : Scheme.{u})
    (hR : ∀ P : (integralOperationsGoodComplex l E W).FullSubcategory,
      @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (ℕ × W.ProEt) (inferInstance : Category.{u} (ℕ × W.ProEt))
        (pullbackTensorSequenceSmall W)
        (coefficientSequenceTopology (ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)
        (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj P.obj))
    (t : (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).prod
      ((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ))) ⋙
      (coefficientTotalTensor.{u, u + 1, u} (coefficientSequenceTopology (ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)) ⋙ ((coefficientSequenceRestriction l E
      W).mapHomologicalComplex (.up ℤ)) ⋙ (HomologicalComplex.complexOfFunctorsToFunctorToComplex (T
      := ℕᵒᵖ) (V := integralTowerModules l E W) (c := .up ℤ)) ≅ integralOperationsTensorTowerFunctor
      l E W) :
    ((integralOperationsGoodLocalization l E W).prod
      (integralOperationsGoodLocalization l E W)) ⋙ (((pullbackTensorCalculus l E W).reduction.prod
      (pullbackTensorCalculus l E W).reduction) ⋙
    (pullbackTensorCalculus l E W).systemClosed.tensor ⋙ coefficientSequenceLimit l E W) ≅
      integralOperationsTensorOnGood l E W := by
  have r := Functor.isoWhiskerRight
      (coefficientSequenceRestriction l E W).mapDerivedCategoryFactors
      (coefficientConstantTowerLimit l E W) ≪≫
    Functor.isoWhiskerLeft ((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ))
      (pullbackTensorRoosModel l E W)
  have a := Functor.isoWhiskerRight
    (Functor.isoWhiskerRight
      (NatIso.prod (pullbackTensorReductionModel l E W) (pullbackTensorReductionModel l E W))
      (pullbackTensorCalculus l E W).systemClosed.tensor) (coefficientSequenceLimit l E W)
  have b := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft ((ObjectProperty.lift
    (CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (ProEt.topology W))
      (R := coefficientSequenceCommRingSheaf l E W))
    ((integralOperationsGoodComplex l E W).ι ⋙ ((pullbackTensorOrdinaryReduction l E
      W).mapHomologicalComplex (.up ℤ)))
    hR).prod (ObjectProperty.lift
    (CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (ProEt.topology W))
      (R := coefficientSequenceCommRingSheaf l E W))
    ((integralOperationsGoodComplex l E W).ι ⋙ ((pullbackTensorOrdinaryReduction l E
      W).mapHomologicalComplex (.up ℤ)))
    hR))
      (pullbackTensorCalculus l E W).systemTensorModel.comparison.symm)
    (coefficientSequenceLimit l E W)
  have c := Functor.isoWhiskerLeft
    (((integralOperationsGoodComplex l E W).ι.prod
      (integralOperationsGoodComplex l E W).ι) ⋙ (((pullbackTensorOrdinaryReduction l E
        W).mapHomologicalComplex (.up ℤ)).prod ((pullbackTensorOrdinaryReduction l E
        W).mapHomologicalComplex (.up ℤ))) ⋙ (coefficientTotalTensor.{u, u + 1, u}
        (coefficientSequenceTopology (ProEt.topology W)) (coefficientSequenceCommRingSheaf l E W)))
        r
  have d := Functor.isoWhiskerLeft
    ((integralOperationsGoodComplex l E W).ι.prod (integralOperationsGoodComplex l E W).ι)
    (Functor.isoWhiskerRight (Functor.isoWhiskerRight t integralOperationsRoosFunctor)
      DerivedCategory.Q)
  refine a ≪≫ ?_
  refine b ≪≫ ?_
  refine c ≪≫ ?_
  exact d

/-- The constructed natural comparison has its prescribed full Roos component.
Source: Stacks 06YU, 08TC, 0941
(blueprint: def-pur-coherent-tensor-roos-comparison).
Proof: evaluate the four whiskered natural isomorphisms. Their component formulas
are respectively reduction of the two factors, the inverse K-flat tensor model,
restriction followed by Roos, and the supplied strict tower comparison. -/
theorem pullbackTensorCoherentTensorRoosComparison_app (W : Scheme.{u})
    (hR : ∀ P : (integralOperationsGoodComplex l E W).FullSubcategory,
      @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (ℕ × W.ProEt) (inferInstance : Category.{u} (ℕ × W.ProEt))
        (pullbackTensorSequenceSmall W)
        (coefficientSequenceTopology (ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)
        (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj P.obj))
    (t : (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).prod
      ((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ))) ⋙
      (coefficientTotalTensor.{u, u + 1, u} (coefficientSequenceTopology (ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)) ⋙ ((coefficientSequenceRestriction l E
      W).mapHomologicalComplex (.up ℤ)) ⋙ (HomologicalComplex.complexOfFunctorsToFunctorToComplex (T
      := ℕᵒᵖ) (V := integralTowerModules l E W) (c := .up ℤ)) ≅ integralOperationsTensorTowerFunctor
      l E W)
    (P Q : (integralOperationsGoodComplex l E W).FullSubcategory) :
    (pullbackTensorCoherentTensorRoosComparison l E W hR t).app (P,Q) =
      (coefficientSequenceLimit l E W).mapIso
        ((pullbackTensorCalculus l E W).systemClosed.tensor.mapIso
          (Iso.prod ((pullbackTensorReductionModel l E W).app P)
            ((pullbackTensorReductionModel l E W).app Q))) ≪≫
      (coefficientSequenceLimit l E W).mapIso
        (CoefficientTensorModels.iso.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)
          (pullbackTensorCalculus l E W).systemClosed
          (pullbackTensorCalculus l E W).systemTensorModel
          (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj P.obj)
            (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj Q.obj) (hR
            P) (hR Q)).symm ≪≫
      ((coefficientConstantTowerLimit l E W).mapIso
        ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.app
          ((coefficientTotalTensor.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)).obj
          (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj P.obj,
            ((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj Q.obj))) ≪≫
        (pullbackTensorRoosModel l E W).app
          (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj
            ((coefficientTotalTensor.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)).obj
          (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj P.obj,
            ((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj Q.obj)))) ≪≫
      DerivedCategory.Q.mapIso
        (integralOperationsRoosFunctor.mapIso (t.app (P.obj,Q.obj))) := by
  apply Iso.ext
  rfl

private theorem pullbackTensorNaturality_of_components
    {C : Type*} [Category* C] {A B A' B' : C} {a : A ⟶ B} {b : A' ⟶ B'}
    {eA eA' : A ≅ A'} {eB eB' : B ≅ B'} (hA : eA = eA') (hB : eB = eB')
    (h : a ≫ eB'.hom = eA'.hom ≫ b) : a ≫ eB.hom = eA.hom ≫ b :=
  (congrArg (fun e : B ≅ B' ↦ a ≫ e.hom) hB).trans
    (h.trans (congrArg (fun e : A ≅ A' ↦ e.hom ≫ b) hA).symm)

attribute [local irreducible] pullbackTensorTensorLevelComparison
  integralOperationsTensorLevel in
private theorem pullbackTensorTowerNaturality_from_levelComparison (W : Scheme.{u})
    (e : ∀ P Q : CochainComplex (integralTowerModules l E W) ℤ,
      pullbackTensorRestrictedTower l E W
        ((coefficientTotalTensor.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)).obj
          ((((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj P),
            (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj Q))) ≅
        (integralOperationsTensorTowerFunctor l E W).obj (P,Q))
    (he : ∀ P Q n, (e P Q).app (op n) =
      (pullbackTensorTensorLevelComparison l E W n).app (P,Q))
    {P Q : CochainComplex (integralTowerModules l E W) ℤ ×
      CochainComplex (integralTowerModules l E W) ℤ} (g : P ⟶ Q) :
    HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
        (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).map
          ((coefficientTotalTensor.{u, u + 1, u}
            (coefficientSequenceTopology (ProEt.topology W))
            (coefficientSequenceCommRingSheaf l E W)).map
            ((((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).prod
              ((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ))).map g))) ≫
      (e Q.1 Q.2).hom =
    (e P.1 P.2).hom ≫
      (integralOperationsTensorTowerFunctor l E W).map g := by
  apply NatTrans.ext
  funext n
  obtain ⟨n⟩ := n
  exact pullbackTensorNaturality_of_components (he P.1 P.2 n) (he Q.1 Q.2 n)
    ((pullbackTensorTensorLevelComparison l E W n).hom.naturality g)

attribute [local semireducible] coefficientTotalTensor in
private theorem pullbackTensorSequenceKFlat_of_evaluations (W : Scheme.{u})
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (hC : ∀ n : ℕ, CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n)
      (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C)) :
    CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf l E W) C := by
  let R := coefficientSequenceCommRingSheaf l E W
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  let D := (SemilinearSections.semilinearDerivedSections.{u + 1, u, u}
    (ProEt.topology W) (integralCoefficientCommRingSheaf l E W)
    (coefficientSequenceCommRingTransition l E W)).some.systems
  intro Z hZ i
  apply (D.componentwise _).2
  intro n
  have hZn : (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex
      (.up ℤ)).obj Z).Acyclic := by
    intro j
    exact (hZ j).map (coefficientSequenceEvaluation l E W n)
  exact (hC n _ hZn i).of_iso (coefficientEvaluationTensorIso l E W n Z C).symm

end WeilConjectures
