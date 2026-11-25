/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientEvaluationTensorNaturality
import all WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorEvaluationUnit

/-! # Inverse evaluation of total unit generators

Source: Stacks Tags 07A4, 0941 and 03D2.
(blueprint: lem-pur-completed-pullback-tensor-evaluation-inverse-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures

attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  pullbackTensorSequenceInverse pullbackTensorSystemComparison
  pullbackTensorInverseEvaluationComplex finitePullbackTensorConstruction
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  pullbackTensorCalculus pullbackTensorSequenceDerived

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  Scheme.coefficientProEtaleModuleAdjunction Scheme.coefficientProEtaleModulePullback

attribute [local instance] sfIntrinsicPullback_additive

attribute [local implicit_reducible] integralOperationsLevelPullback
  pullbackTensorSequenceDirect coefficientSequenceEvaluation pullbackTensorSequenceBase
  pullbackTensorSequenceCochain

attribute [local irreducible] coefficientTotalTensor coefficientTensorGenerator
  sfIntrinsicPullback coefficientSequenceEvaluation coefficientEvaluationTensorIso
  coefficientSequenceCommRingSheaf coefficientSequenceCommRingPresheaf
  coefficientSequenceCommRingSystem coefficientSequenceTopology
  SheafOfModules.monoidalCategory

-- Pointwise section transports of the two adjunctions have large implicit types.
/-- Inverse evaluation transports finite unit generators to evaluated sequence units.
Source: Stacks Tags 07A4, 0941 and 03D2
(blueprint: lem-pur-completed-pullback-tensor-evaluation-inverse-unit).
Proof: naturality moves the inverse tensor-evaluation map through the intrinsic
unit. The generator normalization identifies its inverse image with the evaluated
sequence tensor generator. The ordinary evaluation-mate unit formula identifies
the preimage under the inverse mate with the evaluated sequence adjunction unit.
This computes only the source unit, before either tensor comparison is applied.
-/
theorem completedPullbackTensor_evaluation_inverse_unit {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ)
    (c : integralOperationsLevelPullback l E f n ≅
      sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f)
    (hc : ∀ (A : normalizedDVRModules l E Y n) (U : Y.ProEt)
      (x : A.val.obj (op U)),
      (c.hom.app A).val.app (op ((proEtaleBaseChange f).obj U))
        (((coefficientProEtaleModuleAdjunction.{u, u} f
          (CommRingCat.of (ULift.{u + 1}
            (finiteCoefficientRing l E (n + 1))))).unit.app A).val.app (op U) x) =
      ((sfIntrinsicConstantModuleAdjunction f
        (finiteCoefficientRing l E (n + 1))).unit.app A).val.app (op U) x)
    (P Q : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (p q i : ℤ) (hpq : p + q = i) (U : Y.ProEt)
    (x : (P.X p).val.obj (op (n, U))) (y : (Q.X q).val.obj (op (n, U))) :
    let F : CochainComplex (coefficientSequenceModules l E Y) ℤ ⥤
        CochainComplex (coefficientSequenceModules l E X) ℤ :=
      (pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)
    let V : CochainComplex (coefficientSequenceModules l E Y) ℤ ⥤
        CochainComplex (normalizedDVRModules l E Y n) ℤ :=
      (coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)
    let W : CochainComplex (coefficientSequenceModules l E X) ℤ ⥤
        CochainComplex (normalizedDVRModules l E X n) ℤ :=
      (coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)
    let G : CochainComplex (normalizedDVRModules l E Y n) ℤ ⥤
        CochainComplex (normalizedDVRModules l E X n) ℤ :=
      (sfIntrinsicPullback
        (finiteCoefficientRing l E (n + 1)) f).mapHomologicalComplex (.up ℤ)
    let tY := coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (ProEt.topology Y)) (coefficientSequenceCommRingSheaf l E Y)
    let tY' := coefficientTotalTensor.{u, u + 1, u}
      (ProEt.topology Y) (integralCoefficientCommRingSheaf l E Y n)
    let d (A : CochainComplex (coefficientSequenceModules l E Y) ℤ) :
        W.obj (F.obj A) ≅ G.obj (V.obj A) :=
      (pullbackTensorInverseEvaluationComplex l E f n).symm.app A ≪≫
        (NatIso.mapHomologicalComplex c (.up ℤ)).app (V.obj A)
    let v : V.obj (tY.obj (P, Q)) ≅ tY'.obj (V.obj P, V.obj Q) :=
      coefficientEvaluationTensorIso l E Y n P Q
    let sg := coefficientTensorGenerator.{u, u + 1, u}
      (coefficientSequenceTopology (ProEt.topology Y))
      (coefficientSequenceCommRingSheaf l E Y) P Q p q i hpq (op (n, U)) x y
    let gen := coefficientTensorGenerator.{u, u + 1, u}
      (ProEt.topology Y) (integralCoefficientCommRingSheaf l E Y n)
      (V.obj P) (V.obj Q) p q i hpq (op U)
      (coefficientEvaluationSection l E Y (P.X p) n (op U) x)
      (coefficientEvaluationSection l E Y (Q.X q) n (op U) y)
    ((d (tY.obj (P, Q))).inv.f i).val.app (op ((proEtaleBaseChange f).obj U))
      (((G.map v.inv).f i).val.app (op ((proEtaleBaseChange f).obj U))
        (((sfIntrinsicConstantModuleAdjunction f
          (finiteCoefficientRing l E (n + 1))).unit.app _).val.app (op U) gen)) =
    coefficientEvaluationSection l E X
      ((pullbackTensorSequenceInverse l E f).obj ((tY.obj (P, Q)).X i)) n
      (op ((proEtaleBaseChange f).obj U))
      (((pullbackTensorSequenceAdjunction l E f).unit.app
        ((tY.obj (P, Q)).X i)).val.app (op (n, U)) sg) := by
  intro F V W G tY tY' d v sg gen
  change ((d (tY.obj (P, Q))).inv.f i).val.app _
    (((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).map
      (v.inv.f i)).val.app _
      (((sfIntrinsicConstantModuleAdjunction f
        (finiteCoefficientRing l E (n + 1))).unit.app _).val.app (op U) gen)) = _
  erw [intrinsic_unit_map l E f n (v.inv.f i) U]
  have hv := pullbackTensorEvaluationTensor_generator_cast l E Y n P Q p q i hpq (op U) x y
  have hvi := cochainIso_inv_section v i (op U) _ _ hv
  erw [hvi]
  have hdu := evaluation_complex_unit l E f n c hc (tY.obj (P, Q)) i U sg
  change ((d (tY.obj (P, Q))).hom.f i).val.app (op ((proEtaleBaseChange f).obj U))
      (coefficientEvaluationSection l E X
        ((pullbackTensorSequenceInverse l E f).obj ((tY.obj (P, Q)).X i)) n
        (op ((proEtaleBaseChange f).obj U))
        (((pullbackTensorSequenceAdjunction l E f).unit.app
          ((tY.obj (P, Q)).X i)).val.app (op (n, U)) sg)) = _ at hdu
  exact cochainIso_inv_section (d (tY.obj (P, Q))) i
    (op ((proEtaleBaseChange f).obj U)) _ _ hdu

end WeilConjectures
