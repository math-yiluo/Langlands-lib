/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryQuotientModel
public import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryReductionTensorGeneric

/-! # Tensor presentations of the ordinary quotient system

Source: Stacks 03EK, 07A4 and 0941.

For an ordinary quotient-system model `M`, the finite evaluations of the system tensor
product of `M.quotient P` and `M.quotient Q` are identified with the finite scalar
extensions of the total tensor product of `P` and `Q`. These identifications commute
with the strict transition maps. The section calculation is the generic
`OrdinaryReductionTensor.tensorPresentation_transition`.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
namespace OrdinaryQuotient

noncomputable section
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

attribute [local irreducible] coefficientFiniteQuotientExistence
  coefficientFiniteQuotientDerivedExistence coefficientFiniteQuotientModel
  coefficientFiniteQuotientExtension coefficientFiniteQuotientUnitSection
  SheafOfModules.monoidalCategory scalarReductionExistence scalarReductionDerivedExistence
  scalarReductionExtension coefficientFiniteQuotientDerived HasDerivedCategory.standard
  CoefficientClosedStructure.tensor coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem
  coefficientSequenceTopology constantSheaf coefficientSequenceEvaluation

attribute [local implicit_reducible] integralCoefficientSheaf
  integralCoefficientCommRingSheaf CategoryTheory.sheafCompose
  CommRingCat.hasForgetToRingCat

attribute [local irreducible] coefficientTotalTensor coefficientTensorGenerator

/-- The strict transition on sections is horizontal restriction.
Source: Stacks 0941. -/
theorem coefficientSequenceTransition_section {m n : ℕ} (h : n ≤ m)
    (M : coefficientSequenceModules l E W) (U : W.ProEtᵒᵖ) (x : M.val.obj (op (m, U.unop))) :
    coefficientRestrictionSection (normalizedDVRQuotient l E W h)
      ((coefficientSequenceEvaluation l E W n).obj M) U
      (((coefficientSequenceTransition l E W h).app M).val.app U
        (coefficientEvaluationSection l E W M m U x)) =
      coefficientEvaluationSection l E W M n U
        (M.val.presheaf.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x) := by
  have hh := (coefficientSequenceTransition_exists l E W h).exists.choose_spec M U
  exact OrdinaryReductionTensor.transported_transition_section (normalizedDVRQuotient l E W h)
    (coefficientSequenceEvaluation l E W m) (coefficientSequenceEvaluation l E W n)
    (coefficientSequenceTransition l E W h) M U
    (coefficientSequenceEvaluationAb_eq l E W M m U)
    (coefficientSequenceEvaluationAb_eq l E W M n U) _ hh x

/-- Evaluation sections exhaust the sections of a finite evaluation.
Source: Stacks 0941. -/
theorem coefficientEvaluationSection_surjective (M : coefficientSequenceModules l E W) (n : ℕ)
    (U : W.ProEtᵒᵖ) : Function.Surjective (coefficientEvaluationSection l E W M n U) :=
  OrdinaryReductionTensor.eqToHom_surjective
    (coefficientSequenceEvaluationAb_eq l E W M n U).symm

/-- The strict quotient map is the mate of the composition of restrictions.
Source: Stacks 03D7, 06YY. -/
theorem coefficientOrdinaryQuotient_app_eq {m n : ℕ} (h : n ≤ m)
    (X : scalarReductionSource l E W) :
    (coefficientOrdinaryQuotient l E W h).app X =
      (coefficientQuotientNatTrans (coefficientOrdinaryScalarAdjunction l E W m)
        (coefficientOrdinaryScalarAdjunction l E W n)
        (normalizedDVRModuleRes l E W h)
        (eqToIso (coefficientRestrictionComp l E W h))).app X := by
  unfold coefficientOrdinaryQuotient
  exact (coefficientOrdinaryQuotient_exists l E W h).choose_spec.1 X

/-- The completed coefficient projection, with its target the finite coefficient sheaf.
Source: Stacks 0941. -/
abbrev completedProjection (n : ℕ) :
    SheafOfModules.derivedChangeRingIndependentCoefficients (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W) ⟶ integralCoefficientSheaf l E W n :=
  (sheafCompose (Scheme.ProEt.topology W)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      (completedIntegralCommRingProjectionUnrestricted l E W n)

/-- The strict quotient map is the mate of the composition of restrictions.
Source: Stacks 03D7, 06YY. -/
theorem coefficientOrdinaryQuotient_mateLaw {m n : ℕ} (h : n ≤ m) :
    OrdinaryReductionTensor.QuotientMateLaw (coefficientOrdinaryScalarAdjunction l E W m)
      (coefficientOrdinaryScalarAdjunction l E W n) (eqToIso (coefficientRestrictionComp l E W h))
      (coefficientOrdinaryQuotient l E W h) :=
  ⟨coefficientOrdinaryQuotient_app_eq l E W h⟩

/-- The strict quotient map sends unit sections to unit sections.
Source: Stacks 03D7, 06YY. -/
theorem coefficientOrdinaryQuotient_unitLaw {m n : ℕ} (h : n ≤ m) :
    OrdinaryReductionTensor.QuotientUnitLaw
      ((sheafCompose (Scheme.ProEt.topology W)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
          (completedIntegralCommRingProjectionUnrestricted l E W m))
      ((sheafCompose (Scheme.ProEt.topology W)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
          (completedIntegralCommRingProjectionUnrestricted l E W n))
      (coefficientOrdinaryQuotient l E W h) (coefficientOrdinaryScalarAdjunction l E W m)
      (coefficientOrdinaryScalarAdjunction l E W n) :=
  OrdinaryReductionTensor.quotientUnitLaw_of_mateLaw (completedProjection l E W m)
    (normalizedDVRQuotient l E W h) (completedProjection l E W n)
    (coefficientRestrictionComp l E W h) (coefficientOrdinaryScalarAdjunction l E W m)
    (coefficientOrdinaryScalarAdjunction l E W n) (coefficientOrdinaryQuotient l E W h)
    (coefficientOrdinaryQuotient_mateLaw l E W h)

/-- The unit-section formula characterizing the ordinary scalar tensor comparison.
Source: Stacks 03EK, 07A4. -/
theorem coefficientScalarTensorIso_generators (n : ℕ)
    (P Q : CochainComplex (scalarReductionSource l E W) ℤ) :
    CoefficientScalarTensorGenerators.{u, t + 1, t} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)
      (integralCoefficientCommRingSheaf l E W n) (scalarReductionExtension l E W n)
      (hF := coefficientFiniteExtensionAdditive l E W n)
      (coefficientIntegralScalarUnitSection l E W n) P Q
      (coefficientScalarTensorIso l E W n P Q) := by
  unfold coefficientScalarTensorIso coefficientUniqueComparisonChoice
  exact (coefficientScalarTensorIso_exists l E W n P Q).choose_spec.1

/-- The generator formula characterizing the ordinary evaluation tensor comparison.
Source: Stacks 03EK, 0941. -/
theorem coefficientEvaluationTensorIso_generator (n : ℕ)
    (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (p q k : ℤ) (h : p + q = k) (U : W.ProEtᵒᵖ)
    (x : (P.X p).val.obj (op (n, U.unop))) (y : (Q.X q).val.obj (op (n, U.unop))) :
    ((coefficientEvaluationTensorIso l E W n P Q).hom.f k).val.app U
      (coefficientEvaluationSection l E W _ n U
        (coefficientTensorGenerator.{u, t + 1, t}
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W) P Q p q k h (op (n, U.unop)) x y)) =
      coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)
        (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj P)
        (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj Q) p q k h U
        (coefficientEvaluationSection l E W (P.X p) n U x)
        (coefficientEvaluationSection l E W (Q.X q) n U y) := by
  unfold coefficientEvaluationTensorIso coefficientUniqueComparisonChoice
  exact (coefficientEvaluationTensorIso_exists l E W n P Q).choose_spec.1 p q k h U x y

/-- The finite presentation of the system tensor product of two ordinary quotient systems.
Source: Stacks 03EK, 07A4 and 0941. -/
def OrdinaryModel.tensorPresentation (M : OrdinaryModel l E W) (n : ℕ)
    (P Q : CochainComplex (scalarReductionSource l E W) ℤ) :
    ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj
        ((coefficientTotalTensor.{u, t + 1, t}
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)).obj
            ((M.quotient l E W).obj P, (M.quotient l E W).obj Q)) ≅
      ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj
        ((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)) :=
  coefficientEvaluationTensorIso l E W n _ _ ≪≫
    (coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n)).mapIso
      (((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).app P).prod
        ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).app Q)) ≪≫
    (coefficientScalarTensorIso l E W n P Q).symm

-- Instantiating the generic calculation checks several large coefficient interfaces.
/-- The finite presentations of a system tensor product commute with strict transitions.
Source: Stacks 03EK, 07A4 and 0941. -/
theorem OrdinaryModel.tensorPresentation_transition (M : OrdinaryModel l E W)
    (P Q : CochainComplex (scalarReductionSource l E W) ℤ) {m n : ℕ} (h : n ≤ m) :
    (NatTrans.mapHomologicalComplex (coefficientSequenceTransition l E W h) (.up ℤ)).app
        ((coefficientTotalTensor.{u, t + 1, t}
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)).obj
            ((M.quotient l E W).obj P, (M.quotient l E W).obj Q)) ≫
      ((normalizedDVRModuleRes l E W h).mapHomologicalComplex (.up ℤ)).map
        (M.tensorPresentation l E W n P Q).hom =
    (M.tensorPresentation l E W m P Q).hom ≫
      (NatTrans.mapHomologicalComplex (coefficientOrdinaryQuotient l E W h) (.up ℤ)).app
        ((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)) := by
  exact OrdinaryReductionTensor.tensorPresentation_transition
    (hEm := coefficientFiniteExtensionAdditive l E W m)
    (hEn := coefficientFiniteExtensionAdditive l E W n)
    (hevm := coefficientSequenceEvaluation_additiveInstance l E W m)
    (hevn := coefficientSequenceEvaluation_additiveInstance l E W n)
    ((sheafCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        (completedIntegralCommRingProjectionUnrestricted l E W m))
    ((sheafCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        (completedIntegralCommRingProjectionUnrestricted l E W n))
    (normalizedDVRQuotient l E W h)
    (coefficientOrdinaryScalarAdjunction l E W m) (coefficientOrdinaryScalarAdjunction l E W n)
    (coefficientOrdinaryQuotient l E W h) (coefficientOrdinaryQuotient_unitLaw l E W h)
    (coefficientSequenceTransition l E W h) h
    (fun N U x ↦ coefficientEvaluationSection l E W N m U x)
    (fun N U x ↦ coefficientEvaluationSection l E W N n U x)
    (fun N U ↦ coefficientEvaluationSection_surjective l E W N m U)
    (coefficientSequenceTransition_section l E W h) P Q
    ((M.quotient l E W).obj P) ((M.quotient l E W).obj Q)
    ((NatIso.mapHomologicalComplex (M.evaluation m) (.up ℤ)).app P)
    ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).app P)
    ((NatIso.mapHomologicalComplex (M.evaluation m) (.up ℤ)).app Q)
    ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).app Q)
    (fun p ↦ M.transition (P.X p) h) (fun p ↦ M.transition (Q.X p) h)
    (coefficientEvaluationTensorIso l E W m _ _)
    (coefficientEvaluationTensorIso_generator l E W m _ _)
    (coefficientEvaluationTensorIso l E W n _ _)
    (coefficientEvaluationTensorIso_generator l E W n _ _)
    (coefficientScalarTensorIso l E W m P Q) (coefficientScalarTensorIso_generators l E W m P Q)
    (coefficientScalarTensorIso l E W n P Q) (coefficientScalarTensorIso_generators l E W n P Q)

end
end OrdinaryQuotient
end WeilConjectures
