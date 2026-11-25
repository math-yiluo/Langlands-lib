/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedReductionModels
import WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedSequenceSemilinear
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearCartesianProjection
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarDataExistence
import all WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedEvaluationTensorChain
import all WeilConjectures.SixFunctors.Supporting.SemilinearTotalTensorEvaluation
import all WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearTensorEvaluation

/-! # Components of normalized coefficient evaluation projection

Source: Stacks 07A4, 08J9 and 0941; Zheng Construction 4.1.
(blueprint: lem-coef-normalized-evaluation-projection-components).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u a b
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

attribute [local implicit_reducible] CategoryTheory.uniformProd
  coefficientSequenceCommRingSheaf SemilinearSections.systemRing
  integralCoefficientSheaf integralCoefficientCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem
  coefficientSequenceCommRingTransition coefficientSequenceEvaluation
  SemilinearSections.evaluation SemilinearSections.ringPresheaf SemilinearSections.rings
  CategoryTheory.sheafCompose CommRingCat.hasForgetToRingCat
  integralReductionTargetHasDerivedCategory coefficientFiniteHasDerived
  coefficientSequenceHasDerived
attribute [local irreducible] DerivedCategory _root_.instCategoryDerivedCategory
  DerivedCategory.Q DerivedCategory.Qh HasDerivedCategory.standard
  coefficientTotalTensor coefficientTensorGenerator CoefficientClosedStructure.tensor
  SheafOfModules.instPreadditive HomologicalComplex.instPreadditive
  SheafOfModules.monoidalCategory
  coefficientIntegralTensorModelIso coefficientFiniteTensorModelIso
  coefficientSystemTensorModelIso coefficientScalarTensorIso coefficientEvaluationTensorIso
  CoefficientTensorModels.iso coefficientEvaluationSection SemilinearSections.evalSection
  constantSheaf presheafToSheaf Functor.ofSequence Functor.ofOpSequence
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

-- Reuse already typed coefficient-site arguments; Lean's kernel checks the result.
local elab "kernel_exact " t:term : tactic => Lean.Elab.Tactic.withMainContext do
  let e ← Lean.Elab.Term.elabTerm t none
  (← Lean.Elab.Tactic.getMainGoal).assign e
  Lean.Elab.Tactic.replaceMainGoal []

attribute [local instance] coefficientSequenceEvaluation_additive

attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian in
private theorem total_eq (n : ℕ)
    (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    evaluationTotalIso.{t + 1, t, u} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W)
      (coefficientSequenceCommRingTransition l E W) n P Q =
        coefficientEvaluationTensorIso l E W n P Q := by
  apply (coefficientEvaluationTensorIso_exists l E W n P Q).unique
  · kernel_exact evaluationTotal_forward.{t + 1, t, u} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W)
      (coefficientSequenceCommRingTransition l E W) n
      (fun M U x ↦ coefficientEvaluationSection l E W M n U x)
      (evaluationSection_heq l E W n) P Q
  · unfold coefficientEvaluationTensorIso coefficientUniqueComparisonChoice
    exact (coefficientEvaluationTensorIso_exists l E W n P Q).choose_spec.1

private theorem inverseSquare
    {A : Type a} [Category.{b} A] {X₀ X₁ X₂ X₃ X₄ X₅ : A}
    (a : X₀ ≅ X₁) (b : X₁ ≅ X₂) (c : X₂ ≅ X₃) (d : X₃ ≅ X₄)
    (e : X₅ ≅ X₄) (z : X₀ ≅ X₅)
    (h : a.hom ≫ b.hom ≫ c.hom = z.hom ≫ e.hom ≫ d.inv)
    (e' : X₅ ≅ X₄) (he : e = e') :
    d.inv ≫ c.inv ≫ b.inv ≫ a.inv ≫ z.hom = e'.inv := by
  have h' := congrArg (fun f ↦ f ≫ d.hom ≫ e.inv) h
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id] at h'
  exact (SemilinearSections.inverseChain a b c d e.inv z.hom h').trans
    (congrArg Iso.inv he)

attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian in
private noncomputable def evaluationModel
    (R : CoefficientDerivedSystemReduction l E W)
    (hE : CoefficientEvaluationTensorNormalization l E W R) (n : ℕ) :
    letI := coefficientSequenceEvaluation_additive l E W n
    letI := (coefficientSequenceEvaluation_exact l E W n).1
    letI := (coefficientSequenceEvaluation_exact l E W n).2
    SemilinearSections.TensorComparisonModel.{t + 1, t, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology W)) (Scheme.ProEt.topology W)
      (coefficientSequenceCommRingSheaf l E W) (integralCoefficientCommRingSheaf l E W n)
      (coefficientSequenceEvaluation l E W n) R.systemClosed (R.finiteClosed n)
      R.systemTensorModel (R.finiteTensorModel n) (R.evaluationTensor n) := by
  run_tac Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let t ← Lean.Meta.whnf (← goal.getType)
    let .const _ levels := t.getAppFn | Lean.throwError "tensor model expected"
    let ctor := Lean.mkAppN
      (Lean.mkConst ``SemilinearSections.TensorComparisonModel.mk levels) t.getAppArgs
    Lean.Elab.Tactic.replaceMainGoal (← goal.apply ctor { newGoals := .all })
  · kernel_exact SemilinearSections.ordinaryEvaluationTensor.{t + 1, t, u}
      (Scheme.ProEt.topology W) (integralCoefficientCommRingSheaf l E W)
      (coefficientSequenceCommRingTransition l E W) n
  · intro P Q
    kernel_exact (evaluationTotalIso.{t + 1, t, u} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W)
      (coefficientSequenceCommRingTransition l E W) n P Q).inv
  · intro P Q p q k h
    kernel_exact evaluationTotalIso_summand.{t + 1, t, u} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W)
      (coefficientSequenceCommRingTransition l E W) n P Q p q k h
  · intro P hP _
    kernel_exact (coefficientTensorModelPreservation l E W).2 P hP n
  · intro P Q hP hQ flatP flatQ
    have hn := hE n P Q hP hQ
    unfold CoefficientTensorComparisonSquare at hn
    let a := (coefficientSequenceDerivedEvaluation l E W n).mapIso
      (coefficientSystemTensorModelIso l E W R.toCoefficientDerivedSystemTensors P Q hP hQ)
    let b := (R.evaluationTensor n).app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)
    let c := (R.finiteClosed n).tensor.mapIso
      (((coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.app P).prod
        ((coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.app Q))
    let d := coefficientFiniteTensorModelIso l E W R.toCoefficientDerivedSystemTensors n _ _
      ((coefficientTensorModelPreservation l E W).2 P hP n)
      ((coefficientTensorModelPreservation l E W).2 Q hQ n)
    let e := DerivedCategory.Q.mapIso (coefficientEvaluationTensorIso l E W n P Q)
    let e' := DerivedCategory.Q.mapIso (evaluationTotalIso.{t + 1, t, u}
      (Scheme.ProEt.topology W) (integralCoefficientCommRingSheaf l E W)
      (coefficientSequenceCommRingTransition l E W) n P Q)
    let z := (coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.app
      ((SemilinearSections.totalTensor.{t + 1, t, u}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)).obj (P, Q))
    have he := congrArg (fun iso ↦ DerivedCategory.Q.mapIso iso)
      (total_eq l E W n P Q).symm
    have h := inverseSquare a b c d.symm e z hn e' he
    kernel_exact h

attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian in
/-- Every finite evaluation of the unit-defined normalized projection is invertible.
This is the componentwise finite-prefix calculation; the remaining joint detection
of isomorphisms is proved in `coefficientNormalizedEvaluationProjection`.
Source: Zheng Construction 4.1 and Proposition 4.17(a); Stacks 07A4 and 08J9;
the component calculation in step 3 of
`lem-coef-normalized-evaluation-projection`.
(blueprint: lem-coef-normalized-evaluation-projection-components).

Proof: convert coefficient normalization to semilinear normalization using the
actual transition's sectionwise characterization and the scalar adjunction.
Identify the canonical total evaluation comparison with the specified coefficient
comparison, and invert the representative square supplied by `hE` to obtain the
semilinear comparison model. Apply the existing semilinear Cartesian projection
theorem to the actual reduction data and adjunction, then map its isomorphism
by evaluation at `q`. -/
theorem coefficientNormalizedEvaluationProjection_components
    (R : CoefficientDerivedSystemReduction l E W)
    (hE : CoefficientEvaluationTensorNormalization l E W R)
    (M : coefficientSequenceDerived l E W)
    (hM : IsNormalizedCoefficientSequence l E W M) (n : ℕ)
    (L : normalizedDVRDerived l E W n ⥤ coefficientSequenceDerived l E W)
    (adj : L ⊣ coefficientSequenceDerivedEvaluation l E W n)
    (P : normalizedDVRDerived l E W n) (q : ℕ) :
    IsIso ((coefficientSequenceDerivedEvaluation l E W q).map
      ((adj.homEquiv _ _).symm
        ((R.finiteClosed n).tensor.map
            (Prod.mkHom (adj.unit.app P)
              (𝟙 ((coefficientSequenceDerivedEvaluation l E W n).obj M))) ≫
          (R.evaluationTensor n).inv.app (L.obj P, M)))) := by
  classical
  let J := Scheme.ProEt.topology W
  let B := integralCoefficientCommRingSheaf l E W
  let τ := coefficientSequenceCommRingTransition l E W
  let scalar : ∀ {m n : ℕ} (h : n ≤ m),
      SemilinearSections.ScalarData.{t + 1, t, max u (t + 1)}
        (SemilinearSections.coefficientMap J B τ h) :=
    fun h ↦ (SemilinearSections.scalarData_nonempty.{t + 1, t, u} J
      (SemilinearSections.coefficientMap J B τ h)).some
  have hf := SemilinearSections.semilinearCartesianProjection.{t + 1, t, u} J B τ
    scalar R.systemClosed R.systemTensorModel R.finiteClosed R.finiteTensorModel
    R.evaluationTensor (evaluationModel l E W R hE)
    (fun _ _ _ ↦ rfl) M (coefficientNormalizedSequence_semilinear l E W scalar M hM) n L adj P
  exact @Functor.map_isIso _ _ _ _ _ _ (coefficientSequenceDerivedEvaluation l E W q) _ hf

end WeilConjectures
