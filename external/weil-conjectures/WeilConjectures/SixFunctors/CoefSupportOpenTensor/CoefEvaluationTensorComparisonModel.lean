/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SixFunctors.CoefSupportOpenTensor.CoefOpenTensorEvaluationData
import all WeilConjectures.SixFunctors.Supporting.SemilinearTotalTensorEvaluation
import all WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearTensorEvaluation
import all WeilConjectures.AlgebraicGeometry.System.SystemOrdinaryTensorReduction

/-! # The native evaluation tensor comparison model

Source: Stacks 03EK, 07A4 and 0941. This constructs the representative model
for the tensor evaluation already specified by a coefficient calculus.
(blueprint: lem-coef-evaluation-tensor-comparison-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open WeilConjectures.SemilinearSections
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  HasDerivedCategory.standard SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive Functor.ofSequence Functor.ofOpSequence
  constantSheaf presheafToSheaf MorphismProperty.Over.pullback
  DerivedCategory DerivedCategory.Q DerivedCategory.Qh _root_.instCategoryDerivedCategory
namespace WeilConjectures.CoefSupportOpenTensor

attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian
  SemilinearSections.abelianSheafify SemilinearSections.locallyBijective
  SemilinearSections.sequenceSmall SemilinearSections.sliceSmall

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local instance 2000] coefficientSequenceEvaluation_additiveInstance
  coefficientSequenceEvaluation_limits coefficientSequenceEvaluation_colimits
attribute [local irreducible] coefficientTensorGenerator coefficientTotalTensor
  SheafOfModules.monoidalCategory CoefficientClosedStructure.tensor
  coefficientSystemTensorModelIso coefficientFiniteTensorModelIso

attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  coefficientSequenceCommRingSheaf coefficientSequenceCommRingPresheaf
  coefficientSequenceCommRingSystem coefficientSequenceCommRingTransition
  coefficientSequenceEvaluation coefficientSequenceHasDerived
  integralCoefficientSheafTransition compactSupportSystemLevel compactSupportSystemQuotient
  ProEtale.VaryingRing.coefficientTransition RingHom.ulift
  SemilinearSections.moduleAbelian SemilinearSections.hasDerived
  CategoryTheory.sheafCompose CommRingCat.hasForgetToRingCat
  SemilinearSections.systemRing SemilinearSections.ringPresheaf SemilinearSections.rings
  SemilinearSections.evaluation
  SheafOfModules.pushforward SheafOfModules.restrictScalars
  PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj ModuleCat.restrictScalars ModuleCat.RestrictScalars.obj'
  ProEtale.StrictTower.moduleDirectImage proEtaleRingModuleDirectImage
  ProEtale.VaryingRing.push ProEtale.VaryingRing.baseChange ProEtale.StrictTower.modulePullback
  coefficientEvaluationSection SemilinearSections.evalSection pullSection finitePullSection
attribute [local instance 2000] ProEtale.VaryingRing.extensionAdditive
  ProEtale.VaryingRing.extensionLimits ProEtale.VaryingRing.extensionColimits
  ProEtale.VaryingRing.pullAdditive ProEtale.VaryingRing.pullLimits
  ProEtale.VaryingRing.pullColimits ProEtale.StrictTower.moduleJ_additive
  ProEtale.StrictTower.moduleJ_finiteLimits ProEtale.StrictTower.moduleJ_finiteColimits
  ProEtale.StrictTower.modulePullback_additive ProEtale.StrictTower.modulePullback_finiteLimits
  ProEtale.StrictTower.modulePullback_finiteColimits

section GenericForward
attribute [local instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian
  SemilinearSections.abelianSheafify SemilinearSections.locallyBijective
  SemilinearSections.sequenceSmall SemilinearSections.sliceSmall
universe c v r
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

private theorem evaluationTotal_forward (n : ℕ)
    (P Q : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ)
    (p q k : ℤ) (h : p + q = k) (U : Cᵒᵖ)
    (x : (P.X p).val.obj (op (n, U.unop)))
    (y : (Q.X q).val.obj (op (n, U.unop))) :
    ((evaluationTotalIso.{c, v, r} J B τ n P Q).hom.f k).val.app U
      (evalSection.{c, v, r} J B τ n _ U
        (coefficientTensorGenerator.{r, c, v} (coefficientSequenceTopology J)
          (systemRing J B τ) P Q p q k h (op (n, U.unop)) x y)) =
    coefficientTensorGenerator.{r, c, v} J (B n)
      (((SemilinearSections.evaluation J B τ n).mapHomologicalComplex (.up ℤ)).obj P)
      (((SemilinearSections.evaluation J B τ n).mapHomologicalComplex (.up ℤ)).obj Q)
      p q k h U (evalSection.{c, v, r} J B τ n (P.X p) U x)
      (evalSection.{c, v, r} J B τ n (Q.X q) U y) := by
  let e := evaluationTotalIso.{c, v, r} J B τ n P Q
  have hh := congrArg (fun f ↦ (f.f k).val.app U
    (coefficientTensorGenerator.{r, c, v} J (B n)
      (((SemilinearSections.evaluation J B τ n).mapHomologicalComplex (.up ℤ)).obj P)
      (((SemilinearSections.evaluation J B τ n).mapHomologicalComplex (.up ℤ)).obj Q)
      p q k h U (evalSection.{c, v, r} J B τ n (P.X p) U x)
      (evalSection.{c, v, r} J B τ n (Q.X q) U y))) e.inv_hom_id
  change (e.hom.f k).val.app U ((e.inv.f k).val.app U _) = _ at hh
  rw [evaluationTotalIso_inv_generator] at hh
  exact hh
end GenericForward

-- Reuse the instances stored in a model instead of asking elaboration to rebuild
-- its large coefficient-site specialization. The resulting applications are
-- ordinary terms and are checked by Lean's kernel.
local elab "modelField% " f:ident m:term:max : term => do
  let e ← Lean.Elab.Term.elabTerm m none
  let t ← Lean.Meta.whnf (← Lean.Meta.inferType e)
  let .const head levels := t.getAppFn | Lean.throwError "model structure expected"
  return Lean.mkAppN (Lean.mkConst (head ++ f.getId) levels) (t.getAppArgs.push e)

local elab "kernel_exact " t:term : tactic => Lean.Elab.Tactic.withMainContext do
  let e ← Lean.Elab.Term.elabTerm t none
  (← Lean.Elab.Tactic.getMainGoal).assign e
  Lean.Elab.Tactic.replaceMainGoal []

private theorem evaluationTotal_eq (W : Scheme.{u}) (n : ℕ)
    (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    coefficientEvaluationTensorIso l E W n P Q =
      evaluationTotalIso.{u+1, u, u} (ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W)
        (coefficientSequenceCommRingTransition l E W) n P Q := by
  apply (coefficientEvaluationTensorIso_exists l E W n P Q).unique
  · exact (coefficientEvaluationTensorIso_exists l E W n P Q).choose_spec.1
  · intro p q k h U x y
    exact evaluationTotal_forward.{u+1, u, u} (ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W)
      (coefficientSequenceCommRingTransition l E W) n P Q p q k h U x y

private theorem inverse_tensor_relation
    {C : Type*} [Category C] {X₀ X₁ X₂ X₃ X₄ X₅ : C}
    (a : X₀ ≅ X₁) (b : X₁ ≅ X₂) (c : X₂ ≅ X₃)
    (d : X₄ ≅ X₃) (e : X₅ ≅ X₄) (w : X₀ ⟶ X₅)
    (hn : a.hom ≫ b.hom ≫ c.hom = w ≫ e.hom ≫ d.hom) :
    d.hom ≫ c.inv ≫ b.inv ≫ a.inv ≫ w = e.inv := by
  have hh : a.hom ≫ b.hom ≫ c.hom ≫ d.inv ≫ e.inv = w := by
    rw [reassoc_of% hn]
    simp only [Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  exact inverseChain a b c d.symm e.inv w hh

private def evaluationModel (W : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus.{u, u} l E W) (n : ℕ) :
    let := coefficientSequenceEvaluation_additiveInstance l E W n
    let := coefficientSequenceEvaluation_limits l E W n
    let := coefficientSequenceEvaluation_colimits l E W n
    @TensorComparisonModel.{u+1, u, u}
      (ℕ × W.ProEt) _ (coefficientSequenceTopology (ProEt.topology W))
      (ProEtale.VaryingRing.sequenceSiteSmall W)
      W.ProEt _ (WeilConjectures.instEssentiallySmallProEt_weilConjectures W) (ProEt.topology W)
      (coefficientSequenceCommRingSheaf l E W) (integralCoefficientCommRingSheaf l E W n)
      (coefficientSequenceEvaluation l E W n)
      (coefficientSequenceEvaluation_additiveInstance l E W n)
      (coefficientSequenceEvaluation_limits l E W n)
      (coefficientSequenceEvaluation_colimits l E W n)
      S.systemClosed (S.finiteClosed n) S.systemTensorModel (S.finiteTensorModel n)
      (S.evaluationTensor n) := by
  run_tac Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let t ← Lean.Meta.whnf (← goal.getType)
    let .const _ levels := t.getAppFn | Lean.throwError "tensor model expected"
    let ctor := Lean.mkAppN (Lean.mkConst ``TensorComparisonModel.mk levels) t.getAppArgs
    Lean.Elab.Tactic.replaceMainGoal (← goal.apply ctor { newGoals := .all })
  · exact ordinaryEvaluationTensor.{u+1, u, u} (ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W)
      (coefficientSequenceCommRingTransition l E W) n
  · intro P Q
    exact (evaluationTotalIso.{u+1, u, u} (ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W)
      (coefficientSequenceCommRingTransition l E W) n P Q).inv
  · intro P Q p q k h
    exact evaluationTotalIso_summand.{u+1, u, u}
      (ProEt.topology W) (integralCoefficientCommRingSheaf l E W)
      (coefficientSequenceCommRingTransition l E W) n P Q p q k h
  · intro P hP _
    exact (coefficientTensorModelPreservation l E W).2 P hP n
  · intro P Q hP hQ fP fQ
    have hn := S.evaluationTensor_normalization n P Q hP hQ
    unfold CoefficientTensorComparisonSquare at hn
    rw [evaluationTotal_eq l E W n P Q] at hn
    let a := (coefficientSequenceDerivedEvaluation l E W n).mapIso
      (coefficientSystemTensorModelIso l E W S.toCoefficientDerivedSystemTensors
        P Q hP hQ)
    let b := (S.evaluationTensor n).app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)
    let c := (S.finiteClosed n).tensor.mapIso
      (((coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.app P).prod
        ((coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.app Q))
    let d := coefficientFiniteTensorModelIso l E W S.toCoefficientDerivedSystemTensors n
      _ _ ((coefficientTensorModelPreservation l E W).2 P hP n)
      ((coefficientTensorModelPreservation l E W).2 Q hQ n)
    let e := DerivedCategory.Q.mapIso (evaluationTotalIso.{u+1, u, u} (ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W)
      (coefficientSequenceCommRingTransition l E W) n P Q)
    let w := (coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app
      ((totalTensor.{u+1, u, u} (coefficientSequenceTopology (ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)).obj (P, Q))
    have h := inverse_tensor_relation a b c d e w hn
    kernel_exact h

/-- The specified tensor evaluation has the ordinary comparison fixed on pure tensors.
Source: Stacks 03EK, 07A4 and 0941.
(blueprint: lem-coef-evaluation-tensor-comparison-model).

Proof: use the ordinary evaluation tensor isomorphism and the inverse normalized
isomorphism on total complexes. Its total-summand equation gives the chain field.
The unique pure-generator normalization identifies this total isomorphism with
coefficientEvaluationTensorIso. Evaluation preserves the independently K-flat
class. The calculus normalization, followed by cancellation of the four model
isomorphisms, gives the required derived equation. These constructions apply to
all complexes, every level, and the empty site, without extra flatness hypotheses. -/
theorem coefficientEvaluationTensorModel_exists (W : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus.{u, u} l E W) (n : ℕ) :
    ∃ model : (
      let := coefficientSequenceEvaluation_additiveInstance l E W n
      let := coefficientSequenceEvaluation_limits l E W n
      let := coefficientSequenceEvaluation_colimits l E W n
      @TensorComparisonModel.{u+1, u, u}
        (ℕ × W.ProEt) _ (coefficientSequenceTopology (ProEt.topology W))
        (ProEtale.VaryingRing.sequenceSiteSmall W)
        W.ProEt _ (WeilConjectures.instEssentiallySmallProEt_weilConjectures W) (ProEt.topology W)
        (coefficientSequenceCommRingSheaf l E W) (integralCoefficientCommRingSheaf l E W n)
        (coefficientSequenceEvaluation l E W n)
        (coefficientSequenceEvaluation_additiveInstance l E W n)
        (coefficientSequenceEvaluation_limits l E W n)
        (coefficientSequenceEvaluation_colimits l E W n)
        S.systemClosed (S.finiteClosed n) S.systemTensorModel (S.finiteTensorModel n)
        (S.evaluationTensor n)),
      ∀ M N : coefficientSequenceModules l E W,
        (modelField% ordinary model) M N =
          ordinaryEvaluationTensor.{u+1, u, u} (ProEt.topology W)
            (integralCoefficientCommRingSheaf l E W)
            (coefficientSequenceCommRingTransition l E W) n M N := by
  refine ⟨evaluationModel l E W S n, ?_⟩
  intro M N
  rfl

end WeilConjectures.CoefSupportOpenTensor
