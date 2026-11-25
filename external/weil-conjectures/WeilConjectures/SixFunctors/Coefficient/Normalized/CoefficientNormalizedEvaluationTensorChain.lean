/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
import all WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearTensorEvaluation
import all WeilConjectures.SixFunctors.Supporting.SemilinearTotalTensorEvaluation
import all WeilConjectures.AlgebraicGeometry.ProjectionTensorCore.SemilinearTensorReductionCochain
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Natural prescribed evaluation tensor comparison on complexes

Source: Stacks 03EK, 07A4 and 0941.
(blueprint: lem-coef-normalized-evaluation-tensor-chain).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian
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

-- Avoid re-elaborating the already typed coefficient-site instance arguments.
-- The declaration's proof is still checked by Lean's kernel.
local elab "kernel_exact " t:term : tactic => Lean.Elab.Tactic.withMainContext do
  let e ← Lean.Elab.Term.elabTerm t none
  (← Lean.Elab.Tactic.getMainGoal).assign e
  Lean.Elab.Tactic.replaceMainGoal []

section EvaluationChains
attribute [local instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian
  SemilinearSections.abelianSheafify SemilinearSections.locallyBijective
  SemilinearSections.sequenceSmall SemilinearSections.sliceSmall
attribute [local semireducible] coefficientTotalTensor
open CategoryTheory.MonoidalCategory SemilinearSections
universe c v r
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

private theorem evaluationChainIso (n : ℕ) :
    ∃ b : totalTensor.{c, v, r} (coefficientSequenceTopology J) (systemRing J B τ) ⋙
        (SemilinearSections.evaluation J B τ n).mapHomologicalComplex (.up ℤ) ≅
      ((SemilinearSections.evaluation J B τ n).mapHomologicalComplex (.up ℤ)).prod
        ((SemilinearSections.evaluation J B τ n).mapHomologicalComplex (.up ℤ)) ⋙
          totalTensor.{c, v, r} J (B n),
      ∀ P Q, b.app (P, Q) = evaluationTotalIso.{c, v, r} J B τ n P Q := by
  let F := SemilinearSections.evaluation J B τ n
  let G := WeilConjectures.SequenceModuleEvaluation.coFor J
    (ring (coefficientSequenceTopology J) (systemRing J B τ)) n (ring J (B n))
    (evaluation_ring J B τ n)
  let adj : F ⊣ G := by
    dsimp only [F]
    unfold SemilinearSections.evaluation
    exact WeilConjectures.SequenceModuleEvaluation.coForAdj J
      (ring (coefficientSequenceTopology J) (systemRing J B τ)) n (ring J (B n))
      (evaluation_ring J B τ n)
  let := SheafOfModules.monoidalCategory (systemRing J B τ)
  let := SheafOfModules.monoidalCategory (B n)
  let := SheafOfModules.isMonoidal_W_independentCoefficients (systemRing J B τ)
  let := SheafOfModules.isMonoidal_W_independentCoefficients (B n)
  let := SheafOfModules.cochainModulesPreadditive (systemRing J B τ)
  let := SheafOfModules.cochainModulesPreadditive (B n)
  let μ : ∀ M N : Systems.{c, v, max c v r} J B τ,
      F.obj (M ⊗ N) ≅ F.obj M ⊗ F.obj N :=
    ordinaryEvaluationTensor.{c, v, r} J B τ n
  have hn : ∀ {M M' N N' : Systems.{c, v, max c v r} J B τ}
      (f : M ⟶ M') (g : N ⟶ N'),
      F.map (f ⊗ₘ g) ≫ (μ M' N').hom = (μ M N).hom ≫ (F.map f ⊗ₘ F.map g) := by
    intro M M' N N' f g
    exact evaluation_tensor_natural.{c, v, r} J B τ n f g
  let e := SemilinearSections.exactTensorTotalIso F μ hn G adj
  refine ⟨e.symm, ?_⟩
  intro P Q
  unfold evaluationTotalIso
  rfl

private theorem evaluationTotal_forward (n : ℕ)
    (σ : ∀ (M : Systems.{c, v, max c v r} J B τ) (U : Cᵒᵖ),
      M.val.obj (op (n, U.unop)) →
        ((SemilinearSections.evaluation J B τ n).obj M).val.obj U)
    (hσ : ∀ M U x, HEq (σ M U x) x)
    (P Q : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ)
    (p q k : ℤ) (h : p + q = k) (U : Cᵒᵖ)
    (x : (P.X p).val.obj (op (n, U.unop)))
    (y : (Q.X q).val.obj (op (n, U.unop))) :
    ((evaluationTotalIso.{c, v, r} J B τ n P Q).hom.f k).val.app U
      (σ _ U
        (coefficientTensorGenerator.{r, c, v} (coefficientSequenceTopology J)
          (systemRing J B τ) P Q p q k h (op (n, U.unop)) x y)) =
    coefficientTensorGenerator.{r, c, v} J (B n)
      (((SemilinearSections.evaluation J B τ n).mapHomologicalComplex (.up ℤ)).obj P)
      (((SemilinearSections.evaluation J B τ n).mapHomologicalComplex (.up ℤ)).obj Q)
      p q k h U (σ (P.X p) U x)
      (σ (Q.X q) U y) := by
  have hs (M : Systems.{c, v, max c v r} J B τ) (U : Cᵒᵖ)
      (x : M.val.obj (op (n, U.unop))) :
      σ M U x = evalSection.{c, v, r} J B τ n M U x :=
    eq_of_heq ((hσ M U x).trans (evalSection_heq.{c, v, r} J B τ n M U x).symm)
  simp_rw [hs]
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
end EvaluationChains

universe z
private theorem transport_heq {A B : AddCommGrpCat.{z}}
    (h : A = B) (x : A) : HEq ((eqToHom h) x) x := by
  cases h
  rfl

private theorem evaluationSection_heq (n : ℕ)
    (M : coefficientSequenceModules l E W) (U : W.ProEtᵒᵖ)
    (x : M.val.obj (op (n, U.unop))) :
    HEq (coefficientEvaluationSection l E W M n U x) x := by
  unfold coefficientEvaluationSection
  exact transport_heq _ _

/-- The prescribed evaluation tensor maps assemble naturally on all complexes.
Source: Stacks 03EK, 07A4 and 0941.

Proof: totalize the natural ordinary evaluation tensor isomorphism. Evaluation
preserves the coproducts defining each degree because it is a left adjoint; its
summand formula is compatible with both differentials. Its inverse generator
formula and inverse cancellation give the forward generator formula. Every
section transport heterogeneously equal to the identity equals the canonical
transport, so this formula holds for coefficientEvaluationSection. The unique
generator characterization of coefficientEvaluationTensorIso identifies each
component of the natural total isomorphism with that prescribed map.
(blueprint: lem-coef-normalized-evaluation-tensor-chain). -/
theorem coefficientNormalizedEvaluationTensorChain (n : ℕ) :
    ∃ b : coefficientTotalTensor.{u, t+1, t}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W) ⋙
        (coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ) ≅
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).prod
        ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)) ⋙
          coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
            (integralCoefficientCommRingSheaf l E W n),
      ∀ P Q, b.app (P, Q) = coefficientEvaluationTensorIso l E W n P Q := by
  obtain ⟨b, hb⟩ := evaluationChainIso.{t+1, t, u} (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W)
    (coefficientSequenceCommRingTransition l E W) n
  refine ⟨b, ?_⟩
  intro P Q
  refine (hb P Q).trans ?_
  apply (coefficientEvaluationTensorIso_exists l E W n P Q).unique
  · intro p q k h U x y
    kernel_exact evaluationTotal_forward.{t+1, t, u} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W)
      (coefficientSequenceCommRingTransition l E W) n
      (fun M U x ↦ coefficientEvaluationSection l E W M n U x)
      (evaluationSection_heq l E W n) P Q p q k h U x y
  · unfold coefficientEvaluationTensorIso coefficientUniqueComparisonChoice
    exact (coefficientEvaluationTensorIso_exists l E W n P Q).choose_spec.1

end WeilConjectures
