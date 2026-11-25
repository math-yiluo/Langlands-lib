/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.CategoryTheory.StageSystem.StageSystemFunctorDescent
public import WeilConjectures.CategoryTheory.StageSystem.Functor

/-! # Normalized descent for the specified common-stage pullback -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option linter.privateModule false

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.Scheme
open WeilConjectures.AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients (inclusion)

attribute [local irreducible] rationalDerivedPullback commonStageDerivedPullback
  ObjectProperty.FullSubcategory.category

section NormalizedDescent
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X Y : Scheme.{u}} (g : X ⟶ Y)
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- Rational scalar comparison conjugated by the recorded stage-transition identifications.
Source: current blueprint common-stage pullback paragraph
(blueprint: lem-pod-common-stage-pullback-normalized-descent). -/
def commonStagePullbackTransition {E L : Index l Ω} (h : E ≤ L) :
    rationalDerivedPullback l (Coefficient.{u} l Ω E) g ⋙
        (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T h ≅
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).T h ⋙
        rationalDerivedPullback l (Coefficient.{u} l Ω L) g :=
  Functor.isoWhiskerLeft _ (operationStageTransitionIso l Ω X E L h) ≪≫
    rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) g ≪≫
    Functor.isoWhiskerRight (operationStageTransitionIso l Ω Y E L h).symm _

/-- The specified quotient pullback is the functor of its normalized coherent stage morphism.
Source: current blueprint sec-six-functors/sk-rem-sf-pf-done/
lem-fix-weil-operations.proof.md, common-stage pullback paragraph.
(blueprint: lem-pod-common-stage-pullback-normalized-descent).

Proof: the existing comparison-data theorem gives coherent transition comparisons.
Their prescribed components identify them with the scalar comparisons conjugated
by the recorded transition identifications. Substitute this equality in their tower
law. The resulting stage-system morphism has the specified object formula, and
its representative action has exactly the prescribed conjugation formula, by the
same component identities. Uniqueness of the specified quotient functor identifies
it with this descended functor. No shift or inverse comparison is needed. -/
theorem commonStagePullbackNormalizedDescent :
    ∃ hcoh : StageSystem.pairFunctorCoherent
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y)
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X)
      (fun E ↦ rationalDerivedPullback l (Coefficient.{u} l Ω E) g)
      (commonStagePullbackTransition l Ω g),
      commonStageDerivedPullback l Ω g =
        (⟨fun E ↦ rationalDerivedPullback l (Coefficient.{u} l Ω E) g,
            commonStagePullbackTransition l Ω g, hcoh⟩ :
          (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).Morphism
            (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X)).functor := by
  obtain ⟨b, hb, hcoh⟩ := commonStagePullback_comparison_data l Ω g
  have eb : @b = @commonStagePullbackTransition l _ Ω _ _ _ X Y g _ _ := by
    funext E L h
    apply Iso.ext
    ext K
    have h := eq_of_heq (hb h K).1
    simpa only [commonStagePullbackTransition, commonStagePullbackComparison,
      commonStagePullbackObject, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom,
      Functor.mapIso_hom, Iso.app_hom, Iso.app_inv] using h
  cases eb
  refine ⟨hcoh, ?_⟩
  unfold commonStageDerivedPullback
  apply (commonStageDerivedPullback_existsUnique l Ω g).unique
    (commonStageDerivedPullback_existsUnique l Ω g).exists.choose_spec
  refine ⟨fun P ↦ rfl, ?_⟩
  intro P Q L hP hQ f
  cases P with
  | mk E P =>
    cases Q with
    | mk E' Q =>
      have hp := eq_of_heq (hb hP P).1
      have hq := eq_of_heq (hb hQ Q).2
      change HEq (StageSystem.PairCategory.mkHom
        (X := commonStagePullbackObject l Ω g ⟨E, P⟩)
        (Y := commonStagePullbackObject l Ω g ⟨E', Q⟩) L hP hQ
        ((commonStagePullbackTransition l Ω g hP).hom.app P ≫
          (rationalDerivedPullback l (Coefficient.{u} l Ω L) g).map f ≫
          (commonStagePullbackTransition l Ω g hQ).inv.app Q)) _
      rw [hp, hq]

end NormalizedDescent

end WeilConjectures
