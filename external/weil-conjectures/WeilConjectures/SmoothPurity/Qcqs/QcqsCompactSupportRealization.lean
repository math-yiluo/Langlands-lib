/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralRationalQbarCompactSupport
public import WeilConjectures.SmoothPurity.Compact.CompactSupportFiniteAction
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
public import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportStrictReductionComparison
import all WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportNormalizedIsoExistence
import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportFiniteComparison
import WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionShiftedHomFiniteAlgClosed
import WeilConjectures.SmoothPurity.Derived.DerivedCompleteFiniteReductionDetection

/-! # Compact-support realization without separated structure morphisms

Source: Bhatt--Scholze, Definition 6.7.6 and Lemma 6.7.7; Stacks Tag 0F7J
(blueprint: def-weil-integral-rational-qbar-compact-support).

The object values and the integral and rational actions are the published ones.
The comparison below retains their chosen Roos projections, on every constructible
integral input, without requiring the schemes themselves to be separated over the field.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open PurCompactSupport

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
  [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
  [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

/-- Projection normalization for the ambient realization of the recorded integral functor.
The finite comparison is the actual scalar-adjunction mate of open extension followed
by proper image; its source projection is the chosen Roos projection, not a freely
chosen reduction isomorphism. Source: Bhatt--Scholze, Definition 6.7.6
(blueprint: def-weil-integral-rational-qbar-compact-support). -/
def SfQcqsCompactSupportRealizationSpec
    (τ : (sfIntegralConstructible l E X).ι ⋙ image (completed l E) c ≅
      sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
        (sfIntegralConstructible l E Y).ι) : Prop :=
  ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
    (scalarReductionDerivedExtension l E Y n).map (τ.hom.app K) ≫
        (sfCompactSupportFiniteReductionIso l K₀ hl c E K n).hom =
      (finiteReductionIso l E Y n).inv.app ((image (completed l E) c).obj K.obj) ≫
        (comparison (reduction l E (n + 1) (Nat.le_add_left 1 n)) c).app K.obj ≫
        (finiteImageIso l E n c).hom.app
          ((pbcDerivedExtend (projection l E (n + 1) (Nat.le_add_left 1 n) X)).obj K.obj) ≫
        (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).map
          ((finiteReductionIso l E X n).hom.app K.obj)

/-- The actual strict reduction-unit/proper-open-mate/total-limit composite.
Source: Bhatt--Scholze, Definition 6.7.6; Stacks 0941, 0F7J
(blueprint: def-weil-integral-rational-qbar-compact-support).

The chosen data consist of a whole coherent strict comparison and its recorded
limit identification. The map is their displayed universal-adjunction composite. -/
def sfQcqsCompactSupportRealizationMap :
    (sfIntegralConstructible l E X).ι ⋙ image (completed l E) c ⟶
      sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
        (sfIntegralConstructible l E Y).ι :=
  let H := qcqsCompactSupport_strictReductionComparison l E K₀ hl c
  let SY := H.choose_spec.choose
  let β := H.choose_spec.choose_spec.choose
  let γ := H.choose_spec.choose_spec.choose_spec.choose
  let A := (sfIntegralConstructible l E X).ι ⋙ image (completed l E) c
  Functor.whiskerLeft A SY.adjunction.unit ≫
    Functor.whiskerRight (Functor.whiskerLeft (sfIntegralConstructible l E X).ι β)
      (coefficientSequenceLimit l E Y) ≫ γ.inv

/-- The explicit universal comparison has the finite proper/open projection coordinates.
Source: Bhatt--Scholze, Definition 6.7.6; Stacks 0941, 0F7J
(blueprint: def-weil-integral-rational-qbar-compact-support).

Proof: transpose the actual reduction unit and total-limit projection under the
finite scalar adjunction. The normalized strict comparison equations identify the
two resulting factors with the actual proper/open mate in the stated coordinates. -/
theorem sfQcqsCompactSupportRealizationMap_spec :
    ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
      (scalarReductionDerivedExtension l E Y n).map
          ((sfQcqsCompactSupportRealizationMap l E K₀ hl c).app K) ≫
          (sfCompactSupportFiniteReductionIso l K₀ hl c E K n).hom =
        (finiteReductionIso l E Y n).inv.app ((image (completed l E) c).obj K.obj) ≫
          (comparison (reduction l E (n + 1) (Nat.le_add_left 1 n)) c).app K.obj ≫
          (finiteImageIso l E n c).hom.app
            ((pbcDerivedExtend (projection l E (n + 1) (Nat.le_add_left 1 n) X)).obj K.obj) ≫
          (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1))
            c).map ((finiteReductionIso l E X n).hom.app K.obj) := by
  let H := qcqsCompactSupport_strictReductionComparison l E K₀ hl c
  let SX := H.choose
  let SY := H.choose_spec.choose
  let β := H.choose_spec.choose_spec.choose
  let γ := H.choose_spec.choose_spec.choose_spec.choose
  have hβ := H.choose_spec.choose_spec.choose_spec.choose_spec.1
  have hγ := H.choose_spec.choose_spec.choose_spec.choose_spec.2
  intro K n
  exact (projection_transpose (coefficientFiniteAdjunction l E Y n) SY.adjunction
    (coefficientSequenceDerivedEvaluation l E Y n) (coefficientSequenceProjection l E Y n)
    (SY.reductionEvaluation n) (fun P ↦ SY.unit_projection P n)
    (β.app K.obj) (γ.app K)
    _ (sfCompactSupportFiniteReductionIso l K₀ hl c E K n).hom (hγ K n)).trans (hβ K.obj n)

/-- The explicit comparison is invertible on every integral constructible input.
Source: Bhatt--Scholze, Lemma 6.7.7; Stacks 0941, 0F7J
(blueprint: def-weil-integral-rational-qbar-compact-support).

Proof: its finite reductions are the invertible proper/open coefficient mates.
Completeness of the actual output and these reductions give its constructibility.
The constructible cone then has zero reductions; its completeness Roos triangle
makes it zero. Componentwise invertibility gives invertibility of the transformation. -/
theorem sfQcqsCompactSupportRealizationMap_isIso :
    IsIso (sfQcqsCompactSupportRealizationMap l E K₀ hl c) := by
  let τ := sfQcqsCompactSupportRealizationMap l E K₀ hl c
  have hcomponent (K : sfIntegralConstructibleCategory l E X) : IsIso (τ.app K) := by
    obtain ⟨hcomplete, hfinite⟩ := sfQcqsCompactSupport_finiteComparison l E K₀ hl c K
    have hred (n : ℕ) :
        IsIso ((scalarReductionDerivedExtension l E Y n).map (τ.app K)) := by
      have := hfinite n
      have : IsIso ((scalarReductionDerivedExtension l E Y n).map (τ.app K) ≫
          (sfCompactSupportFiniteReductionIso l K₀ hl c E K n).hom) := by
        rw [show (scalarReductionDerivedExtension l E Y n).map (τ.app K) ≫
            (sfCompactSupportFiniteReductionIso l K₀ hl c E K n).hom = _ from
          sfQcqsCompactSupportRealizationMap_spec l E K₀ hl c K n]
        infer_instance
      exact IsIso.of_isIso_comp_right
        ((scalarReductionDerivedExtension l E Y n).map (τ.app K))
        (sfCompactSupportFiniteReductionIso l K₀ hl c E K n).hom
    have himage := constructible_of_complete_reduction_isos l E Y hcomplete
      ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K).property
      (fun n ↦ @asIso _ _ _ _
        ((scalarReductionDerivedExtension l E Y n).map (τ.app K)) (hred n))
    exact constructible_isIso_of_reductions l E Y (τ.app K) himage
      ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K).property hred
  let : ∀ K, IsIso (τ.app K) := hcomponent
  exact NatIso.isIso_of_isIso_app τ

/-- The constructed realization of the recorded integral compact-support action.
Source: Bhatt--Scholze, Definition 6.7.6 and Lemma 6.7.7; Stacks 0941, 0F7J
(blueprint: def-weil-integral-rational-qbar-compact-support). -/
def sfQcqsCompactSupportRealization :
    (sfIntegralConstructible l E X).ι ⋙ image (completed l E) c ≅
      sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
        (sfIntegralConstructible l E Y).ι :=
  letI := sfQcqsCompactSupportRealizationMap_isIso l E K₀ hl c
  asIso (sfQcqsCompactSupportRealizationMap l E K₀ hl c)

/-- The constructed realization has the actual finite proper/open projection coordinates.
Source: Bhatt--Scholze, Definition 6.7.6; Stacks 0941, 0F7J
(blueprint: def-weil-integral-rational-qbar-compact-support).

Proof: these are the projection equations of the explicit universal comparison. -/
theorem sfQcqsCompactSupportRealization_spec :
    SfQcqsCompactSupportRealizationSpec l E K₀ hl c
      (sfQcqsCompactSupportRealization l E K₀ hl c) :=
  sfQcqsCompactSupportRealizationMap_spec l E K₀ hl c

end WeilConjectures
