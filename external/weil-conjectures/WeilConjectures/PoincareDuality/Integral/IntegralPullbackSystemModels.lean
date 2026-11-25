/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralPullbackSystemComparison
public import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
public import WeilConjectures.SmoothPurity.CompletedOperations.NormalizedCompletedOperationModels
public import WeilConjectures.TraceFormula.Supporting.EffectiveQuotientModelDescent
import WeilConjectures.PoincareDuality.Integral.IntegralPullbackCounitProjection
import WeilConjectures.TraceFormula.Primitive.PrimitiveQuotientRealizationsUnique
import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedQuotientPullbackRealizationNormalization

/-! # The pinned system comparison of integral pullback

Source: Stacks Project, Tags 099N(5) and 0941; Bhatt--Scholze, Lemma 3.5.7
(blueprint: lem-pod-integral-pullback-system-comparison).

The comparison of `integralPullbackSystemComparison` is only asserted to exist. Here the
same construction is recorded as a definition: the fixed evaluation calculus, a fixed Roos
model, a fixed normalized pullback realization model, and the coherent counit. Its finite
evaluations are the projection-adjoint maps. Later scalar-extension arguments use that this
comparison is literally the transposed realization of a pullback model.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- A Roos model exists on every scheme with l invertible.
Source: Stacks 0941 (blueprint: lem-pod-integral-pullback-system-comparison).
Proof: take the Roos field of the normalized completed operation models. -/
theorem integralSystemRoos_nonempty (X : Scheme.{u})
    (hX : ∀ x : X, IsUnit (l : X.residueField x)) :
    Nonempty (IntegralComparisonRoosModel l E X) := by
  obtain ⟨M, _⟩ := CompletedOperations.normalizedCompletedOperationModels l E
    (fun _ : Unit ↦ X) (fun _ ↦ hX)
  exact ⟨M.roos ()⟩

/-- The fixed Roos model used by the pinned system pullback comparison.
Source: Stacks 0941 (blueprint: lem-pod-integral-pullback-system-comparison). -/
def integralSystemRoos (X : Scheme.{u}) (hX : ∀ x : X, IsUnit (l : X.residueField x)) :
    IntegralComparisonRoosModel l E X :=
  Classical.choice (integralSystemRoos_nonempty l E X hX)

/-- The fixed normalized realization model of completed pullback, over the fixed
evaluation calculus of the target and the fixed Roos model of the source.
Source: Stacks 099N(5), 0941 (blueprint: lem-pod-integral-pullback-system-comparison). -/
def integralSystemPullbackModel {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : ∀ x : X, IsUnit (l : X.residueField x))
    (hY : ∀ y : Y, IsUnit (l : Y.residueField y)) :
    IntegralComparisonPullbackModel l E f
      (coefficientDerivedSystemEvaluationCalculus l E Y).choose
      (integralSystemRoos l E X hX) :=
  Classical.choice (effectiveQuotientModelDescent l E E (AlgHom.id _ _) f hX hY
    (coefficientDerivedSystemEvaluationCalculus l E Y).choose
    (coefficientDerivedSystemEvaluationCalculus l E X).choose
    (coefficientDerivedSystemEvaluationCalculus l E Y).choose
    (integralSystemRoos l E X hX) (integralSystemRoos l E Y hY)).2.1

/-- The transposed realization: reduction of the realization followed by the coherent counit.
Source: Stacks 099N(5), 0941 (blueprint: lem-pod-integral-pullback-system-comparison). -/
def integralPullbackSystemTransformation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : ∀ x : X, IsUnit (l : X.residueField x))
    (hY : ∀ y : Y, IsUnit (l : Y.residueField y)) :
    integralDerivedPullback l E f ⋙
        (coefficientDerivedSystemEvaluationCalculus l E X).choose.reduction ⟶
      (coefficientDerivedSystemEvaluationCalculus l E Y).choose.reduction ⋙
        integralComparisonDerivedSequencePullback l E f :=
  Functor.whiskerRight (integralSystemPullbackModel l E f hX hY).realization.hom
      (coefficientDerivedSystemEvaluationCalculus l E X).choose.reduction ≫
    Functor.whiskerLeft ((coefficientDerivedSystemEvaluationCalculus l E Y).choose.reduction ⋙
        integralComparisonDerivedSequencePullback l E f)
      (coefficientDerivedSystemEvaluationCalculus l E X).choose.adjunction.counit

/-- On constructible inputs the transposed realization is invertible.
Source: Stacks 0941; Bhatt--Scholze, Lemma 3.5.7
(blueprint: lem-pod-integral-pullback-system-comparison).
Proof: the realization is an isomorphism, and effective quotient model descent makes the
coherent counit invertible on the pulled-back reduction system. -/
theorem integralPullbackSystemTransformation_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : ∀ x : X, IsUnit (l : X.residueField x))
    (hY : ∀ y : Y, IsUnit (l : Y.residueField y))
    (K : sfIntegralConstructibleCategory l E Y) :
    IsIso ((integralPullbackSystemTransformation l E f hX hY).app K.obj) := by
  have : IsIso ((coefficientDerivedSystemEvaluationCalculus l E X).choose.adjunction.counit.app
      ((integralComparisonDerivedSequencePullback l E f).obj
        ((coefficientDerivedSystemEvaluationCalculus l E Y).choose.reduction.obj K.obj))) :=
    ((effectiveQuotientModelDescent l E E (AlgHom.id _ _) f hX hY
      (coefficientDerivedSystemEvaluationCalculus l E Y).choose
      (coefficientDerivedSystemEvaluationCalculus l E X).choose
      (coefficientDerivedSystemEvaluationCalculus l E Y).choose
      (integralSystemRoos l E X hX) (integralSystemRoos l E Y hY)).1 K.obj).2.2.2.2.2.1
  dsimp only [integralPullbackSystemTransformation, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  have hi : IsIso ((integralSystemPullbackModel l E f hX hY).realization.hom.app K.obj) :=
    Iso.isIso_hom ((integralSystemPullbackModel l E f hX hY).realization.app K.obj)
  exact IsIso.comp_isIso' (Functor.map_isIso _ _) this

set_option allowUnsafeReducibility true in
attribute [local irreducible] integralSystemPullbackReductionIso
  integralDerivedPullback integralSystemReductionEvaluation
  finiteSystemDerivedPullbackEvaluation

set_option allowUnsafeReducibility true in
attribute [local reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  coefficientFiniteDerivedExtension constructibleIntegralPullback integralSystemReduction
  Functor.comp ObjectProperty.ι CategoryTheory.inducedFunctor

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The pinned natural system comparison beta_f of integral pullback with exact finite
inverse image of reduction systems.
Source: Stacks 099N(5), 0941; Bhatt--Scholze, Lemma 3.5.7
(blueprint: lem-pod-integral-pullback-system-comparison).
Its component at K is the reduction of the fixed realization model followed by the
coherent counit; it is invertible on constructible inputs. -/
def integralPullbackSystemIso {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (f : X ⟶ Y) :
    constructibleIntegralPullback l E f ⋙ integralSystemReduction l E X ≅
      integralSystemReduction l E Y ⋙
        finiteSystemDerivedPullback (integralSystemRings l E) (integralSystemTransition l E) f :=
  NatIso.ofComponents
    (fun K ↦ @asIso _ _ _ _
      ((integralPullbackSystemTransformation l E f
        (fun x ↦ isUnit_of_invertible (l : X.residueField x))
        (fun y ↦ isUnit_of_invertible (l : Y.residueField y))).app K.obj)
      (integralPullbackSystemTransformation_isIso l E f _ _ K))
    (fun {_ _} a ↦ (integralPullbackSystemTransformation l E f
        (fun x ↦ isUnit_of_invertible (l : X.residueField x))
        (fun y ↦ isUnit_of_invertible (l : Y.residueField y))).naturality a.hom)

/-- The component formula of the pinned comparison.
Source: Stacks 099N(5) (blueprint: lem-pod-integral-pullback-system-comparison).
Proof: definitional unfolding. -/
theorem integralPullbackSystemIso_hom_app {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (f : X ⟶ Y)
    (K : sfIntegralConstructibleCategory l E Y) :
    (integralPullbackSystemIso l E f).hom.app K =
      (integralPullbackSystemTransformation l E f
        (fun x ↦ isUnit_of_invertible (l : X.residueField x))
        (fun y ↦ isUnit_of_invertible (l : Y.residueField y))).app K.obj := rfl

/-- The pinned comparison evaluates to the actual projection-adjoint reductions.
Source: Stacks 099N(5), 0941; Bhatt--Scholze, Lemma 3.5.7
(blueprint: lem-pod-integral-pullback-system-comparison).
Proof: this is the counit projection formula for the fixed realization model, transported
through the unit-normalized finite pullback presentation, exactly as in
integralPullbackSystemComparison. -/
theorem integralPullbackSystemIso_evaluation {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (f : X ⟶ Y)
    (K : sfIntegralConstructibleCategory l E Y)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (e : (DerivedCategory.Q (C := scalarReductionSource l E Y)).obj P.obj ≅ K.obj) (n : ℕ) :
    (finiteSystemDerivedEvaluation (integralSystemRings l E)
      (integralSystemTransition l E) X n).map ((integralPullbackSystemIso l E f).hom.app K) ≫
        (finiteSystemDerivedPullbackEvaluation (integralSystemRings l E)
          (integralSystemTransition l E) f n).hom.app
            ((integralSystemReduction l E Y).obj K) ≫
        (proEtaleConstantRingDerivedPullback
          (Padic.coefficientExtensionRing l E (n + 1)) f).map
            ((integralSystemReductionEvaluation l E Y n).hom.app K) =
      (integralSystemReductionEvaluation l E X n).hom.app
          ((constructibleIntegralPullback l E f).obj K) ≫
        (integralSystemPullbackReductionIso l E f K P e n).hom := by
  let S (X : Scheme.{u}) : CoefficientDerivedSystemCalculus l E X :=
    (coefficientDerivedSystemEvaluationCalculus l E X).choose
  have h := integralPullbackCounitProjection l E f (S Y) (S X)
    (integralSystemRoos l E X (fun x ↦ isUnit_of_invertible (l : X.residueField x)))
    (integralSystemPullbackModel l E f
      (fun x ↦ isUnit_of_invertible (l : X.residueField x))
      (fun y ↦ isUnit_of_invertible (l : Y.residueField y)))
    K.obj P e n
  have h' := congrArg
    (fun q ↦ ((S X).reductionEvaluation n).hom.app
      ((integralDerivedPullback l E f).obj K.obj) ≫ q) h
  simp only [Iso.hom_inv_id_app_assoc] at h'
  have h'' := congrArg
    (fun q ↦ (show
        (finiteSystemDerivedEvaluation (integralSystemRings l E)
          (integralSystemTransition l E) X n).obj
            ((S X).reduction.obj ((integralDerivedPullback l E f).obj K.obj)) ⟶
          (proEtaleConstantRingDerivedPullback
            (Padic.coefficientExtensionRing l E (n + 1)) f).obj
              ((scalarReductionDerivedExtension l E Y n).obj K.obj) from q)) h'
  rw [integralPullbackSystemIso_hom_app]
  unfold integralSystemReductionEvaluation integralSystemPullbackReductionIso
  unfold constructibleIntegralPullback
  dsimp only [Functor.comp, ObjectProperty.lift, ObjectProperty.ι, inducedFunctor,
    NatIso.ofComponents, asIso, Functor.mapIso, Iso.trans, Iso.symm, Iso.app] at h'' ⊢
  simp only [Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    ObjectProperty.ι_obj]
  simp only [integralPullbackSystemTransformation, S, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_obj] at h'' ⊢
  exact h''

/-- The pinned pullback realization model is the transported completed-quotient realization.
Source: Stacks 099N(5), 0941 (blueprint: lem-pod-integral-pullback-system-comparison).
Proof: both are normalized pullback models for the same calculus and Roos model, and
normalized realizations are unique. -/
theorem integralSystemPullbackModel_realization {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : ∀ x : X, IsUnit (l : X.residueField x))
    (hY : ∀ y : Y, IsUnit (l : Y.residueField y)) :
    (integralSystemPullbackModel l E f hX hY).realization =
      CompletedQuotient.completedQuotientPullbackRealization l E f := by
  have hd := effectiveQuotientModelDescent l E E (AlgHom.id _ _) f hX hY
    (coefficientDerivedSystemEvaluationCalculus l E Y).choose
    (coefficientDerivedSystemEvaluationCalculus l E X).choose
    (coefficientDerivedSystemEvaluationCalculus l E Y).choose
    (integralSystemRoos l E X hX) (integralSystemRoos l E Y hY)
  let M : IntegralComparisonPullbackModel l E f
      (coefficientDerivedSystemEvaluationCalculus l E Y).choose (integralSystemRoos l E X hX) :=
    ⟨CompletedQuotient.completedQuotientPullbackRealization l E f,
      CompletedQuotient.completedQuotientPullbackRealization_normalized l E f
        (integralSystemRoos l E X hX)⟩
  exact (primitiveQuotientRealizations_unique l E E (AlgHom.id _ _) f
    (coefficientDerivedSystemEvaluationCalculus l E Y).choose (integralSystemRoos l E X hX)
    (integralSystemRoos l E Y hY) M hd.2.2.some).1 (integralSystemPullbackModel l E f hX hY)

/-- The whole-system comparison chosen in integralPullbackSystemComparison is the pinned
comparison integralPullbackSystemIso.
Source: Stacks 099N(5), 0941 (blueprint: lem-pod-integral-pullback-system-comparison).
Proof: both components are the reduction of the same realization followed by the coherent
counit (integralSystemPullbackModel_realization). -/
theorem integralPullbackSystemComparison_choose {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (f : X ⟶ Y) :
    (integralPullbackSystemComparison l E).choose f = integralPullbackSystemIso l E f := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  rw [(integralPullbackSystemComparison l E).choose_spec.2 f K,
    integralPullbackSystemIso_hom_app]
  simp only [integralPullbackSystemTransformation, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, integralSystemPullbackModel_realization]
  rfl

end WeilConjectures
