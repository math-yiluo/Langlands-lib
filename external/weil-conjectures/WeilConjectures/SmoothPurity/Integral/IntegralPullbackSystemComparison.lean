/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralSystemReductionFullyFaithful
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.ProperBaseChange.IntegralFinitePullbackComposition
public import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedQuotientPullbackRealization
import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import WeilConjectures.SmoothPurity.CompletedOperations.NormalizedCompletedOperationModels
import WeilConjectures.TraceFormula.Supporting.EffectiveQuotientModelDescent
import WeilConjectures.PoincareDuality.Integral.IntegralPullbackCounitProjection
import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedQuotientPullbackRealizationNormalization

/-! # Integral pullback and coherent finite-system reduction

Source: Stacks Project, Tags 099N(5) and 0941; Bhatt--Scholze, Lemma 3.5.7
(blueprint: lem-pod-integral-pullback-system-comparison).
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

/-- The canonical reduction rho of integral pullback, computed using any good resolution.
The first factor is the actual projection-adjoint map, whose invertibility is precisely
part (1) of integralOperations_preserve_constructible. The other factors only change
finite pullback presentation and identify the reduction of the representative with
that of K through the universal reduction counit.
Source: Stacks Tag 099N(5); Bhatt--Scholze, Lemma 6.5.9(5)
(blueprint: lem-pod-integral-pullback-system-comparison). -/
def integralSystemPullbackReductionIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfIntegralConstructibleCategory l E Y)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (e : (DerivedCategory.Q (C := scalarReductionSource l E Y)).obj P.obj ≅ K.obj) (n : ℕ) :
    (scalarReductionDerivedExtension l E X n).obj
        ((constructibleIntegralPullback l E f).obj K).obj ≅
      (proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)) f).obj
        ((scalarReductionDerivedExtension l E Y n).obj K.obj) :=
  letI := ((integralOperations_preserve_constructible l E f).1 K.obj K.property).2 P e n
  asIso (integralPullbackFiniteComparison l E f K.obj P e n) ≪≫
    DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex (integralFinitePullbackModel l E f n)
        (ComplexShape.up ℤ)).app ((unrestrictedIntegralFiniteComplex l E Y n).obj P.obj)) ≪≫
    ((proEtaleConstantRingPullback
      (Padic.coefficientExtensionRing l E (n + 1)) f).mapDerivedCategoryFactors.app
        ((unrestrictedIntegralFiniteComplex l E Y n).obj P.obj)).symm ≪≫
    (proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)) f).mapIso
      ((coefficientFiniteReductionModel l E Y P.obj P.property.1 n).symm ≪≫
        (scalarReductionDerivedExtension l E Y n).mapIso e)

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

/-- Integral pullback reduces to exact inverse image on coherent finite systems, with the
whole-system value of the comparison recorded.
The evaluated comparison is the adjoint of the actual Roos projection, for every
flat-term K-flat representative. No composition comparison is asserted here.
Source: Stacks 099N(5), 0941; Bhatt--Scholze, Lemma 3.5.7
(blueprint: lem-pod-integral-pullback-system-comparison).

Proof: reduce one flat-term K-flat representative with the strict quotient maps.
Change of rings preserves its K-flatness; quotient tensor reassociation and finite
inverse image preserve normalization. The strict Roos comparison, natural on chain
maps and their localization, identifies the actual integral pullback with total
limit of this pulled-back reduction system, preserving its projections. Apply the
reduction/total-limit adjunction counit to this identification. Normalized DVR
effectivity makes its evaluations invertible; the evaluation criterion in the
coefficient calculus makes the system map invertible. Naturality of the adjunction
and Roos comparison gives a natural system isomorphism. The counit projection
formula identifies its evaluation with the scalar adjoint of the defining tower
projection. Transport through the unit-normalized finite pullback presentation
and the universal reduction counit gives exactly the displayed formula, for every
representative and every positive uniformizer exponent.
The second clause records the whole-system value: the comparison is the coherent
reduction of the Roos-normalized realization `completedQuotientPullbackRealization`
followed by the coherent counit, not only its finite evaluations. -/
theorem integralPullbackSystemComparison :
    ∃ β : ∀ {X Y : Scheme.{u}}
        [∀ x : X, Invertible (l : X.residueField x)]
        [∀ y : Y, Invertible (l : Y.residueField y)] (f : X ⟶ Y),
        constructibleIntegralPullback l E f ⋙ integralSystemReduction l E X ≅
          integralSystemReduction l E Y ⋙
            finiteSystemDerivedPullback (integralSystemRings l E) (integralSystemTransition l E) f,
      (∀ {X Y : Scheme.{u}}
        [∀ x : X, Invertible (l : X.residueField x)]
        [∀ y : Y, Invertible (l : Y.residueField y)] (f : X ⟶ Y)
        (K : sfIntegralConstructibleCategory l E Y)
        (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
        (e : (DerivedCategory.Q (C := scalarReductionSource l E Y)).obj P.obj ≅ K.obj) (n : ℕ),
        (finiteSystemDerivedEvaluation (integralSystemRings l E)
          (integralSystemTransition l E) X n).map ((β f).hom.app K) ≫
            (finiteSystemDerivedPullbackEvaluation (integralSystemRings l E)
              (integralSystemTransition l E) f n).hom.app
                ((integralSystemReduction l E Y).obj K) ≫
            (proEtaleConstantRingDerivedPullback
              (Padic.coefficientExtensionRing l E (n + 1)) f).map
                ((integralSystemReductionEvaluation l E Y n).hom.app K) =
          (integralSystemReductionEvaluation l E X n).hom.app
              ((constructibleIntegralPullback l E f).obj K) ≫
            (integralSystemPullbackReductionIso l E f K P e n).hom) ∧
      ∀ {X Y : Scheme.{u}}
        [∀ x : X, Invertible (l : X.residueField x)]
        [∀ y : Y, Invertible (l : Y.residueField y)] (f : X ⟶ Y)
        (K : sfIntegralConstructibleCategory l E Y),
        (β f).hom.app K =
          (pullbackTensorCalculus l E X).reduction.map
              ((CompletedQuotient.completedQuotientPullbackRealization l E f).hom.app K.obj) ≫
            (pullbackTensorCalculus l E X).adjunction.counit.app
              ((integralComparisonDerivedSequencePullback l E f).obj
                ((pullbackTensorCalculus l E Y).reduction.obj K.obj)) := by
  classical
  let S (X : Scheme.{u}) : CoefficientDerivedSystemCalculus l E X :=
    (coefficientDerivedSystemEvaluationCalculus l E X).choose
  have hr (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)] :
      Nonempty (IntegralComparisonRoosModel l E X) := by
    obtain ⟨M, _⟩ := CompletedOperations.normalizedCompletedOperationModels l E
      (fun _ : Unit ↦ X) (fun _ x ↦ isUnit_of_invertible (l : X.residueField x))
    exact ⟨M.roos ()⟩
  let ρ (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)] :=
    Classical.choice (hr X)
  have hd {X Y : Scheme.{u}}
      [∀ x : X, Invertible (l : X.residueField x)]
      [∀ y : Y, Invertible (l : Y.residueField y)] (f : X ⟶ Y) :=
    effectiveQuotientModelDescent l E E (AlgHom.id _ _) f
      (fun x ↦ isUnit_of_invertible (l : X.residueField x))
      (fun y ↦ isUnit_of_invertible (l : Y.residueField y))
      (S Y) (S X) (S Y) (ρ X) (ρ Y)
  let M {X Y : Scheme.{u}}
      [∀ x : X, Invertible (l : X.residueField x)]
      [∀ y : Y, Invertible (l : Y.residueField y)] (f : X ⟶ Y) :
      IntegralComparisonPullbackModel l E f (S Y) (ρ X) :=
    ⟨CompletedQuotient.completedQuotientPullbackRealization l E f,
      CompletedQuotient.completedQuotientPullbackRealization_normalized l E f (ρ X)⟩
  let τ {X Y : Scheme.{u}}
      [∀ x : X, Invertible (l : X.residueField x)]
      [∀ y : Y, Invertible (l : Y.residueField y)] (f : X ⟶ Y) :
      integralDerivedPullback l E f ⋙ (S X).reduction ⟶
        (S Y).reduction ⋙ integralComparisonDerivedSequencePullback l E f :=
    Functor.whiskerRight (M f).realization.hom (S X).reduction ≫
      Functor.whiskerLeft ((S Y).reduction ⋙ integralComparisonDerivedSequencePullback l E f)
        (S X).adjunction.counit
  have ht {X Y : Scheme.{u}}
      [∀ x : X, Invertible (l : X.residueField x)]
      [∀ y : Y, Invertible (l : Y.residueField y)] (f : X ⟶ Y)
      (K : sfIntegralConstructibleCategory l E Y) : IsIso ((τ f).app K.obj) := by
    have : IsIso ((S X).adjunction.counit.app
        ((integralComparisonDerivedSequencePullback l E f).obj ((S Y).reduction.obj K.obj))) :=
      ((hd f).1 K.obj).2.2.2.2.2.1
    dsimp only [τ, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    have hi : IsIso ((M f).realization.hom.app K.obj) :=
      Iso.isIso_hom ((M f).realization.app K.obj)
    exact IsIso.comp_isIso' (Functor.map_isIso _ _) this
  unfold constructibleIntegralPullback integralSystemReduction finiteSystemDerivedPullback
  refine ⟨fun {X Y} _ _ f ↦ ?_, ?_, ?_⟩
  · refine NatIso.ofComponents (fun K ↦ ?_) ?_
    · exact @asIso _ _ _ _ ((τ f).app K.obj) (ht f K)
    · intro A B a
      exact (τ f).naturality a.hom
  · intro X Y _ _ f K P e n
    have h := integralPullbackCounitProjection l E f (S Y) (S X) (ρ X) (M f)
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
    unfold integralSystemReductionEvaluation integralSystemPullbackReductionIso
    unfold constructibleIntegralPullback
    dsimp only [Functor.comp, ObjectProperty.lift, ObjectProperty.ι, inducedFunctor,
      NatIso.ofComponents, asIso, Functor.mapIso, Iso.trans, Iso.symm, Iso.app] at h'' ⊢
    simp only [Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      ObjectProperty.ι_obj]
    simp only [τ, S, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.comp_obj] at h'' ⊢
    exact h''
  · intro X Y _ _ f K
    rfl

end WeilConjectures
