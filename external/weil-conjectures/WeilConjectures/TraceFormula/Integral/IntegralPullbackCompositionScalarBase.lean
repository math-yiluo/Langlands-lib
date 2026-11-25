/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralPullbackCompositionScalarHeq
public import WeilConjectures.TraceFormula.Integral.IntegralPullbackComposition
public import WeilConjectures.PoincareDuality.Integral.IntegralPullbackSystemModels
public import WeilConjectures.TraceFormula.Primitive.PrimitiveQuotientScalarModelExistence
import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerCoherence
import WeilConjectures.TraceFormula.Supporting.QuotientSystemMixedCoherence
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import all WeilConjectures.SmoothPurity.Finite.FiniteSystemPullbackCoherence

/-! # Scalar extension carries the integral pullback compositor: base lemmas

Source: Stacks Project, Tags 06YY, 07A4, 0941 and 0D6D; Bhatt--Scholze, Lemma 3.5.7
(blueprint: lem-pod-integral-pullback-composition-scalar).

For a coefficient inclusion E to L, completed scalar extension carries the specified
integral composition comparison at E to the one at L, conjugated by the canonical
scalar/pullback comparisons. Both sides are compared after the fully faithful coherent
reduction at L: the system-level composition clause of integralPullbackComposition at
E and at L, the system scalar comparison, the pullback/scalar square of
scalarExtensionTowerCoherence, and whole-system mixed coherence.
The rationalized statement follows by localization on pure tensors.

This file holds the integral system
models and the system scalar comparison used by IntegralPullbackCompositionScalar.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

omit [Fact (Nat.Prime l)] in
private theorem coefficientPrime_isUnit (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] : IsUnit (l : Γ(W, ⊤)) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    apply RingedSpace.isUnit_of_isUnit_germ W.toSheafedSpace ⊤
    intro x hx
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    simpa only [map_natCast] using
      (isUnit_of_invertible (l : W.residueField x)).ne_zero

/-- The completed-operation models with the pinned calculus, Roos model and pullback
realization models of integralPullbackSystemIso; the remaining fields are transported
from the normalized models along the unique comparison of left adjoints of total limit.
Source: Stacks 0941 (blueprint: lem-pod-integral-pullback-composition-scalar).
Construction: keep the pinned fields and transport the rest along the left-adjoint comparison. -/
def integralSystemModels (W : Bool → Scheme.{u})
    (hl : ∀ (a : Bool) (x : W a), IsUnit (l : (W a).residueField x)) :
    CompletedOperations.Models l E W :=
  let M0 := (CompletedOperations.normalizedCompletedOperationModels l E W hl).choose
  { calculus := fun a ↦ (coefficientDerivedSystemEvaluationCalculus l E (W a)).choose
    system := M0.system
    completion := fun a ↦ M0.completion a ≪≫ Functor.isoWhiskerRight
      ((M0.calculus a).adjunction.leftAdjointUniq
        (coefficientDerivedSystemEvaluationCalculus l E (W a)).choose.adjunction)
      (coefficientSequenceLimit l E (W a))
    completion_unit := fun a K ↦
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun t ↦ t ≫ (coefficientSequenceLimit l E (W a)).map
          (((M0.calculus a).adjunction.leftAdjointUniq
            (coefficientDerivedSystemEvaluationCalculus l E (W a)).choose.adjunction).hom.app K))
          (M0.completion_unit a K)).trans
        (Adjunction.unit_leftAdjointUniq_hom_app _ _ K))
    roos := fun a ↦ integralSystemRoos l E (W a) (hl a)
    pullback := fun {a b} f ↦ integralSystemPullbackModel l E f (hl a) (hl b) }

section SystemScalar
variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] HasDerivedCategory.standard
  Functor.mapDerivedCategoryFactors integralComparisonSequenceScalarModel
attribute [local implicit_reducible] integralScalarExtension integralScalarExtensionOfUniverses
  integralComparisonDerivedSequenceScalar

/-- The fixed normalized realization model of completed scalar extension, over the pinned
evaluation calculus at E and the pinned Roos model at L.
Source: Stacks 06YY, 0941 (blueprint: lem-pod-integral-pullback-composition-scalar).
Construction: a chosen model from primitiveQuotientScalarModelExistence. -/
def integralSystemScalarModel (X : Scheme.{u}) (hX : ∀ x : X, IsUnit (l : X.residueField x)) :
    IntegralComparisonScalarModel l E L ι X
      (coefficientDerivedSystemEvaluationCalculus l E X).choose
      (integralSystemRoos l L X hX) :=
  Classical.choice (primitiveQuotientScalarModelExistence l E L ι X hX _ _)

/-- Reduction of the scalar realization, followed by the coherent counit.
Source: Stacks 06YY, 0941 (blueprint: lem-pod-integral-pullback-composition-scalar).
Construction: whisker the realization of the scalar model and compose with the counit. -/
def integralSystemScalarTransformation (X : Scheme.{u})
    (hX : ∀ x : X, IsUnit (l : X.residueField x)) :
    integralScalarExtensionOfUniverses l E L ι X ⋙
        (coefficientDerivedSystemEvaluationCalculus l L X).choose.reduction ⟶
      (coefficientDerivedSystemEvaluationCalculus l E X).choose.reduction ⋙
        integralComparisonDerivedSequenceScalar l E L ι X :=
  Functor.whiskerRight (integralSystemScalarModel l E L ι X hX).realization.hom
      (coefficientDerivedSystemEvaluationCalculus l L X).choose.reduction ≫
    Functor.whiskerLeft ((coefficientDerivedSystemEvaluationCalculus l E X).choose.reduction ⋙
        integralComparisonDerivedSequenceScalar l E L ι X)
      (coefficientDerivedSystemEvaluationCalculus l L X).choose.adjunction.counit

/-- The system scalar transformation is invertible.
Source: Stacks 0941 (blueprint: lem-pod-integral-pullback-composition-scalar).
Proof: the realization is an isomorphism and effective quotient model descent makes the
coherent counit invertible on scalar extensions of reduction systems. -/
theorem integralSystemScalarTransformation_isIso (X : Scheme.{u})
    (hX : ∀ x : X, IsUnit (l : X.residueField x))
    (K : DerivedCategory (scalarReductionSource l E X)) :
    IsIso ((integralSystemScalarTransformation l E L ι X hX).app K) := by
  have : IsIso ((coefficientDerivedSystemEvaluationCalculus l L X).choose.adjunction.counit.app
      ((integralComparisonDerivedSequenceScalar l E L ι X).obj
        ((coefficientDerivedSystemEvaluationCalculus l E X).choose.reduction.obj K))) :=
    ((effectiveQuotientModelDescent l E L ι (𝟙 X) hX hX
      (coefficientDerivedSystemEvaluationCalculus l E X).choose
      (coefficientDerivedSystemEvaluationCalculus l E X).choose
      (coefficientDerivedSystemEvaluationCalculus l L X).choose
      (integralSystemRoos l E X hX) (integralSystemRoos l L X hX)).1 K).2.2.2.2.2.2.1
  dsimp only [integralSystemScalarTransformation, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  have hi : IsIso ((integralSystemScalarModel l E L ι X hX).realization.hom.app K) :=
    Iso.isIso_hom ((integralSystemScalarModel l E L ι X hX).realization.app K)
  exact IsIso.comp_isIso' (Functor.map_isIso _ _) this

set_option allowUnsafeReducibility true in
attribute [local reducible] integralSystemReduction

/-- The system scalar comparison p_X : S ⋙ R_L ≅ R_E ⋙ H on constructible objects.
Source: Stacks 06YY, 0941 (blueprint: lem-pod-integral-pullback-composition-scalar).
Construction: componentwise the invertible system scalar transformation. -/
def integralSystemScalarIso (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)] :
    sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
        E L ι X ⋙ integralSystemReduction l L X ≅
      integralSystemReduction l E X ⋙ integralComparisonDerivedSequenceScalar l E L ι X :=
  NatIso.ofComponents
    (fun K ↦ @asIso _ _ _ _ ((integralSystemScalarTransformation l E L ι X
      (fun x ↦ isUnit_of_invertible (l : X.residueField x))).app K.obj)
      (integralSystemScalarTransformation_isIso l E L ι X _ K.obj))
    (fun {_ _} a ↦ (integralSystemScalarTransformation l E L ι X
      (fun x ↦ isUnit_of_invertible (l : X.residueField x))).naturality a.hom)

/-- Coherent reduction intertwines the scalar/pullback comparison of completed pullback
with the whole-system scalar/pullback comparison.
Source: Stacks 07A4, 0941 (blueprint: lem-pod-integral-pullback-composition-scalar).
Proof: this is the pullback clause of scalarExtensionTowerCoherence, for the
completed-operation models whose calculus, Roos and pullback fields are the pinned
ones, and the pinned scalar models. -/
theorem integralPullbackSystemIso_scalar {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (f : X ⟶ Y)
    (K : sfIntegralConstructibleCategory l E Y) :
    (integralSystemReduction l L X).map (integralPullbackScalarComparison l E L ι f K).hom ≫
        (integralPullbackSystemIso l L f).hom.app
          ((sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
            E L ι Y).obj K) ≫
        (finiteSystemDerivedPullback (integralSystemRings l L)
          (integralSystemTransition l L) f).map
            ((integralSystemScalarIso l E L ι Y).hom.app K) =
      (integralSystemScalarIso l E L ι X).hom.app ((constructibleIntegralPullback l E f).obj K) ≫
        (integralComparisonDerivedSequenceScalar l E L ι X).map
          ((integralPullbackSystemIso l E f).hom.app K) ≫
        (integralComparisonSystemScalarPullback l E L ι f).hom.app
          ((integralSystemReduction l E Y).obj K) := by
  let W : Bool → Scheme.{u} := fun b ↦ cond b X Y
  have hl : ∀ (a : Bool) (x : W a), IsUnit (l : (W a).residueField x) := by
    intro a
    cases a
    · exact fun y ↦ isUnit_of_invertible (l : Y.residueField y)
    · exact fun x ↦ isUnit_of_invertible (l : X.residueField x)
  let ME := integralSystemModels l E W hl
  let ML := integralSystemModels l L W hl
  exact (ScalarExtensionTower.scalarExtensionTowerCoherence l E L ι W ME ML
    (integralSystemScalarModel l E L ι X (hl true))
    (integralSystemScalarModel l E L ι Y (hl false))
    (ScalarExtensionTower.realizationModels l E L ι W ME ML hl false).1.some
    (ScalarExtensionTower.realizationModels l L L (AlgHom.id _ _) W ML ML hl false).1.some
    f (coefficientPrime_isUnit l X) (coefficientPrime_isUnit l Y) K K).2.2.1


end SystemScalar

end WeilConjectures
