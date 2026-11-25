/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralReconstruction.ExceptionalIntegralReconstructionInterfaces
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Etale origins of bounded constructible coefficient systems
Source: Zheng Construction 4.1 and Lemma 4.10.
(blueprint: lem-sf-exceptional-integral-coordinate-origin).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local semireducible] AlgebraicGeometry.exceptionalProSystemDerived
  AlgebraicGeometry.exceptionalProLevelDerived AlgebraicGeometry.strictEtaleLevelDerived
universe u
open SheafOfModules CategoryTheory.Functor
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralReconstruction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem lowerBoundOfEvaluations (W : Scheme.{u})
    (P : ExceptionalProEvaluation W (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E))
    (M : DerivedCategory (CoefficientSystem (J := ProEt.topology W)
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E))) (a : ℤ)
    (h : ∀ n, ((P.evaluation n).obj M).IsGE a) : M.IsGE a := by
  apply (DerivedCategory.isGE_iff M a).2
  intro q hq
  apply (IsZero.iff_id_eq_zero _).2
  have hext {A B : CoefficientSystem (J := ProEt.topology W)
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E)}
      (f g : A ⟶ B) (hf : ∀ n, f.app n = g.app n) : f = g := by
    change CoefficientSystem.Hom (J := ProEt.topology W) A B at f g
    have hf' : f.app = g.app := funext hf
    cases f
    cases g
    cases hf'
    rfl
  apply hext
  intro n
  let ev := coefficientEvaluation (J := ProEt.topology W)
    (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E) n
  let := (coefficientEvaluation_exact (J := ProEt.topology W)
    (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E) n).1
  let := (coefficientEvaluation_exact (J := ProEt.topology W)
    (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E) n).2
  let ei := integralExceptionalProEvaluationModel l E W P n
  let hi : P.evaluation n ⋙ DerivedCategory.homologyFunctor _ q ≅
      DerivedCategory.homologyFunctor _ q ⋙ ev :=
    isoWhiskerRight ei (DerivedCategory.homologyFunctor _ q) ≪≫
      (ev.mapDerivedCategoryHomologyFunctorIso q).symm
  have hz := ((DerivedCategory.isGE_iff _ a).1 (h n) q hq).of_iso ((hi.app M).symm)
  exact hz.eq_of_src _ _

/-- Common finite constructible bounds imply origin in the recorded site comparison.
Source: Zheng Construction 4.1 and Lemma 4.10; finite-ring constructible origin.
(blueprint: lem-sf-exceptional-integral-coordinate-origin).

Proof: choose finite bounded constructible etale antecedents using finite-ring
comparison. Lift them through the exact quotient-ring realization equivalence.
Compose the site inverse comparison, its realization counit, the finite origin
isomorphism and the coordinate evaluation comparison. Full faithfulness of finite
realization lifts this isomorphism to the recorded evaluation category. Exact
inverse realization preserves the antecedent's lower bound. For the whole system,
the common input lower bound is preserved and reflected by the exact coordinate
realizations. Evaluation commutes with homology; the ordinary strict components
detect zero objects, proving the same lower bound on the whole system. The zero
and empty cases follow from the same componentwise zero-homology argument.
-/
theorem exceptionalIntegralCoordinateOrigin (W : Scheme.{u})
    (P : StrictEtaleEvaluation W (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E))
    (C : ExceptionalSystemSiteComparison _ _ W P)
    (M : IntegralSystemRealization.System l E W)
    (hM : IntegralSystemRealization.LevelBounds l E W M) :
    C.origin ((coordinates l E W).functor.obj M) := by
  classical
  obtain ⟨a, b, c, d, hab, hcd, hlevels⟩ := hM
  have finite (n : ℕ) : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
  let := finite
  have hlevel (n : ℕ) : ((coefficientSequenceDerivedEvaluation l E W n).obj M).IsGE a :=
    (DerivedCategory.isGE_iff _ a).2 fun q hq ↦ by
      by_contra hz
      have hb : a ≤ q ∧ q ≤ b := (hlevels n).2.1 hz
      omega
  have heval (n : ℕ) :
      ((C.proEvaluation.evaluation n).obj ((coordinates l E W).functor.obj M)).IsGE a := by
    let R := sfIntrinsicModuleEquivalence W
      (Padic.coefficientExtensionRing l E (n + 1))
    let Q := integralExceptionalProRealization l E W n
    let : Q.asEquivalence.functor.Additive :=
      inferInstanceAs (integralExceptionalProRealization l E W n).Additive
    let := hlevel n
    have hR := R.inverse.isGE_mapDerivedCategory_obj
      ((coefficientSequenceDerivedEvaluation l E W n).obj M) a
    let e := integralExceptionalCoordinatesFixed l E W C.proEvaluation M n
    have hQ : (Q.mapDerivedCategory.obj
        ((C.proEvaluation.evaluation n).obj ((coordinates l E W).functor.obj M))).IsGE a := by
      exact ⟨(DerivedCategory.TStructure.t.ge a).prop_of_iso e.symm hR.ge⟩
    let := hQ
    have hInv := Q.asEquivalence.inverse.isGE_mapDerivedCategory_obj
      (Q.mapDerivedCategory.obj
        ((C.proEvaluation.evaluation n).obj ((coordinates l E W).functor.obj M))) a
    exact ⟨(DerivedCategory.TStructure.t.ge a).prop_of_iso
      (Q.asEquivalence.mapDerivedCategory.unitIso.app _).symm hInv.ge⟩
  refine ⟨⟨a, lowerBoundOfEvaluations l E W C.proEvaluation _ a heval⟩, ?_⟩
  intro n
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let R := sfIntrinsicModuleEquivalence W A
  let V := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) W
  have horigin : ∃ L : Etale.BoundedConstructibleDerivedCategory
      (ULift.{u + 1, u} A) W,
      Nonempty ((ProEtale.finiteCoefficientIntrinsicDerivedComparison W A).obj L.obj ≅
        (coefficientSequenceDerivedEvaluation l E W n).obj M) := by
    apply (finiteRing_constructibleDerived_origin W A).2.2.1 _ |>.2
    refine ⟨(hlevels n).1.2, a, b, hab, ?_⟩
    intro q hq
    by_contra hz
    have hb : a ≤ q ∧ q ≤ b := (hlevels n).2.1 hz
    omega
  obtain ⟨L, ⟨eL⟩⟩ := horigin
  let eFixed : V.mapDerivedCategory.obj L.obj ≅ R.inverse.mapDerivedCategory.obj
      ((coefficientSequenceDerivedEvaluation l E W n).obj M) :=
    R.mapDerivedCategory.unitIso.app (V.mapDerivedCategory.obj L.obj) ≪≫
      R.inverse.mapDerivedCategory.mapIso
        ((Functor.mapDerivedCategoryCompIso V R.functor).app L.obj ≪≫ eL)
  let T := integralExceptionalEtaleRealization l E W n
  let : T.asEquivalence.functor.Additive :=
    inferInstanceAs (integralExceptionalEtaleRealization l E W n).Additive
  let N := T.asEquivalence.inverse.mapDerivedCategory.obj L.obj
  obtain ⟨r, t, hrt, hv⟩ := L.property.2
  have : L.obj.IsGE r := (DerivedCategory.isGE_iff _ r).2 fun q hq ↦ hv q (Or.inl hq)
  have hN : N.IsGE r := T.asEquivalence.inverse.isGE_mapDerivedCategory_obj L.obj r
  let B := Systems.siteRealization l E W P C
  let Q := integralExceptionalProRealization l E W n
  let e : Q.mapDerivedCategory.obj ((C.image.level n).inverse.obj N) ≅
      Q.mapDerivedCategory.obj
        ((C.proEvaluation.evaluation n).obj ((coordinates l E W).functor.obj M)) :=
    (integralExceptionalSiteDerivedInverse l E W P B n).app N ≪≫
      V.mapDerivedCategory.mapIso (T.asEquivalence.mapDerivedCategory.counitIso.app L.obj) ≪≫
      eFixed ≪≫ (integralExceptionalCoordinatesFixed l E W C.proEvaluation M n).symm
  exact ⟨N, ⟨r, hN⟩, ⟨Q.mapDerivedCategory.preimageIso e⟩⟩

end WeilConjectures.ExceptionalIntegralReconstruction
