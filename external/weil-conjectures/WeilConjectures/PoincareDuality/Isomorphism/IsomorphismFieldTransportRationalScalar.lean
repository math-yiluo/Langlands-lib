/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Isomorphism.IsomorphismFieldTransportClauses

/-! # A step of normalized isomorphism transport -/

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

open scoped TensorProduct

private theorem dependent_app_heq {A : Sort*} {B : A → Sort*}
    (f : (a : A) → B a) {a b : A} (h : a = b) : HEq (f a) (f b) := by
  cases h
  rfl

private theorem map_heq {C : Type*} [Category* C] {D : Type*} [Category* D]
    (F : C ⥤ D) {K M K' M' : C} (hK : K = K') (hM : M = M')
    {f : K ⟶ M} {g : K' ⟶ M'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hK
  cases hM
  cases h
  rfl

/-- The integral inverse/scalar square localizes with its specified components.
Source: current blueprint sec-six-functors/sk-rem-sf-pf-done/
lem-fix-weil-operations.proof.md, inverse automorphism paragraph;
step 4 of lem-pod-isomorphism-field-transport.
(blueprint: lem-pod-isomorphism-field-transport-rational-scalar).

Proof: every rational object is the localization of its integral underlying object.
Replace both rational epsilons by their integral localized components, using the
stage normalization fields. The specified rational scalar comparison has exactly
the localized integral alpha component. The pure-tensor pullback formula, with
coefficient one, identifies its image with the localization of the integral
pullback image. The scalar-extension localization square identifies the right side
with the localization of the integral scalar image. Apply the localization functor
to the assumed integral inverse/scalar equation, using preservation of composition.
The endpoint equalities are precisely those in the prescribed object formulas;
transporting along them yields the displayed equality. These are component equations
of the existing natural transformations, whose naturality already covers all
localized arrows; no choice of an integral representative of a rational arrow is used.
-/
theorem isomorphismFieldTransportRationalScalar
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (SE : IsomorphismFieldTransportStage l E g hX hY)
    (SL : IsomorphismFieldTransportStage l L g hX hY)
    (h : isomorphismFieldTransportScalarLaw l E L ι g) :
    isomorphismFieldTransportRationalScalarLaw l E L ι g hX hY SE SL := by
  intro K
  let P := constructibleIntegralPullback l E g
  let Q := constructibleIntegralPullback l E (inv g)
  let PL := constructibleIntegralPullback l L g
  let QL := constructibleIntegralPullback l L (inv g)
  let Pr := rationalDerivedPullback l E g
  let Qr := rationalDerivedPullback l E (inv g)
  let PLr := rationalDerivedPullback l L g
  let QLr := rationalDerivedPullback l L (inv g)
  let S (W : Scheme.{u}) := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W
  let T (W : Scheme.{u}) := sfRationalScalarExtension l E W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι
  let J (W : Scheme.{u}) := sfRationalConstructibleLocalization l E W
  let JL (W : Scheme.{u}) := sfRationalConstructibleLocalization l L W
  have oP (Z : sfRationalConstructibleCategory l E Y) :
      Pr.obj Z = (J X).obj (P.obj Z.obj) := SE.rational_object Z
  have oQ (Z : sfRationalConstructibleCategory l E X) :
      Qr.obj Z = (J Y).obj (Q.obj Z.obj) :=
    (rationalDerivedPullback_existsUnique l E (inv g)).exists.choose_spec.2.1 Z
  have oPL (Z : sfRationalConstructibleCategory l L Y) :
      PLr.obj Z = (JL X).obj (PL.obj Z.obj) := SL.rational_object Z
  have oQL (Z : sfRationalConstructibleCategory l L X) :
      QLr.obj Z = (JL Y).obj (QL.obj Z.obj) :=
    (rationalDerivedPullback_existsUnique l L (inv g)).exists.choose_spec.2.1 Z
  have oT (W : Scheme.{u}) (Z : sfRationalConstructibleCategory l E W) :
      (T W).obj Z = (JL W).obj ((S W).obj Z.obj) :=
    (sfRationalScalarExtension_existsUnique l E W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec.2.1 Z
  have mQL (A B : sfIntegralConstructibleCategory l L X) (f : A ⟶ B) :
      HEq (QLr.map ((JL X).map f)) ((JL Y).map (QL.map f)) := by
    exact (rationalDerivedPullback_existsUnique l L (inv g)).exists.choose_spec.2.2 A B f 1
  have mT (W : Scheme.{u}) (A B : sfIntegralConstructibleCategory l E W)
      (f : A ⟶ B) :
      HEq ((T W).map ((J W).map f)) ((JL W).map ((S W).map f)) := by
    have hh := (sfRationalScalarExtension_existsUnique l E W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec.2.2 A B f 1
    simpa only [T, J, JL, S, sfRationalScalarExtension,
      sfRationalConstructibleLocalization, ScalarLocalization.localization, map_one] using hh
  let a := (integralPullbackScalarComparison l E L ι g K.obj).hom
  let b := (integralPullbackScalarComparison l E L ι (inv g) (P.obj K.obj)).hom
  have hI : b ≫ QL.map a ≫ SL.epsilon.hom.app ((S Y).obj K.obj) =
      (S Y).map (SE.epsilon.hom.app K.obj) := by
    apply ObjectProperty.hom_ext
    change b.hom ≫ (integralDerivedPullback l L (inv g)).map a.hom ≫
        (SL.epsilon.hom.app ((S Y).obj K.obj)).hom =
      (integralScalarExtensionOfUniverses l E L ι Y).map (SE.epsilon.hom.app K.obj).hom
    rw [eq_of_heq (SL.epsilon_formula _), eq_of_heq (SE.epsilon_formula _)]
    exact eq_of_heq (h K.obj)
  have hb : HEq
      ((rationalPullbackScalarComparison l E L ι (inv g)).hom.app (Pr.obj K))
      ((JL Y).map b) := by
    have hh := (rationalPullbackScalarComparison_existsUnique l E L ι
      (inv g)).exists.choose_spec (Pr.obj K)
    exact hh.trans (dependent_app_heq
      (fun Z : sfRationalConstructibleCategory l E X ↦
        (JL Y).map (integralPullbackScalarComparison l E L ι (inv g) Z.obj).hom) (oP K))
  have ha : HEq ((rationalPullbackScalarComparison l E L ι g).hom.app K)
      ((JL X).map a) :=
    (rationalPullbackScalarComparison_existsUnique l E L ι g).exists.choose_spec K
  have hx : (T X).obj (Pr.obj K) = (JL X).obj ((S X).obj (P.obj K.obj)) := by
    simp only [oT, oP]
    rfl
  have hy : PLr.obj ((T Y).obj K) = (JL X).obj (PL.obj ((S Y).obj K.obj)) := by
    simp only [oPL, oT]
    rfl
  have hm := (map_heq QLr hx hy ha).trans (mQL _ _ a)
  have he : HEq (SL.rationalEpsilon.hom.app ((T Y).obj K))
      ((JL Y).map (SL.epsilon.hom.app ((S Y).obj K.obj))) :=
    (SL.rational_epsilon_formula ((T Y).obj K)).trans
      (dependent_app_heq (fun Z : sfRationalConstructibleCategory l L Y ↦
        (JL Y).map (SL.epsilon.hom.app Z.obj)) (oT Y K))
  have h0 : (T Y).obj (Qr.obj (Pr.obj K)) =
      (JL Y).obj ((S Y).obj (Q.obj (P.obj K.obj))) := by
    simp only [oT, oQ, oP]
    rfl
  have h1 : QLr.obj ((T X).obj (Pr.obj K)) =
      (JL Y).obj (QL.obj ((S X).obj (P.obj K.obj))) := by
    simp only [oQL, oT, oP]
    rfl
  have h2 : QLr.obj (PLr.obj ((T Y).obj K)) =
      (JL Y).obj (QL.obj (PL.obj ((S Y).obj K.obj))) := by
    simp only [oQL, oPL, oT]
    rfl
  have hleft := heq_comp h0 h1 (oT Y K) hb (heq_comp h1 h2 (oT Y K) hm he)
  have hPQ : Qr.obj (Pr.obj K) = (J Y).obj (Q.obj (P.obj K.obj)) := by
    simp only [oQ, oP]
    rfl
  have hright := (map_heq (T Y) hPQ rfl (SE.rational_epsilon_formula K)).trans
    (mT Y _ _ (SE.epsilon.hom.app K.obj))
  have hloc := congrArg (JL Y).map hI
  simp only [Functor.map_comp] at hloc
  exact eq_of_heq (hleft.trans ((heq_of_eq hloc).trans hright.symm))

end WeilConjectures
