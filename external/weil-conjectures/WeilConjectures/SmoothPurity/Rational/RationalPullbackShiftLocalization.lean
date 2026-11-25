/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
import WeilConjectures.CategoryTheory.ScalarLocalization.SemilinearScalarLocalization
import all WeilConjectures.SmoothPurity.Sf.SfRationalScalarExactOfIntegral

/-! # Localization of normalized pullback shifts

Source: the rationalization paragraph of the open-closed localization proof.
(blueprint: lem-sf-rational-pullback-shift-localization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry TensorProduct
namespace WeilConjectures
attribute [local irreducible] constructibleIntegralPullback rationalDerivedPullback
  sfRationalTriangulationDatum
private theorem localization_shift_obj (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) (J : sfRationalConstructibleCategory l E W) :
    J⟦(1 : ℤ)⟧ = (sfRationalConstructibleLocalization l E W).obj (J.obj⟦(1 : ℤ)⟧) :=
  Functor.congr_obj (sfRationalTriangulationDatum l E W).choose_spec.choose_spec.1 J

private theorem rational_shift_exact
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [(constructibleIntegralPullback l E g).CommShift ℤ]
    [(constructibleIntegralPullback l E g).IsTriangulated]
    [(constructibleIntegralPullback l E g).Linear (Padic.coefficientExtensionIntegers l E)] :
    ∃ s : (rationalDerivedPullback l E g).CommShift ℤ,
      (fun [_s : (rationalDerivedPullback l E g).CommShift ℤ] ↦
        (rationalDerivedPullback l E g).IsTriangulated ∧
        ∀ K : sfIntegralConstructibleCategory l E Y,
          HEq (((rationalDerivedPullback l E g).commShiftIso (1 : ℤ)).hom.app
            ((sfRationalConstructibleLocalization l E Y).obj K))
          ((sfRationalConstructibleLocalization l E X).map
            (((constructibleIntegralPullback l E g).commShiftIso (1 : ℤ)).hom.app K)))
        (_s := s) := by
  classical
  let R := Padic.coefficientExtensionIntegers l E
  let t := Padic.coefficientExtensionUniformizer l E
  let F := constructibleIntegralPullback l E g
  have : F.Additive := inferInstance
  let hF : ScalarLocalization.IsSemilinear (RingHom.id R) F :=
    fun K M a f ↦ F.map_smul a f
  let h := IsLocalization.Away.algebraMap_isUnit t (S := Localization.Away t)
  let J := ScalarLocalization.extension t t (RingHom.id R) h F hF
  have hc : ScalarLocalization.coefficientMap t t (RingHom.id R) h =
      RingHom.id (Localization.Away t) := by
    symm
    apply (ScalarLocalization.coefficientMap_unique _ _ _ _ _).1
    rfl
  have heq : rationalDerivedPullback l E g = J := by
    unfold rationalDerivedPullback
    apply (rationalDerivedPullback_existsUnique l E g).unique
      (rationalDerivedPullback_existsUnique l E g).exists.choose_spec
    refine ⟨inferInstance, fun K ↦ rfl, ?_⟩
    intro K M a c
    apply heq_of_eq
    change ScalarLocalization.extensionHom t t (RingHom.id R) h F hF K M
      (c ⊗ₜ[R] a) = c ⊗ₜ[R] F.map a
    have hm := (ScalarLocalization.existsUnique_semilinearHom t t
      (RingHom.id R) h F hF K M).exists.choose_spec c a
    simpa only [ScalarLocalization.extensionHom, hc, RingHom.id_apply] using hm
  rw [heq]
  let : (ScalarLocalization.localization R (sfIntegralConstructibleCategory l E Y)
      t).CommShift ℤ := sfRationalLocalizationCommShift l E Y
  let : (ScalarLocalization.localization R (sfIntegralConstructibleCategory l E X)
      t).CommShift ℤ := sfRationalLocalizationCommShift l E X
  exact ScalarLocalization.extension_exact t t (RingHom.id R) h
    (sfRationalTriangulationDatum l E Y).choose_spec.choose_spec.1
    (sfRationalTriangulationDatum l E X).choose_spec.choose_spec.1
    ((sfRationalTriangulationDatum l E Y).choose_spec.choose_spec.2
      |>.choose_spec.choose_spec.1)
    ((sfRationalTriangulationDatum l E X).choose_spec.choose_spec.2
      |>.choose_spec.choose_spec.1)
    ((sfRationalTriangulationDatum l E Y).choose_spec.choose_spec.2
      |>.choose_spec.choose_spec.2.choose_spec.2.2)
    ((sfRationalTriangulationDatum l E X).choose_spec.choose_spec.2
      |>.choose_spec.choose_spec.2.choose_spec.2.2)
    F hF

/-- A linear exact integral pullback localizes with its canonical shift square.
Source: current blueprint, sec-smooth-purity/sk-prop-sf-localization,
prop-sf-open-closed-triangle-all-stages.proof.md, rationalization paragraph.
(blueprint: lem-sf-rational-pullback-shift-localization).

Proof: identify the rational pullback with the semilinear extension for the identity
coefficient map using the object and pure-tensor formulas. Apply extension_exact to
obtain the normalized comparison at one and exactness for the image triangles.
The same formulas give the identity-component localization comparison. Its square at
one follows from the two normalized localization comparisons. The CommShift laws
extend that square to positive shifts by addition and to negative shifts by inverses.
This retains the localization comparisons at every integer, including zero. -/
theorem rationalPullbackShiftLocalization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [(constructibleIntegralPullback l E g).CommShift ℤ]
    [(constructibleIntegralPullback l E g).IsTriangulated]
    [(constructibleIntegralPullback l E g).Linear (Padic.coefficientExtensionIntegers l E)] :
    ∃ s : (rationalDerivedPullback l E g).CommShift ℤ,
      (fun [_s : (rationalDerivedPullback l E g).CommShift ℤ] ↦
        (rationalDerivedPullback l E g).IsTriangulated ∧
        (∀ K : sfRationalConstructibleCategory l E Y,
          HEq (((rationalDerivedPullback l E g).commShiftIso (1 : ℤ)).hom.app K)
            ((sfRationalConstructibleLocalization l E X).map
              (((constructibleIntegralPullback l E g).commShiftIso (1 : ℤ)).hom.app K.obj))) ∧
        ∃ e : sfRationalConstructibleLocalization l E Y ⋙ rationalDerivedPullback l E g ≅
            constructibleIntegralPullback l E g ⋙ sfRationalConstructibleLocalization l E X,
          (∀ K, HEq (e.hom.app K)
            (𝟙 ((rationalDerivedPullback l E g).obj
              ((sfRationalConstructibleLocalization l E Y).obj K)))) ∧
          NatTrans.CommShift e.hom ℤ) (_s := s) := by
  classical
  obtain ⟨s, hs, hn⟩ := rational_shift_exact l E g
  let := s
  let Q := sfRationalConstructibleLocalization l E Y
  let P := sfRationalConstructibleLocalization l E X
  let T := constructibleIntegralPullback l E g
  let F := rationalDerivedPullback l E g
  have ho (K : sfRationalConstructibleCategory l E Y) :
      F.obj K = P.obj (T.obj K.obj) := by
    simpa only [F, P, T, rationalDerivedPullback, sfRationalConstructibleLocalization,
      ScalarLocalization.localization] using
      (rationalDerivedPullback_existsUnique l E g).exists.choose_spec.2.1 K
  let e : Q ⋙ F ≅ T ⋙ P := NatIso.ofComponents
    (fun K ↦ eqToIso (ho (Q.obj K))) (by
      intro K M a
      change F.map (Q.map a) ≫ eqToHom (ho (Q.obj M)) =
        eqToHom (ho (Q.obj K)) ≫ P.map (T.map a)
      have hm : HEq (F.map (Q.map a)) (P.map (T.map a)) := by
        simpa only [F, Q, P, T, sfRationalConstructibleLocalization,
          ScalarLocalization.localization] using
          (show HEq ((rationalDerivedPullback l E g).map
              ((sfRationalConstructibleLocalization l E Y).map a))
            ((sfRationalConstructibleLocalization l E X).map
              ((constructibleIntegralPullback l E g).map a)) from by
            unfold rationalDerivedPullback
            have hm := (rationalDerivedPullback_existsUnique l E g).exists.choose_spec.2.2
              K M a 1
            dsimp only [sfRationalConstructibleLocalization, ScalarLocalization.localization]
              at hm ⊢
            with_unfolding_all exact hm)
      exact eq_of_heq ((comp_eqToHom_heq _ _).trans
        (hm.trans (eqToHom_comp_heq _ _).symm)))
  refine ⟨s, hs, fun K ↦ hn K.obj, e, ?_, ?_⟩
  · intro K
    exact eqToHom_heq_id_dom _ _ (ho (Q.obj K))
  · apply commShift_of_one
    apply localized_comparison_core Q P T F (fun K ↦ ho (Q.obj K)) e (fun _ ↦ rfl)
    · intro K
      exact (localization_shift_obj l E Y (Q.obj K)).symm
    · intro K
      exact (localization_shift_obj l E X (P.obj K)).symm
    · exact (sfRationalTriangulationDatum l E Y).choose_spec.choose_spec.2
        |>.choose_spec.choose_spec.1
    · exact (sfRationalTriangulationDatum l E X).choose_spec.choose_spec.2
        |>.choose_spec.choose_spec.1
    · exact hn

end WeilConjectures
