/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
import WeilConjectures.CategoryTheory.ScalarLocalization.SemilinearScalarLocalization

/-! # A step of coherent isomorphism pullback -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
namespace WeilConjectures
attribute [local irreducible] constructibleIntegralPullback rationalDerivedPullback
  sfRationalTriangulationDatum

/-- Localization of an already linear triangulated integral pullback, with its
prescribed rational degree-one shift normalization.
Source: current blueprint sec-poincare-duality/sk-thm-frobenius,
prop-constructible-truncations.proof.md, final automorphism sentence; parent step 6.
(blueprint: lem-pod-isomorphism-pullback-rational-exact).

Proof: apply semilinear scalar localization with the identity map of the coefficient
integers. Its coefficient map is the identity by uniqueness. The extension functor has
exactly the object and pure-tensor formulas of rationalDerivedPullback, so uniqueness
identifies them. Use the two published raw scalar-localization triangulation data:
their degree-one shifts are the integral shifts tensored with one, their localization
shift comparisons are identities, and their distinguished triangles are precisely
isomorphic images of integral distinguished triangles. The extension_exact theorem
therefore provides the displayed rational shift and exactness. This fixes the connecting
arrow as well as the first two triangle arrows. It does not assert integral exactness,
construct an inverse-image comparison, preserve standard halves, or compare coefficients.
Zero objects, torsion maps and empty schemes cause no exception. -/
theorem isomorphismPullbackRationalExact
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
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

end WeilConjectures
