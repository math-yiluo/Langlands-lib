/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FiniteRationalDerivedOperations
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SmoothPurity.Rational.RationalScalarExtensionRightAdjoint
import WeilConjectures.SmoothPurity.Rational.RationalRestrictionPullbackUnit

/-! # A single finite coefficient extension and the rational pullback right mate

Source: Bhatt--Scholze, Lemma 6.7.2, 6.8.14(2), Remark 6.8.15;
the finite-free coefficient step of the derived direct-image construction.
(blueprint: lem-sf-rational-pullback-scalar-right-mate).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

/-- The right mate of the normalized pullback comparison for one coefficient inclusion.

Source: Bhatt--Scholze, Lemma 6.7.2, 6.8.14(2), Remark 6.8.15; finite-free
coefficient argument in the derived direct-image construction
(blueprint: lem-sf-rational-pullback-scalar-right-mate).

Proof: write T for extension of coefficients and U for restriction. The finite
extension F/E is separable. The nondegenerate trace pairing identifies the dual
of F over E with F, so after inverting the uniformizer, U is left adjoint to T,
as well as right adjoint to T. These adjunctions restrict to the constructible
categories: restriction along a finite free coefficient extension preserves
finite generation, constructibility and derived completeness. The normalized
completed scalar functor agrees with ordinary scalar extension on complete
objects by finiteFreeCompletedScalarComparison. Localizing the integral
normalizations therefore gives the recorded rational T and its trace adjunction.

Transpose the inverse normalized scalar/pullback comparison under U left
adjoint to T. On a flat-term K-flat representative the result is the comparison
between pullback after forgetting the F action and forgetting that action after
pullback. It is invertible: both routes use the same underlying tensor complex,
and completed pullback and restriction commute with the normalized reduction
limits. The scalar unit sends a tensor generator m to 1 tensor m; the trace
counit contracts the dual basis. These formulas identify the transpose of the
recorded comparison, not merely an isomorphism between its endpoints. They
remain valid for E = F and for zero complexes and empty schemes.

Transpose a second time using the supplied adjunctions aE and aF. The iterated
mates identity identifies this double transpose with conjugation between the
composite adjunctions L_E U_X left adjoint to T_X R_E and U_Y L_F left adjoint
to R_F T_Y. Conjugation preserves and reflects isomorphisms. Consequently the
specified right mate is invertible, for any supplied right adjoints; no existence
of geometric right adjoints is assumed or concluded. -/
theorem rationalPullbackScalar_rightMate_isIso
    (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (RE : sfRationalConstructibleCategory l E X ⥤ sfRationalConstructibleCategory l E Y)
    (RF : sfRationalConstructibleCategory l F X ⥤ sfRationalConstructibleCategory l F Y)
    (aE : rationalDerivedPullback l E f ⊣ RE)
    (aF : rationalDerivedPullback l F f ⊣ RF) :
    IsIso ((mateEquiv aE aF
      (TwoSquare.mk _ _ _ _ (rationalPullbackScalarComparison l E F ι f).inv))) := by
  let TX := sfRationalScalarExtension l E X 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι
  let TY := sfRationalScalarExtension l E Y 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι
  let : TX.IsRightAdjoint := rationalScalarExtension_isRightAdjoint l E F ι X
  let : TY.IsRightAdjoint := rationalScalarExtension_isRightAdjoint l E F ι Y
  let bX := Adjunction.ofIsRightAdjoint TX
  let bY := Adjunction.ofIsRightAdjoint TY
  obtain ⟨e, he⟩ := rationalRestrictionPullback_unit l E F ι f
    TX.leftAdjoint TY.leftAdjoint bX bY
  let α := TwoSquare.mk _ _ _ _ (rationalPullbackScalarComparison l E F ι f).inv
  let δ := (mateEquiv bY bX).symm α
  have hδ : δ = e.hom := by
    ext K
    apply (bX.homEquiv _ _).injective
    change bX.unit.app _ ≫ TX.map (δ.app K) =
      bX.unit.app _ ≫ TX.map (e.hom.app K)
    rw [← he K]
    exact (unit_mateEquiv_symm bY bX α K).symm
  have : IsIso δ := by
    rw [hδ]
    infer_instance
  have h := iterated_mateEquiv_conjugateEquiv bY bX aF aE δ
  rw [Equiv.apply_symm_apply] at h
  change IsIso (mateEquiv aE aF α)
  rw [h]
  infer_instance

end WeilConjectures
