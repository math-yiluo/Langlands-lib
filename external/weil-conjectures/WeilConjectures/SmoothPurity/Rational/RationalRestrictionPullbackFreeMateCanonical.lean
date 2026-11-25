/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FiniteRationalDerivedOperations
import WeilConjectures.SmoothPurity.Rational.RationalRestrictionPullbackFreeMateAfterExtension
public import WeilConjectures.SmoothPurity.Rational.RationalScalarExtensionReflectsIsomorphisms
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Canonical finite-free mate calculation

Source: Bhatt--Scholze, Proposition 6.8.14(2), Remark 6.8.15;
finite-free trace coordinates on the canonical restriction adjunction.
(blueprint: new-sf-rational-restriction-pullback-free-mate-canonical).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.style.haveILetI false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

/-- The normalized mate is invertible on scalar-extended objects for the
canonical restriction adjunction supplied by finite rational scalar extension.

Source: Bhatt--Scholze, Proposition 6.8.14(2), Remark 6.8.15.

Proof: choose an E-basis of F and its trace-dual basis. On a K-flat
representative, finite-free completion identifies the canonical restriction
and extension adjunction with the ordinary tensor/restriction adjunction.
Pullback preserves the finite coordinate sums, and the two dual-basis
identities show that the inverse normalized scalar comparison has an invertible
mate on the scalar extension of every E-object. Localization and the recorded
normalization transport this equality to the raw rational categories. -/
theorem rationalRestrictionPullback_freeMate_canonical
    (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (M : sfRationalConstructibleCategory l E Y) :
    IsIso (((mateEquiv
      (rationalScalarExtension_leftAdjunction l E F ι Y)
      (rationalScalarExtension_leftAdjunction l E F ι X)).symm
      (TwoSquare.mk _ _ _ _ (rationalPullbackScalarComparison l E F ι f).inv)).app
        ((sfRationalScalarExtension l E Y 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι).obj M)) := by
  let TX := sfRationalScalarExtension l E X 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι
  letI : TX.ReflectsIsomorphisms :=
    rationalScalarExtension_reflects_isomorphisms l E F ι X
  have h := rationalRestrictionPullback_freeMate_after_extension l E F ι f M
  letI := h
  exact isIso_of_reflects_iso _ TX

end WeilConjectures
