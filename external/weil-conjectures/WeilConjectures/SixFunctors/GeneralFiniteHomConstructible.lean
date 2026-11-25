/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Stability.HomDevissage

/-!
# Finite coefficient internal Hom preserves constructibility

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/`
`sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/`
`thm-coef-finite-hom.proof.md`, Paragraph 1 (blueprint: lem-coef-general-finite-hom-constructible).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite AlgebraicGeometry Scheme
open AlgebraicGeometry

namespace WeilConjectures

/-- For a finite or algebraically closed field and a finite coefficient ring killed by
an ell-power, internal derived Hom preserves bounded constructibility and finite Tor amplitude.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/`
`sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/`
`thm-coef-finite-hom.proof.md`, Paragraph 1 (blueprint: lem-coef-general-finite-hom-constructible).

The source library proves the stronger result for every field with an invertible coefficient
exponent.  The hypotheses here provide such an exponent directly: if `ell ^ n` annihilates `A`,
then its image in `Γ(Spec k)` is a unit because `ell` is a unit in `k`; transport along `aX`
gives the required instance on `X`.
-/
theorem generalFiniteHomConstructible
    {k : Type u} [Field k] (_hk : Finite k ∨ IsAlgClosed k)
    (ell : ℕ) [Fact ell.Prime] (_hell : IsUnit (ell : k))
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (_hA : ∃ n : ℕ, (ell ^ n : A) = 0)
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    {K M : AlgebraicGeometry.Etale.DerivedCategoryModule A X}
    (hK : AlgebraicGeometry.Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} A) X K)
    (hM : AlgebraicGeometry.Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} A) X M) :
    AlgebraicGeometry.Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} A) X
      (((AlgebraicGeometry.Etale.derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj M) := by
  obtain ⟨n, hn⟩ := _hA
  have : HasInvertibleExponent A (Spec (.of k)) := by
    refine ⟨ell ^ n, ?_, ?_, ?_⟩
    · exact pow_pos (Fact.out : ell.Prime).pos n
    · simpa only [Nat.cast_pow] using hn
    · simpa only [map_pow, map_natCast, Nat.cast_pow] using
        (_hell.map (Scheme.ΓSpecIso (.of k)).inv.hom).pow n
  let _ : HasInvertibleExponent A X := HasInvertibleExponent.of_hom aX
  exact AlgebraicGeometry.Etale.constructibleFiniteTor_derivedHom_of_field A aX hK hM

end WeilConjectures
