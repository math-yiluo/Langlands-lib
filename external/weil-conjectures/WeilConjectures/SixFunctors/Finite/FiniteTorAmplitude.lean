/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude

/-!
# Constructible coefficient categories with finite Tor amplitude

Source: Weil conjectures blueprint, `sec-smooth-purity/sk-def-sf-operations`,
`definition-constructible-sheaves`, order 1464 (blueprint: definition-constructible-sheaves).

Finite coefficients impose finite Tor amplitude in addition to constructibility.
Integral coefficients impose one Tor interval for all positive finite reductions.
At field coefficients the notation is an alias for the bounded constructible category
itself, including its common-stage interpretation at algebraically closed coefficients;
`finiteTorFieldCoefficientCategory` expresses this alias parametrically in that category.
Triangulated closure is supplied by separate statement nodes, not by these definitions.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- The finite-level predicate defining `Dᵇ_ctf(Y,A_{E,n})`: bounded constructibility
and finite Tor amplitude. Its full subcategory is `finiteTorConstructibleCategory`.
Source: blueprint order 1464 (blueprint: definition-constructible-sheaves). -/
noncomputable def finiteTorConstructible
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    (Y : AlgebraicGeometry.Scheme.{u}) :
    ObjectProperty (proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E n)) :=
  intrinsicFiniteTorsionConstructible l E n hn Y ⊓
    fun K ↦ HasFiniteProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E n) K

/-- The full finite-level constructible category of finite Tor amplitude.
Source: blueprint order 1464 (blueprint: definition-constructible-sheaves). -/
noncomputable abbrev finiteTorConstructibleCategory
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    (Y : AlgebraicGeometry.Scheme.{u}) :=
  (finiteTorConstructible l E n hn Y).FullSubcategory

/-- The integral predicate defining `Dᵇ_ctf(Y,O_E)`: membership in the actual
bounded constructible derived-complete category and a single ordered Tor interval
for all reductions. Index `n` denotes exponent `n+1`, so every positive level occurs.
Source: blueprint order 1464 (blueprint: definition-constructible-sheaves). -/
noncomputable def finiteTorConstructibleIntegral
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (Y : AlgebraicGeometry.Scheme.{u}) :
    ObjectProperty (DerivedCategory (scalarReductionSource.{u, u} l E Y)) :=
  sfIntegralConstructible l E Y ⊓
    fun K ↦ ∃ a b : ℤ, a ≤ b ∧ ∀ n : ℕ,
      HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E (n + 1))
        ((scalarReductionDerivedExtension.{u, u} l E Y n).obj K) a b

/-- The full integral finite-Tor subcategory of `Dᵇ_c(Y,O_E)`.
Source: blueprint order 1464 (blueprint: definition-constructible-sheaves). -/
noncomputable abbrev finiteTorConstructibleIntegralCategory
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (Y : AlgebraicGeometry.Scheme.{u}) :=
  (finiteTorConstructibleIntegral l E Y).FullSubcategory

end WeilConjectures
