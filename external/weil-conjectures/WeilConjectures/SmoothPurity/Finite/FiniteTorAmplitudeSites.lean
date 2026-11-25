/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude

/-! # The finite-Tor constructible categories in the two site presentations

Source: Weil conjectures blueprint, sec-smooth-purity/sk-def-sf-operations,
order 1464 (blueprint: definition-constructible-sheaves).

This module supplies the ordinary-etale presentation using the recorded finite-value
constructibility and Tor-amplitude conventions. The recorded pro-etale, integral and
field-stage definitions remain unchanged in `WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace WeilConjectures

/-- The etale presentation of `Dᵇ_ctf(Y,A_{E,n})`, using the same quotient ring,
with its canonical universe lift, and the recorded etale constructibility convention.
Source: blueprint order 1464 (blueprint: definition-constructible-sheaves). -/
noncomputable def finiteTorConstructibleEtale
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (Y : Scheme.{u}) :
    ObjectProperty (Etale.DerivedCategoryModule
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) Y) :=
  letI : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  Etale.DerivedCategory.isBoundedConstructible
    (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) Y ⊓
    fun K ↦ ∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) Y a b K

end WeilConjectures
