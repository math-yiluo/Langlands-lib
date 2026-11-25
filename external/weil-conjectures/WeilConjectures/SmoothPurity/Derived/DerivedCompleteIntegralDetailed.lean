/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedComplete
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Bounded constructible derived-complete integral coefficients

Source: Weil conjectures blueprint, `sec-smooth-purity/sk-def-sf-operations`,
order 1459 (blueprint: def-weil-derived-complete-integral-detailed).
The integral triangulation statement compiles this same canonical interface in a
paired source packet to retain its recorded independent coefficient universes.
-/

@[expose] public section

set_option autoImplicit false

universe d u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- The bounded constructible derived-complete integral objects are the objects whose
reductions are finite-torsion constructible in a common cohomological interval.
Source: blueprint order 1459 (blueprint: def-weil-derived-complete-integral-detailed).
The reduction at level `n + 1` is `integralDerivedReduction`; the predicate
`intrinsicFiniteTorsionConstructible` renders bounded constructibility, and
`proEtaleCohomologicalSupport` renders the support condition. -/
noncomputable def boundedConstructibleDerivedCompleteIntegral
    (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (Y : AlgebraicGeometry.Scheme.{u}) :
    ObjectProperty (completedIntegralDerivedCategory l E Y D hl) :=
  fun K ↦ IsDerivedComplete l E Y D hl K ∧
    ∃ r s : ℤ, r ≤ s ∧
      ∀ n : ℕ,
        intrinsicFiniteTorsionConstructible l E (n + 1)
          (Nat.succ_le_succ (Nat.zero_le n)) Y
          ((integralDerivedReduction l E Y D hl n).obj K) ∧
          ∀ i : ℤ,
            i ∈ proEtaleCohomologicalSupport
              ((integralDerivedReduction l E Y D hl n).obj K) →
              r ≤ i ∧ i ≤ s

/-- The full subcategory `Dᵇ_c(Y, O_E)` on the derived-complete integral objects with
constructible reductions in one common cohomological interval. Triangulated closure
is a separate theorem and is not assumed in this definition.
Source: Weil conjectures blueprint, order 1459
(blueprint: def-weil-derived-complete-integral-detailed). -/
noncomputable abbrev boundedConstructibleDerivedCompleteIntegralCategory
    (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (Y : AlgebraicGeometry.Scheme.{u}) :=
  (boundedConstructibleDerivedCompleteIntegral D l hl E Y).FullSubcategory

end WeilConjectures

/- Stage-2 paired-interface rebuild for NZ integral Tor triangulation. -/
