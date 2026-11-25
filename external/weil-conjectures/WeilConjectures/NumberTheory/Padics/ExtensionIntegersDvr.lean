/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique

/-!
# The ring of integers of a finite extension of the p-adic numbers

Source: Weil conjectures blueprint, `chap-Nagata-compactification-and-Chows-lemma`,
`proposition-dense-compactifications-form-cofiltered-category`, `def-weil-finite-field-fiber`, order
411; Serre, Local Fields, Chapter II, §2, Proposition 3 and Chapter I, §1, Proposition 1
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

namespace Padic

/-- The sets of elements of absolute value at most one and less than one in a finite
extension of `ℚ_[l]` form its ring of integers and maximal ideal. The ring is a DVR with
finite residue field. Uniformizers attain the largest nonzero value in the maximal ideal,
exist, and differ by units; every nonzero field element has a unique unit-times-integer-power
expression for a fixed uniformizer.

Source: blueprint `def-weil-finite-field-fiber`, order 411; Serre, Local Fields, Chapter II,
§2, Proposition 3 and Chapter I, §1, Proposition 1.
(auxiliary; not a blueprint node)

Proof: (1) By lem-weil-l-adic-extension-absolute-value the extending absolute value is
nonarchimedean. Equip `E` with its normed and valued field structures. The finite-dimensional
properness theorem lem-weil-l-adic-extension-proper, applied over the proper field `ℚ_[l]`,
makes `E` proper. (2) Apply lem-weil-l-adic-extension-dvr-finite-residue to obtain the DVR
and finite residue field. Its integer ring and maximal ideal have exactly the indicated
membership conditions. (3) The ultrametric inequality and multiplicativity give subring
and ideal closure. An integer is a unit exactly when its value is one, by considering its
inverse. Thus the ideal is the unique maximal ideal; every field element or its inverse
is integral, giving the fraction field. (4) Choose a generator of the nonzero maximal ideal
using def-sc-discrete-valuation-ring. By lem-weil-pbc-dvr-unit-times-uniformizer-power every
nonzero integer is a unit times a nonnegative power of this generator. Units have value one,
so the nonzero values in the maximal ideal are its value to positive integer powers. The
largest is its value; an integer generates the ideal precisely when its exponent is one.
Writing a nonzero field element as a quotient of integers gives an integer exponent.
Comparison of absolute values gives uniqueness of the exponent, and cancellation gives
uniqueness of the unit. In particular, any two generators differ by a unit. -/
theorem extension_integers_dvr (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (abv : AbsoluteValue E ℝ)
    (h_ext : ∀ a : ℚ_[l], abv (algebraMap ℚ_[l] E a) = ‖a‖) :
    ∃ O : Subring E, ∃ m : Ideal O,
      (∀ x : E, x ∈ O ↔ abv x ≤ 1) ∧
      (∀ x : O, x ∈ m ↔ abv (x : E) < 1) ∧
      (∀ x : O, IsUnit x ↔ abv (x : E) = 1) ∧
      IsLocalRing O ∧ m.IsMaximal ∧
      (∀ J : Ideal O, J.IsMaximal → J = m) ∧
      IsFractionRing O E ∧
      IsDiscreteValuationRing O ∧ IsPrincipalIdealRing O ∧ m ≠ ⊥ ∧
      (∀ J : Ideal O, J.IsPrime ∧ J ≠ ⊥ ↔ J = m) ∧
      Finite (O ⧸ m) ∧
      (∃ r : ℝ,
        (∃ y : O, y ∈ m ∧ y ≠ 0 ∧ abv (y : E) = r) ∧
        (∀ y : O, y ∈ m → y ≠ 0 → abv (y : E) ≤ r) ∧
        (∀ π : O, Ideal.span ({π} : Set O) = m ↔ π ≠ 0 ∧ abv (π : E) = r)) ∧
      (∃ π : O, Ideal.span ({π} : Set O) = m) ∧
      (∀ π π' : O, Ideal.span ({π} : Set O) = m →
        Ideal.span ({π'} : Set O) = m → ∃ v : Oˣ, π' = (v : O) * π) ∧
      (∀ π : O, Ideal.span ({π} : Set O) = m → ∀ x : Eˣ,
        ∃! p : Oˣ × ℤ, (x : E) = ((p.1 : O) : E) * (π : E) ^ p.2) := by
  obtain ⟨O, m, hcore⟩ := extension_integers_dvr_core l E abv h_ext
  rcases hcore with ⟨hO, hm, hu, hlocal, hmax, hmax_unique, hfrac, hdvr,
    hpid, hm0, hprime, hfinite, hr, hgen⟩
  obtain ⟨hassoc, hexists⟩ :=
    extension_integers_dvr_factorization E O m hdvr hm0 hmax hfrac hgen
  have hunique := extension_integers_dvr_factorization_unique E O m hdvr hmax hfrac
  refine ⟨O, m, hO, hm, hu, hlocal, hmax, hmax_unique, hfrac, hdvr, hpid, hm0,
    hprime, hfinite, hr, hgen, hassoc, ?_⟩
  intro π hπ x
  obtain ⟨p, hp⟩ := hexists π hπ x
  refine ⟨p, hp, ?_⟩
  intro q hq
  exact (hunique π hπ x p q hp hq).symm

end Padic
