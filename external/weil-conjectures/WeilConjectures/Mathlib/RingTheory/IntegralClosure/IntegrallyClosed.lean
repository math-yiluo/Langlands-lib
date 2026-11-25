/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Powers in the fraction field of an integrally closed domain

## Main statements

- `IsIntegrallyClosed.not_exists_pow_eq_algebraMap`: if `R` is an integrally closed domain with
  fraction field `K` and `a ∈ P \ P ^ 2` for a prime ideal `P` of `R`, then `a` is not an `n`-th
  power in `K` for any `2 ≤ n`.
-/

@[expose] public section

open Polynomial

/-- Let `R` be an integrally closed domain with fraction field `K`, and `a ∈ P \ P ^ 2` for a
prime ideal `P` of `R`. Then `a` is not an `n`-th power in `K` for `2 ≤ n`: an `n`-th root of `a`
in `K` is integral over `R`, hence lies in `R`, hence in `P`, so that `a ∈ P ^ n ⊆ P ^ 2`. -/
theorem IsIntegrallyClosed.not_exists_pow_eq_algebraMap {R K : Type*} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K] {P : Ideal R}
    [P.IsPrime] {a : R} (ha : a ∈ P) (ha2 : a ∉ P ^ 2) {n : ℕ} (hn : 2 ≤ n) :
    ¬ ∃ u : K, u ^ n = algebraMap R K a := by
  rintro ⟨u, hu⟩
  have hint : IsIntegral R u :=
    ⟨X ^ n - C a, monic_X_pow_sub_C a (by omega), by simp [hu]⟩
  obtain ⟨v, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← map_pow] at hu
  obtain rfl := IsFractionRing.injective R K hu
  exact ha2 (Ideal.pow_le_pow_right hn
    (Ideal.pow_mem_pow (Ideal.IsPrime.mem_of_pow_mem ‹_› n ha) n))
