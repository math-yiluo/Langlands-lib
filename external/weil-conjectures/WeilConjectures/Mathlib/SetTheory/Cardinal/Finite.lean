/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Cardinality of a finite product

If a finite product `∀ i, β i` has the same nonzero cardinality as one of its factors `β i`,
then every other factor is a subsingleton.

## Main results

- `Nat.subsingleton_of_card_pi_eq`.
-/

@[expose] public section

/-- If the finite product `∀ i, β i` has the same nonzero cardinality as its factor `β i`, then
every other factor `β j`, `j ≠ i`, is a subsingleton. -/
theorem Nat.subsingleton_of_card_pi_eq {ι : Type*} [Finite ι] {β : ι → Type*} {i j : ι}
    (hij : j ≠ i) (h : Nat.card (∀ i, β i) = Nat.card (β i)) (hi : Nat.card (β i) ≠ 0) :
    Subsingleton (β j) := by
  classical
  have := Fintype.ofFinite ι
  rw [Nat.card_pi, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)] at h
  have h1 : ∏ x ∈ Finset.univ.erase i, Nat.card (β x) = 1 := (Nat.mul_eq_left hi).1 h
  have hj : Nat.card (β j) ∣ 1 :=
    h1 ▸ Finset.dvd_prod_of_mem _ (Finset.mem_erase.2 ⟨hij, Finset.mem_univ j⟩)
  exact (Nat.card_eq_one_iff_unique.1 (Nat.dvd_one.1 hj)).1
