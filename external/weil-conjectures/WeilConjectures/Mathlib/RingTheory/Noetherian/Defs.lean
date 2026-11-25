/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Bounded torsion in Noetherian modules

In a Noetherian module the `a`-power torsion is killed by a fixed power of `a`
(`IsNoetherian.exists_pow_smul_eq_zero_of_pow_smul_eq_zero`): the increasing chain of the
kernels of `aᵏ` stabilizes.
-/

@[expose] public section

/-- **The `a`-power torsion of a Noetherian module is bounded**: there is `c` such that every
element killed by some power of `a` is killed by `aᶜ`. -/
lemma IsNoetherian.exists_pow_smul_eq_zero_of_pow_smul_eq_zero {R N : Type*} [CommRing R]
    [AddCommGroup N] [Module R N] [IsNoetherian R N] (a : R) :
    ∃ c : ℕ, ∀ (y : N) (k : ℕ), a ^ k • y = 0 → a ^ c • y = 0 := by
  let f : ℕ →o Submodule R N :=
    ⟨fun k ↦ LinearMap.ker (a ^ k • LinearMap.id), fun k k' h y hy ↦ by
      simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at hy ⊢
      rw [← Nat.sub_add_cancel h, pow_add, mul_smul, hy, smul_zero]⟩
  obtain ⟨c, hc⟩ := monotone_stabilizes_iff_noetherian.2 inferInstance f
  refine ⟨c, fun y k hk ↦ ?_⟩
  rcases le_total c k with h | h
  · have hy : y ∈ f k := by simpa [f] using hk
    rw [← hc k h] at hy
    simpa [f] using hy
  · exact f.monotone h (by simpa [f] using hk)
