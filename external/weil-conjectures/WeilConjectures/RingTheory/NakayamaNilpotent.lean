/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Nakayama's lemma for a nilpotent ideal

Source: Stacks Project, Algebra, Lemma 00DV (lemma-NAK), parts (9)--(11)
(blueprint: lem-weil-pbc-nakayama-nilpotent).
-/

@[expose] public section

universe u v w

namespace RingTheory

/-- Let `R` be a commutative ring, `I` a nilpotent ideal, and `u : N →ₗ[R] M` a
linear map. If the induced map `N/IN → M/IM` (`Submodule.mapQ` on the quotients by
`I • ⊤`) is surjective, then `u` is surjective.

Source: Stacks Project, Algebra, Lemma 00DV (lemma-NAK), part (11),
using parts (9) and (10).

Proof:
0. Surjectivity of `N/IN → M/IM` says `M = u(N) + IM`, i.e.
   `LinearMap.range u ⊔ I • ⊤ = ⊤`.
1. If a module `Q` equals `I • Q`, induction gives `Q = I ^ n • Q` for every `n`.
   A power of the nilpotent ideal is zero, so `Q = 0`.
2. For submodules `L, L'` with `M = L + I • L'`, the quotient `M/L` equals
   `I • (M/L)`, so Step 1 gives `M = L`.
3. Apply Step 2 with `L = range u` and `L' = ⊤`; Step 0 then gives
   `range u = ⊤`, which is surjectivity of `u`.

(blueprint: lem-weil-pbc-nakayama-nilpotent)
-/
theorem surjective_of_surjective_mod_nilpotent
    (R : Type u) [CommRing R] (N : Type v) (M : Type w)
    [AddCommGroup N] [AddCommGroup M] [Module R N] [Module R M]
    (I : Ideal R) (u : N →ₗ[R] M)
    (hI : ∃ k : ℕ, 0 < k ∧ I ^ k = ⊥)
    (h : Function.Surjective ((I • ⊤ : Submodule R N).mapQ (I • ⊤ : Submodule R M) u
      (Submodule.smul_top_le_comap_smul_top I u))) :
    Function.Surjective u := by
  have hrange : (I • ⊤ : Submodule R M) ⊔ u.range = ⊤ := by
    apply (Submodule.map_mkQ_eq_top _ _).mp
    rw [← Submodule.range_mapQ (I • ⊤ : Submodule R N)
      (I • ⊤ : Submodule R M) u (Submodule.smul_top_le_comap_smul_top I u)]
    exact LinearMap.range_eq_top.mpr h
  have hpow : ∀ n : ℕ, (I ^ n • ⊤ : Submodule R M) ⊔ u.range = ⊤ := by
    intro n
    induction n with
    | zero => simp [Ideal.one_eq_top]
    | succ n ih =>
      calc
        (I ^ (n + 1) • ⊤ : Submodule R M) ⊔ u.range =
            I ^ n • (I • ⊤ : Submodule R M) ⊔ u.range := by
          rw [pow_succ, Submodule.mul_smul]
        _ = I ^ n • ((I • ⊤ : Submodule R M) ⊔ u.range) ⊔ u.range := by
          rw [Submodule.smul_sup, sup_assoc,
            sup_of_le_right (Submodule.smul_le_right (I := I ^ n) (N := u.range))]
        _ = (I ^ n • ⊤ : Submodule R M) ⊔ u.range := by rw [hrange]
        _ = ⊤ := ih
  obtain ⟨k, _, hk⟩ := hI
  apply LinearMap.range_eq_top.mp
  simpa [hk] using hpow k

end RingTheory
