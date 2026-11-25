/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Derivations and powers of an ideal

A derivation lowers the `I`-adic order by at most one: it maps `I ^ (r + 1)` into `I ^ r`.
-/

@[expose] public section

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A] {I : Ideal A}

/-- A derivation lowers the `I`-adic order by at most one. -/
theorem Derivation.map_mem_pow_of_mem_pow_succ (D : Derivation k A A) {r : ℕ} {a : A}
    (ha : a ∈ I ^ (r + 1)) : D a ∈ I ^ r := by
  induction r generalizing a with
  | zero => simp
  | succ r ih =>
    rw [pow_succ'] at ha
    refine Submodule.mul_induction_on ha (fun b hb c hc ↦ ?_) (fun b c hb hc ↦ ?_)
    · rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, pow_succ']
      exact add_mem (Ideal.mul_mem_mul hb (ih hc))
        (Ideal.mul_mem_right _ _ (by rw [← pow_succ']; exact hc))
    · rw [map_add]
      exact add_mem hb hc
