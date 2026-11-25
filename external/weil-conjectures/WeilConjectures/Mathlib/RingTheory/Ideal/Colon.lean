/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.Tactic.LinearCombination

/-!
# Colon ideals of principal ideals

For a non-zerodivisor `v`, the colon ideal `(v g) : (v)` is `(g)`
(`Ideal.colon_span_singleton_mul`).
-/

@[expose] public section

/-- For a non-zerodivisor `v`, the colon ideal `(v g) : (v)` is `(g)`. -/
lemma Ideal.colon_span_singleton_mul {B : Type*} [CommRing B] {v : B} (hv : v ∈ nonZeroDivisors B)
    (g : B) : (Ideal.span {v * g}).colon (Ideal.span {v} : Set B) = Ideal.span {g} := by
  ext c
  rw [Submodule.mem_colon, Ideal.mem_span_singleton']
  constructor
  · intro h
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp (h v (Ideal.mem_span_singleton_self v))
    refine ⟨r, ?_⟩
    have : v * (r * g - c) = 0 := by rw [smul_eq_mul] at hr; linear_combination hr
    exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hv).1 _ this)
  · rintro ⟨r, rfl⟩ s hs
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hs
    exact Ideal.mem_span_singleton'.mpr ⟨r * t, by rw [smul_eq_mul]; ring⟩
