/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Ideal.Operations

/-!
# The order of an element with respect to an ideal

An element not in `⋂ₙ Iⁿ` lies in some `I ^ r` but not in `I ^ (r + 1)`. We also record that if
`c * a ∈ I` for every `a` in a generating set `S`, then `c * x ∈ I` for every `x ∈ span S`, and
that an element of `I • M` is `∑ₖ γₖ • wₖ` for given generators `γ` of `I`.
-/

@[expose] public section

variable {A : Type*} [CommRing A] {I : Ideal A}

namespace Ideal

/-- If `a ∉ ⋂ₙ Iⁿ`, then `a` has a well-defined `I`-adic order. -/
theorem exists_mem_pow_notMem_pow_succ_of_notMem_iInf {a : A} (h : a ∉ ⨅ r : ℕ, I ^ r) :
    ∃ r, a ∈ I ^ r ∧ a ∉ I ^ (r + 1) := by
  rw [Submodule.mem_iInf, not_forall] at h
  obtain ⟨n, hn⟩ := h
  induction n with
  | zero => simp at hn
  | succ n ih =>
    by_cases h : a ∈ I ^ n
    exacts [⟨n, h, hn⟩, ih h]

/-- If `c * a ∈ I` for all `a ∈ S`, then `c * x ∈ I` for all `x ∈ span S`. -/
lemma mul_mem_of_mem_span_of_forall (S : Set A) (I : Ideal A) (c : A) (h : ∀ a ∈ S, c * a ∈ I)
    {x : A} (hx : x ∈ Ideal.span S) : c * x ∈ I := by
  induction hx using Submodule.span_induction with
  | mem a ha => exact h a ha
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact I.add_mem hx hy
  | smul r x _ hx => rw [smul_eq_mul, mul_left_comm]; exact I.mul_mem_left r hx

end Ideal

namespace Submodule

/-- An element of `I • M` is `∑ₖ γₖ • wₖ` for given generators `γ` of `I`. -/
lemma exists_eq_sum_smul_of_mem_smul_top {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {r : ℕ} {γ : Fin r → R} {I : Ideal R} (hγ : Ideal.span (Set.range γ) = I)
    {x : M} (hx : x ∈ I • (⊤ : Submodule R M)) : ∃ w : Fin r → M, x = ∑ k, γ k • w k := by
  let Φ : (Fin r → M) →ₗ[R] M :=
    { toFun := fun w ↦ ∑ k, γ k • w k
      map_add' := fun _ _ ↦ by simp [Finset.sum_add_distrib, smul_add]
      map_smul' := fun c w ↦ by
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
        exact Finset.sum_congr rfl fun k _ ↦ smul_comm _ _ _ }
  have hle : I • (⊤ : Submodule R M) ≤ LinearMap.range Φ := by
    rw [Submodule.smul_le]
    intro c hc m _
    rw [← hγ, Submodule.mem_span_range_iff_exists_fun] at hc
    obtain ⟨a, rfl⟩ := hc
    refine ⟨fun k ↦ a k • m, ?_⟩
    simp [Φ, Finset.sum_smul, smul_smul, mul_comm]
  obtain ⟨w, hw⟩ := hle hx
  exact ⟨w, hw.symm⟩

end Submodule
