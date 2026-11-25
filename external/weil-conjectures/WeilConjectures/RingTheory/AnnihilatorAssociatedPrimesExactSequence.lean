/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.AnnihilatorAssociatedPrimes
public import Mathlib.Algebra.Exact.Basic

/-!
# Associated primes in a short exact sequence over an arbitrary ring

Source: Stacks Project, Algebra, Lemma 02M3 (lemma-ass), first two assertions
(blueprint: lem-weil-pbc-associated-primes-exact-sequence).
-/

@[expose] public section

universe uR uSub uMid uQuot

namespace RingTheory

/-- In a short exact sequence, associated primes of the submodule are associated to the
middle module, whose associated primes belong to those of either outer module.
An injective linear map also preserves every element annihilator.
Source: Stacks Project, Algebra, Lemma 02M3, first two assertions and their proof
(blueprint: lem-weil-pbc-associated-primes-exact-sequence).

Proof (the three elementary steps of the node):
1. Linearity gives `a • f z' = f (a • z')`; injectivity makes this zero exactly when
   `a • z' = 0`. Thus annihilators are equal and the first inclusion follows.
2. Let `q = Ann(z)` be prime. If some `s ∉ q` has `s • z` in the image of `f`, write
   it as `f z'`. Primality gives `a * s ∈ q` iff `a ∈ q`, so `Ann(s • z) = q`.
   Step 1 gives `Ann(z') = q`, placing `q` among the submodule's associated primes.
3. Otherwise every `s ∉ q` has `s • g z ≠ 0`, by exactness. Elements of `q` kill
   `g z` by linearity, and no element outside `q` does. Thus `Ann(g z) = q` and
   `q` is associated to the quotient. The two cases prove the second inclusion.
No Noetherian assumption is used; surjectivity is retained as part of short exactness. -/
theorem annihilatorAssociatedPrimes_of_shortExact
    {R : Type uR} [CommRing R]
    {M' : Type uSub} [AddCommGroup M'] [Module R M']
    {M : Type uMid} [AddCommGroup M] [Module R M]
    {M'' : Type uQuot} [AddCommGroup M''] [Module R M'']
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'')
    (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) :
    (annihilatorAssociatedPrimes R M' ⊆ annihilatorAssociatedPrimes R M) ∧
    (∀ z' : M', (⊥ : Submodule R M).colon {f z'} =
      (⊥ : Submodule R M').colon {z'}) ∧
    (annihilatorAssociatedPrimes R M ⊆
      annihilatorAssociatedPrimes R M' ∪ annihilatorAssociatedPrimes R M'') := by
  classical
  have _ := hg
  have hann (z' : M') : (⊥ : Submodule R M).colon {f z'} =
      (⊥ : Submodule R M').colon {z'} := by
    ext a
    simp only [Submodule.mem_colon_singleton, Submodule.mem_bot]
    rw [← map_smul, map_eq_zero_iff f hf]
  refine ⟨?_, hann, ?_⟩
  · rintro q ⟨hq, z', hz'⟩
    exact ⟨hq, f z', hz'.trans (hann z').symm⟩
  · rintro q ⟨hq, z, hz⟩
    have hmem (a : R) : a ∈ q ↔ a • z = 0 := by
      rw [hz, Submodule.mem_colon_singleton, Submodule.mem_bot]
    by_cases h : ∃ s : R, s ∉ q ∧ ∃ z' : M', f z' = s • z
    · obtain ⟨s, hs, z', hz'⟩ := h
      left
      refine ⟨hq, z', ?_⟩
      rw [← hann z', hz']
      ext a
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot, ← mul_smul]
      rw [← hmem]
      exact ⟨fun ha ↦ q.mul_mem_right s ha,
        fun has ↦ (hq.mem_or_mem has).resolve_right hs⟩
    · right
      refine ⟨hq, g z, ?_⟩
      ext a
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
      constructor
      · intro ha
        rw [← map_smul, (hmem a).mp ha, map_zero]
      · intro ha
        by_contra haq
        apply h
        refine ⟨a, haq, ?_⟩
        have hker : a • z ∈ LinearMap.ker g := by
          rw [LinearMap.mem_ker, map_smul, ha]
        rw [hfg.linearMap_ker_eq] at hker
        exact hker

end RingTheory
