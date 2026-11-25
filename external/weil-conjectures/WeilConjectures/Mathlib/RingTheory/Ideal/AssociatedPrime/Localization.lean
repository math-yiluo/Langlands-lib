/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import WeilConjectures.Mathlib.RingTheory.Ideal.AssociatedPrime.Basic

/-!
# Associated primes of `M / xⁿ M`

Let `R` be a Noetherian ring, `M` a finite `R`-module, `p` an associated prime of `M` and `x ∈ R`.
Every prime `q` minimal over `p + (x)` is an associated prime of `M / xⁿ M` for some `n ≥ 1`
(Stacks `0CN5`). The proof uses Artin–Rees for the cyclic submodule `R z ≅ R / p` and the fact
that minimal primes of the annihilator of a finite module are associated.
-/

@[expose] public section

open scoped Pointwise

namespace Module

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- Let `R` be Noetherian and `M` a finite `R`-module, `p` an associated prime of `M`, `x ∈ R`,
and `q` a prime minimal over `p + (x)`. Then `q` is an associated prime of `M / xⁿ M` for some
`n ≥ 1`. -/
theorem exists_mem_annihilatorAssociatedPrimes_quotient_pow_of_isNoetherianRing
    [IsNoetherianRing R] [Module.Finite R M] {x : R} {p q : Ideal R}
    (hp : p ∈ annihilatorAssociatedPrimes R M) (hq : q ∈ (p ⊔ Ideal.span {x}).minimalPrimes) :
    ∃ n ≥ 1, q ∈ annihilatorAssociatedPrimes R (M ⧸ (x ^ n • ⊤ : Submodule R M)) := by
  classical
  obtain ⟨-, z, hz⟩ := mem_annihilatorAssociatedPrimes_iff.mp hp
  set N : Submodule R M := R ∙ z
  obtain ⟨c, hc⟩ := (Ideal.span {x}).exists_pow_inf_eq_pow_smul (M := M) N
  refine ⟨c + 1, by omega, ?_⟩
  set Q := M ⧸ (x ^ (c + 1) • ⊤ : Submodule R M)
  set zb : Q := Submodule.Quotient.mk z
  set K : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R Q zb)
  have hK (a : R) : a ∈ K ↔ a • zb = 0 := by simp [K]
  -- `K ≤ p + (x)`, by Artin–Rees.
  have hKle : K ≤ p ⊔ Ideal.span {x} := by
    intro a ha
    rw [hK, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at ha
    have hmem : a • z ∈ Ideal.span {x} ^ (c + 1) • (⊤ : Submodule R M) ⊓ N := by
      rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul]
      exact ⟨ha, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self z)⟩
    rw [hc (c + 1) (by omega), Nat.add_sub_cancel_left, pow_one] at hmem
    have hmem' : a • z ∈ x • N := by
      rw [← Submodule.ideal_span_singleton_smul]
      exact Submodule.smul_mono le_rfl inf_le_right hmem
    obtain ⟨b, hb, hbz⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.mp hmem'
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hb
    have hp' : a - x * r ∈ p := by
      rw [hz, sub_smul, mul_smul, hbz,
        sub_self]
    have : a = (a - x * r) + x * r := by ring
    rw [this]
    exact Submodule.add_mem_sup hp' (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self x))
  have hpK : p ≤ K := by
    intro a ha
    rw [hK, ← Submodule.Quotient.mk_smul]
    rw [hz] at ha
    rw [ha, Submodule.Quotient.mk_zero]
  have hxK : x ^ (c + 1) ∈ K := by
    rw [hK, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
  -- `q` is a minimal prime of `K`.
  have hqK : q ∈ K.minimalPrimes := by
    refine ⟨⟨hq.1.1, hKle.trans hq.1.2⟩, fun q' hq' hq'q ↦ hq.2 ⟨hq'.1, ?_⟩ hq'q⟩
    refine sup_le (hpK.trans hq'.2) ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hq'.1.mem_of_pow_mem _ (hq'.2 hxK)
  -- Hence `q` is associated to `R ⧸ K`, which embeds into `Q`.
  have hqR : q ∈ associatedPrimes R (R ⧸ K) := by
    apply associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R (R ⧸ K)
    rwa [Ideal.annihilator_quotient]
  have hinj : Function.Injective (K.liftQ (LinearMap.toSpanSingleton R Q zb) le_rfl) := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
  rw [annihilatorAssociatedPrimes_eq_associatedPrimes]
  exact associatedPrimes.subset_of_injective hinj hqR

end Module
