/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.QuotSMulTop
import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Ideal.MinimalPrime.Colon

/-!
# Associated primes of quotients by powers of an element

Source: Stacks Project, Algebra, Lemma 0CN5 (lemma-inherit-minimal-primes)
(blueprint: lem-weil-pbc-associated-prime-power-quotient).
-/

@[expose] public section

universe u v

namespace Module

/-- Source: Stacks Project, Algebra, Lemma 0CN5
(blueprint: lem-weil-pbc-associated-prime-power-quotient).
A prime minimal over `p + (x)`, with `p` associated to `M`, is associated to
`M / x^n M` for some positive `n`.

Proof:
1. Choose `z` with annihilator `p`; its cyclic submodule `N = Rz` is isomorphic to `R/p`,
   and `N/xN` is isomorphic to `R/(p + (x))`.
2. Apply Artin--Rees (lem-weil-pbc-artin-rees) to `(x)` and `N` inside `M`.
   If its constant is `c`, take `n = c + 1`, giving `N ∩ x^n M ⊆ xN`.
3. Let `Nbar` be the image of `N` in `M/x^n M`. It is finite and isomorphic to
   `N/(N ∩ x^n M)`. By lem-weil-pbc-associated-prime-submodule it suffices to
   show that `q` is associated to `Nbar`.
4. The inclusion in step 2 gives a surjection `Nbar → R/(p + (x))`, so
   `Ann(Nbar) ⊆ p + (x) ⊆ q`. By lem-weil-pbc-finite-module-support-annihilator,
   `q` belongs to the support of `Nbar`.
5. Both `p` and `x^n` annihilate `Nbar`. Any prime in its support contained in `q`
   therefore contains `p` and `x`, hence equals `q` by minimality over `p + (x)`.
   Thus `q` is minimal in the support, using the support-annihilator lemma again.
6. By lem-weil-pbc-minimal-support-prime-associated, `q` is associated to `Nbar`;
   the submodule lemma then puts it in the associated primes of `M/x^n M`. -/
theorem exists_mem_associatedPrimes_quotient_pow
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R)
    (p q : Ideal R) (hp : p ∈ associatedPrimes R M)
    (hq : q ∈ (p ⊔ Ideal.span {x}).minimalPrimes) :
    ∃ n : ℕ, 1 ≤ n ∧ q ∈ associatedPrimes R (QuotSMulTop (x ^ n) M) := by
  open scoped Pointwise in
    have hx0 := hx
    clear hx0 hx
    rcases (isAssociatedPrime_iff.mp hp) with ⟨_, z, hz⟩
    let N : Submodule R M := Submodule.span R {z}
    let I : Ideal R := Ideal.span {x}
    obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul I N
    have hbound : (x ^ (c + 1) • (⊤ : Submodule R M)) ⊓ N ≤ x • N := by
      have h := hc (c + 1) (Nat.le_add_right c 1)
      simp only [Nat.add_sub_cancel_left, pow_one] at h
      dsimp [I] at h
      rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul] at h
      rw [h, Submodule.ideal_span_singleton_smul]
      exact smul_mono_right x inf_le_right
    let Q := QuotSMulTop (x ^ (c + 1)) M
    let w : Q := Submodule.Quotient.mk z
    let A : Ideal R := (⊥ : Submodule R Q).colon {w}
    have hA : A ≤ p ⊔ I := by
      intro r hr
      have hrz : r • z ∈ x ^ (c + 1) • (⊤ : Submodule R M) := by
        have hr0 := Submodule.mem_colon_singleton.mp hr
        change (x ^ (c + 1) • (⊤ : Submodule R M)).mkQ (r • z) = 0 at hr0
        exact (Submodule.Quotient.mk_eq_zero _).mp hr0
      have hrN : r • z ∈ N := N.smul_mem r (Submodule.mem_span_singleton_self z)
      have hb := hbound ⟨hrz, hrN⟩
      rcases (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hb with ⟨t, ht, he⟩
      rcases Submodule.mem_span_singleton.mp ht with ⟨a, ha⟩
      have hz0 : (r - x * a) • z = 0 := by
        rw [sub_smul, mul_smul, ha, he, sub_self]
      have hrp : r - x * a ∈ p := by
        rw [hz, Submodule.mem_colon_singleton]
        exact hz0
      have hxa : x * a ∈ I := I.mul_mem_right a (Ideal.subset_span (Set.mem_singleton x))
      have hm := (p ⊔ I).add_mem ((show p ≤ p ⊔ I from le_sup_left) hrp)
        ((show I ≤ p ⊔ I from le_sup_right) hxa)
      simpa using hm
    have hpA : p ≤ A := by
      intro r hr
      have hrz : r • z = 0 := by simpa [hz, Submodule.mem_colon_singleton] using hr
      apply Submodule.mem_colon_singleton.mpr
      change r • w = 0
      change (x ^ (c + 1) • (⊤ : Submodule R M)).mkQ (r • z) = 0
      rw [hrz, map_zero]
    have hxA : x ^ (c + 1) ∈ A := by
      exact Submodule.mem_colon_singleton.mpr
        (Module.mem_annihilator.mp (QuotSMulTop.mem_annihilator M (x ^ (c + 1))) w)
    have hqA : q ∈ A.minimalPrimes := by
      refine ⟨⟨hq.isPrime, hA.trans hq.le⟩, ?_⟩
      intro q' hq' hle
      have hxq' : x ∈ q' := hq'.1.mem_of_pow_mem (c + 1) (hq'.2 hxA)
      have hI : I ≤ q' := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hxq')
      exact hq.2 ⟨hq'.1, sup_le (hpA.trans hq'.2) hI⟩ hle
    obtain ⟨w', hw'⟩ := Submodule.exists_eq_colon_of_mem_minimalPrimes hqA
    refine ⟨c + 1, Nat.le_add_left 1 c, ?_⟩
    exact isAssociatedPrime_iff.mpr ⟨hq.isPrime, w', hw'⟩


end Module
