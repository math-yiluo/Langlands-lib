/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.LinearAlgebra.Pi

/-!
# Injectivity of localization at associated primes

Source: Stacks Project, Algebra, Lemma 10.63.19, Tag 0311
(blueprint: lem-weil-pbc-module-injects-localizations-associated-primes).
-/

@[expose] public section

universe u v

namespace Module

/-- Over a Noetherian ring, the canonical linear map to the product of localizations at
associated primes is injective. Equivalently, an element killed by a denominator outside
each associated prime is zero. No finite generation assumption on the module is needed.
Mathlib's `associatedPrimes` agrees with the annihilator definition here by
`isAssociatedPrime_iff`. The product may be empty, in which case it is the zero module.

Source: Stacks Project, Algebra, Lemma 10.63.19, Tag 0311
(blueprint: lem-weil-pbc-module-injects-localizations-associated-primes).

Proof: Suppose a nonzero element `m` maps to zero in all the localizations. The cyclic
submodule `N = Rm` is nonzero, and zero is a zero divisor on it. By
`lem-weil-pbc-noetherian-module-zerodivisors-union-associated-primes`, it has an associated
prime `p`. By `lem-weil-pbc-associated-prime-submodule`, this prime is associated to `M`.
Choose `z = r • m` in `N` whose annihilator is `p`. The vanishing of `m/1` at `p`, using
`def-weil-pbc-module-localization` and `def-weil-pbc-localization-at-prime`, gives `s` outside
`p` with `s • m = 0`. Commutativity gives `s • z = 0`, contradicting the annihilator of `z`.
Thus the kernel is zero and the linear map is injective. The same argument gives the
stated elementwise criterion. A nonzero element produces an associated prime, so the
argument also includes an empty product. -/
theorem injective_pi_localization_associatedPrimes
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] :
    Function.Injective
      (LinearMap.pi (fun p : associatedPrimes R M =>
        (LocalizedModule.mkLinearMap p.1.primeCompl M :
          M →ₗ[R] LocalizedModule.AtPrime p.1 M))) ∧
    (∀ m : M, (∀ p : associatedPrimes R M,
      ∃ s : R, s ∉ p.1 ∧ s • m = 0) → m = 0) := by
  have hzero : ∀ m : M,
      (∀ p : associatedPrimes R M,
        ∃ s : R, s ∉ p.1 ∧ s • m = 0) → m = 0 := by
    intro m hm
    by_contra hmn
    obtain ⟨p, hp, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R m hmn
    obtain ⟨s, hsp, hsm⟩ := hm ⟨p, hp⟩
    have hsann : s ∈ (⊥ : Submodule R M).colon {m} := by
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
      exact hsm
    exact hsp (hle hsann)
  refine ⟨?_, hzero⟩
  intro x y hxy
  apply sub_eq_zero.mp
  apply hzero (x - y)
  intro p
  have hmap : (LocalizedModule.mkLinearMap p.1.primeCompl M :
      M →ₗ[R] LocalizedModule.AtPrime p.1 M) (x - y) = 0 := by
    have h := congr_fun hxy p
    rw [map_sub]
    exact sub_eq_zero.mpr h
  obtain ⟨s, hs, hsm⟩ := (LocalizedModule.mem_ker_mkLinearMap_iff.mp hmap)
  exact ⟨s, hs, hsm⟩

end Module
