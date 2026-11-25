/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.UniqueFactorizationDomain.Kaplansky
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic

/-!
# Applications of Kaplansky's criterion

Using Kaplansky's criterion (an integral domain is a UFD iff every nonzero prime ideal contains a
prime element), we prove:

## Main results

- `UniqueFactorizationMonoid.of_isLocalization_away`: Nagata's criterion. Let `R` be a domain
  satisfying the ascending chain condition on principal ideals and `x ∈ R` a prime element. If
  `R[1/x]` is a UFD, then so is `R`.
- `UniqueFactorizationMonoid.of_forall_isPrincipal_of_mem_minimalPrimes`: a domain in which every
  prime ideal minimal over a nonzero principal ideal is principal is a UFD.
-/

@[expose] public section

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Let `x` be a prime element of a domain `R` and `b ∈ R` not divisible by `x`. If the image of
`b` in `R[1/x]` is prime, then `b` is prime. -/
theorem Prime.of_prime_algebraMap_away {x b : R} (hx : Prime x) (hb : ¬x ∣ b) (A : Type*)
    [CommRing A] [Algebra R A] [IsLocalization.Away x A] (h : Prime (algebraMap R A b)) :
    Prime b := by
  have inj : Function.Injective (algebraMap R A) :=
    IsLocalization.injective A (powers_le_nonZeroDivisors_of_noZeroDivisors hx.ne_zero)
  have key (c : R) (hc : algebraMap R A b ∣ algebraMap R A c) : b ∣ c := by
    obtain ⟨e, he⟩ := hc
    obtain ⟨⟨a, ⟨_, m, rfl⟩⟩, hae⟩ := IsLocalization.surj (Submonoid.powers x) e
    have hca : c * x ^ m = b * a := inj (by
      rw [map_mul, map_mul, he, mul_assoc, ← hae])
    obtain ⟨g, rfl⟩ := hx.pow_dvd_of_dvd_mul_left m hb ⟨c, by rw [← hca, mul_comm]⟩
    exact ⟨g, mul_right_cancel₀ (pow_ne_zero m hx.ne_zero) (by rw [hca]; ring)⟩
  refine ⟨fun h0 ↦ h.ne_zero (by simp [h0]), fun hu ↦ h.not_isUnit (hu.map _), fun c d hcd ↦ ?_⟩
  rcases h.dvd_or_dvd (by simpa using map_dvd (algebraMap R A) hcd) with h1 | h1
  · exact .inl (key c h1)
  · exact .inr (key d h1)

namespace UniqueFactorizationMonoid

/-- **Nagata's criterion**: let `R` be a domain satisfying the ascending chain condition on
principal ideals (e.g. a noetherian domain) and `x ∈ R` a prime element. If the localization
`R[1/x]` is a UFD, then so is `R`. -/
theorem of_isLocalization_away [WfDvdMonoid R] {x : R} (hx : Prime x) (A : Type*) [CommRing A]
    [Algebra R A] [IsLocalization.Away x A] [UniqueFactorizationMonoid A] :
    UniqueFactorizationMonoid R := by
  have inj : Function.Injective (algebraMap R A) :=
    IsLocalization.injective A (powers_le_nonZeroDivisors_of_noZeroDivisors hx.ne_zero)
  have : IsDomain A := IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers x) A
    (powers_le_nonZeroDivisors_of_noZeroDivisors hx.ne_zero)
  rw [iff_exists_prime_mem_of_isPrime]
  intro P hP0 hP
  by_cases hxP : x ∈ P
  · exact ⟨x, hxP, hx⟩
  have hdisj := (Ideal.disjoint_powers_iff_notMem_of_isPrime x).2 hxP
  have hP' := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers x) A P hP hdisj
  have hcomap := IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers x) A hP hdisj
  have hP'0 : P.map (algebraMap R A) ≠ ⊥ := fun h ↦
    hP0 (hcomap ▸ (h ▸ Ideal.comap_bot_of_injective _ inj))
  obtain ⟨q, hqP', hq⟩ := hP'.exists_mem_prime_of_ne_bot hP'0
  obtain ⟨⟨a, ⟨_, k, rfl⟩⟩, ha⟩ := IsLocalization.surj (Submonoid.powers x) q
  have hu (n : ℕ) : IsUnit (algebraMap R A (x ^ n)) :=
    IsLocalization.map_units A (⟨x ^ n, n, rfl⟩ : Submonoid.powers x)
  have haP : a ∈ P := by
    rw [← hcomap, Ideal.under, Ideal.mem_comap, ← ha]
    exact Ideal.mul_mem_right _ _ hqP'
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, (hu k).mul_left_eq_zero] at ha
    exact hq.ne_zero ha
  obtain ⟨j, b, hxb, rfl⟩ := WfDvdMonoid.max_power_factor ha0 hx.irreducible
  have hbP : b ∈ P := (hP.mem_or_mem haP).resolve_left fun h ↦ hxP (hP.mem_of_pow_mem j h)
  refine ⟨b, hbP, hx.of_prime_algebraMap_away hxb A ?_⟩
  have : Associated q (algebraMap R A (x ^ j) * algebraMap R A b) := by
    rw [← map_mul, ← ha]
    exact associated_mul_unit_right _ _ (hu k)
  exact (this.trans (associated_unit_mul_left _ _ (hu j))).prime hq

/-- A domain in which every prime ideal minimal over a nonzero principal ideal is principal is a
UFD. -/
theorem of_forall_isPrincipal_of_mem_minimalPrimes
    (h : ∀ f : R, f ≠ 0 → ∀ P ∈ (Ideal.span {f}).minimalPrimes, P.IsPrincipal) :
    UniqueFactorizationMonoid R := by
  rw [iff_exists_prime_mem_of_isPrime]
  intro Q hQ0 hQ
  obtain ⟨f, hfQ, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ0
  obtain ⟨P, hP, hPQ⟩ := Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem _).2 hfQ)
  obtain ⟨a, rfl⟩ := (h f hf0 P hP).principal
  have ha0 : a ≠ 0 := by
    rintro rfl
    have := hP.1.2 (Ideal.mem_span_singleton_self f)
    rw [Submodule.span_singleton_eq_bot.2 rfl, Ideal.mem_bot] at this
    exact hf0 this
  exact ⟨a, hPQ (Submodule.mem_span_singleton_self a), (Ideal.span_singleton_prime ha0).1 hP.1.1⟩

end UniqueFactorizationMonoid
