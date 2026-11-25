/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Ideal.Prime

/-!
# Base change to the fraction field

Let `R ⟶ O` be an injective map of domains and `K` the fraction field of `R`. Then
`O ⊗[R] K` is the localization of `O` at the nonzero elements of `R`. It is the fraction field of
`O` as soon as every nonzero prime ideal of `O` meets `R` in a nonzero ideal.

## Main results

- `IsFractionRing.tensorProduct_of_comap_eq_bot`: `O ⊗[R] K` is a fraction field of `O` if every
  prime of `O` lying over `0` is `0`.
-/

@[expose] public section

open scoped TensorProduct

/-- **Base change to the fraction field.** Let `R ⟶ O` be an injective map of domains such that
every prime ideal of `O` lying over the zero ideal of `R` is zero, and let `K` be a fraction field
of `R`. Then `O ⊗[R] K` is a fraction field of `O`. -/
theorem IsFractionRing.tensorProduct_of_comap_eq_bot {R O : Type*} [CommRing R] [IsDomain R]
    [CommRing O] [IsDomain O] [Algebra R O] (hinj : Function.Injective (algebraMap R O))
    (h : ∀ q : Ideal O, q.IsPrime → q.comap (algebraMap R O) = ⊥ → q = ⊥)
    (K : Type*) [CommRing K] [Algebra R K] [IsFractionRing R K] :
    IsFractionRing O (O ⊗[R] K) := by
  have : IsLocalization (Algebra.algebraMapSubmonoid O (nonZeroDivisors R)) (O ⊗[R] K) :=
    inferInstance
  refine IsLocalization.of_le_of_exists_dvd
    (Algebra.algebraMapSubmonoid O (nonZeroDivisors R)) _ ?_ ?_
  · rintro _ ⟨r, hr, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h ↦ ?_
    exact nonZeroDivisors.ne_zero hr (hinj (h.trans (map_zero _).symm))
  · intro a ha
    by_contra! hdvd
    obtain ⟨q, hq, hsub, hdisj⟩ := Ideal.exists_le_prime_disjoint (Ideal.span {a})
      (Algebra.algebraMapSubmonoid O (nonZeroDivisors R)) (by
        rw [Set.disjoint_left]
        rintro b hb ⟨r, hr, rfl⟩
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hb
        exact hdvd _ ⟨r, hr, rfl⟩ ⟨c, by rw [← hc, mul_comm]⟩)
    have hq0 : q.comap (algebraMap R O) = ⊥ := by
      refine eq_bot_iff.2 fun r hr ↦ ?_
      by_contra hr0
      exact Set.disjoint_left.1 hdisj hr
        ⟨r, mem_nonZeroDivisors_of_ne_zero hr0, rfl⟩
    have := h q hq hq0
    exact nonZeroDivisors.ne_zero ha (by
      have : a ∈ q := hsub (Ideal.mem_span_singleton_self a)
      rwa [‹q = ⊥›, Ideal.mem_bot] at this)
