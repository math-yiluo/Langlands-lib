/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Unramified extensions of discrete valuation rings

Let `R ⟶ O` be a homomorphism of discrete valuation rings mapping the maximal ideal of `R` onto
that of `O`, so that a uniformiser of `R` stays a uniformiser of `O`. Then the base change
`O ⊗[R] K` of the fraction field `K` of `R` is the fraction field of `O`
(`IsDiscreteValuationRing.isFractionRing_tensorProduct`): inverting a uniformiser of `O` already
inverts every nonzero element.

We also show that if `B` is a flat algebra over a discrete valuation ring `R` with uniformiser
`ϖ` whose special fibre `B ⧸ ϖB` is reduced, then every idempotent of `B[1/ϖ]` comes from `B`
(`IsDiscreteValuationRing.exists_eq_algebraMap_of_isIdempotentElem`, the algebraic core of
Stacks 055J).
-/

@[expose] public section

open IsLocalRing TensorProduct

namespace IsDiscreteValuationRing

variable {R O : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing O]
  [IsDomain O] [IsDiscreteValuationRing O] [Algebra R O]

/-- Under a homomorphism of discrete valuation rings mapping the maximal ideal onto the maximal
ideal, a uniformiser maps to a uniformiser. -/
lemma irreducible_algebraMap_of_map_maximalIdeal
    (hm : (maximalIdeal R).map (algebraMap R O) = maximalIdeal O) {ϖ : R} (hϖ : Irreducible ϖ) :
    Irreducible (algebraMap R O ϖ) := by
  rw [irreducible_iff_uniformizer, ← hm, (irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.map_span,
    Set.image_singleton]

/-- A homomorphism of discrete valuation rings mapping the maximal ideal onto the maximal ideal
is injective. -/
lemma algebraMap_injective_of_map_maximalIdeal
    (hm : (maximalIdeal R).map (algebraMap R O) = maximalIdeal O) :
    Function.Injective (algebraMap R O) := by
  refine (injective_iff_map_eq_zero _).2 fun r hr ↦ ?_
  by_contra h
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible h hϖ
  have hϖ' := irreducible_algebraMap_of_map_maximalIdeal hm hϖ
  rw [map_mul, map_pow] at hr
  exact (mul_ne_zero ((u.isUnit.map _).ne_zero) (pow_ne_zero n hϖ'.ne_zero)) hr

/-- **Base change of the fraction field along an unramified extension.** Let `R ⟶ O` be a
homomorphism of discrete valuation rings with `𝔪_R O = 𝔪_O`, and `K` a fraction field of `R`.
Then `O ⊗[R] K` is a fraction field of `O`. -/
lemma isFractionRing_tensorProduct
    (hm : (maximalIdeal R).map (algebraMap R O) = maximalIdeal O) (K : Type*) [CommRing K]
    [Algebra R K] [IsFractionRing R K] : IsFractionRing O (O ⊗[R] K) := by
  have : IsLocalization (Algebra.algebraMapSubmonoid O (nonZeroDivisors R)) (O ⊗[R] K) :=
    inferInstance
  refine IsLocalization.of_le_of_exists_dvd
    (Algebra.algebraMapSubmonoid O (nonZeroDivisors R)) _ ?_ ?_
  · rintro _ ⟨r, hr, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h ↦ ?_
    exact nonZeroDivisors.ne_zero hr ((algebraMap_injective_of_map_maximalIdeal hm)
      (h.trans (map_zero _).symm))
  · intro a ha
    obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
    have hϖ' := irreducible_algebraMap_of_map_maximalIdeal hm hϖ
    obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero ha) hϖ'
    refine ⟨algebraMap R O (ϖ ^ n), ⟨ϖ ^ n, mem_nonZeroDivisors_of_ne_zero
      (pow_ne_zero n hϖ.ne_zero), rfl⟩, ?_⟩
    rw [map_pow]
    exact ⟨↑u⁻¹, by rw [mul_comm (u : O), mul_assoc, Units.mul_inv, mul_one]⟩

omit [IsDiscreteValuationRing R] in
/-- Let `R` be a discrete valuation ring with uniformiser `ϖ` and `B` a flat `R`-algebra whose
special fibre `B ⧸ ϖB` is reduced. Then every idempotent of `B[1/ϖ]` comes from `B`.

The proof only uses that `R` is a domain and `ϖ ≠ 0`. -/
theorem exists_eq_algebraMap_of_isIdempotentElem {B : Type*} [CommRing B] [Algebra R B]
    [Module.Flat R B] {ϖ : R} (hϖ : Irreducible ϖ)
    (hred : IsReduced (B ⧸ Ideal.span {algebraMap R B ϖ}))
    {e : Localization.Away (algebraMap R B ϖ)} (he : IsIdempotentElem e) :
    ∃ b : B, algebraMap B _ b = e := by
  have hcancel (m : ℕ) (x y : B) (h : algebraMap R B ϖ ^ m * x = algebraMap R B ϖ ^ m * y) :
      x = y := by
    refine ((Module.Flat.isSMulRegular_of_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero)).pow m) ?_
    simpa [Algebra.smul_def] using h
  have hinj (x y : B) (h : algebraMap B (Localization.Away (algebraMap R B ϖ)) x =
      algebraMap B _ y) : x = y := by
    obtain ⟨⟨_, m, rfl⟩, hc⟩ :=
      (IsLocalization.eq_iff_exists (Submonoid.powers (algebraMap R B ϖ)) _).1 h
    exact hcancel m x y hc
  obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj (algebraMap R B ϖ) e
  induction n generalizing b with
  | zero => exact ⟨b, by simpa using hb.symm⟩
  | succ n ih =>
    have hsq : b * b = algebraMap R B ϖ ^ (n + 1) * b := by
      refine hinj _ _ ?_
      rw [map_mul, map_mul, map_pow, ← hb]
      linear_combination (algebraMap B (Localization.Away (algebraMap R B ϖ))
        (algebraMap R B ϖ) ^ (n + 1)) ^ 2 * he.eq
    have hb0 : Ideal.Quotient.mk (Ideal.span {algebraMap R B ϖ}) b = 0 := by
      refine IsReduced.eq_zero _ ⟨2, ?_⟩
      rw [pow_two, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, hsq, pow_succ, mul_assoc]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 hb0)
    refine ih c ((IsLocalization.Away.algebraMap_isUnit (algebraMap R B ϖ)).mul_left_inj.1 ?_)
    rw [mul_assoc, ← pow_succ, hb, map_mul]

section Roots

variable {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]

/-- In a discrete valuation ring `S` with uniformiser `ϖ`, if `ϖ ^ a` is an `N`-th power in
`S[1/ϖ]`, then `N ∣ a`: the valuation of an `N`-th power is divisible by `N`. -/
theorem dvd_of_pow_eq_pow_away {ϖ : S} (hϖ : Irreducible ϖ) {N a : ℕ} (hN : N ≠ 0)
    {t : Localization.Away ϖ} (ht : t ^ N = algebraMap S _ ϖ ^ a) : N ∣ a := by
  obtain ⟨k, x, hx⟩ := IsLocalization.Away.surj ϖ t
  have hinj : Function.Injective (algebraMap S (Localization.Away ϖ)) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hϖ.ne_zero)
  have hxN : x ^ N = ϖ ^ (a + k * N) := hinj (by
    rw [map_pow, ← hx, mul_pow, ht, map_pow, pow_add, ← pow_mul, mul_comm k N, pow_mul])
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow hN] at hxN
    exact pow_ne_zero _ hϖ.ne_zero hxN.symm
  obtain ⟨j, u, rfl⟩ := eq_unit_mul_pow_irreducible hx0 hϖ
  have h : ((u ^ N : Sˣ) : S) * ϖ ^ (j * N) = ((1 : Sˣ) : S) * ϖ ^ (a + k * N) := by
    rw [Units.val_pow_eq_pow_val, pow_mul, ← mul_pow, hxN, Units.val_one, one_mul]
  have hjk := unit_mul_pow_congr_pow hϖ hϖ _ _ _ _ h
  exact (Nat.dvd_add_left (dvd_mul_left N k)).1 (hjk ▸ dvd_mul_left N j)


end Roots

end IsDiscreteValuationRing


namespace IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R] {t : R}

/-- In a local ring whose maximal ideal is generated by `t`, an element outside `⋂ₙ tⁿR` is a
power of `t` times a unit. -/
lemma exists_eq_pow_mul_unit_of_notMem_iInf (hm : maximalIdeal R = Ideal.span {t}) {x : R}
    (hx : x ∉ ⨅ n : ℕ, Ideal.span {t ^ n}) : ∃ (n : ℕ) (u : Rˣ), x = t ^ n * u := by
  classical
  have hex : ∃ n, x ∉ Ideal.span {t ^ n} := by
    by_contra! h
    exact hx (Submodule.mem_iInf _ |>.2 h)
  obtain ⟨N, hN, hN'⟩ : ∃ N, x ∉ Ideal.span {t ^ (N + 1)} ∧ x ∈ Ideal.span {t ^ N} := by
    have h0 : Nat.find hex ≠ 0 := by
      intro h
      have := Nat.find_spec hex
      rw [h, pow_zero, Ideal.span_singleton_one] at this
      exact this Submodule.mem_top
    refine ⟨Nat.find hex - 1, ?_, not_not.1 (Nat.find_min hex (Nat.sub_one_lt h0))⟩
    rw [Nat.sub_one_add_one h0]
    exact Nat.find_spec hex
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hN'
  have hyu : IsUnit y := by
    by_contra hy'
    have : y ∈ Ideal.span {t} := hm ▸ (mem_maximalIdeal y).2 hy'
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 this
    exact hN (Ideal.mem_span_singleton'.2 ⟨z, by ring⟩)
  exact ⟨N, hyu.unit, by rw [IsUnit.unit_spec, mul_comm]⟩


/-- In a local ring whose maximal ideal is generated by a non-zero-divisor `t`, the ideal
`⋂ₙ tⁿR` is prime. -/
lemma isPrime_iInf_span_pow (hm : maximalIdeal R = Ideal.span {t})
    (ht : t ∈ nonZeroDivisors R) : (⨅ n : ℕ, Ideal.span {t ^ n}).IsPrime := by
  refine ⟨fun h ↦ ?_, fun {x y} hxy ↦ ?_⟩
  · have h1 : (1 : R) ∈ ⨅ n : ℕ, Ideal.span {t ^ n} := h ▸ Submodule.mem_top
    have : (1 : R) ∈ Ideal.span {t ^ 1} := Submodule.mem_iInf _ |>.1 h1 1
    rw [pow_one, ← hm] at this
    exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 this)
  · by_contra! h
    obtain ⟨n, u, rfl⟩ := exists_eq_pow_mul_unit_of_notMem_iInf hm h.1
    obtain ⟨m, v, rfl⟩ := exists_eq_pow_mul_unit_of_notMem_iInf hm h.2
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 (Submodule.mem_iInf _ |>.1 hxy (n + m + 1))
    have hcancel : t ^ (n + m) * (u * v) = t ^ (n + m) * (t * z) := by
      linear_combination -hz
    have := (mul_cancel_left_mem_nonZeroDivisors (pow_mem ht _)).1 hcancel
    have hmem : ((u * v : Rˣ) : R) ∈ maximalIdeal R := by
      rw [hm, Units.val_mul, this]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self t)
    exact (mem_maximalIdeal _).1 hmem (Units.isUnit _)


/-- In a local ring whose maximal ideal is generated by a non-zero-divisor `t`, the element `t`
is not in `⋂ₙ tⁿR`. -/
lemma notMem_iInf_span_pow (hm : maximalIdeal R = Ideal.span {t}) (ht : t ∈ nonZeroDivisors R) :
    t ∉ ⨅ n : ℕ, Ideal.span {t ^ n} := by
  intro h
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 (Submodule.mem_iInf _ |>.1 h 2)
  have h1 : t * (z * t) = t * 1 := by linear_combination hz
  have h2 := (mul_cancel_left_mem_nonZeroDivisors ht).1 h1
  have : (1 : R) ∈ maximalIdeal R := by
    rw [← h2, hm]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self t)
  exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 this)

/-- In a local ring whose maximal ideal is generated by a non-zero-divisor `t`, the image of `t`
in the quotient `R ⧸ ⋂ₙ tⁿR` is irreducible. -/
lemma irreducible_mk_iInf_span_pow (hm : maximalIdeal R = Ideal.span {t})
    (ht : t ∈ nonZeroDivisors R) :
    Irreducible (Ideal.Quotient.mk (⨅ n : ℕ, Ideal.span {t ^ n}) t) := by
  set I := ⨅ n : ℕ, Ideal.span {t ^ n}
  have := isPrime_iInf_span_pow hm ht
  have ht0 : Ideal.Quotient.mk I t ≠ 0 := fun h ↦
    notMem_iInf_span_pow hm ht (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have hnu : ¬ IsUnit (Ideal.Quotient.mk I t) := by
    rintro ⟨u, hu⟩
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (u⁻¹ : (R ⧸ I)ˣ).1
    have h1 : Ideal.Quotient.mk I (t * y - 1) = 0 := by
      rw [map_sub, map_mul, map_one, hy, ← hu, Units.mul_inv, sub_self]
    have h2 : t * y - 1 ∈ maximalIdeal R := by
      have := Submodule.mem_iInf _ |>.1 (Ideal.Quotient.eq_zero_iff_mem.1 h1) 1
      rwa [pow_one, ← hm] at this
    have h3 : t * y ∈ maximalIdeal R :=
      hm ▸ Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self t)
    have : (1 : R) ∈ maximalIdeal R := by
      have := Ideal.sub_mem _ h3 h2
      rwa [sub_sub_cancel] at this
    exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 this)
  refine ⟨hnu, fun {a b} hab ↦ ?_⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  have ha : a ∉ I := fun h ↦ ht0 (by rw [hab, Ideal.Quotient.eq_zero_iff_mem.2 h, zero_mul])
  have hb : b ∉ I := fun h ↦ ht0 (by rw [hab, Ideal.Quotient.eq_zero_iff_mem.2 h, mul_zero])
  obtain ⟨i, u, rfl⟩ := exists_eq_pow_mul_unit_of_notMem_iInf hm ha
  obtain ⟨j, v, rfl⟩ := exists_eq_pow_mul_unit_of_notMem_iInf hm hb
  rcases i with _ | i
  · exact Or.inl (by simpa using (u.isUnit.map (Ideal.Quotient.mk I)))
  rcases j with _ | j
  · exact Or.inr (by simpa using (v.isUnit.map (Ideal.Quotient.mk I)))
  refine (hnu ?_).elim
  have h : Ideal.Quotient.mk I t * 1 = Ideal.Quotient.mk I t *
      (Ideal.Quotient.mk I t * (Ideal.Quotient.mk I t ^ (i + j) *
        Ideal.Quotient.mk I ((u * v : Rˣ) : R))) := by
    conv_lhs => rw [mul_one, hab]
    simp only [map_mul, map_pow, Units.val_mul]
    ring
  exact IsUnit.of_mul_eq_one _ (mul_left_cancel₀ ht0 h).symm


/-- **A local ring with principal regular maximal ideal has a discrete valuation ring as a
quotient.** If the maximal ideal of the local ring `R` is generated by a non-zero-divisor `t`,
then `R ⧸ ⋂ₙ tⁿR` is a discrete valuation ring, with uniformiser the image of `t`
(`IsLocalRing.irreducible_mk_iInf_span_pow`): every element outside `⋂ₙ tⁿR` is a power of `t`
times a unit. -/
theorem isDiscreteValuationRing_quotient_iInf_span_pow (hm : maximalIdeal R = Ideal.span {t})
    (ht : t ∈ nonZeroDivisors R) [IsDomain (R ⧸ ⨅ n : ℕ, Ideal.span {t ^ n})] :
    IsDiscreteValuationRing (R ⧸ ⨅ n : ℕ, Ideal.span {t ^ n}) := by
  refine .ofHasUnitMulPowIrreducibleFactorization
    ⟨_, irreducible_mk_iInf_span_pow hm ht, fun {x} hx ↦ ?_⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨n, u, rfl⟩ := exists_eq_pow_mul_unit_of_notMem_iInf hm
    fun h ↦ hx (Ideal.Quotient.eq_zero_iff_mem.2 h)
  exact ⟨n, ⟨(u.map (Ideal.Quotient.mk _).toMonoidHom), by simp⟩⟩


end IsLocalRing
