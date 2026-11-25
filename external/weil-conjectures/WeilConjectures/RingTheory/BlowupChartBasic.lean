/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The affine chart `R[T]/(xT - y)` of a blow-up

Let `C = R[T]/(xT - y)`, the chart of the blow-up of `Spec R` along `(x, y)` on which `x`
generates the exceptional ideal and `T = y/x`. We prove its elementary properties:

* every element of `C` becomes an element of `R` after multiplication by a power of `x`;
* if `R` is a domain, `x ≠ 0` and `y` is a non-zero-divisor modulo `x`, then `R → C` is injective,
  `x` is a non-zero-divisor on `C` and `C` is a domain;
* the homogeneous form `∑_{j ≤ n} p_j x ^ (n - j) y ^ j` equals `x ^ n p(T)` on `C`;
* if `R` is local and `(x, y)` is its maximal ideal, then `C/(x) = κ[T]`.

The ring `C` is written `R[X] ⧸ Ideal.span {C x * X - C y}` (this is `blowupChart x y`).

## Main results

- `BlowupChart.algebraMap_sum_eq_pow_mul`: `∑_{j ≤ n} p_j x ^ (n - j) y ^ j = x ^ n p(T)`.
- `BlowupChart.exists_pow_mul_eq_algebraMap`: `x ^ n c ∈ R` for some `n`.
- `BlowupChart.isDomain`: the chart is a domain.
- `BlowupChart.toResidue`: the map `C → κ[T]`, whose kernel is `(x)`
  (`BlowupChart.ker_toResidue`).
-/

@[expose] public section

universe u

open Polynomial IsLocalRing

namespace BlowupChart

variable {R : Type u} [CommRing R] (x y : R)

/-- The image of a constant polynomial in the chart. -/
theorem mk_C (r : R) :
    Ideal.Quotient.mk (Ideal.span {C x * X - C y}) (C r) =
      algebraMap R (R[X] ⧸ Ideal.span {C x * X - C y}) r := rfl

/-- In the chart, `x T = y`. -/
theorem algebraMap_mul_mk_X :
    algebraMap R (R[X] ⧸ Ideal.span {C x * X - C y}) x * Ideal.Quotient.mk _ X =
      algebraMap R (R[X] ⧸ Ideal.span {C x * X - C y}) y := by
  rw [← mk_C, ← mk_C, ← map_mul, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _

/-- On the chart, the homogeneous form `∑_{j ≤ n} p_j x ^ (n - j) y ^ j` is `x ^ n p(T)`. -/
theorem algebraMap_sum_eq_pow_mul (p : R[X]) {n : ℕ} (hp : p.natDegree ≤ n) :
    algebraMap R (R[X] ⧸ Ideal.span {C x * X - C y})
        (∑ j ∈ Finset.range (n + 1), p.coeff j * x ^ (n - j) * y ^ j) =
      algebraMap R _ x ^ n * Ideal.Quotient.mk _ p := by
  conv_rhs => rw [p.as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le hp)]
  simp only [map_sum, map_mul, map_pow, Finset.mul_sum, mk_C]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [← algebraMap_mul_mk_X x y, mul_pow, show n = n - j + j by omega, pow_add,
    Nat.add_sub_cancel]
  ring

/-- Every element of the chart becomes an element of `R` after multiplication by a power of `x`.
-/
theorem exists_pow_mul_eq_algebraMap (c : R[X] ⧸ Ideal.span {C x * X - C y}) :
    ∃ (n : ℕ) (r : R), algebraMap R _ x ^ n * c = algebraMap R _ r := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective c
  exact ⟨p.natDegree, _, (algebraMap_sum_eq_pow_mul x y p le_rfl).symm⟩

variable {x y}

/-- If `R` is a domain and `x ≠ 0`, then `R` injects into the chart. -/
theorem algebraMap_injective [IsDomain R] (hx : x ≠ 0) :
    Function.Injective (algebraMap R (R[X] ⧸ Ideal.span {C x * X - C y})) := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  rw [← mk_C, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hr
  obtain ⟨q, hq⟩ := hr
  by_cases hq0 : q = 0
  · rw [hq0, zero_mul, eq_comm, C_eq_zero] at hq
    exact hq
  · have hdeg := congrArg natDegree hq
    rw [natDegree_C, natDegree_mul hq0 (fun h => by
      have := congrArg natDegree h
      rw [natDegree_sub_C, natDegree_C_mul_X _ hx, natDegree_zero] at this
      exact one_ne_zero this), natDegree_sub_C, natDegree_C_mul_X _ hx] at hdeg
    omega

/-- If `R` is a domain, `x ≠ 0` and `y` is a non-zero-divisor modulo `x`, then `x` is a
non-zero-divisor on the chart. -/
theorem eq_zero_of_algebraMap_mul_eq_zero [IsDomain R] (hx : x ≠ 0)
    (hy : ∀ a : R ⧸ Ideal.span {x}, Ideal.Quotient.mk _ y * a = 0 → a = 0)
    {c : R[X] ⧸ Ideal.span {C x * X - C y}} (hc : algebraMap R _ x * c = 0) : c = 0 := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [← mk_C, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hc
  obtain ⟨q, hq⟩ := hc
  have h2 : q.map (Ideal.Quotient.mk (Ideal.span {x})) * C (Ideal.Quotient.mk _ y) = 0 := by
    have := congrArg (Polynomial.map (Ideal.Quotient.mk (Ideal.span {x}))) hq
    simpa [Polynomial.map_mul, Ideal.Quotient.mk_singleton_self] using this
  have hq' : q ∈ (Ideal.span {x}).map (C : R →+* R[X]) := by
    rw [Ideal.mem_map_C_iff]
    intro n
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply hy
    have := congrArg (coeff · n) h2
    simpa [coeff_mul_C, mul_comm] using this
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hq'
  obtain ⟨q', rfl⟩ := hq'
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
  refine ⟨q', mul_left_cancel₀ (C_ne_zero.mpr hx) ?_⟩
  rw [← hq]
  ring


/-- If `R` is a domain, `x ≠ 0` and `y` is a non-zero-divisor modulo `x`, then the chart is a
domain: it embeds into `R[1/x]`. -/
theorem isDomain [IsDomain R] (hx : x ≠ 0)
    (hy : ∀ a : R ⧸ Ideal.span {x}, Ideal.Quotient.mk _ y * a = 0 → a = 0) :
    IsDomain (R[X] ⧸ Ideal.span {C x * X - C y}) := by
  have hinj := algebraMap_injective (y := y) hx
  have : Nontrivial (R[X] ⧸ Ideal.span {C x * X - C y}) := hinj.nontrivial
  have hpow : ∀ (n : ℕ) {c : R[X] ⧸ Ideal.span {C x * X - C y}},
      algebraMap R _ x ^ n * c = 0 → c = 0 := by
    intro n
    induction n with
    | zero => intro c hc; simpa using hc
    | succ n ih =>
      intro c hc
      rw [pow_succ', mul_assoc] at hc
      exact ih (eq_zero_of_algebraMap_mul_eq_zero hx hy hc)
  refine @NoZeroDivisors.to_isDomain _ _ this ⟨fun {a b} hab => ?_⟩
  obtain ⟨n, r, hr⟩ := exists_pow_mul_eq_algebraMap x y a
  obtain ⟨m, s, hs⟩ := exists_pow_mul_eq_algebraMap x y b
  have hrs : algebraMap R (R[X] ⧸ Ideal.span {C x * X - C y}) (r * s) = 0 := by
    rw [map_mul, ← hr, ← hs, mul_mul_mul_comm, hab, mul_zero]
  rw [← map_zero (algebraMap R (R[X] ⧸ Ideal.span {C x * X - C y})), hinj.eq_iff,
    mul_eq_zero] at hrs
  rcases hrs with rfl | rfl
  · exact Or.inl (hpow n (by rw [hr, map_zero]))
  · exact Or.inr (hpow m (by rw [hs, map_zero]))

section Residue

variable [IsLocalRing R]

/-- The reduction `C → κ[T]` of the chart modulo the maximal ideal of `R`, for `x, y ∈ 𝔪`. -/
noncomputable def toResidue (hx : x ∈ maximalIdeal R) (hy : y ∈ maximalIdeal R) :
    R[X] ⧸ Ideal.span {C x * X - C y} →+* (ResidueField R)[X] :=
  Ideal.Quotient.lift _ (mapRingHom (residue R)) fun a ha => by
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp [(residue_eq_zero_iff x).mpr hx, (residue_eq_zero_iff y).mpr hy]

/-- The reduction map on the class of a polynomial. -/
@[simp]
theorem toResidue_mk (hx : x ∈ maximalIdeal R) (hy : y ∈ maximalIdeal R) (p : R[X]) :
    toResidue hx hy (Ideal.Quotient.mk _ p) = p.map (residue R) := rfl

/-- The reduction map is surjective. -/
theorem toResidue_surjective (hx : x ∈ maximalIdeal R) (hy : y ∈ maximalIdeal R) :
    Function.Surjective (toResidue hx hy) := by
  intro q
  obtain ⟨p, rfl⟩ := Polynomial.map_surjective _ (residue_surjective (R := R)) q
  exact ⟨_, toResidue_mk hx hy p⟩

/-- If `(x, y)` is the maximal ideal, the kernel of the reduction `C → κ[T]` is `(x)`. -/
theorem ker_toResidue (hm : maximalIdeal R = Ideal.span {x, y}) :
    RingHom.ker (toResidue (hm ▸ Ideal.subset_span (by simp) : x ∈ maximalIdeal R)
      (hm ▸ Ideal.subset_span (by simp) : y ∈ maximalIdeal R)) =
      Ideal.span {algebraMap R (R[X] ⧸ Ideal.span {C x * X - C y}) x} := by
  refine le_antisymm (fun c hc => ?_) ?_
  · obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [RingHom.mem_ker, toResidue_mk] at hc
    have hp : p ∈ (maximalIdeal R).map (C : R →+* R[X]) := by
      rw [Ideal.mem_map_C_iff]
      intro n
      rw [← residue_eq_zero_iff, ← coeff_map, hc, coeff_zero]
    rw [hm, Ideal.map_span, Set.image_pair, Ideal.mem_span_pair] at hp
    obtain ⟨a, b, rfl⟩ := hp
    rw [Ideal.mem_span_singleton']
    refine ⟨Ideal.Quotient.mk _ a + Ideal.Quotient.mk _ b * Ideal.Quotient.mk _ X, ?_⟩
    rw [map_add, map_mul, map_mul, mk_C, mk_C, ← algebraMap_mul_mk_X x y]
    ring
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, ← mk_C,
      toResidue_mk, Polynomial.map_C, (residue_eq_zero_iff x).mpr
        (hm ▸ Ideal.subset_span (by simp)), map_zero]

end Residue

end BlowupChart
