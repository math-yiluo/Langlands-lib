/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import WeilConjectures.Mathlib.RingTheory.PowerSeries.Derivative
public import WeilConjectures.Mathlib.RingTheory.PowerSeries.Expand
public import WeilConjectures.Mathlib.RingTheory.PowerSeries.Inverse
public import WeilConjectures.Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Locally finite products of power series

A family `(f j)` of power series is *locally finite* if for every `n` all but finitely many of
the `f j` are congruent to `1` modulo `X ^ (n + 1)`. Such a family is multipliable in the
product topology, and the coefficients of degree at most `n` of its product are those of a
finite partial product over any finite set containing the exceptional indices for `n`.

The product `∏ₓ (1 - X ^ eₓ)⁻¹` of a family of degrees `eₓ ≥ 1` taking every value finitely often
is an example: it is the shape of the zeta function of a scheme of finite type over a finite
field. It is not a polynomial as soon as the family is nonempty, since it has nonnegative
coefficients and dominates each of its factors.

## Main statements

- `PowerSeries.WithPiTopology.hasProd_of_X_pow_dvd_sub_one`
- `PowerSeries.WithPiTopology.coeff_tprod_of_X_pow_dvd_sub_one`
- `PowerSeries.WithPiTopology.multipliable_inv_one_sub_X_pow`
- `PowerSeries.WithPiTopology.tprod_inv_one_sub_X_pow_ne_coe`
-/

@[expose] public section

namespace PowerSeries

variable {R : Type*} [CommRing R]

namespace WithPiTopology

open scoped PowerSeries.WithPiTopology

variable [TopologicalSpace R]

/-- A locally finite family of power series is multipliable: if `S n` is a finite set of
indices outside of which every `f j` is congruent to `1` modulo `X ^ (n + 1)`, then the product
of the family has, in degree `n`, the coefficient of the finite product over `S n`. -/
theorem hasProd_of_X_pow_dvd_sub_one {J : Type*} {f : J → R⟦X⟧} (S : ℕ → Finset J)
    (hS : ∀ n, ∀ j ∉ S n, X ^ (n + 1) ∣ f j - 1) :
    HasProd f (mk fun n ↦ coeff n (∏ j ∈ S n, f j)) := by
  classical
  rw [HasProd, tendsto_iff_coeff_tendsto]
  intro n
  rw [coeff_mk]
  refine tendsto_nhds_of_eventually_eq ?_
  filter_upwards [Filter.eventually_ge_atTop (S n)] with t ht
  have h := X_pow_dvd_prod_sub_prod_of_subset ht f (n + 1) fun j _ hj ↦ hS n j hj
  rw [X_pow_dvd_iff] at h
  exact sub_eq_zero.1 (by simpa using h n (Nat.lt_succ_self n))

variable [T2Space R]

/-- The coefficients of degree at most `n` of the product of a locally finite family of power
series are those of the finite product over any finite set `s` of indices outside of which all
factors are congruent to `1` modulo `X ^ (n + 1)`. -/
theorem coeff_tprod_of_X_pow_dvd_sub_one {J : Type*} {f : J → R⟦X⟧} (S : ℕ → Finset J)
    (hS : ∀ n, ∀ j ∉ S n, X ^ (n + 1) ∣ f j - 1) {n : ℕ} (s : Finset J)
    (hs : ∀ j ∉ s, X ^ (n + 1) ∣ f j - 1) {k : ℕ} (hk : k ≤ n) :
    coeff k (∏' j, f j) = coeff k (∏ j ∈ s, f j) := by
  classical
  rw [(hasProd_of_X_pow_dvd_sub_one S hS).tprod_eq, coeff_mk]
  have h₁ := X_pow_dvd_prod_sub_prod_of_subset (Finset.subset_union_left (s₂ := s)) f (k + 1)
    fun j hj hjS ↦ hS k j hjS
  have h₂ := X_pow_dvd_prod_sub_prod_of_subset (Finset.subset_union_right (s₁ := S k)) f (k + 1)
    fun j hj hjs ↦ (pow_dvd_pow X (by omega)).trans (hs j hjs)
  rw [X_pow_dvd_iff] at h₁ h₂
  have e₁ := sub_eq_zero.1 (by simpa using h₁ k (Nat.lt_succ_self k))
  have e₂ := sub_eq_zero.1 (by simpa using h₂ k (Nat.lt_succ_self k))
  rw [← e₁, e₂]

end WithPiTopology

end PowerSeries

namespace PowerSeries

namespace WithPiTopology

open scoped PowerSeries.WithPiTopology

variable {R : Type*} [Field R] [TopologicalSpace R]

/-- The power series supported on the multiples of `f` form a closed submonoid. -/
theorem isClosed_dvdSupportSubmonoid [T2Space R] (f : ℕ) :
    IsClosed ((dvdSupportSubmonoid f : Submonoid R⟦X⟧) : Set R⟦X⟧) := by
  have : ((dvdSupportSubmonoid f : Submonoid R⟦X⟧) : Set R⟦X⟧) =
      ⋂ n, ⋂ (_ : ¬ f ∣ n), {G | coeff n G = 0} := by
    ext G
    simp [mem_dvdSupportSubmonoid_iff]
  rw [this]
  exact isClosed_iInter fun n ↦ isClosed_iInter fun _ ↦
    isClosed_eq (continuous_coeff R n) continuous_const

/-- A family `∏ₓ (1 - X ^ eₓ)⁻¹` with all `eₓ ≥ 1` and only finitely many `eₓ` below any bound is
multipliable. -/
theorem multipliable_inv_one_sub_X_pow {β : Type*} {e : β → ℕ} (he : ∀ b, e b ≠ 0)
    (hfin : ∀ n, {b | e b ≤ n}.Finite) :
    Multipliable fun b ↦ ((1 : R⟦X⟧) - X ^ e b)⁻¹ := by
  refine ⟨_, hasProd_of_X_pow_dvd_sub_one (fun n ↦ (hfin n).toFinset) fun n b hb ↦ ?_⟩
  have hnb : n + 1 ≤ e b := by
    by_contra h
    exact hb ((hfin n).mem_toFinset.2 (show e b ≤ n by omega))
  refine (pow_dvd_pow X hnb).trans ⟨((1 : R⟦X⟧) - X ^ e b)⁻¹, ?_⟩
  have h₁ : constantCoeff ((1 : R⟦X⟧) - X ^ e b) ≠ 0 := by simp [he b]
  have h₂ : ((1 : R⟦X⟧) - X ^ e b)⁻¹ * ((1 : R⟦X⟧) - X ^ e b) = 1 :=
    (eq_inv_iff_mul_eq_one h₁).1 rfl
  linear_combination h₂

/-- A family `∏_b (f b)⁻¹` with `f b ≡ 1` modulo `X ^ e b`, all `e b ≥ 1` and only finitely many
`e b` below any bound is multipliable. -/
theorem multipliable_inv_of_X_pow_dvd_sub_one {β : Type*} {e : β → ℕ} {f : β → R⟦X⟧}
    (he : ∀ b, e b ≠ 0) (hf : ∀ b, X ^ e b ∣ f b - 1) (hfin : ∀ n, {b | e b ≤ n}.Finite) :
    Multipliable fun b ↦ (f b)⁻¹ := by
  refine ⟨_, hasProd_of_X_pow_dvd_sub_one (fun n ↦ (hfin n).toFinset) fun n b hb ↦ ?_⟩
  have hnb : n + 1 ≤ e b := by
    by_contra h
    exact hb ((hfin n).mem_toFinset.2 (show e b ≤ n by omega))
  obtain ⟨q, hq⟩ := hf b
  have h₁ : constantCoeff (f b) = 1 := by
    have h := congrArg constantCoeff hq
    rw [map_sub, map_one, map_mul, map_pow, constantCoeff_X, zero_pow (he b), zero_mul,
      sub_eq_zero] at h
    exact h
  have h₂ : (f b)⁻¹ * f b = 1 := PowerSeries.inv_mul_cancel _ (by rw [h₁]; exact one_ne_zero)
  refine (pow_dvd_pow X hnb).trans ⟨-(f b)⁻¹ * q, ?_⟩
  linear_combination h₂ - (f b)⁻¹ * hq

open ComplexOrder

/-- The power series over `ℂ` with nonnegative real coefficients and constant coefficient `1`. -/
def nonnegOneSubmonoid : Submonoid ℂ⟦X⟧ where
  carrier := {G | (∀ n, 0 ≤ coeff n G) ∧ constantCoeff G = 1}
  mul_mem' {G H} hG hH := by
    refine ⟨fun n ↦ ?_, by simp [hG.2, hH.2]⟩
    rw [coeff_mul]
    exact Finset.sum_nonneg fun p _ ↦ mul_nonneg (hG.1 _) (hH.1 _)
  one_mem' := ⟨fun n ↦ by rw [coeff_one]; split_ifs <;> simp, by simp⟩

theorem inv_one_sub_X_pow_mem_nonnegOneSubmonoid {e : ℕ} (he : e ≠ 0) :
    ((1 : ℂ⟦X⟧) - X ^ e)⁻¹ ∈ nonnegOneSubmonoid := by
  rw [inv_one_sub_X_pow_eq_mk he]
  refine ⟨fun n ↦ ?_, by simp⟩
  rw [coeff_mk]
  split_ifs <;> simp

/-- The coefficients of `∏ₓ (1 - X ^ eₓ)⁻¹` in the degrees `e_{x₀} k` are at least `1`: the
product dominates its factor `(1 - X ^ e_{x₀})⁻¹ = ∑ₖ X ^ (e_{x₀} k)`, all factors having
nonnegative coefficients. -/
theorem one_le_coeff_tprod_inv_one_sub_X_pow {β : Type*} {e : β → ℕ} (he : ∀ b, e b ≠ 0)
    (hm : Multipliable fun b ↦ ((1 : ℂ⟦X⟧) - X ^ e b)⁻¹) (b₀ : β) (k : ℕ) :
    1 ≤ coeff (e b₀ * k) (∏' b, ((1 : ℂ⟦X⟧) - X ^ e b)⁻¹) := by
  classical
  set F : β → ℂ⟦X⟧ := fun b ↦ ((1 : ℂ⟦X⟧) - X ^ e b)⁻¹
  let T : Set ℂ⟦X⟧ := {G | 1 ≤ coeff (e b₀ * k) G}
  have hT : IsClosed T := isClosed_le continuous_const (continuous_coeff ℂ _)
  refine hT.mem_of_tendsto hm.hasProd ?_
  filter_upwards [Filter.eventually_ge_atTop {b₀}] with s hs
  have hb₀ : b₀ ∈ s := hs (Finset.mem_singleton_self b₀)
  rw [← Finset.mul_prod_erase s F hb₀]
  have hG : ∏ b ∈ s.erase b₀, F b ∈ nonnegOneSubmonoid :=
    Submonoid.prod_mem _ fun b _ ↦ inv_one_sub_X_pow_mem_nonnegOneSubmonoid (he b)
  have hF := inv_one_sub_X_pow_mem_nonnegOneSubmonoid (he b₀)
  change 1 ≤ coeff (e b₀ * k) (F b₀ * ∏ b ∈ s.erase b₀, F b)
  rw [coeff_mul]
  have hmem : (e b₀ * k, 0) ∈ Finset.HasAntidiagonal.antidiagonal (e b₀ * k) := by simp
  refine le_trans ?_ (Finset.single_le_sum (fun p _ ↦ mul_nonneg (hF.1 p.1) (hG.1 p.2)) hmem)
  have h0 : coeff 0 (∏ b ∈ s.erase b₀, F b) = 1 := by simpa using hG.2
  simp only [h0, mul_one, F, inv_one_sub_X_pow_eq_mk (he b₀), coeff_mk, dvd_mul_right,
    ite_true, le_refl]

/-- The product `∏ₓ (1 - X ^ eₓ)⁻¹` over a nonempty family is not a polynomial. -/
theorem tprod_inv_one_sub_X_pow_ne_coe {β : Type*} [Nonempty β] {e : β → ℕ}
    (he : ∀ b, e b ≠ 0) (hm : Multipliable fun b ↦ ((1 : ℂ⟦X⟧) - X ^ e b)⁻¹)
    (R : Polynomial ℂ) : ∏' b, ((1 : ℂ⟦X⟧) - X ^ e b)⁻¹ ≠ (R : ℂ⟦X⟧) := by
  intro h
  obtain ⟨b₀⟩ := ‹Nonempty β›
  have h₁ := one_le_coeff_tprod_inv_one_sub_X_pow he hm b₀ (R.natDegree + 1)
  rw [h, Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt] at h₁
  · exact absurd h₁ (zero_lt_one (α := ℂ)).not_ge
  · calc R.natDegree < R.natDegree + 1 := Nat.lt_succ_self _
      _ ≤ e b₀ * (R.natDegree + 1) := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (he b₀))

end WithPiTopology

end PowerSeries

namespace PowerSeries

variable {R : Type*} [CommRing R]

namespace WithPiTopology

open scoped PowerSeries.WithPiTopology

variable [TopologicalSpace R] [T2Space R]

/-- The logarithmic derivative of a locally finite product: if `X fⱼ' = aⱼ fⱼ` for all `j`, and
for every `n` all `fⱼ` with `j` outside the finite set `S n` are congruent to `1`, and all `aⱼ`
to `0`, modulo `X ^ (n + 1)`, then `X (∏' fⱼ)' = A ∏' fⱼ` for the sum `A = ∑ aⱼ`, whose `n`-th
coefficient is that of the finite sum over `S n`. -/
theorem X_mul_derivative_tprod_of_X_pow_dvd_sub_one {J : Type*} {f a : J → R⟦X⟧}
    (S : ℕ → Finset J) (hS : ∀ n, ∀ j ∉ S n, X ^ (n + 1) ∣ f j - 1)
    (ha : ∀ n, ∀ j ∉ S n, X ^ (n + 1) ∣ a j)
    (hf : ∀ j, X * derivative (R := R) (f j) = a j * f j) {A : R⟦X⟧}
    (hA : ∀ n, coeff n A = ∑ j ∈ S n, coeff n (a j)) :
    X * derivative (R := R) (∏' j, f j) = A * ∏' j, f j := by
  classical
  ext n
  have hP (k : ℕ) (hk : k ≤ n) : coeff k (∏' j, f j) = coeff k (∏ j ∈ S n, f j) :=
    coeff_tprod_of_X_pow_dvd_sub_one S hS (S n) (hS n) hk
  have hcoeff (i : ℕ) (hi : i ≤ n) : coeff i A = coeff i (∑ j ∈ S n, a j) := by
    have hz (m : ℕ) (hm : i ≤ m) (j : J) (hj : j ∉ S m) : coeff i (a j) = 0 :=
      (X_pow_dvd_iff.1 ((pow_dvd_pow X (by omega : i + 1 ≤ m + 1)).trans (ha m j hj))) i
        (Nat.lt_succ_self i)
    rw [hA, map_sum]
    exact (Finset.sum_subset (Finset.subset_union_left (s₂ := S n))
      fun j _ hj ↦ hz i le_rfl j hj).trans (Finset.sum_subset
        (Finset.subset_union_right (s₁ := S i)) fun j _ hj ↦ hz n hi j hj).symm
  rw [coeff_X_mul_derivative, hP n le_rfl, ← coeff_X_mul_derivative,
    X_mul_derivative_prod _ fun j _ ↦ hf j, coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have h := Finset.mem_antidiagonal.1 hp
  rw [hcoeff p.1 (by omega), hP p.2 (by omega)]

end WithPiTopology

end PowerSeries
