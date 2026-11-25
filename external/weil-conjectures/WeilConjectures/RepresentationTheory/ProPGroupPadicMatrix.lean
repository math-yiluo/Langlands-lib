/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
# ℓ-adic matrix representations of pro-`p` groups

Let `p ≠ ℓ` be primes. A continuous representation `ρ : G →* GL_n(ℤ_[ℓ])` of a topological
group `G` in which `g ^ (p ^ k) → 1` for every `g` (a pro-`p` condition) is trivial on an open
subgroup of `G`, namely on the kernel of reduction modulo `ℓ`.

The key input is the congruence `(1 + ℓ ^ m A) ^ N ≡ 1 + N ℓ ^ m A (mod ℓ ^ (m + 1))`
for `m ≥ 1`, which shows that raising to a power `N` prime to `ℓ` does not move a matrix
closer to `1` in the `ℓ`-adic topology.
-/

@[expose] public section

/-- First-order binomial expansion: `(1 + x) ^ N = 1 + N • x + x ^ 2 * y` for some `y`. -/
theorem exists_one_add_pow_eq_one_add_nsmul_add_sq_mul {R : Type*} [Ring R] (x : R) (N : ℕ) :
    ∃ y : R, (1 + x) ^ N = 1 + N • x + x ^ 2 * y := by
  induction N with
  | zero => exact ⟨0, by simp⟩
  | succ N ih =>
    obtain ⟨y, hy⟩ := ih
    refine ⟨N + y + x * y, ?_⟩
    rw [pow_succ', hy]
    simp only [nsmul_eq_mul, Nat.cast_succ, pow_two, mul_add, add_mul, one_mul, mul_one,
      mul_assoc, (Nat.cast_commute N x).eq]
    abel

namespace PadicInt

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- A `ℓ`-adic integer divisible by every power of `ℓ` is zero. -/
theorem eq_zero_of_forall_pow_dvd {x : ℤ_[ℓ]} (hx : ∀ m : ℕ, (ℓ : ℤ_[ℓ]) ^ m ∣ x) : x = 0 := by
  by_contra h
  obtain ⟨n, hn⟩ := FiniteMultiplicity.of_not_isUnit prime_p.not_isUnit h
  exact hn (hx _)

/-- The set of `ℓ`-adic integers divisible by `ℓ ^ k` is open. -/
theorem isOpen_setOf_pow_dvd (k : ℕ) : IsOpen {x : ℤ_[ℓ] | (ℓ : ℤ_[ℓ]) ^ k ∣ x} := by
  have hset : {x : ℤ_[ℓ] | (ℓ : ℤ_[ℓ]) ^ k ∣ x} =
      Metric.closedBall 0 ((ℓ : ℝ) ^ (-k : ℤ)) := by
    ext x
    rw [Set.mem_ofPred_eq, mem_closedBall_zero_iff, norm_le_pow_iff_mem_span_pow,
      Ideal.mem_span_singleton]
  rw [hset]
  exact IsUltrametricDist.isOpen_closedBall _ (zpow_ne_zero _ (by exact_mod_cast
    (Fact.out : ℓ.Prime).ne_zero))

/-- The set of matrices congruent to `1` modulo `ℓ ^ k` entrywise is open. -/
theorem isOpen_setOf_matrix_sub_one_pow_dvd (n : Type*) [Finite n] [DecidableEq n] (k : ℕ) :
    IsOpen {M : Matrix n n ℤ_[ℓ] | ∀ i j, (ℓ : ℤ_[ℓ]) ^ k ∣ (M - 1) i j} := by
  simp only [Set.ofPred_forall]
  refine isOpen_iInter_of_finite fun i ↦ isOpen_iInter_of_finite fun j ↦ ?_
  exact (isOpen_setOf_pow_dvd k).preimage
    (((continuous_id.sub continuous_const).matrix_elem i j))

/-- If `A` is not divisible by `ℓ` and `N` is prime to `ℓ`, then for `m ≥ 1` the matrix
`(1 + ℓ ^ m • A) ^ N - 1` is not divisible by `ℓ ^ (m + 1)`. -/
theorem not_forall_pow_succ_dvd_one_add_pow_smul_pow_sub_one {n : Type*} [Fintype n]
    [DecidableEq n] (A : Matrix n n ℤ_[ℓ]) {m : ℕ} (hm : 1 ≤ m) {N : ℕ} (hN : N.Coprime ℓ)
    (hA : ¬ ∀ i j, (ℓ : ℤ_[ℓ]) ∣ A i j) :
    ¬ ∀ i j, (ℓ : ℤ_[ℓ]) ^ (m + 1) ∣ ((1 + (ℓ : ℤ_[ℓ]) ^ m • A) ^ N - 1) i j := by
  intro h
  refine hA fun i j ↦ ?_
  obtain ⟨Y, hY⟩ := exists_one_add_pow_eq_one_add_nsmul_add_sq_mul ((ℓ : ℤ_[ℓ]) ^ m • A) N
  have hNu : IsUnit (N : ℤ_[ℓ]) := isUnit_iff.2 (norm_natCast_eq_one_iff.2 hN.symm)
  have hij := h i j
  have key : ((1 + (ℓ : ℤ_[ℓ]) ^ m • A) ^ N - 1) i j =
      (ℓ : ℤ_[ℓ]) ^ m * (N * A i j + (ℓ : ℤ_[ℓ]) ^ m * (A ^ 2 * Y) i j) := by
    rw [hY, add_assoc, add_sub_cancel_left, smul_pow, smul_mul_assoc, Matrix.add_apply,
      Matrix.smul_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
      nsmul_eq_mul]
    ring
  rw [key, pow_succ, mul_dvd_mul_iff_left (pow_ne_zero _ (Nat.cast_ne_zero.2
      (Fact.out : ℓ.Prime).ne_zero))] at hij
  have hℓ : (ℓ : ℤ_[ℓ]) ∣ N * A i j := by
    refine (dvd_add_left ?_).1 hij
    exact (dvd_pow_self _ (by omega)).mul_right _
  exact (hNu.dvd_mul_left).1 hℓ

end PadicInt

open PadicInt

/-- In a continuous `ℓ`-adic matrix representation of a pro-`p` group, `p ≠ ℓ`, every element
congruent to `1` modulo `ℓ` acts trivially. -/
theorem eq_one_of_forall_dvd_sub_one_of_tendsto_pow_prime_pow {G : Type*} [Group G]
    [TopologicalSpace G] {ℓ p : ℕ} [Fact ℓ.Prime] (hp : p.Prime) (hpℓ : p ≠ ℓ)
    (hG : ∀ g : G, Filter.Tendsto (fun k : ℕ ↦ g ^ (p ^ k)) Filter.atTop (nhds 1))
    {n : Type*} [Fintype n] [DecidableEq n] (ρ : G →* (Matrix n n ℤ_[ℓ])ˣ)
    (hρ : Continuous fun g ↦ (ρ g : Matrix n n ℤ_[ℓ])) (g : G)
    (hg : ∀ i j, (ℓ : ℤ_[ℓ]) ∣ ((ρ g : Matrix n n ℤ_[ℓ]) - 1) i j) : ρ g = 1 := by
  have hcop (k : ℕ) : (p ^ k).Coprime ℓ :=
    ((Nat.coprime_primes hp (Fact.out : ℓ.Prime)).2 hpℓ).pow_left k
  have hall (m : ℕ) (hm : 1 ≤ m) :
      ∀ i j, (ℓ : ℤ_[ℓ]) ^ m ∣ ((ρ g : Matrix n n ℤ_[ℓ]) - 1) i j := by
    induction m, hm using Nat.le_induction with
    | base => simpa using hg
    | succ m hm ih =>
      choose A hA using ih
      have hρg : (ρ g : Matrix n n ℤ_[ℓ]) = 1 + (ℓ : ℤ_[ℓ]) ^ m • Matrix.of A := by
        ext i j : 1
        rw [Matrix.add_apply, ← sub_eq_iff_eq_add', ← Matrix.sub_apply, hA]
        simp
      by_cases hdiv : ∀ i j, (ℓ : ℤ_[ℓ]) ∣ Matrix.of A i j
      · intro i j
        rw [hA, pow_succ]
        exact mul_dvd_mul_left _ (hdiv i j)
      · have hlim := (hρ.tendsto 1).comp (hG g)
        rw [map_one, Units.val_one] at hlim
        obtain ⟨k, hk⟩ := (hlim.eventually ((isOpen_setOf_matrix_sub_one_pow_dvd n
          (m + 1)).mem_nhds (by simp))).exists
        refine absurd ?_ (not_forall_pow_succ_dvd_one_add_pow_smul_pow_sub_one _ hm
          (hcop k) hdiv)
        simpa [Function.comp, map_pow, Units.val_pow_eq_pow_val, hρg] using hk
  refine Units.ext (sub_eq_zero.1 (Matrix.ext fun i j ↦ eq_zero_of_forall_pow_dvd fun m ↦ ?_))
  exact (pow_dvd_pow _ (Nat.le_succ m)).trans (hall (m + 1) (by omega) i j)

/-- A continuous `ℓ`-adic matrix representation of a pro-`p` group, `p ≠ ℓ`, is trivial on an
open subgroup: its kernel is open, being the kernel of reduction modulo `ℓ`. -/
theorem exists_isOpen_forall_eq_one_of_tendsto_pow_prime_pow {G : Type*} [Group G]
    [TopologicalSpace G] {ℓ p : ℕ} [Fact ℓ.Prime] (hp : p.Prime) (hpℓ : p ≠ ℓ)
    (hG : ∀ g : G, Filter.Tendsto (fun k : ℕ ↦ g ^ (p ^ k)) Filter.atTop (nhds 1))
    {n : Type*} [Fintype n] [DecidableEq n] (ρ : G →* (Matrix n n ℤ_[ℓ])ˣ)
    (hρ : Continuous fun g ↦ (ρ g : Matrix n n ℤ_[ℓ])) :
    ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ g ∈ U, ρ g = 1 := by
  refine ⟨ρ.ker, ?_, fun g hg ↦ hg⟩
  have hker : (ρ.ker : Set G) = (fun g ↦ (ρ g : Matrix n n ℤ_[ℓ])) ⁻¹'
      {M | ∀ i j, (ℓ : ℤ_[ℓ]) ^ 1 ∣ (M - 1) i j} := by
    ext g
    refine ⟨fun hg ↦ ?_, fun hg ↦ ?_⟩
    · simp [MonoidHom.mem_ker.1 hg]
    · exact eq_one_of_forall_dvd_sub_one_of_tendsto_pow_prime_pow hp hpℓ hG ρ hρ g
        (by simpa using hg)
  rw [hker]
  exact (isOpen_setOf_matrix_sub_one_pow_dvd n 1).preimage hρ
