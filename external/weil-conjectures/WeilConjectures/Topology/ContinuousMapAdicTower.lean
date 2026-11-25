/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# The adic tower of continuous maps into a complete normed ring

Let `T` be a complete normed ring all of whose elements have norm `≤ 1` (e.g. the ring of
integers of a complete non-archimedean field) and `n : ℤ` with `‖(n : T)‖ < 1`. For any
topological space `W`, the map `(xᵢ) ↦ (xᵢ - n • xᵢ₊₁)` is a bijection of `ℕ → C(W, T)`
(`ContinuousMap.bijective_sub_zsmul_succ`): it is injective since `T` is `n`-adically separated,
and the inverse is `(yᵢ) ↦ (∑ₖ nᵏ yᵢ₊ₖ)`, the series converging uniformly on `W`.

In other words, the abelian group `C(W, T)` is derived `n`-adically complete.
-/

@[expose] public section

variable {T : Type*} [NormedRing T]

/-- In a normed ring whose elements all have norm `≤ 1`, `‖cᵏ x‖ ≤ ‖c‖ᵏ`. -/
lemma norm_pow_mul_le_pow_of_forall_norm_le_one (hT : ∀ x : T, ‖x‖ ≤ 1) (c x : T) (k : ℕ) :
    ‖c ^ k * x‖ ≤ ‖c‖ ^ k := by
  induction k with
  | zero => simpa using hT x
  | succ k ih =>
    rw [pow_succ', mul_assoc, pow_succ']
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ih (norm_nonneg _))

namespace ContinuousMap

variable {W : Type*} [TopologicalSpace W]

/-- Let `T` be a normed ring whose elements all have norm `≤ 1`, and `n : ℤ` with
`‖(n : T)‖ < 1`. Then the map `(xᵢ) ↦ (xᵢ - n • xᵢ₊₁)` on `ℕ → C(W, T)` is injective. -/
lemma injective_sub_zsmul_succ (n : ℤ) (hn : ‖(n : T)‖ < 1) (hT : ∀ x : T, ‖x‖ ≤ 1) :
    Function.Injective fun x : ℕ → C(W, T) ↦ fun i ↦ x i - n • x (i + 1) := by
  intro x x' hxx'
  have hd (i : ℕ) (w : W) : (x i - x' i) w = (n : T) * (x (i + 1) - x' (i + 1)) w := by
    have h := sub_eq_sub_iff_sub_eq_sub.1 (congrFun hxx' i)
    rw [h, ← smul_sub, ContinuousMap.zsmul_apply, zsmul_eq_mul]
  have hb (k i : ℕ) (w : W) : ‖(x i - x' i) w‖ ≤ ‖(n : T)‖ ^ k := by
    induction k generalizing i with
    | zero => simpa using hT _
    | succ k ih =>
      rw [hd, pow_succ']
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (ih _) (norm_nonneg _))
  funext i
  refine ContinuousMap.ext fun w ↦ sub_eq_zero.1 (norm_le_zero_iff.1 ?_)
  exact ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hn)
    fun k ↦ hb k i w

/-- Let `T` be a complete normed ring whose elements all have norm `≤ 1`, and `n : ℤ` with
`‖(n : T)‖ < 1`. Then the map `(xᵢ) ↦ (xᵢ - n • xᵢ₊₁)` on `ℕ → C(W, T)` is surjective: a
preimage of `(yᵢ)` is `(∑ₖ nᵏ yᵢ₊ₖ)`. -/
lemma surjective_sub_zsmul_succ [CompleteSpace T] (n : ℤ) (hn : ‖(n : T)‖ < 1)
    (hT : ∀ x : T, ‖x‖ ≤ 1) :
    Function.Surjective fun x : ℕ → C(W, T) ↦ fun i ↦ x i - n • x (i + 1) := by
  intro y
  have hg := summable_geometric_of_lt_one (norm_nonneg _) hn
  have hb (i k : ℕ) (w : W) : ‖(n : T) ^ k * y (i + k) w‖ ≤ ‖(n : T)‖ ^ k :=
    norm_pow_mul_le_pow_of_forall_norm_le_one hT _ _ k
  have hs (i : ℕ) (w : W) : Summable fun k ↦ (n : T) ^ k * y (i + k) w :=
    Summable.of_norm_bounded hg (hb i · w)
  let x (i : ℕ) : C(W, T) := ⟨fun w ↦ ∑' k, (n : T) ^ k * y (i + k) w,
    continuous_tsum (fun k ↦ continuous_const.mul (y (i + k)).continuous) hg (hb i)⟩
  refine ⟨x, funext fun i ↦ ContinuousMap.ext fun w ↦ ?_⟩
  have h : ∑' k, (n : T) ^ (k + 1) * y (i + (k + 1)) w =
      (n : T) * ∑' k, (n : T) ^ k * y (i + 1 + k) w := by
    rw [← (hs (i + 1) w).tsum_mul_left]
    refine tsum_congr fun k ↦ ?_
    rw [pow_succ', mul_assoc, add_comm k 1, add_assoc]
  simp only [ContinuousMap.sub_apply, zsmul_eq_mul, x, ContinuousMap.coe_mk]
  rw [(hs i w).tsum_eq_zero_add, h]
  simp

/-- Let `T` be a complete normed ring whose elements all have norm `≤ 1`, and `n : ℤ` with
`‖(n : T)‖ < 1`. Then the map `(xᵢ) ↦ (xᵢ - n • xᵢ₊₁)` on `ℕ → C(W, T)` is bijective. -/
lemma bijective_sub_zsmul_succ [CompleteSpace T] (n : ℤ) (hn : ‖(n : T)‖ < 1)
    (hT : ∀ x : T, ‖x‖ ≤ 1) :
    Function.Bijective fun x : ℕ → C(W, T) ↦ fun i ↦ x i - n • x (i + 1) :=
  ⟨injective_sub_zsmul_succ n hn hT, surjective_sub_zsmul_succ n hn hT⟩

end ContinuousMap
