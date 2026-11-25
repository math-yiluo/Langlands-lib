/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Residually independent families and valuation independence

Let `v` be a valuation on a field `F` and `K ⊆ F` a subfield. A family `z` of elements of `F` of
value `1` is *residually independent* over `K` if every combination `∑ c j • z j` with
coefficients `c j ∈ K` of value `≤ 1` and of value `< 1` has all its coefficients of value `< 1`
(i.e. the residues of the `z j` are linearly independent over the residue field of `K`).

## Main statements

- `Valuation.ResiduallyIndependent.map_sum_smul`: for a residually independent family `z`,
  `v (∑ c j • z j) = max_j v (c j)`.
- `Valuation.ResiduallyIndependent.linearIndependent_mul`: if moreover the `w i` are nonzero
  with values pairwise distinct modulo `v(Kˣ)`, the products `w i * z j` are `K`-linearly
  independent; `Valuation.ResiduallyIndependent.card_mul_card_le_finrank` is the corresponding
  inequality `e * f ≤ [E : K]`.
- `ValuationSubring.exists_basis_residuallyIndependent`: the *cartesian lemma*: if `K` is the
  fraction field of a complete discrete valuation ring `R`, `𝒪` is a valuation ring of `F` with
  `𝒪 ∩ K = R` and every value of `F` is a value of `K`, then every finite-dimensional
  `K`-subspace of `F` has a residually independent basis of elements of value `1`.
-/

@[expose] public section

open Module

namespace Valuation

variable {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀)
  (K : Type*) [Field K] [Algebra K F]

/-- A family `z` is residually independent over `K` for `v` if every `v`-integral linear
combination with coefficients in `K` of value `< 1` has all coefficients of value `< 1`. -/
def ResiduallyIndependent {ι : Type*} [Fintype ι] (z : ι → F) : Prop :=
  ∀ c : ι → K, (∀ j, v (algebraMap K F (c j)) ≤ 1) → v (∑ j, c j • z j) < 1 →
    ∀ j, v (algebraMap K F (c j)) < 1

variable {v K}

/-- **Residually independent families are valuation independent**: the value of a combination
of a residually independent family of elements of value `1` is the maximum of the values of the
coefficients. -/
theorem ResiduallyIndependent.map_sum_smul {ι : Type*} [Fintype ι] {z : ι → F}
    (h : v.ResiduallyIndependent K z) (hz : ∀ j, v (z j) = 1) (c : ι → K) :
    v (∑ j, c j • z j) = Finset.univ.sup fun j => v (algebraMap K F (c j)) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [bot_eq_zero]
  obtain ⟨j₀, -, hj₀⟩ := Finset.univ.exists_max_image (fun j => v (algebraMap K F (c j)))
    Finset.univ_nonempty
  have hsup : (Finset.univ.sup fun j => v (algebraMap K F (c j))) = v (algebraMap K F (c j₀)) :=
    le_antisymm (Finset.sup_le fun j _ => hj₀ j (Finset.mem_univ j))
      (Finset.le_sup (f := fun j => v (algebraMap K F (c j))) (Finset.mem_univ j₀))
  rw [hsup]
  by_cases h0 : c j₀ = 0
  · have hc (j : ι) : c j = 0 := by simpa [h0] using hj₀ j (Finset.mem_univ j)
    simp [hc]
  have key : ∑ j, c j • z j = c j₀ • ∑ j, (c j / c j₀) • z j := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, mul_div_cancel₀ _ h0]
  have hle (j : ι) : v (algebraMap K F (c j / c j₀)) ≤ 1 := by
    rw [map_div₀, map_div₀]
    exact div_le_one_of_le₀ (hj₀ j (Finset.mem_univ _)) zero_le
  have h1 : v (∑ j, (c j / c j₀) • z j) = 1 := by
    refine le_antisymm (v.map_sum_le fun j _ => ?_) (not_lt.1 fun hlt => ?_)
    · rw [Algebra.smul_def, map_mul, hz, mul_one]
      exact hle j
    · simpa [div_self h0] using h _ hle hlt j₀
  rw [key, Algebra.smul_def, map_mul, h1, mul_one]

/-- A residually independent family of elements of value `1` is linearly independent. -/
theorem ResiduallyIndependent.linearIndependent {ι : Type*} [Fintype ι] {z : ι → F}
    (h : v.ResiduallyIndependent K z) (hz : ∀ j, v (z j) = 1) : LinearIndependent K z := by
  refine Fintype.linearIndependent_iff.2 fun c hc j => ?_
  have h0 := h.map_sum_smul hz c
  have hj := Finset.le_sup (f := fun j => v (algebraMap K F (c j))) (Finset.mem_univ j)
  rw [← h0, hc, map_zero] at hj
  simpa using le_antisymm hj zero_le

/-- If a finite sum vanishes and its nonzero terms have pairwise distinct values, then all
terms vanish. -/
theorem eq_zero_of_sum_eq_zero {κ : Type*} [Fintype κ] {x : κ → F}
    (hx : ∀ i i', i ≠ i' → x i ≠ 0 → x i' ≠ 0 → v (x i) ≠ v (x i')) (hsum : ∑ i, x i = 0)
    (i : κ) : x i = 0 := by
  classical
  by_contra hne
  obtain ⟨i₀, -, hi₀⟩ := Finset.univ.exists_max_image (fun i => v (x i)) ⟨i, Finset.mem_univ i⟩
  have h0 : v (x i₀) ≠ 0 := fun h =>
    hne (v.zero_iff.1 (le_antisymm ((hi₀ i (Finset.mem_univ i)).trans h.le) zero_le))
  have hlt : v (∑ i ∈ Finset.univ.erase i₀, x i) < v (x i₀) := v.map_sum_lt h0 fun i hi => by
    rcases eq_or_ne (x i) 0 with h | h
    · rw [h, map_zero]
      exact zero_lt_iff.2 h0
    · exact lt_of_le_of_ne (hi₀ i (Finset.mem_univ i))
        (hx i i₀ (Finset.ne_of_mem_erase hi) h (v.ne_zero_iff.1 h0))
  have h' := congrArg v hsum
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), v.map_add_eq_of_lt_left hlt,
    map_zero] at h'
  exact h0 h'

/-- If `z` is a residually independent family of elements of value `1` and the `w i` are nonzero
with values pairwise distinct modulo `v(Kˣ)`, then the products `w i * z j` are linearly
independent over `K`. -/
theorem ResiduallyIndependent.linearIndependent_mul {ι κ : Type*} [Fintype ι] [Finite κ]
    {z : ι → F} (h : v.ResiduallyIndependent K z) (hz : ∀ j, v (z j) = 1) {w : κ → F}
    (hw : ∀ i, w i ≠ 0)
    (hdist : ∀ i i', i ≠ i' → ∀ c : K, v (w i) ≠ v (algebraMap K F c) * v (w i')) :
    LinearIndependent K fun p : κ × ι => w p.1 * z p.2 := by
  cases nonempty_fintype κ
  classical
  refine Fintype.linearIndependent_iff.2 fun g hg p => ?_
  have hs (i : κ) : ∃ c : K, v (∑ j, g (i, j) • z j) = v (algebraMap K F c) := by
    rcases isEmpty_or_nonempty ι with hι | hι
    · exact ⟨0, by simp⟩
    obtain ⟨j, -, hj⟩ := Finset.univ.exists_mem_eq_sup Finset.univ_nonempty
      (fun j => v (algebraMap K F (g (i, j))))
    exact ⟨g (i, j), by rw [h.map_sum_smul hz, hj]⟩
  choose c hc using hs
  have hzero := v.eq_zero_of_sum_eq_zero (x := fun i => w i * ∑ j, g (i, j) • z j)
    (fun i i' hii' h1 h2 heq => ?_) ?_ p.1
  · have hsum : ∑ j, g (p.1, j) • z j = 0 := (mul_eq_zero.1 hzero).resolve_left (hw p.1)
    exact Fintype.linearIndependent_iff.1 (h.linearIndependent hz) (fun j => g (p.1, j)) hsum p.2
  · simp only [map_mul, hc] at heq
    have hci : v (algebraMap K F (c i)) ≠ 0 := by
      intro h0
      rw [← hc, v.zero_iff] at h0
      exact h1 (by simp [h0])
    refine hdist i i' hii' (c i' / c i) ?_
    rw [map_div₀, map_div₀, div_mul_eq_mul_div, eq_div_iff hci, heq, mul_comm]
  · rw [← hg, Fintype.sum_prod_type]
    simp [Finset.mul_sum]

/-- The inequality `e * f ≤ [E : K]` deduced from
`Valuation.ResiduallyIndependent.linearIndependent_mul`. -/
theorem ResiduallyIndependent.card_mul_card_le_finrank {ι κ : Type*} [Fintype ι] [Fintype κ]
    {z : ι → F} (h : v.ResiduallyIndependent K z) (hz : ∀ j, v (z j) = 1) {w : κ → F}
    (hw : ∀ i, w i ≠ 0)
    (hdist : ∀ i i', i ≠ i' → ∀ c : K, v (w i) ≠ v (algebraMap K F c) * v (w i'))
    (E : Submodule K F) [FiniteDimensional K E] (hE : ∀ i j, w i * z j ∈ E) :
    Fintype.card κ * Fintype.card ι ≤ finrank K E := by
  rw [← Fintype.card_prod]
  have hli : LinearIndependent K (E.subtype ∘ fun p : κ × ι => ⟨w p.1 * z p.2, hE p.1 p.2⟩) :=
    h.linearIndependent_mul hz hw hdist
  exact (LinearIndependent.of_comp _ hli).fintype_card_le_finrank

end Valuation

/-- `ϖ`-adic approximation: if `R` is `ϖ`-adically precomplete and every element of `M` is a
combination of the `m j` modulo `ϖ M`, then every element of `M` is a combination of the `m j`
modulo `ϖ ^ N M` for all `N`, with coefficients independent of `N`. -/
theorem exists_sum_smul_add_pow_smul {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] {ϖ : R} (hR : IsPrecomplete (Ideal.span {ϖ}) R) (m : ι → M)
    (hm : ∀ y : M, ∃ a : ι → R, ∃ y' : M, y = ∑ j, a j • m j + ϖ • y') (y : M) :
    ∃ b : ι → R, ∀ N : ℕ, ∃ z : M, y = ∑ j, b j • m j + ϖ ^ N • z := by
  choose a y' hy using hm
  obtain ⟨s, hs⟩ : ∃ s : ℕ → M, s = fun n => y'^[n] y := ⟨_, rfl⟩
  obtain ⟨f, hfdef⟩ : ∃ f : ι → ℕ → R, f = fun j N => ∑ n ∈ Finset.range N, ϖ ^ n * a (s n) j :=
    ⟨_, rfl⟩
  have hf (N : ℕ) : y = ∑ j, f j N • m j + ϖ ^ N • s N := by
    induction N with
    | zero => simp [hfdef, hs]
    | succ N ih =>
      have hsN : s (N + 1) = y' (s N) := by
        rw [hs]
        exact Function.iterate_succ_apply' _ _ _
      rw [ih, hy (s N), ← hsN]
      simp [hfdef, Finset.sum_range_succ, add_smul, Finset.sum_add_distrib, smul_add,
        Finset.smul_sum, smul_smul, pow_succ, add_assoc]
  have hlim (j : ι) : ∃ L : R, ∀ N, f j N ≡ L [SMOD Ideal.span {ϖ} ^ N • (⊤ : Submodule R R)] := by
    refine hR.prec fun {k n} hkn => ?_
    rw [SModEq.sub_mem, hfdef]
    dsimp only
    rw [← Finset.sum_range_add_sum_Ico _ hkn]
    simp only [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, sub_add_cancel_left]
    refine (Ideal.neg_mem_iff _).2 (Submodule.sum_mem _ fun i hi => Ideal.mem_span_singleton.2 ?_)
    exact (pow_dvd_pow ϖ (Finset.mem_Ico.1 hi).1).mul_right _
  choose L hL using hlim
  refine ⟨L, fun N => ?_⟩
  have ht (j : ι) : ∃ t : R, f j N = L j + ϖ ^ N * t := by
    have := (SModEq.sub_mem.1 (hL j N))
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at this
    obtain ⟨t, ht⟩ := this
    exact ⟨t, by rw [← ht, add_sub_cancel]⟩
  choose t ht using ht
  refine ⟨∑ j, t j • m j + s N, ?_⟩
  rw [hf N]
  simp [ht, add_smul, Finset.sum_add_distrib, smul_add, Finset.smul_sum, smul_smul, add_assoc]

namespace Valuation

variable {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation F Γ₀}
  {K : Type*} [Field K] [Algebra K F]

/-- Residual independence is invariant under reindexing. -/
theorem ResiduallyIndependent.comp_equiv {ι ι' : Type*} [Fintype ι] [Fintype ι'] {z : ι → F}
    (h : v.ResiduallyIndependent K z) (σ : ι' ≃ ι) : v.ResiduallyIndependent K (z ∘ σ) := by
  intro c hc hlt j
  have h' := h (c ∘ σ.symm) (fun j => hc _) ?_ (σ j)
  · simpa using h'
  · rw [← σ.sum_comp]
    simpa using hlt

/-- A residually independent family can be extended by any `y` of value `1` which is not
congruent modulo the maximal ideal to an integral combination of the family. -/
theorem ResiduallyIndependent.snoc {k : ℕ} {m : Fin k → F} (h : v.ResiduallyIndependent K m)
    {y : F} (hy : v y = 1)
    (hy' : ∀ a : Fin k → K, (∀ j, v (algebraMap K F (a j)) ≤ 1) → ¬ v (y - ∑ j, a j • m j) < 1) :
    v.ResiduallyIndependent K (Fin.snoc m y : Fin (k + 1) → F) := by
  intro c hc hlt
  rw [Fin.sum_univ_castSucc] at hlt
  simp only [Fin.snoc_castSucc, Fin.snoc_last] at hlt
  have hlast : v (algebraMap K F (c (Fin.last k))) < 1 := by
    refine lt_of_le_of_ne (hc _) fun h1 => hy' (fun j => -(c j.castSucc / c (Fin.last k)))
      (fun j => ?_) ?_
    · rw [(algebraMap K F).map_neg, Valuation.map_neg, map_div₀, map_div₀, h1, div_one]
      exact hc _
    · have hc0 : c (Fin.last k) ≠ 0 := by
        rintro h0
        simp [h0] at h1
      have heq : y - ∑ j, (-(c j.castSucc / c (Fin.last k))) • m j =
          (c (Fin.last k))⁻¹ • (∑ j, c j.castSucc • m j + c (Fin.last k) • y) := by
        rw [smul_add, smul_smul, inv_mul_cancel₀ hc0, one_smul, Finset.smul_sum]
        simp [smul_smul, div_eq_inv_mul, mul_comm, add_comm]
      rw [heq, Algebra.smul_def, map_mul, map_inv₀, map_inv₀, h1, inv_one, one_mul]
      exact hlt
  have hrest : v (∑ j, c j.castSucc • m j) < 1 := by
    rw [← add_sub_cancel_right (∑ j, c j.castSucc • m j) (c (Fin.last k) • y), sub_eq_add_neg]
    refine v.map_add_lt hlt ?_
    rw [Valuation.map_neg, Algebra.smul_def, map_mul, hy, mul_one]
    exact hlast
  intro j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simpa using hlast
  · simpa using h _ (fun j => hc _) hrest j

end Valuation

/-- Version of `exists_sum_smul_add_pow_smul` for a submodule `P`. -/
theorem Submodule.exists_sum_smul_add_pow_smul {R M ι : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Fintype ι] {ϖ : R} (hR : IsPrecomplete (Ideal.span {ϖ}) R) (P : Submodule R M)
    {m : ι → M} (hmP : ∀ j, m j ∈ P)
    (hm : ∀ y ∈ P, ∃ a : ι → R, ∃ y' ∈ P, y = ∑ j, a j • m j + ϖ • y') {y : M} (hy : y ∈ P) :
    ∃ b : ι → R, ∀ N : ℕ, ∃ z ∈ P, y = ∑ j, b j • m j + ϖ ^ N • z := by
  have hm' (y : P) : ∃ a : ι → R, ∃ y' : P, y = ∑ j, a j • (⟨m j, hmP j⟩ : P) + ϖ • y' := by
    obtain ⟨a, y', hy'P, hy'⟩ := hm y y.2
    exact ⟨a, ⟨y', hy'P⟩, Subtype.ext (by simpa using hy')⟩
  obtain ⟨b, hb⟩ := _root_.exists_sum_smul_add_pow_smul hR _ hm' ⟨y, hy⟩
  refine ⟨b, fun N => ?_⟩
  obtain ⟨z, hz⟩ := hb N
  exact ⟨z, z.2, by simpa using congrArg Subtype.val hz⟩

namespace ValuationSubring

open IsLocalRing

variable {R K F : Type*} [CommRing R] [Field K] [Algebra R K] [Field F] [Algebra K F] [Algebra R F]
  [IsScalarTower R K F] {𝒪 : ValuationSubring F}

/-- If `𝒪 ∩ K = R`, elements of `R` are integral for `𝒪`. -/
theorem valuation_algebraMap_le_one
    (hO : ∀ x : K, algebraMap K F x ∈ 𝒪 ↔ x ∈ (algebraMap R K).range) (r : R) :
    𝒪.valuation (algebraMap R F r) ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply R K F, valuation_le_one_iff, hO]
  exact ⟨r, rfl⟩

/-- If `𝒪 ∩ K = R`, units of `R` have value `1`. -/
theorem valuation_algebraMap_unit
    (hO : ∀ x : K, algebraMap K F x ∈ 𝒪 ↔ x ∈ (algebraMap R K).range) (u : Rˣ) :
    𝒪.valuation (algebraMap R F u) = 1 := by
  refine le_antisymm (valuation_algebraMap_le_one hO _) ?_
  calc (1 : 𝒪.ValueGroup) = 𝒪.valuation (algebraMap R F (u * u⁻¹ : Rˣ)) := by simp
    _ = 𝒪.valuation (algebraMap R F u) * 𝒪.valuation (algebraMap R F (u⁻¹ : Rˣ)) := by
        rw [Units.val_mul, map_mul, map_mul]
    _ ≤ 𝒪.valuation (algebraMap R F u) :=
        mul_le_of_le_one_right' (valuation_algebraMap_le_one hO _)

/-- If `𝒪 ∩ K = R`, nonunits of `R` have value `< 1`. -/
theorem valuation_algebraMap_lt_one [IsFractionRing R K]
    (hO : ∀ x : K, algebraMap K F x ∈ 𝒪 ↔ x ∈ (algebraMap R K).range) {r : R}
    (hr : ¬IsUnit r) : 𝒪.valuation (algebraMap R F r) < 1 := by
  refine lt_of_le_of_ne (valuation_algebraMap_le_one hO r) fun h1 => hr ?_
  have hr0 : algebraMap R K r ≠ 0 := by
    rintro h0
    rw [IsScalarTower.algebraMap_apply R K F, h0, map_zero, map_zero] at h1
    exact zero_ne_one h1
  obtain ⟨s, hs⟩ := (hO (algebraMap R K r)⁻¹).1 (by
    rw [← valuation_le_one_iff, map_inv₀, map_inv₀, ← IsScalarTower.algebraMap_apply, h1,
      inv_one])
  refine IsUnit.of_mul_eq_one s (IsFractionRing.injective R K ?_)
  rw [map_mul, hs, mul_inv_cancel₀ hr0, map_one]

/-- If the values of `F` are values of `K`, a value `< 1` is at most the value of a
uniformizer of `R`. -/
theorem valuation_le_of_lt_one [IsDomain R] [IsDiscreteValuationRing R]
    (hO : ∀ x : K, algebraMap K F x ∈ 𝒪 ↔ x ∈ (algebraMap R K).range)
    (hval : ∀ y : F, y ≠ 0 → ∃ c : K, 𝒪.valuation y = 𝒪.valuation (algebraMap K F c))
    {ϖ : R} (hϖ : Irreducible ϖ) {y : F} (hy : 𝒪.valuation y < 1) :
    𝒪.valuation y ≤ 𝒪.valuation (algebraMap R F ϖ) := by
  rcases eq_or_ne y 0 with rfl | hy0
  · simp
  obtain ⟨c, hc⟩ := hval y hy0
  rw [hc] at hy ⊢
  obtain ⟨r, rfl⟩ := (hO c).1 ((valuation_le_one_iff _ _).1 hy.le)
  rw [← IsScalarTower.algebraMap_apply] at hy ⊢
  have hr : r ∈ maximalIdeal R := fun hu =>
    (valuation_algebraMap_unit hO hu.unit).not_lt (by simpa using hy)
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hr
  obtain ⟨t, rfl⟩ := hr
  rw [map_mul, map_mul]
  exact mul_le_of_le_one_right' (valuation_algebraMap_le_one hO t)

/-- If the values of `F` are values of `K`, the valuation has rank one. -/
theorem exists_pow_lt_valuation [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]
    (hO : ∀ x : K, algebraMap K F x ∈ 𝒪 ↔ x ∈ (algebraMap R K).range)
    (hval : ∀ y : F, y ≠ 0 → ∃ c : K, 𝒪.valuation y = 𝒪.valuation (algebraMap K F c))
    {ϖ : R} (hϖ : Irreducible ϖ) {y : F} (hy : y ≠ 0) :
    ∃ N : ℕ, 𝒪.valuation (algebraMap R F ϖ) ^ N < 𝒪.valuation y := by
  have hϖ1 := valuation_algebraMap_lt_one hO hϖ.not_isUnit
  have hϖ0 : 0 < 𝒪.valuation (algebraMap R F ϖ) := by
    rw [zero_lt_iff, Valuation.ne_zero_iff, IsScalarTower.algebraMap_apply R K F]
    exact (map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hϖ.ne_zero)
  obtain ⟨c, hc⟩ := hval y hy
  rw [hc]
  by_cases h1 : 1 ≤ 𝒪.valuation (algebraMap K F c)
  · exact ⟨1, by rw [pow_one]; exact hϖ1.trans_le h1⟩
  obtain ⟨r, rfl⟩ := (hO c).1 ((valuation_le_one_iff _ _).1 (not_le.1 h1).le)
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp only [map_zero, Valuation.zero_iff] at hc
    exact hy hc
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr0 hϖ
  refine ⟨n + 1, ?_⟩
  rw [← IsScalarTower.algebraMap_apply, map_mul, map_mul, valuation_algebraMap_unit hO, one_mul,
    map_pow, map_pow]
  exact pow_lt_pow_right_of_lt_one₀ hϖ0 hϖ1 (Nat.lt_succ_self n)

end ValuationSubring

namespace Valuation

variable {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀)
  {K : Type*} [Field K] [Algebra K F]

/-- A finite-dimensional `K`-subspace `V` contains a maximal residually independent family of
elements of value `1`: every element of `V` of value `≤ 1` is congruent, modulo elements of value
`< 1`, to an integral combination of the family. -/
theorem exists_residuallyIndependent_approx (V : Submodule K F) [FiniteDimensional K V] :
    ∃ k, ∃ m : Fin k → F, (∀ j, m j ∈ V) ∧ (∀ j, v (m j) = 1) ∧ v.ResiduallyIndependent K m ∧
      ∀ y ∈ V, v y ≤ 1 → ∃ a : Fin k → K, (∀ j, v (algebraMap K F (a j)) ≤ 1) ∧
        v (y - ∑ j, a j • m j) < 1 := by
  classical
  let Good : ℕ → Prop := fun k => ∃ m : Fin k → F, (∀ j, m j ∈ V) ∧ (∀ j, v (m j) = 1) ∧
    v.ResiduallyIndependent K m
  have hbound {k : ℕ} (hk : Good k) : k ≤ finrank K V := by
    obtain ⟨m, hmV, hm1, hm⟩ := hk
    have hli : LinearIndependent K (V.subtype ∘ fun j => (⟨m j, hmV j⟩ : V)) :=
      hm.linearIndependent hm1
    simpa using (LinearIndependent.of_comp _ hli).fintype_card_le_finrank
  have h0 : Good 0 := ⟨Fin.elim0, fun j => j.elim0, fun j => j.elim0, fun _ _ _ j => j.elim0⟩
  obtain ⟨m, hmV, hm1, hm⟩ := Nat.findGreatest_spec (Nat.zero_le (finrank K V)) h0
  refine ⟨_, m, hmV, hm1, hm, fun y hyV hy => ?_⟩
  by_contra hcon
  push Not at hcon
  have hy1 : v y = 1 := le_antisymm hy (by simpa using hcon 0 (by simp))
  have hgood : Good (Nat.findGreatest Good (finrank K V) + 1) := by
    refine ⟨Fin.snoc m y, fun j => ?_, fun j => ?_, hm.snoc hy1 fun a ha => not_lt.2 (hcon a ha)⟩
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa using hyV
      · simpa using hmV j
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa using hy1
      · simpa using hm1 j
  exact Nat.findGreatest_is_greatest (Nat.lt_succ_self _) (hbound hgood) hgood

end Valuation

namespace ValuationSubring

open IsLocalRing

variable {R K F : Type*} [CommRing R] [Field K] [Algebra R K] [Field F] [Algebra K F]
  [Algebra R F] [IsScalarTower R K F] {𝒪 : ValuationSubring F}

/-- Over a complete discrete valuation ring, a family `m` in `V` of value `1` such that every
element of `V` of value `≤ 1` is congruent to an integral combination of `m` modulo elements of
value `< 1` spans `V`. -/
theorem exists_eq_sum_smul [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (maximalIdeal R) R] [IsFractionRing R K]
    (hO : ∀ x : K, algebraMap K F x ∈ 𝒪 ↔ x ∈ (algebraMap R K).range)
    (hval : ∀ y : F, y ≠ 0 → ∃ c : K, 𝒪.valuation y = 𝒪.valuation (algebraMap K F c))
    {V : Submodule K F} {k : ℕ} {m : Fin k → F} (hmV : ∀ j, m j ∈ V)
    (hm1 : ∀ j, 𝒪.valuation (m j) = 1)
    (happrox : ∀ y ∈ V, 𝒪.valuation y ≤ 1 → ∃ a : Fin k → K,
      (∀ j, 𝒪.valuation (algebraMap K F (a j)) ≤ 1) ∧ 𝒪.valuation (y - ∑ j, a j • m j) < 1)
    {y : F} (hy : y ∈ V) : ∃ c : Fin k → K, y = ∑ j, c j • m j := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hR : IsPrecomplete (Ideal.span {ϖ}) R := hϖ.maximalIdeal_eq ▸ inferInstance
  have hϖK : algebraMap R K ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hϖ.ne_zero
  have hϖ0 : 0 < 𝒪.valuation (algebraMap R F ϖ) := by
    rw [zero_lt_iff, Valuation.ne_zero_iff, IsScalarTower.algebraMap_apply R K F]
    exact (map_ne_zero _).2 hϖK
  obtain ⟨M, hM⟩ : ∃ M : Submodule R F, ∀ y, y ∈ M ↔ y ∈ V ∧ 𝒪.valuation y ≤ 1 :=
    ⟨{ carrier := {y | y ∈ V ∧ 𝒪.valuation y ≤ 1}
       add_mem' := fun ha hb =>
        ⟨V.add_mem ha.1 hb.1, (Valuation.map_add _ _ _).trans (max_le ha.2 hb.2)⟩
       zero_mem' := ⟨V.zero_mem, by simp⟩
       smul_mem' := fun r y hy => ⟨V.smul_of_tower_mem r hy.1, by
         rw [Algebra.smul_def, map_mul]
         exact mul_le_one' (valuation_algebraMap_le_one hO r) hy.2⟩ }, fun y => Iff.rfl⟩
  have hstep (y : F) (hy : y ∈ M) : ∃ a : Fin k → R, ∃ y' ∈ M, y = ∑ j, a j • m j + ϖ • y' := by
    rw [hM] at hy
    obtain ⟨a, ha, hlt⟩ := happrox y hy.1 hy.2
    choose r hr using fun j => (hO (a j)).1 ((valuation_le_one_iff _ _).1 (ha j))
    have hsum : ∑ j, a j • m j = ∑ j, r j • m j := by simp [← hr, algebraMap_smul]
    refine ⟨r, (algebraMap R K ϖ)⁻¹ • (y - ∑ j, r j • m j), (hM _).2 ⟨?_, ?_⟩, ?_⟩
    · exact V.smul_mem _ (V.sub_mem hy.1 (V.sum_mem fun j _ => V.smul_of_tower_mem _ (hmV j)))
    · rw [Algebra.smul_def, map_mul, map_inv₀, map_inv₀, ← IsScalarTower.algebraMap_apply]
      exact (inv_mul_le_one₀ hϖ0).2 (valuation_le_of_lt_one hO hval hϖ (hsum ▸ hlt))
    · rw [← algebraMap_smul K ϖ, smul_smul, mul_inv_cancel₀ hϖK, one_smul, add_sub_cancel]
  have hM' (y : F) (hy : y ∈ M) : ∃ c : Fin k → K, y = ∑ j, c j • m j := by
    obtain ⟨b, hb⟩ := Submodule.exists_sum_smul_add_pow_smul hR M
      (fun j => (hM _).2 ⟨hmV j, (hm1 j).le⟩) hstep hy
    refine ⟨fun j => algebraMap R K (b j), ?_⟩
    simp only [algebraMap_smul]
    rw [← sub_eq_zero]
    by_contra hne
    obtain ⟨N, hN⟩ := exists_pow_lt_valuation hO hval hϖ hne
    obtain ⟨z, hz, hyz⟩ := hb N
    refine hN.not_ge ?_
    rw [hyz, add_sub_cancel_left, Algebra.smul_def, map_mul, map_pow, map_pow]
    exact mul_le_of_le_one_right' ((hM z).1 hz).2
  rcases eq_or_ne y 0 with rfl | hy0
  · exact ⟨0, by simp⟩
  obtain ⟨c, hc⟩ := hval y hy0
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp only [map_zero, Valuation.zero_iff] at hc
    exact hy0 hc
  obtain ⟨d, hd⟩ := hM' (c⁻¹ • y) ((hM _).2 ⟨V.smul_mem _ hy, by
    rw [Algebra.smul_def, map_mul, map_inv₀, map_inv₀, ← hc,
      inv_mul_cancel₀ (𝒪.valuation.ne_zero_iff.2 hy0)]⟩)
  refine ⟨fun j => c * d j, ?_⟩
  rw [← smul_inv_smul₀ hc0 y, hd, Finset.smul_sum]
  simp [smul_smul]

/-- **Cartesian lemma.** Let `R` be a complete discrete valuation ring with fraction field `K`,
and let `𝒪` be a valuation ring of an extension `F` of `K` with `𝒪 ∩ K = R`, such that every
value of `F` is a value of `K`. Then every finite-dimensional `K`-subspace `V` of `F` has a
residually independent basis of elements of value `1`. -/
theorem exists_basis_residuallyIndependent [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (maximalIdeal R) R] [IsFractionRing R K]
    (hO : ∀ x : K, algebraMap K F x ∈ 𝒪 ↔ x ∈ (algebraMap R K).range)
    (hval : ∀ y : F, y ≠ 0 → ∃ c : K, 𝒪.valuation y = 𝒪.valuation (algebraMap K F c))
    (V : Submodule K F) [FiniteDimensional K V] :
    ∃ e : Basis (Fin (finrank K V)) K V, (∀ j, 𝒪.valuation (e j : F) = 1) ∧
      𝒪.valuation.ResiduallyIndependent K fun j => (e j : F) := by
  obtain ⟨k, m, hmV, hm1, hm, happrox⟩ := 𝒪.valuation.exists_residuallyIndependent_approx V
  have hli' : LinearIndependent K (V.subtype ∘ fun j => (⟨m j, hmV j⟩ : V)) :=
    hm.linearIndependent hm1
  have hsp : ⊤ ≤ Submodule.span K (Set.range fun j => (⟨m j, hmV j⟩ : V)) := by
    rintro ⟨y, hy⟩ -
    obtain ⟨c, hc⟩ := exists_eq_sum_smul hO hval hmV hm1 happrox hy
    have hyc : (⟨y, hy⟩ : V) = ∑ j, c j • ⟨m j, hmV j⟩ := Subtype.ext (by simpa using hc)
    rw [hyc]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  let e := Basis.mk (LinearIndependent.of_comp _ hli') hsp
  obtain rfl : k = finrank K V := by simpa using (finrank_eq_card_basis e).symm
  have he : (fun j => (e j : F)) = m := funext fun j => by simp [e]
  exact ⟨e, fun j => by simp [e, hm1], he ▸ hm⟩

/-- The basis of `exists_basis_residuallyIndependent` computes valuations: the value of a
combination is the maximum of the values of the coefficients. -/
theorem exists_basis_valuation_sum_smul_eq_sup [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (maximalIdeal R) R] [IsFractionRing R K]
    (hO : ∀ x : K, algebraMap K F x ∈ 𝒪 ↔ x ∈ (algebraMap R K).range)
    (hval : ∀ y : F, y ≠ 0 → ∃ c : K, 𝒪.valuation y = 𝒪.valuation (algebraMap K F c))
    (V : Submodule K F) [FiniteDimensional K V] :
    ∃ e : Basis (Fin (finrank K V)) K V, (∀ j, 𝒪.valuation (e j : F) = 1) ∧
      ∀ c : Fin (finrank K V) → K, 𝒪.valuation (∑ j, c j • (e j : F)) =
        Finset.univ.sup fun j => 𝒪.valuation (algebraMap K F (c j)) := by
  obtain ⟨e, he1, he⟩ := exists_basis_residuallyIndependent hO hval V
  exact ⟨e, he1, he.map_sum_smul he1⟩

end ValuationSubring
