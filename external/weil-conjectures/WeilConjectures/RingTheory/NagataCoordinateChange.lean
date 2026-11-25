/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Sihan Su, Wan Lin, Xiaoyang Su, Claude
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.RingHom.Finite
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Data.List.Indexes

/-!
# Nagata's change of coordinates

`Mathlib.RingTheory.NoetherNormalization` proves, privately, that for a nonzero polynomial
`f ∈ k[X₀, …, Xₙ]` over a field `k` there is a `k`-algebra automorphism `σ` of `k[X₀, …, Xₙ]`
(Nagata's `Xᵢ ↦ Xᵢ + X₀ ^ rᵢ`) such that `σ f`, viewed as a polynomial in `X₀` over
`k[X₁, …, Xₙ]`, has invertible leading coefficient. This file makes this public
(`NoetherNormalization.exists_algEquiv_isUnit_leadingCoeff`, the proof is copied from Mathlib),
and records

* a variant fixing an extra last variable
  (`NoetherNormalization.exists_algEquiv_isUnit_leadingCoeff_rename_castSucc`);
* that `R[X₀, …, Xₙ] ⧸ (p)` is finite over `R[X₁, …, Xₙ]` when `p` has invertible leading
  coefficient in `X₀` (`MvPolynomial.finite_quotient_comp_rename_succ`);
* that a closed subset of `V(Xₙ) ⊆ Spec R[X₀, …, Xₙ]` other than `V(Xₙ)` lies in the zero locus of
  a nonzero polynomial in `X₀, …, X_{n-1}`
  (`MvPolynomial.exists_rename_castSucc_mem_vanishingIdeal`).
-/

@[expose] public section

open Polynomial MvPolynomial

namespace NoetherNormalization

section equivT

variable {k : Type*} [Field k] {n : ℕ} (f : MvPolynomial (Fin (n + 1)) k)
variable (v w : Fin (n + 1) →₀ ℕ)

/-- `up` is defined as `2 + f.totalDegree`. Any big enough number would work. -/
local notation3 "up" => 2 + f.totalDegree

variable {f v} in
private lemma lt_up' (vlt : ∀ i, v i < up) : ∀ l ∈ List.ofFn v, l < up := by
  grind

/-- `r` maps `(i : Fin (n + 1))` to `up ^ i`. -/
local notation3 "r" => fun (i : Fin (n + 1)) ↦ up ^ i.1

private lemma t1_comp_t1_neg' (c : k) : (T1 f c).comp (T1 f (-c)) = AlgHom.id _ _ := by
  rw [comp_aeval, ← MvPolynomial.aeval_X_left]
  ext i v
  cases i using Fin.cases <;> simp

/-- `T1 f 1` leads to an algebra equiv `T' f`. -/
private noncomputable abbrev T' := AlgEquiv.ofAlgHom (T1 f 1) (T1 f (-1))
  (t1_comp_t1_neg' f 1) (by simpa using t1_comp_t1_neg' f (-1))

private lemma sum_r_mul_ne' (vlt : ∀ i, v i < up) (wlt : ∀ i, w i < up) (ne : v ≠ w) :
    ∑ x : Fin (n + 1), r x * v x ≠ ∑ x : Fin (n + 1), r x * w x := by
  intro h
  refine ne <| Finsupp.ext <| congrFun <| List.ofFn_inj.mp ?_
  apply Nat.ofDigits_inj_of_len_eq (Nat.lt_add_right f.totalDegree one_lt_two)
    (by simp) (lt_up' vlt) (lt_up' wlt)
  simpa only [Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_eq_ofFn, List.get_ofFn, List.length_ofFn,
    Fin.val_cast, mul_comm, List.sum_ofFn] using! h

private lemma degreeOf_zero_t' {a : k} (ha : a ≠ 0) : ((T' f) (monomial v a)).degreeOf 0 =
    ∑ i : Fin (n + 1), (r i) * v i := by
  rw [← natDegree_finSuccEquiv, monomial_eq, Finsupp.prod_pow v fun a ↦ X a]
  simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, map_mul, map_prod, map_pow,
    AlgEquiv.ofAlgHom_apply, MvPolynomial.aeval_C, MvPolynomial.aeval_X, ite_eq_left,
    Fin.succ_ne_zero,
    ite_false, one_smul, map_add, finSuccEquiv_X_zero, finSuccEquiv_X_succ, algebraMap_eq]
  have h (i : Fin n) :
      (Polynomial.C (X (R := k) i) + Polynomial.X ^ r i.succ) ^ v i.succ ≠ 0 :=
    pow_ne_zero (v i.succ) (leadingCoeff_ne_zero.mp <| by simp [add_comm, leadingCoeff_X_pow_add_C])
  rw [natDegree_mul (by simp [ha]) (mul_ne_zero (by simp) (Finset.prod_ne_zero_iff.mpr
    (fun i _ ↦ h i))), natDegree_mul (by simp) (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ h i)),
    natDegree_prod _ _ (fun i _ ↦ h i), natDegree_finSuccEquiv, degreeOf_C]
  simpa only [natDegree_pow, zero_add, natDegree_X, mul_one, Fin.val_zero, pow_zero, one_mul,
    add_right_inj] using Finset.sum_congr rfl (fun i _ ↦ by
    rw [add_comm (Polynomial.C _), natDegree_X_pow_add_C, mul_comm])

/-- `T'` maps different monomials of `f` to polynomials with different degrees in `X_0`. -/
private lemma degreeOf_t_ne_of_ne' (hv : v ∈ f.support) (hw : w ∈ f.support) (ne : v ≠ w) :
    (T' f <| monomial v <| f.coeff v).degreeOf 0 ≠
    (T' f <| monomial w <| f.coeff w).degreeOf 0 := by
  rw [degreeOf_zero_t' _ _ <| mem_support_iff.mp hv, degreeOf_zero_t' _ _ <| mem_support_iff.mp hw]
  refine sum_r_mul_ne' f v w (fun i ↦ ?_) (fun i ↦ ?_) ne <;>
  exact lt_of_le_of_lt ((monomial_le_degreeOf i ‹_›).trans (degreeOf_le_totalDegree f i))
    (by lia)

private lemma leadingCoeff_finSuccEquiv_t' :
    (finSuccEquiv k n ((T' f) ((monomial v) (f.coeff v)))).leadingCoeff =
    algebraMap k _ (f.coeff v) := by
  rw [monomial_eq, Finsupp.prod_fintype]
  · simp only [map_mul, map_prod, leadingCoeff_mul, leadingCoeff_prod]
    rw [AlgEquiv.ofAlgHom_apply, algHom_C, algebraMap_eq, finSuccEquiv_apply,
      eval₂Hom_C, RingHom.coe_comp]
    simp only [AlgEquiv.ofAlgHom_apply, Function.comp_apply, leadingCoeff_C, map_pow,
      leadingCoeff_pow, algebraMap_eq]
    have : ∀ j, ((finSuccEquiv k n) ((T1 f) 1 (X j))).leadingCoeff = 1 := fun j ↦ by
      by_cases h : j = 0
      · simp [h, finSuccEquiv_apply]
      · simp only [aeval_eq_bind₁, bind₁_X_right, ite_eq_right h, one_smul, map_add, map_pow]
        obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.mpr h
        simp [finSuccEquiv_X_succ, finSuccEquiv_X_zero, add_comm]
    simp only [this, one_pow, Finset.prod_const_one, mul_one]
  exact fun i ↦ pow_zero _

/-- `T'` maps `f` to a polynomial in `X_0` whose leading coefficient is invertible. -/
private lemma T'_leadingcoeff_isUnit (fne : f ≠ 0) :
    IsUnit (finSuccEquiv k n (T' f f)).leadingCoeff := by
  obtain ⟨v, vin, vs⟩ := Finset.exists_max_image f.support
    (fun v ↦ (T' f ((monomial v) (f.coeff v))).degreeOf 0) (support_nonempty.mpr fne)
  set h := fun w ↦ (MvPolynomial.monomial w) (f.coeff w)
  simp only [← natDegree_finSuccEquiv] at vs
  replace vs : ∀ x ∈ f.support \ {v}, (finSuccEquiv k n ((T' f) (h x))).degree <
      (finSuccEquiv k n ((T' f) (h v))).degree := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hx
    apply degree_lt_degree <| lt_of_le_of_ne (vs x h1) ?_
    simpa only [natDegree_finSuccEquiv]
      using degreeOf_t_ne_of_ne' f _ _ h1 vin <| List.ne_of_not_mem_cons h2
  have coeff : (finSuccEquiv k n ((T' f) (h v + ∑ x ∈ f.support \ {v}, h x))).leadingCoeff =
      (finSuccEquiv k n ((T' f) (h v))).leadingCoeff := by
    simp only [map_add, map_sum]
    rw [add_comm]
    apply leadingCoeff_add_of_degree_lt <| (lt_of_le_of_lt <| degree_sum_le _ _) ?_
    have h2 : h v ≠ 0 := by simpa [h] using mem_support_iff.mp vin
    replace h2 : (finSuccEquiv k n ((T' f) (h v))) ≠ 0 := fun eq ↦ h2 <|
      by simpa only [map_eq_zero_iff _ (AlgEquiv.injective _)] using eq
    exact (Finset.sup_lt_iff <| Ne.bot_lt (fun x ↦ h2 <| degree_eq_bot.mp x)).mpr vs
  nth_rw 2 [← f.support_sum_monomial_coeff]
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem vin h]
  rw [leadingCoeff_finSuccEquiv_t'] at coeff
  simpa only [coeff, algebraMap_eq] using (mem_support_iff.mp vin).isUnit.map MvPolynomial.C

/-- **Nagata's change of coordinates**: for a nonzero polynomial `f ∈ k[X₀, …, Xₙ]` over a
field `k`, there is a `k`-algebra automorphism `σ` of `k[X₀, …, Xₙ]` such that `σ f`, viewed as
a polynomial in `X₀` over `k[X₁, …, Xₙ]`, has invertible leading coefficient. -/
theorem exists_algEquiv_isUnit_leadingCoeff (hf : f ≠ 0) :
    ∃ σ : MvPolynomial (Fin (n + 1)) k ≃ₐ[k] MvPolynomial (Fin (n + 1)) k,
      IsUnit (finSuccEquiv k n (σ f)).leadingCoeff :=
  ⟨T' f, T'_leadingcoeff_isUnit f hf⟩

end equivT

end NoetherNormalization

namespace MvPolynomial

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Viewing a polynomial in `X₀, …, Xₙ` as one in `X₀, …, X_{n+1}` commutes with splitting off
the variable `X₀`. -/
lemma finSuccEquiv_rename_castSucc (p : MvPolynomial (Fin (n + 1)) R) :
    finSuccEquiv R (n + 1) (rename Fin.castSucc p) =
      (finSuccEquiv R n p).map (rename Fin.castSucc :
        MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin (n + 1)) R) := by
  have h : (finSuccEquiv R (n + 1)).toAlgHom.comp (rename Fin.castSucc) =
      (Polynomial.mapAlgHom (rename Fin.castSucc)).comp (finSuccEquiv R n).toAlgHom := by
    refine algHom_ext fun i ↦ ?_
    cases i using Fin.cases with
    | zero => simp [finSuccEquiv_X_zero]
    | succ i =>
      rw [AlgHom.comp_apply, rename_X, ← Fin.succ_castSucc]
      simp [finSuccEquiv_X_succ]
  exact DFunLike.congr_fun h p

/-- The extension of an endomorphism `σ` of `R[X₀, …, X_{n-1}]` to `R[X₀, …, Xₙ]` fixing `Xₙ`
commutes with the inclusion `R[X₀, …, X_{n-1}] ⟶ R[X₀, …, Xₙ]`. -/
lemma aeval_lastCases_comp_rename_castSucc
    (σ : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R) :
    (aeval (Fin.lastCases (X (Fin.last n)) fun i ↦ rename Fin.castSucc (σ (X i)))).comp
      (rename Fin.castSucc) = (rename Fin.castSucc).comp σ :=
  algHom_ext fun i ↦ by simp

/-- Extending endomorphisms of `R[X₀, …, X_{n-1}]` to `R[X₀, …, Xₙ]` by fixing `Xₙ` is compatible
with composition. -/
lemma aeval_lastCases_comp_aeval_lastCases
    (σ τ : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R) :
    (aeval (Fin.lastCases (X (Fin.last n)) fun i ↦ rename Fin.castSucc (σ (X i)))).comp
      (aeval (Fin.lastCases (X (Fin.last n)) fun i ↦ rename Fin.castSucc (τ (X i)))) =
      aeval (Fin.lastCases (X (Fin.last n)) fun i ↦ rename Fin.castSucc (σ (τ (X i)))) := by
  refine algHom_ext fun i ↦ ?_
  cases i using Fin.lastCases with
  | last => simp
  | cast i =>
    rw [AlgHom.comp_apply, aeval_X, aeval_X, Fin.lastCases_castSucc, Fin.lastCases_castSucc,
      ← AlgHom.comp_apply, aeval_lastCases_comp_rename_castSucc, AlgHom.comp_apply]

/-- If `p ∈ R[X₀, …, Xₙ]` has invertible leading coefficient as a polynomial in `X₀` over
`R[X₁, …, Xₙ]`, then `R[X₀, …, Xₙ] ⧸ (p)` is finite over `R[X₁, …, Xₙ]`. -/
theorem finite_quotient_comp_rename_succ (p : MvPolynomial (Fin (n + 1)) R)
    (hp : IsUnit (finSuccEquiv R n p).leadingCoeff) :
    ((Ideal.Quotient.mk (Ideal.span {p})).comp (rename Fin.succ).toRingHom).Finite := by
  have hq := monic_of_isUnit_leadingCoeff_inv_smul hp
  have hle : Ideal.span {hp.unit⁻¹ • finSuccEquiv R n p} ≤
      (Ideal.span {p}).comap (finSuccEquiv R n).symm.toRingEquiv.toRingHom := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, Units.smul_def, Polynomial.smul_eq_C_mul,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, map_mul]
    exact Ideal.mul_mem_left _ _ (by simp)
  have heq : (Ideal.quotientMap _ _ hle).comp
      ((Ideal.Quotient.mk _).comp Polynomial.C) =
      (Ideal.Quotient.mk (Ideal.span {p})).comp (rename Fin.succ).toRingHom := by
    refine ringHom_ext (fun r ↦ ?_) (fun i ↦ ?_)
    · simp only [RingHom.coe_comp, Function.comp_apply, Ideal.quotientMap_mk,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_C, RingEquiv.toRingHom_eq_coe,
        AlgEquiv.coe_toRingEquiv]
      congr 1
      rw [AlgEquiv.symm_apply_eq]
      simp [finSuccEquiv_apply]
    · simp only [RingHom.coe_comp, Function.comp_apply, Ideal.quotientMap_mk]
      rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, AlgEquiv.coe_toRingEquiv, ← finSuccEquiv_X_succ,
        AlgEquiv.symm_apply_apply]
  rw [← heq]
  refine RingHom.Finite.comp (RingHom.Finite.of_surjective _
    (Ideal.quotientMap_surjective (finSuccEquiv R n).symm.surjective)) ?_
  have := hq.finite_quotient
  exact RingHom.finite_algebraMap.mpr this

end MvPolynomial

namespace MvPolynomial

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Extending the identity of `R[X₀, …, X_{n-1}]` to `R[X₀, …, Xₙ]` by fixing `Xₙ` gives the
identity. -/
lemma aeval_lastCases_rename_castSucc_X :
    aeval (Fin.lastCases (X (Fin.last n)) fun i ↦ rename Fin.castSucc (X i)) =
      AlgHom.id R (MvPolynomial (Fin (n + 1)) R) :=
  algHom_ext fun i ↦ by cases i using Fin.lastCases <;> simp

/-- The automorphism of `R[X₀, …, Xₙ]` extending an automorphism `σ` of `R[X₀, …, X_{n-1}]`
and fixing `Xₙ`. -/
noncomputable def algEquivFixLast (σ : MvPolynomial (Fin n) R ≃ₐ[R] MvPolynomial (Fin n) R) :
    MvPolynomial (Fin (n + 1)) R ≃ₐ[R] MvPolynomial (Fin (n + 1)) R :=
  AlgEquiv.ofAlgHom
    (aeval (Fin.lastCases (X (Fin.last n)) fun i ↦ rename Fin.castSucc
      ((σ : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R) (X i))))
    (aeval (Fin.lastCases (X (Fin.last n)) fun i ↦ rename Fin.castSucc
      ((σ.symm : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R) (X i))))
    (by
      rw [aeval_lastCases_comp_aeval_lastCases]
      simp only [AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
      exact aeval_lastCases_rename_castSucc_X)
    (by
      rw [aeval_lastCases_comp_aeval_lastCases]
      simp only [AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply]
      exact aeval_lastCases_rename_castSucc_X)

@[simp]
lemma algEquivFixLast_X_last (σ : MvPolynomial (Fin n) R ≃ₐ[R] MvPolynomial (Fin n) R) :
    algEquivFixLast σ (X (Fin.last n)) = X (Fin.last n) := by
  simp [algEquivFixLast]

@[simp]
lemma algEquivFixLast_rename_castSucc (σ : MvPolynomial (Fin n) R ≃ₐ[R] MvPolynomial (Fin n) R)
    (p : MvPolynomial (Fin n) R) :
    algEquivFixLast σ (rename Fin.castSucc p) = rename Fin.castSucc (σ p) := by
  rw [algEquivFixLast, AlgEquiv.ofAlgHom_apply, ← AlgHom.comp_apply,
    aeval_lastCases_comp_rename_castSucc, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]

end MvPolynomial

open MvPolynomial in
/-- **Nagata's change of coordinates fixing the last variable**: for a nonzero
`f ∈ k[X₀, …, Xₙ]`, there is a `k`-algebra automorphism `σ` of `k[X₀, …, X_{n+1}]` fixing
`X_{n+1}` such that `σ f`, viewed as a polynomial in `X₀` over `k[X₁, …, X_{n+1}]`, has invertible
leading coefficient. -/
theorem NoetherNormalization.exists_algEquiv_isUnit_leadingCoeff_rename_castSucc
    {k : Type*} [Field k] {n : ℕ} (f : MvPolynomial (Fin (n + 1)) k) (hf : f ≠ 0) :
    ∃ σ : MvPolynomial (Fin (n + 2)) k ≃ₐ[k] MvPolynomial (Fin (n + 2)) k,
      σ (X (Fin.last (n + 1))) = X (Fin.last (n + 1)) ∧
      IsUnit (finSuccEquiv k (n + 1) (σ (rename Fin.castSucc f))).leadingCoeff := by
  obtain ⟨τ, hτ⟩ := exists_algEquiv_isUnit_leadingCoeff f hf
  refine ⟨algEquivFixLast τ, algEquivFixLast_X_last τ, ?_⟩
  rw [algEquivFixLast_rename_castSucc, finSuccEquiv_rename_castSucc]
  convert hτ.map (rename Fin.castSucc :
    MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin (n + 1)) k) using 1
  exact Polynomial.leadingCoeff_map_of_injective
    (rename_injective _ (Fin.castSucc_injective _)) _

open MvPolynomial PrimeSpectrum in
/-- A closed subset `Y` of `V(Xₙ) ⊆ Spec R[X₀, …, Xₙ]` with `V(Xₙ) ⊄ Y` lies in the zero locus of a
nonzero polynomial in `X₀, …, X_{n-1}` only. -/
theorem MvPolynomial.exists_rename_castSucc_mem_vanishingIdeal {R : Type*} [CommRing R] {n : ℕ}
    {Y : Set (PrimeSpectrum (MvPolynomial (Fin (n + 1)) R))} (hY : IsClosed Y)
    (hYH : Y ⊆ zeroLocus {X (Fin.last n)}) (hne : ¬ zeroLocus {X (Fin.last n)} ⊆ Y) :
    ∃ g : MvPolynomial (Fin n) R, g ≠ 0 ∧ rename Fin.castSucc g ∈ vanishingIdeal Y := by
  have ht : X (Fin.last n) ∈ vanishingIdeal Y :=
    (subset_zeroLocus_iff_subset_vanishingIdeal (t := Y) (s := _)).mp hYH (Set.mem_singleton _)
  have hspan : Ideal.span {X (Fin.last n)} ≤ vanishingIdeal Y :=
    (Ideal.span_singleton_le_iff_mem _).mpr ht
  obtain ⟨h, hh, hht⟩ : ∃ h ∈ vanishingIdeal Y, h ∉ Ideal.span {X (Fin.last n)} := by
    by_contra! H
    refine hne ?_
    rw [← zeroLocus_span, ← hY.closure_eq, ← zeroLocus_vanishingIdeal_eq_closure]
    exact zeroLocus_anti_mono_ideal H
  let π : MvPolynomial (Fin (n + 1)) R →ₐ[R] MvPolynomial (Fin n) R :=
    aeval (Fin.lastCases 0 X)
  have hπ : (Ideal.Quotient.mkₐ R (Ideal.span {X (Fin.last n)})).comp
      ((rename Fin.castSucc).comp π) = Ideal.Quotient.mkₐ R _ := by
    refine algHom_ext fun i ↦ ?_
    cases i using Fin.lastCases with
    | last =>
      simp [π, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)]
    | cast i => simp [π]
  have hmem : h - rename Fin.castSucc (π h) ∈ Ideal.span {X (Fin.last n)} := by
    rw [← Ideal.Quotient.eq, ← Ideal.Quotient.mkₐ_eq_mk R,
      ← DFunLike.congr_fun hπ h, AlgHom.comp_apply, AlgHom.comp_apply]
  refine ⟨π h, fun h0 ↦ hht ?_, ?_⟩
  · simpa [h0] using hmem
  · simpa using sub_mem hh (hspan hmem)

