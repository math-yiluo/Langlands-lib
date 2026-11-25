/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Polynomial.Identities

/-!

# Newton's lemma over power series rings

Two elementary inputs to the comparison of the Laurent series fields `k'((t)) ⊆ K((t))` of the
generic slices (SGA 4½, [Th. finitude], Lemme 3.3):

* **Hensel's lemma without monicity** (`IsAdicComplete.exists_isRoot_sub_mem`): over an
  `I`-adically complete ring, a polynomial `f` with `f(a₀) ∈ I` and `f'(a₀)` a unit modulo `I` has
  a root `a ≡ a₀ (mod I)`. Mathlib's `HenselianRing` only states this for monic `f`, although the
  Newton iteration proving `IsAdicComplete.henselianRing` does not use monicity.
* **Newton's lemma** (`Polynomial.exists_isRoot_powerSeries_of_sq_mul_X_dvd`): over `k⟦t⟧`, `k` a
  field, if `f'(β)² t ∣ f(β)` then `f` has a root `γ` with `f'(β) t ∣ γ - β`; and the root is
  unique in the sense of `Polynomial.eq_or_sub_dvd_derivative_eval_of_isRoot`: two roots
  `a ≠ b` of `f` in a domain satisfy `a - b ∣ f'(a)`.

-/

@[expose] public section

open Polynomial
open scoped Ring

/-- **Hensel's lemma without monicity**: over an `I`-adically complete ring, a polynomial `f` with
`f(a₀) ∈ I` and `f'(a₀)` a unit modulo `I` has a root `a` with `a - a₀ ∈ I`. This is the Newton
iteration of `IsAdicComplete.henselianRing`, which does not use that `f` is monic. -/
theorem IsAdicComplete.exists_isRoot_sub_mem {R : Type*} [CommRing R] (I : Ideal R)
    [IsAdicComplete I R] (f : R[X]) (a₀ : R) (h₁ : f.eval a₀ ∈ I)
    (h₂ : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀))) :
    ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ I := by
  classical
  let f' := derivative f
  let c : ℕ → R := fun n => Nat.recOn n a₀ fun _ b => b - f.eval b * (f'.eval b)⁻¹ʳ
  have hc : ∀ n, c (n + 1) = c n - f.eval (c n) * (f'.eval (c n))⁻¹ʳ := by
    intro n
    simp only [c]
  have hc_mod : ∀ n, c n ≡ a₀ [SMOD I] := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => ?_
    rw [hc, sub_eq_add_neg, ← add_zero a₀]
    refine ih.add ?_
    rw [SModEq.zero, Ideal.neg_mem_iff]
    refine I.mul_mem_right _ ?_
    rw [← SModEq.zero] at h₁ ⊢
    exact (ih.eval f).trans h₁
  have hf'c : ∀ n, IsUnit (f'.eval (c n)) := by
    intro n
    have := isLocalHom_of_le_jacobson_bot I (IsAdicComplete.le_jacobson_bot I)
    apply IsUnit.of_map (Ideal.Quotient.mk I)
    convert! h₂ using 1
    exact SModEq.def.mp ((hc_mod n).eval _)
  have hfcI : ∀ n, f.eval (c n) ∈ I ^ (n + 1) := by
    intro n
    induction n with
    | zero => simpa only [Nat.rec_zero, zero_add, pow_one] using! h₁
    | succ n ih => ?_
    rw [← taylor_eval_sub (c n), hc, sub_eq_add_neg, sub_eq_add_neg,
      add_neg_cancel_comm]
    rw [eval_eq_sum, sum_over_range' _ _ _ (lt_add_of_pos_right _ zero_lt_two), ←
      Finset.sum_range_add_sum_Ico _ (Nat.le_add_left _ _)]
    swap
    · intro i
      rw [zero_mul]
    refine Ideal.add_mem _ ?_ ?_
    · rw [← one_add_one_eq_two, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
        taylor_coeff_zero, taylor_coeff_one, pow_zero, pow_one, mul_one, mul_neg,
        mul_left_comm, Ring.mul_inverse_cancel _ (hf'c n), mul_one, add_neg_cancel]
      exact Ideal.zero_mem _
    · refine Submodule.sum_mem _ ?_
      simp only [Finset.mem_Ico]
      rintro i ⟨h2i, _⟩
      have aux : n + 2 ≤ i * (n + 1) := by trans 2 * (n + 1) <;> nlinarith only [h2i]
      refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right aux ?_)
      rw [pow_mul']
      exact Ideal.pow_mem_pow ((Ideal.neg_mem_iff _).2 <| Ideal.mul_mem_right _ _ ih) _
  have aux : ∀ m n, m ≤ n → c m ≡ c n [SMOD (I ^ m • ⊤ : Ideal R)] := by
    intro m n hmn
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    clear hmn
    induction k with
    | zero => rw [add_zero]
    | succ k ih => ?_
    rw [← add_assoc, hc, ← add_zero (c m), sub_eq_add_neg]
    refine ih.add ?_
    symm
    rw [SModEq.zero, Ideal.neg_mem_iff]
    refine Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right ?_ (hfcI _))
    rw [add_assoc]
    exact le_self_add
  obtain ⟨a, ha⟩ := IsPrecomplete.prec' c (aux _ _)
  refine ⟨a, ?_, ?_⟩
  · show f.IsRoot a
    suffices ∀ n, f.eval a ≡ 0 [SMOD (I ^ n • ⊤ : Ideal R)] by exact IsHausdorff.haus' _ this
    intro n
    specialize ha n
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] at ha ⊢
    refine (ha.symm.eval f).trans ?_
    rw [SModEq.zero]
    exact Ideal.pow_le_pow_right le_self_add (hfcI _)
  · show a - a₀ ∈ I
    specialize ha (0 + 1)
    rw [hc, pow_one, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, sub_eq_add_neg] at ha
    rw [← SModEq.sub_mem, ← add_zero a₀]
    refine ha.symm.trans (SModEq.rfl.add ?_)
    rw [SModEq.zero, Ideal.neg_mem_iff]
    exact Ideal.mul_mem_right _ _ h₁

/-- **Two roots of a polynomial over a domain are equal or close**: if `a` and `b` are roots of
`f`, then `a = b` or `a - b` divides `f'(a)`. -/
theorem Polynomial.eq_or_sub_dvd_derivative_eval_of_isRoot {R : Type*} [CommRing R] [IsDomain R]
    {f : R[X]} {a b : R} (ha : f.IsRoot a) (hb : f.IsRoot b) :
    a = b ∨ a - b ∣ f.derivative.eval a := by
  by_cases hab : a = b
  · exact Or.inl hab
  refine Or.inr ?_
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion f a (b - a)
  have hk' : (f.derivative.eval a + k * (b - a)) * (b - a) = 0 := by
    rw [add_sub_cancel] at hk
    rw [IsRoot.def] at ha hb
    linear_combination hb - ha - hk
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have h0 := (mul_eq_zero.mp hk').resolve_right hba
  refine ⟨k, ?_⟩
  linear_combination h0


/-- The coefficients of `p(c Y)` are `cʲ pⱼ`. -/
lemma Polynomial.coeff_comp_C_mul_X {R : Type*} [CommRing R] (p : R[X]) (a : R) (j : ℕ) :
    (p.comp (C a * X)).coeff j = a ^ j * p.coeff j := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [add_comp, hp, hq, mul_add]
  | monomial i b =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_pow_comp, mul_pow, ← C_pow,
      ← mul_assoc, ← C_mul, coeff_C_mul_X_pow, coeff_C_mul_X_pow]
    split_ifs with h
    · subst h
      ring
    · simp

/-- **Newton's lemma over `k⟦t⟧`**: if `β` is an approximate root of `f` in the sense that
`f'(β)² t ∣ f(β)`, then `f` has a root `γ` with `f'(β) t ∣ γ - β`. -/
theorem Polynomial.exists_isRoot_powerSeries_of_sq_mul_X_dvd {k : Type*} [Field k]
    (f : (PowerSeries k)[X])
    (β : PowerSeries k)
    (h : (f.derivative.eval β) ^ 2 * PowerSeries.X ∣ f.eval β) :
    ∃ γ, f.IsRoot γ ∧ f.derivative.eval β * PowerSeries.X ∣ γ - β := by
  set c := f.derivative.eval β with hc_def
  by_cases hc : c = 0
  · refine ⟨β, ?_, by simp⟩
    rw [hc, zero_pow two_ne_zero, zero_mul, zero_dvd_iff] at h
    exact h
  obtain ⟨w, hw⟩ := h
  set T := (taylor β f).comp (C c * X) with hT_def
  have hT : ∀ j, T.coeff j = c ^ j * (taylor β f).coeff j := coeff_comp_C_mul_X _ _
  have hdvd : C (c ^ 2) ∣ T - C (f.eval β) - C (c ^ 2) * X := by
    rw [C_dvd_iff_dvd_coeff]
    intro j
    rw [coeff_sub, coeff_sub, coeff_C, coeff_C_mul_X, hT]
    rcases j with _ | _ | j
    · simp [taylor_coeff_zero]
    · simp [taylor_coeff_one, ← hc_def, pow_two]
    · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, sub_zero,
        Nat.add_eq_right]
      exact Dvd.dvd.mul_right (pow_dvd_pow c (by omega)) _
  obtain ⟨G, hG⟩ := hdvd
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  have hG0 : G.coeff 0 = 0 := by
    have := congr(coeff $hG 0)
    rw [coeff_sub, coeff_sub, coeff_C_zero, coeff_C_mul_X, hT, taylor_coeff_zero, coeff_C_mul]
      at this
    have h' : c ^ 2 * G.coeff 0 = 0 := by
      rw [← this]
      simp
    exact (mul_eq_zero.mp h').resolve_left hc2
  have hG1 : G.coeff 1 = 0 := by
    have := congr(coeff $hG 1)
    rw [coeff_sub, coeff_sub, coeff_C, coeff_C_mul_X, hT, taylor_coeff_one, coeff_C_mul,
      ← hc_def] at this
    have h' : c ^ 2 * G.coeff 1 = 0 := by
      rw [← this]
      simp [pow_two]
    exact (mul_eq_zero.mp h').resolve_left hc2
  set g : (PowerSeries k)[X] := C (PowerSeries.X * w) + X + G with hg_def
  have key : ∀ z, f.eval (β + c * z) = c ^ 2 * g.eval z := by
    intro z
    have h1 : T.eval z = f.eval (β + c * z) := by
      rw [hT_def, eval_comp, taylor_eval]
      simp [add_comm]
    have h2 := congr(eval z $hG)
    rw [eval_sub, eval_sub, eval_C, eval_mul, eval_C, eval_X, eval_mul, eval_C, h1] at h2
    rw [hg_def, eval_add, eval_add, eval_C, eval_X]
    linear_combination h2 + hw
  have hg0 : g.eval 0 ∈ Ideal.span {PowerSeries.X} := by
    rw [← coeff_zero_eq_eval_zero, hg_def, coeff_add, coeff_add, coeff_C_zero, coeff_X_zero,
      hG0, add_zero, add_zero]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hg1 : g.derivative.eval 0 = 1 := by
    rw [← coeff_zero_eq_eval_zero, coeff_derivative, hg_def, coeff_add, coeff_add, coeff_C,
      coeff_X_one, hG1]
    simp
  obtain ⟨z, hz, hz0⟩ := IsAdicComplete.exists_isRoot_sub_mem (Ideal.span {PowerSeries.X}) g 0
    hg0 (by rw [hg1, map_one]; exact isUnit_one)
  rw [sub_zero, Ideal.mem_span_singleton] at hz0
  refine ⟨β + c * z, ?_, ?_⟩
  · rw [IsRoot.def, key, hz.eq_zero, mul_zero]
  · rw [add_sub_cancel_left]
    exact mul_dvd_mul_left c hz0


