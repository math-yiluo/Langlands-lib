/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Weights
public import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # A root-free boundary polynomial bounds logarithmic weights

Source: latest blueprint, sec-purity-real-sheaves/sk-p-real-semi/sk-p-real-semi.proof.md,
paragraph 6: roots of 1-alpha*T^d and the preliminary a+2 bound.
(blueprint: lem-wf-boundary-root-weight-bound).
-/

@[expose] public section
set_option autoImplicit false

open AlgebraicGeometry

namespace PowerSeries

/-- A d-th root of the inverse eigenvalue is a zero of its determinant factor, hence lies
outside the disc. Taking logarithms converts its modulus estimate to the weight bound.
Source: latest blueprint, sk-p-real-semi.proof.md, paragraph 6
(blueprint: lem-wf-boundary-root-weight-bound). -/
theorem boundary_weight_le_add_two_of_no_zero
    {E : Type*} [Field E] (ι : E →+* ℂ) (q d : ℕ) (hq : 1 < q) (hd : 0 < d)
    (α : E) (hα : α ≠ 0) (a : ℝ) (B : Polynomial ℂ)
    (hfactor : 1 - Polynomial.C (ι α) * Polynomial.X ^ d ∣ B)
    (hdisc : ∀ z : ℂ, ‖z‖ < (q : ℝ) ^ (-(a / 2 + 1)) → B.eval z ≠ 0) :
    WeilGroup.frobeniusWeight ι (q ^ d) α ≤ a + 2 := by
  have hq' : (1 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := zero_lt_one.trans hq'
  have hia : ι α ≠ 0 := (map_ne_zero ι).2 hα
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (ι α)⁻¹ hd
  have hlocal : (1 - Polynomial.C (ι α) * Polynomial.X ^ d).eval z = 0 := by
    simp [hz, mul_inv_cancel₀ hia]
  have hB : B.eval z = 0 := Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hfactor hlocal
  have hR : (q : ℝ) ^ (-(a / 2 + 1)) ≤ ‖z‖ := by
    by_contra! hlt
    exact hdisc z hlt hB
  have hlogR := Real.log_le_log (Real.rpow_pos_of_pos hq0 _) hR
  rw [Real.log_rpow hq0] at hlogR
  have hnorm : ‖z‖ ^ d = ‖ι α‖⁻¹ := by rw [← norm_pow, hz, norm_inv]
  have hlog := congrArg Real.log hnorm
  rw [Real.log_pow, Real.log_inv] at hlog
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hlogq : Real.log ((q ^ d : ℕ) : ℝ) = (d : ℝ) * Real.log q := by
    rw [Nat.cast_pow, Real.log_pow]
  have hscaled := mul_le_mul_of_nonneg_left hlogR hd'.le
  unfold WeilGroup.frobeniusWeight
  rw [hlogq, div_le_iff₀ (mul_pos hd' (Real.log_pos hq'))]
  nlinarith

end PowerSeries
