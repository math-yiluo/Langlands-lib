/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Complex.Basic
public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.Basic
public import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule

/-!
# Traces of powers of the Frobenius

The traces `tr (Fᵏ)` of the powers of the Frobenius of a Frobenius module behave as expected
under isomorphisms, rescaling, direct sums and duals. For the dual of a module pure of weight
`0` the trace is the complex conjugate: the eigenvalues of the dual are the inverses of those of
`F`, which have absolute value `1`.

## Main results

- `FrobeniusModule.Equiv.trace_frobeniusEnd_pow`, `FrobeniusModule.trace_frobeniusEnd_rescale_pow`,
  `FrobeniusModule.trace_frobeniusEnd_prod_pow`: invariance and additivity.
- `FrobeniusModule.IsPureOfWeight.map_trace_frobeniusEnd_dual_pow`: the trace on the dual of a
  module pure of weight `0` is the complex conjugate of the trace.
- `FrobeniusModule.HasWeightsAtMost.norm_map_trace_frobeniusEnd_pow_le`: the trace of `Fᵏ` on a
  module of weights at most `w` is bounded by `dim · q^{kw/2}`.
-/

@[expose] public section

universe u v t

namespace FrobeniusModule

variable {K : Type v} [Field K]

/-- The inverse of an isomorphism of Frobenius modules intertwines the Frobenius. -/
theorem Equiv.symm_map_frobenius {M N : FrobeniusModule.{u, v} K} (e : M.Equiv N)
    (y : N.carrier) :
    e.toLinearEquiv.symm (N.frobenius y) = M.frobenius (e.toLinearEquiv.symm y) := by
  apply e.toLinearEquiv.injective
  rw [e.map_frobenius]
  simp

/-- The Frobenius of `M.rescale c`, for `c ≠ 0`, is `c • F`. -/
theorem frobeniusEnd_rescale {M : FrobeniusModule.{u, v} K} {c : K} (hc : c ≠ 0) :
    (M.rescale c).frobeniusEnd = c • M.frobeniusEnd :=
  LinearMap.ext fun x ↦ frobeniusEnd_rescale_apply (M := M) hc x

/-- Rescaling the Frobenius by `c` multiplies the trace of its `k`-th power by `cᵏ`. -/
theorem trace_frobeniusEnd_rescale_pow (M : FrobeniusModule.{u, v} K) {c : K} (hc : c ≠ 0)
    (k : ℕ) :
    LinearMap.trace K _ ((M.rescale c).frobeniusEnd ^ k) =
      c ^ k * LinearMap.trace K _ (M.frobeniusEnd ^ k) := by
  rw [frobeniusEnd_rescale hc, smul_pow, map_smul, smul_eq_mul]
  rfl

/-- The trace of the `k`-th power of the Frobenius on a direct sum is the sum of the traces. -/
theorem trace_frobeniusEnd_prod_pow (M : FrobeniusModule.{u, v} K)
    (N : FrobeniusModule.{t, v} K) (k : ℕ) :
    LinearMap.trace K _ ((M.prod N).frobeniusEnd ^ k) =
      LinearMap.trace K _ (M.frobeniusEnd ^ k) + LinearMap.trace K _ (N.frobeniusEnd ^ k) := by
  have h : (M.prod N).frobeniusEnd = M.frobeniusEnd.prodMap N.frobeniusEnd := rfl
  have hp : ∀ j : ℕ, (M.frobeniusEnd.prodMap N.frobeniusEnd) ^ j =
      (M.frobeniusEnd ^ j).prodMap (N.frobeniusEnd ^ j) := fun j ↦ by
    induction j with
    | zero => simp [LinearMap.prodMap_one]
    | succ j ih => rw [pow_succ, ih, LinearMap.prodMap_mul, pow_succ, pow_succ]
  rw [h, hp]
  exact LinearMap.trace_prodMap' _ _

variable [IsAlgClosed K]

/-- The trace of the `k`-th power of the Frobenius is the sum of the `k`-th powers of its
eigenvalues, counted with multiplicity. -/
theorem trace_frobeniusEnd_pow_eq_sum (M : FrobeniusModule.{u, v} K) (k : ℕ) :
    LinearMap.trace K _ (M.frobeniusEnd ^ k) =
      (M.frobeniusEnd.charpoly.roots.map (· ^ k)).sum :=
  LinearMap.trace_pow_eq_sum_pow_roots_charpoly _ k

/-- On the dual of a Frobenius module pure of weight `0`, the image under `ι` of the trace of
`Fᵏ` is the complex conjugate of that on the module: the eigenvalues of the dual are the inverses
`α⁻¹` of the eigenvalues `α` of `F`, and `ι(α⁻¹) = conj (ι α)` since `|ι α| = 1`. -/
theorem IsPureOfWeight.map_trace_frobeniusEnd_dual_pow {ι : K →+* ℂ} {q : ℕ}
    {M : FrobeniusModule.{u, v} K} (h : M.IsPureOfWeight ι q 0) (k : ℕ) :
    ι (LinearMap.trace K _ (M.dual.frobeniusEnd ^ k)) =
      (starRingEnd ℂ) (ι (LinearMap.trace K _ (M.frobeniusEnd ^ k))) := by
  have hroots : M.dual.frobeniusEnd.charpoly.roots =
      M.frobeniusEnd.charpoly.roots.map fun a ↦ a⁻¹ :=
    LinearMap.charpoly_roots_dualMap_symm M.frobenius
  rw [trace_frobeniusEnd_pow_eq_sum, trace_frobeniusEnd_pow_eq_sum, hroots, Multiset.map_map,
    map_multiset_sum, map_multiset_sum, map_multiset_sum, Multiset.map_map, Multiset.map_map,
    Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun α hα ↦ ?_
  have hev : M.frobeniusEnd.HasEigenvalue α := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly]
    exact (Polynomial.mem_roots M.frobeniusEnd.charpoly_monic.ne_zero).1 hα
  have hn : ‖ι α‖ = 1 := by
    rw [h α hev, zero_div, Real.rpow_zero]
  have hconj : (starRingEnd ℂ) (ι α) = (ι α)⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hn]
    simp
  simp only [Function.comp_apply, map_pow, map_inv₀, hconj, inv_pow]

/-- On a Frobenius module of weights at most `w` relative to `q`, the trace of `Fᵏ` has
absolute value at most `dim V · q^{kw/2}`: it is a sum of `dim V` eigenvalue powers `αᵏ`, each
of absolute value at most `q^{kw/2}`. -/
theorem HasWeightsAtMost.norm_map_trace_frobeniusEnd_pow_le {ι : K →+* ℂ} {q : ℕ}
    {M : FrobeniusModule.{u, v} K} {w : ℝ} (h : M.HasWeightsAtMost ι q w) (k : ℕ) :
    ‖ι (LinearMap.trace K _ (M.frobeniusEnd ^ k))‖ ≤
      Module.finrank K M.carrier * ((q : ℝ) ^ (w / 2)) ^ k := by
  rw [trace_frobeniusEnd_pow_eq_sum, map_multiset_sum, Multiset.map_map,
    ← LinearMap.card_roots_charpoly M.frobeniusEnd]
  refine (norm_multiset_sum_le _).trans ?_
  rw [Multiset.map_map]
  refine (Multiset.sum_le_card_nsmul _ _ fun x hx ↦ ?_).trans_eq (by rw [nsmul_eq_mul,
    Multiset.card_map])
  obtain ⟨α, hα, rfl⟩ := Multiset.mem_map.1 hx
  have hev : M.frobeniusEnd.HasEigenvalue α := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly]
    exact (Polynomial.mem_roots M.frobeniusEnd.charpoly_monic.ne_zero).1 hα
  simp only [Function.comp_apply, map_pow, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (h α hev) k

end FrobeniusModule
