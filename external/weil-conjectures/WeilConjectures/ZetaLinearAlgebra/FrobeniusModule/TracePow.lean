/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Real

/-!
# Traces of powers of the Frobenius

The traces `tr (Fⁿ)` of the powers of the Frobenius of a Frobenius module determine its local
polynomial (`FrobeniusModule.isReal_iff_forall_trace_pow`). This file computes them for the
basic constructions: isomorphic modules, direct sums, rescalings and duals. The main
statement is that for `M` pure of weight `w` relative to `q` and `ι c = q ^ w`, the traces of the
twisted dual `M^∨(c)` are the complex conjugates of those of `M`
(`FrobeniusModule.IsPureOfWeight.map_trace_frobeniusEnd_pow_rescale_dual`), so that a direct
sum of two modules with mutually conjugate traces is `ι`-real
(`FrobeniusModule.isReal_prod_of_map_trace_frobeniusEnd_pow`).

## Main statements

- `LinearMap.trace_pow_eq_of_charpoly_eq`: over an algebraically closed field, the traces of
  the powers of an endomorphism only depend on its characteristic polynomial.
- `LinearMap.trace_symm_pow`: the traces of the powers of the inverse of an automorphism are the
  power sums of the inverses of its eigenvalues.
- `FrobeniusModule.IsPureOfWeight.map_trace_frobeniusEnd_pow_rescale_dual`: the twisted dual of
  a pure module has the conjugate traces.
- `FrobeniusModule.isReal_prod_of_map_trace_frobeniusEnd_pow`: a sum of two modules with
  conjugate traces is `ι`-real.
-/

@[expose] public section

universe u v t

open Polynomial

namespace LinearMap

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- The roots of the reverse characteristic polynomial `det (1 - t f)` of an automorphism are
the inverses of the roots of its characteristic polynomial. -/
theorem roots_charpolyRev [IsAlgClosed K] (f : Module.End K V) (hf : IsUnit f.det) :
    f.charpolyRev.roots = f.charpoly.roots.map (·⁻¹) := by
  have h0 := zero_notMem_roots_charpoly hf
  have hlin (a : K) (ha : a ∈ f.charpoly.roots) :
      (1 - C a * X : K[X]) = C (-a) * (X - C a⁻¹) := by
    have ha0 : a ≠ 0 := fun h ↦ h0 (h ▸ ha)
    rw [mul_sub, ← C_mul, neg_mul, mul_inv_cancel₀ ha0, C_neg, C_neg, C_1]
    ring
  have hC : (f.charpoly.roots.map fun a ↦ C (-a)).prod = C (f.charpoly.roots.map (-·)).prod := by
    rw [map_multiset_prod, Multiset.map_map]
    rfl
  have hX : (f.charpoly.roots.map fun a ↦ X - C a⁻¹) =
      (f.charpoly.roots.map (·⁻¹)).map fun b ↦ X - C b := by
    rw [Multiset.map_map]
    rfl
  have hne : (f.charpoly.roots.map (-·)).prod ≠ 0 := Multiset.prod_ne_zero fun h ↦ by
    obtain ⟨a, ha, ha0⟩ := Multiset.mem_map.1 h
    exact h0 (neg_eq_zero.1 ha0 ▸ ha)
  rw [charpolyRev_eq_prod_roots, Multiset.map_congr rfl hlin, Multiset.prod_map_mul, hC, hX,
    roots_C_mul _ hne, roots_multiset_prod_X_sub_C]

/-- Over an algebraically closed field, the traces of the powers of the inverse of an
automorphism `e` are the power sums of the inverses of the eigenvalues of `e`. -/
theorem trace_symm_pow [IsAlgClosed K] (e : V ≃ₗ[K] V) (n : ℕ) :
    trace K V (e.symm.toLinearMap ^ n) =
      (e.toLinearMap.charpoly.roots.map fun a ↦ a⁻¹ ^ n).sum := by
  have h := C_det_mul_charpolyRev (f := e.symm.toLinearMap) (g := e.toLinearMap) (c := 1)
    (LinearMap.ext fun x ↦ by simp)
  rw [C_1, one_mul, comp_X] at h
  have hroots : e.symm.toLinearMap.charpoly.roots = e.toLinearMap.charpolyRev.roots := by
    have h' := congrArg roots h
    rw [roots_C_mul _ (LinearEquiv.isUnit_det' _).ne_zero,
      roots_C_mul _ (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero))] at h'
    exact h'.symm
  rw [trace_pow_eq_sum_pow_roots_charpoly, hroots, roots_charpolyRev _ (LinearEquiv.isUnit_det' e),
    Multiset.map_map]
  rfl

end LinearMap

/-- Conjugation by a linear isomorphism commutes with powers. -/
theorem LinearEquiv.conj_pow {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (e : V ≃ₗ[K] W) (f : Module.End K V) (n : ℕ) :
    e.conj f ^ n = e.conj (f ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Module.End.one_eq_id, Module.End.one_eq_id, conj_id]
  | succ n ih =>
    rw [pow_succ, pow_succ, ih, Module.End.mul_eq_comp, Module.End.mul_eq_comp, conj_comp]

namespace FrobeniusModule

variable {K : Type v} [Field K]

/-- The traces of the powers of the Frobenius of a zero module vanish. -/
theorem trace_frobeniusEnd_pow_eq_zero_of_subsingleton (M : FrobeniusModule.{u, v} K)
    [Subsingleton M.carrier] (n : ℕ) :
    LinearMap.trace K M.carrier (M.frobeniusEnd ^ n) = 0 := by
  rw [Subsingleton.elim (M.frobeniusEnd ^ n) 0, map_zero]

/-- The traces of the powers of the Frobenius of a direct sum are the sums of the traces. -/
theorem trace_frobeniusEnd_pow_prod (M : FrobeniusModule.{u, v} K)
    (N : FrobeniusModule.{t, v} K) (n : ℕ) :
    LinearMap.trace K (M.prod N).carrier ((M.prod N).frobeniusEnd ^ n) =
      LinearMap.trace K M.carrier (M.frobeniusEnd ^ n) +
        LinearMap.trace K N.carrier (N.frobeniusEnd ^ n) := by
  have hF : (M.prod N).frobeniusEnd = M.frobeniusEnd.prodMap N.frobeniusEnd :=
    LinearMap.ext fun _ ↦ rfl
  have hpow (k : ℕ) : (M.frobeniusEnd.prodMap N.frobeniusEnd) ^ k =
      (M.frobeniusEnd ^ k).prodMap (N.frobeniusEnd ^ k) := by
    induction k with
    | zero => rw [pow_zero, pow_zero, pow_zero, LinearMap.prodMap_one]
    | succ k ih => rw [pow_succ, ih, LinearMap.prodMap_mul, pow_succ, pow_succ]
  rw [hF, hpow]
  exact LinearMap.trace_prodMap' _ _

/-- The traces of the powers of a rescaled Frobenius `c F` are `cⁿ tr (Fⁿ)`. -/
theorem trace_frobeniusEnd_pow_rescale (M : FrobeniusModule.{u, v} K) {c : K} (hc : c ≠ 0)
    (n : ℕ) :
    LinearMap.trace K (M.rescale c).carrier ((M.rescale c).frobeniusEnd ^ n) =
      c ^ n * LinearMap.trace K M.carrier (M.frobeniusEnd ^ n) := by
  have hF : (M.rescale c).frobeniusEnd = c • M.frobeniusEnd :=
    LinearMap.ext fun x ↦ frobeniusEnd_rescale_apply (M := M) hc x
  rw [hF, smul_pow, map_smul, smul_eq_mul]
  rfl

/-- The traces of the powers of the Frobenius `(F⁻¹)^∨` of the dual are the traces of the
powers of `F⁻¹`. -/
theorem trace_frobeniusEnd_pow_dual (M : FrobeniusModule.{u, v} K) (n : ℕ) :
    LinearMap.trace K M.dual.carrier (M.dual.frobeniusEnd ^ n) =
      LinearMap.trace K M.carrier (M.frobenius.symm.toLinearMap ^ n) := by
  have hpow (f : Module.End K M.carrier) (k : ℕ) : f.dualMap ^ k = (f ^ k).dualMap := by
    induction k with
    | zero => rw [pow_zero, pow_zero, Module.End.one_eq_id, Module.End.one_eq_id,
        LinearMap.dualMap_id]
    | succ k ih =>
      rw [pow_succ, ih, Module.End.mul_eq_comp, LinearMap.dualMap_comp_dualMap, pow_succ']
      rfl
  refine Eq.trans ?_ (LinearMap.trace_transpose' (M.frobenius.symm.toLinearMap ^ n))
  rw [← LinearMap.dualMap_def, ← hpow]
  rfl

/-- **The twisted dual of a pure module has the conjugate traces.** If `M` is `ι`-pure of weight
`w` relative to `q` and `ι c = q ^ w`, then `ι tr (Fⁿ | M^∨(c)) = conj (ι tr (Fⁿ | M))`: the
eigenvalues of the twisted dual are the `c α⁻¹` for the eigenvalues `α` of `M`, and
`ι (c α⁻¹) = |ι α|² / ι α = conj (ι α)`. -/
theorem IsPureOfWeight.map_trace_frobeniusEnd_pow_rescale_dual [IsAlgClosed K] {ι : K →+* ℂ}
    {q : ℕ} (hq : 0 < q) {M : FrobeniusModule.{u, v} K} {w : ℝ} (h : M.IsPureOfWeight ι q w)
    {c : K} (hc : ι c = (((q : ℝ) ^ w : ℝ) : ℂ)) (n : ℕ) :
    ι (LinearMap.trace K (M.dual.rescale c).carrier ((M.dual.rescale c).frobeniusEnd ^ n)) =
      starRingEnd ℂ (ι (LinearMap.trace K M.carrier (M.frobeniusEnd ^ n))) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, Complex.ofReal_eq_zero] at hc
    exact (Real.rpow_pos_of_pos hq0 w).ne' hc
  have hroot (α : K) (hα : α ∈ M.frobeniusEnd.charpoly.roots) :
      ι c * (ι α)⁻¹ = starRingEnd ℂ (ι α) := by
    have hev : M.frobeniusEnd.HasEigenvalue α :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly _ α).2 (Polynomial.isRoot_of_mem_roots hα)
    have hn := h α hev
    have hα0 : ι α ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hn
      exact (Real.rpow_pos_of_pos hq0 _).ne' hn.symm
    rw [mul_inv_eq_iff_eq_mul₀ hα0, eq_comm, mul_comm, Complex.mul_conj,
      Complex.normSq_eq_norm_sq, hn, hc, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le]
    norm_num
  rw [trace_frobeniusEnd_pow_rescale _ hc0, trace_frobeniusEnd_pow_dual,
    LinearMap.trace_symm_pow, LinearMap.trace_pow_eq_sum_pow_roots_charpoly, map_mul, map_pow,
    map_multiset_sum, map_multiset_sum, map_multiset_sum, Multiset.map_map, Multiset.map_map,
    Multiset.map_map, ← Multiset.sum_map_mul_left]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun α hα ↦ ?_)
  rw [Function.comp_apply, Function.comp_apply, Function.comp_apply, map_pow, map_pow, map_pow,
    map_inv₀, ← mul_pow, hroot α hα]

/-- A direct sum of two Frobenius modules whose traces of powers of the Frobenius are mutually
`ι`-conjugate is `ι`-real. -/
theorem isReal_prod_of_map_trace_frobeniusEnd_pow {ι : K →+* ℂ} {M : FrobeniusModule.{u, v} K}
    {N : FrobeniusModule.{t, v} K}
    (h : ∀ n : ℕ, ι (LinearMap.trace K N.carrier (N.frobeniusEnd ^ n)) =
      starRingEnd ℂ (ι (LinearMap.trace K M.carrier (M.frobeniusEnd ^ n)))) :
    (M.prod N).IsReal ι := by
  rw [isReal_iff_forall_trace_pow]
  intro m
  rw [trace_frobeniusEnd_pow_prod, map_add, h, map_add, Complex.conj_conj, add_comm]

end FrobeniusModule
