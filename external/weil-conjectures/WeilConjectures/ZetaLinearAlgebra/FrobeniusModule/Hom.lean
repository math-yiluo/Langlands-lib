/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.LinearAlgebra.Trace
public import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Trace

/-!
# Traces on spaces of linear maps between Frobenius modules

If a Frobenius module `P` is identified with the space of linear maps `A → B` between two
Frobenius modules, its Frobenius becoming `φ ↦ F_B ∘ φ ∘ F_A⁻¹`, then the trace of `F_Pᵏ` is
`tr (F_Bᵏ) · tr (F_A⁻ᵏ)`. For the dual `A = M^∨` the inverse Frobenius `F_A⁻¹` is the transpose
of `F_M`, with the same traces of powers as `F_M`.

## Main results

- `FrobeniusModule.trace_frobeniusEnd_pow_eq_mul_of_linearEquiv`: the trace on `Hom(A, B)`.
- `FrobeniusModule.trace_dual_frobenius_symm_pow`: `tr (F_{M^∨}⁻ᵏ) = tr (F_Mᵏ)`.
-/

@[expose] public section

universe u v t w

namespace FrobeniusModule

variable {K : Type v} [Field K]

/-- Conjugation by a linear isomorphism commutes with powers. -/
private lemma conj_pow {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] (e : V ≃ₗ[K] W) (f : Module.End K V) (k : ℕ) :
    e.conj f ^ k = e.conj (f ^ k) := by
  induction k with
  | zero => ext x; simp [LinearEquiv.conj_apply]
  | succ k ih => rw [pow_succ, ih, pow_succ, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      LinearEquiv.conj_comp]

/-- If `P ≅ Hom(A, B)` with the Frobenius of `P` becoming `φ ↦ F_B ∘ φ ∘ F_A⁻¹`, then
`tr (F_Pᵏ) = tr (F_Bᵏ) · tr (F_A⁻ᵏ)`. -/
theorem trace_frobeniusEnd_pow_eq_mul_of_linearEquiv (P : FrobeniusModule.{u, v} K)
    (A : FrobeniusModule.{t, v} K) (B : FrobeniusModule.{w, v} K)
    (E : P.carrier ≃ₗ[K] (A.carrier →ₗ[K] B.carrier))
    (hE : ∀ d, E (P.frobenius d) = B.frobeniusEnd ∘ₗ E d ∘ₗ A.frobenius.symm.toLinearMap)
    (k : ℕ) :
    LinearMap.trace K _ (P.frobeniusEnd ^ k) =
      LinearMap.trace K _ (B.frobeniusEnd ^ k) *
        LinearMap.trace K _ (A.frobenius.symm.toLinearMap ^ k) := by
  set C : Module.End K (A.carrier →ₗ[K] B.carrier) :=
    LinearMap.llcomp K A.carrier B.carrier B.carrier B.frobeniusEnd ∘ₗ
      LinearMap.lcomp K B.carrier A.frobenius.symm.toLinearMap
  have hC : E.conj P.frobeniusEnd = C := by
    refine LinearMap.ext fun φ ↦ ?_
    obtain ⟨d, rfl⟩ := E.surjective φ
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    exact (hE d).trans rfl
  have hCk : C ^ k = LinearMap.llcomp K A.carrier B.carrier B.carrier (B.frobeniusEnd ^ k) ∘ₗ
      LinearMap.lcomp K B.carrier (A.frobenius.symm.toLinearMap ^ k) := by
    induction k with
    | zero => ext φ x; simp
    | succ k ih =>
      rw [pow_succ, ih, pow_succ B.frobeniusEnd, pow_succ' A.frobenius.symm.toLinearMap]
      ext φ x
      simp [C, Module.End.mul_apply]
  rw [← LinearMap.trace_conj' _ E, ← conj_pow, hC, hCk, LinearMap.trace_llcomp_comp_lcomp]

/-- The inverse Frobenius of an isomorphic Frobenius module has the same traces of powers. -/
theorem Equiv.trace_frobenius_symm_pow {M : FrobeniusModule.{u, v} K}
    {N : FrobeniusModule.{u, v} K} (e : M.Equiv N) (k : ℕ) :
    LinearMap.trace K _ (N.frobenius.symm.toLinearMap ^ k) =
      LinearMap.trace K _ (M.frobenius.symm.toLinearMap ^ k) := by
  have h : N.frobenius.symm.toLinearMap = e.toLinearEquiv.conj M.frobenius.symm.toLinearMap := by
    refine LinearMap.ext fun y ↦ ?_
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearEquiv.symm_apply_eq, <- e.map_frobenius, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]
  rw [h, conj_pow, LinearMap.trace_conj']

/-- The inverse of the Frobenius of the dual `M^∨` is the transpose of the Frobenius of `M`, so
it has the same traces of powers. -/
theorem trace_dual_frobenius_symm_pow (M : FrobeniusModule.{u, v} K) (k : ℕ) :
    LinearMap.trace K _ (M.dual.frobenius.symm.toLinearMap ^ k) =
      LinearMap.trace K _ (M.frobeniusEnd ^ k) := by
  have h1 : M.dual.frobenius.symm.toLinearMap = Module.Dual.transpose (R := K) M.frobeniusEnd := by
    refine LinearMap.ext fun (f : Module.Dual K M.carrier) ↦ ?_
    rw [LinearEquiv.coe_coe, LinearEquiv.symm_apply_eq]
    refine LinearMap.ext fun x ↦ ?_
    rw [dual_frobenius_apply, LinearMap.comp_apply]
    exact congrArg f (M.frobenius.apply_symm_apply x).symm
  have h2 : ∀ j : ℕ, Module.Dual.transpose (R := K) M.frobeniusEnd ^ j =
      Module.Dual.transpose (R := K) (M.frobeniusEnd ^ j) := fun j ↦ by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [pow_succ, ih, pow_succ']
      rfl
  rw [h1, h2]
  exact LinearMap.trace_transpose' _

section Eigenvalues

variable {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

open Polynomial in
/-- If `ψ ∘ ∏_{μ ∈ s} (A' - μ) = 0` for a nonzero `ψ` with `B ∘ ψ ∘ A' = β ψ`, then some
nonzero `ψ'` with `B ∘ ψ' ∘ A' = β ψ'` satisfies `ψ' ∘ A' = μ ψ'` for some `μ ∈ s`. -/
private lemma exists_comp_eq_smul (B : Module.End K W) (A' : Module.End K V) (β : K) :
    ∀ (s : Multiset K) (ψ : V →ₗ[K] W), ψ ≠ 0 → B ∘ₗ ψ ∘ₗ A' = β • ψ →
      ψ ∘ₗ aeval A' (s.map fun μ ↦ X - C μ).prod = 0 →
      ∃ μ ∈ s, ∃ ψ' : V →ₗ[K] W, ψ' ≠ 0 ∧ ψ' ∘ₗ A' = μ • ψ' ∧ B ∘ₗ ψ' ∘ₗ A' = β • ψ' := by
  intro s
  induction s using Multiset.induction_on with
  | empty =>
    intro ψ hψ _ h0
    exact absurd (by simpa [Module.End.one_eq_id] using h0) hψ
  | cons μ s ih =>
    intro ψ hψ hβ h0
    set ψ₁ := ψ ∘ₗ (A' - μ • LinearMap.id)
    by_cases h₁ : ψ₁ = 0
    · refine ⟨μ, Multiset.mem_cons_self μ s, ψ, hψ, LinearMap.ext fun v ↦ ?_, hβ⟩
      have h := LinearMap.congr_fun h₁ v
      simp only [ψ₁, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, map_sub, map_smul, LinearMap.zero_apply, sub_eq_zero] at h
      simpa using h
    · have hβ₁ : B ∘ₗ ψ₁ ∘ₗ A' = β • ψ₁ := by
        ext v
        have h := LinearMap.congr_fun hβ ((A' - μ • LinearMap.id : Module.End K V) v)
        simp only [ψ₁, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sub_apply,
          LinearMap.id_apply, map_sub, map_smul] at h ⊢
        rw [h, smul_sub, smul_comm μ β]
      have h0₁ : ψ₁ ∘ₗ aeval A' (s.map fun μ ↦ X - C μ).prod = 0 := by
        rw [Multiset.map_cons, Multiset.prod_cons, map_mul, Module.End.mul_eq_comp,
          ← LinearMap.comp_assoc] at h0
        convert h0 using 3
        ext v
        simp [Module.algebraMap_end_eq_smul_id]
      obtain ⟨μ', hμ', ψ', h⟩ := ih ψ₁ h₁ hβ₁ h0₁
      exact ⟨μ', Multiset.mem_cons_of_mem hμ', ψ', h⟩


variable [IsAlgClosed K]

/-- If `P ≅ Hom(A, B)` with the Frobenius of `P` becoming `φ ↦ F_B ∘ φ ∘ F_A⁻¹`, then every
eigenvalue of `F_P` is `λ μ⁻¹` for eigenvalues `λ` of `F_B` and `μ` of `F_A`. -/
theorem exists_eq_mul_inv_of_hasEigenvalue_of_linearEquiv (P : FrobeniusModule.{u, v} K)
    (A : FrobeniusModule.{t, v} K) (B : FrobeniusModule.{w, v} K)
    (E : P.carrier ≃ₗ[K] (A.carrier →ₗ[K] B.carrier))
    (hE : ∀ d, E (P.frobenius d) = B.frobeniusEnd ∘ₗ E d ∘ₗ A.frobenius.symm.toLinearMap)
    {β : K} (hβ : P.frobeniusEnd.HasEigenvalue β) :
    ∃ lam μ : K, B.frobeniusEnd.HasEigenvalue lam ∧ A.frobeniusEnd.HasEigenvalue μ ∧
      β = lam * μ⁻¹ := by
  obtain ⟨d, hd⟩ := hβ.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hd
  set A' : Module.End K A.carrier := A.frobenius.symm.toLinearMap
  have hψ : E d ≠ 0 := (map_ne_zero_iff _ E.injective).2 hd.2
  have hβψ : B.frobeniusEnd ∘ₗ E d ∘ₗ A' = β • E d := by
    rw [← hE, ← map_smul]
    exact congrArg E hd.1
  have h0 : E d ∘ₗ Polynomial.aeval A'
      (A'.charpoly.roots.map fun μ ↦ Polynomial.X - Polynomial.C μ).prod = 0 := by
    rw [← LinearMap.charpoly_eq_prod_roots, LinearMap.aeval_self_charpoly, LinearMap.comp_zero]
  obtain ⟨μ, hμ, ψ, hψ0, hψμ, hψβ⟩ := exists_comp_eq_smul _ _ β _ _ hψ hβψ h0
  -- `μ` is an eigenvalue of `F_A⁻¹`, hence nonzero
  have hμA' : Module.End.HasEigenvalue A' μ := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly]
    exact (Polynomial.mem_roots (LinearMap.charpoly_monic _).ne_zero).1 hμ
  obtain ⟨a, ha⟩ := hμA'.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at ha
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ha
    exact ha.2 (A.frobenius.symm.map_eq_zero_iff.1 ha.1)
  -- an eigenvector of `F_B`
  obtain ⟨v, hv⟩ : ∃ v, ψ v ≠ 0 := by
    by_contra h
    exact hψ0 (LinearMap.ext fun v ↦ not_not.1 fun hv ↦ h ⟨v, hv⟩)
  have hB : B.frobeniusEnd (ψ v) = (β * μ⁻¹) • ψ v := by
    have h1 := LinearMap.congr_fun hψβ v
    have h2 : ψ (A' v) = μ • ψ v := LinearMap.congr_fun hψμ v
    rw [LinearMap.comp_apply, LinearMap.comp_apply, h2, map_smul, LinearMap.smul_apply] at h1
    rw [mul_comm, mul_smul, ← h1, inv_smul_smul₀ hμ0]
  refine ⟨β * μ⁻¹, μ⁻¹, Module.End.hasEigenvalue_of_hasEigenvector
    (Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 hB, hv⟩),
    Module.End.hasEigenvalue_of_hasEigenvector (x := a)
      (Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 ?_, ha.2⟩), ?_⟩
  · have h1 : a = μ • A.frobenius a := by
      simpa [A'] using congrArg A.frobenius ha.1
    change A.frobenius a = μ⁻¹ • a
    conv_rhs => rw [h1, inv_smul_smul₀ hμ0]
  · rw [inv_inv, mul_assoc, inv_mul_cancel₀ hμ0, mul_one]

/-- If `P ≅ Hom(A, B)` with the Frobenius of `P` becoming `φ ↦ F_B ∘ φ ∘ F_A⁻¹`, `A` pure of
weight `wA` and `B` pure of weight `wB`, then `P` is pure of weight `wB - wA`. -/
theorem IsPureOfWeight.of_linearEquiv_hom {ι : K →+* ℂ} {q : ℕ} (hq : 0 < q)
    {P : FrobeniusModule.{u, v} K} {A : FrobeniusModule.{t, v} K} {B : FrobeniusModule.{w, v} K}
    (E : P.carrier ≃ₗ[K] (A.carrier →ₗ[K] B.carrier))
    (hE : ∀ d, E (P.frobenius d) = B.frobeniusEnd ∘ₗ E d ∘ₗ A.frobenius.symm.toLinearMap)
    {wA wB : ℝ} (hA : A.IsPureOfWeight ι q wA) (hB : B.IsPureOfWeight ι q wB) :
    P.IsPureOfWeight ι q (wB - wA) := by
  intro β hβ
  obtain ⟨lam, μ, hlam, hμ, rfl⟩ := exists_eq_mul_inv_of_hasEigenvalue_of_linearEquiv P A B E hE hβ
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  rw [map_mul, map_inv₀, norm_mul, norm_inv, hB _ hlam, hA _ hμ, ← Real.rpow_neg hq'.le,
    ← Real.rpow_add hq']
  congr 1
  ring


end Eigenvalues

end FrobeniusModule
