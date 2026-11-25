/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Continuous functions and base change along a finite free algebra

Let `R` be a topological ring, `M` an `R`-module with the module topology and `N` a finite free
`R`-module, and give `M ⊗_R N` the module topology. For every topological space `U` the map
`C(U, M) ⊗_R N → C(U, M ⊗_R N)`, `f ⊗ n ↦ (x ↦ f x ⊗ n)`
(`ContinuousMap.tensorRight`) is bijective (`ContinuousMap.bijective_tensorRight`): in a basis
`(bᵢ)` of `N`, both sides are `C(U, M)^κ`, the coordinates `M ⊗_R N → M` being linear, hence
continuous. For instance `C(U, M) ⊗_{𝒪_E} 𝒪_F = C(U, M ⊗_{𝒪_E} 𝒪_F)` for a finite extension `F`
of `E` inside `ℚ̄_ℓ`.
-/

@[expose] public section

open TensorProduct

namespace ContinuousMap

variable {R : Type*} [CommRing R] [TopologicalSpace R]
  {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousSMul R M] [IsModuleTopology R M]
  {N : Type*} [AddCommGroup N] [Module R N]
  [TopologicalSpace (M ⊗[R] N)] [IsTopologicalAddGroup (M ⊗[R] N)]
  [ContinuousSMul R (M ⊗[R] N)]
  (U : Type*) [TopologicalSpace U]

/-- The function `x ↦ f x ⊗ n`. -/
def tensorRightAux (f : C(U, M)) (n : N) : C(U, M ⊗[R] N) :=
  ⟨fun x ↦ f x ⊗ₜ n,
    (IsModuleTopology.continuous_of_linearMap ((TensorProduct.mk R M N).flip n)).comp
      f.continuous⟩

variable (R M N) in
/-- The map `C(U, M) ⊗_R N → C(U, M ⊗_R N)`, `f ⊗ n ↦ (x ↦ f x ⊗ n)`. -/
noncomputable def tensorRight : C(U, M) ⊗[R] N →ₗ[R] C(U, M ⊗[R] N) :=
  TensorProduct.lift (LinearMap.mk₂ R (tensorRightAux U)
    (fun f f' n ↦ ext fun x ↦ add_tmul (f x) (f' x) n)
    (fun r f n ↦ ext fun x ↦ (smul_tmul' r (f x) n).symm)
    (fun f n n' ↦ ext fun x ↦ tmul_add (f x) n n')
    (fun r f n ↦ ext fun x ↦ (tmul_smul r (f x) n)))

@[simp]
lemma tensorRight_tmul_apply (f : C(U, M)) (n : N) (x : U) :
    tensorRight R M N U (f ⊗ₜ n) x = f x ⊗ₜ n :=
  rfl

/-- **`C(U, M) ⊗_R N = C(U, M ⊗_R N)` for `N` finite free.** -/
theorem bijective_tensorRight [IsModuleTopology R (M ⊗[R] N)] {κ : Type*} [Finite κ]
    (b : Module.Basis κ R N) : Function.Bijective (tensorRight R M N U) := by
  classical
  have := Fintype.ofFinite κ
  refine ⟨(injective_iff_map_eq_zero _).2 fun t ht ↦ ?_, fun g ↦ ?_⟩
  · let e' := TensorProduct.equivFinsuppOfBasisRight (M := C(U, M)) b
    have ht' : t = ∑ i, e' t i ⊗ₜ b i := by
      conv_lhs => rw [← e'.symm_apply_apply t, TensorProduct.equivFinsuppOfBasisRight_symm_apply,
        Finsupp.sum_fintype _ _ (by simp)]
    have h0 : e' t = 0 := by
      ext i x
      have hx := congrArg (fun g : C(U, M ⊗[R] N) ↦ g x) ht
      rw [ht'] at hx
      simp only [map_sum, ContinuousMap.coe_sum, Finset.sum_apply, tensorRight_tmul_apply,
        ContinuousMap.zero_apply] at hx
      have := TensorProduct.sum_tmul_basis_right_eq_zero b
        (Finsupp.equivFunOnFinite.symm fun i ↦ e' t i x) (by
          rw [Finsupp.sum_fintype _ _ (by simp)]
          simpa using hx)
      simpa using congrArg (fun v ↦ v i) this
    rw [ht', h0]
    simp
  · let e := TensorProduct.equivFinsuppOfBasisRight (M := M) b
    let c (i : κ) : M ⊗[R] N →ₗ[R] M :=
      Finsupp.lapply i ∘ₗ e.toLinearMap
    let g' (i : κ) : C(U, M) := ⟨fun x ↦ c i (g x),
      (IsModuleTopology.continuous_of_linearMap (c i)).comp g.continuous⟩
    refine ⟨∑ i, g' i ⊗ₜ b i, ext fun x ↦ ?_⟩
    rw [map_sum, ContinuousMap.coe_sum, Finset.sum_apply]
    simp only [tensorRight_tmul_apply]
    conv_rhs => rw [← e.symm_apply_apply (g x), TensorProduct.equivFinsuppOfBasisRight_symm_apply,
      Finsupp.sum_fintype _ _ (by simp)]
    rfl

end ContinuousMap
