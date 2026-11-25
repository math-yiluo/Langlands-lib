/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.RingHom.Flat
import WeilConjectures.RingTheory.FiniteCoefficientTensorKernelClosedFiber
import Mathlib.RingTheory.Smooth.Quotient

/-!
# Vanishing of the tensor-map kernel modulo the target maximal ideal

Source: Stacks Project, Remark 07NS (part (4)) and Proposition 07NQ, kernel argument.
(blueprint: lem-weil-pbc-finite-coefficient-tensor-kernel-reduction)
-/

@[expose] public section

universe u v w z

namespace RingHom

/-- The closed-fibre calculation isolated as quotient vanishing.
Source: Stacks Project, Remark 07NS (part (4)).
(blueprint: lem-weil-pbc-finite-coefficient-tensor-kernel-reduction-quotient)

Proof: flat tensor exactness injects the kernel modulo the maximal ideal. Residue
surjectivity reduces tensors to `c ⊗ 1`; the kernel equality puts such a class in
the maximal-ideal multiple of the kernel, so its quotient class is zero.
-/
theorem finite_coefficient_tensor_kernel_reduction_quotient
    {A₀ : Type u} {A : Type v} {B : Type w} {C : Type z}
    [CommRing A₀] [CommRing A] [CommRing B] [CommRing C]
    [Algebra A₀ A] [Algebra A₀ C]
    [IsLocalRing A₀] [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
    (α : A₀ →+* A) (hα : algebraMap A₀ A = α) [IsLocalHom α]
    (hres : Function.Bijective (IsLocalRing.ResidueField.map α))
    (γ : A₀ →+* C) (hγ : algebraMap A₀ C = γ) [IsLocalHom γ]
    (φ : A →+* B) [IsLocalHom φ]
    (ψ : C →+* B) [IsLocalHom ψ] (hψγ : ψ.comp γ = φ.comp α)
    (F : TensorProduct A₀ C A →+* B)
    (hF : ∀ c a, F (TensorProduct.tmul A₀ c a) = ψ c * φ a)
    (hflat : RingHom.Flat φ) (hsurj : Function.Surjective F)
    (hker : RingHom.ker
      ((Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A).map φ)).comp ψ) =
      (IsLocalRing.maximalIdeal A₀).map γ) :
    ∀ x : TensorProduct A₀ C A, x ∈ RingHom.ker F →
    Submodule.mkQ (((IsLocalRing.maximalIdeal A).map
        (Algebra.TensorProduct.includeRight (R := A₀) (A := C)).toRingHom) •
        (RingHom.ker F : Submodule (TensorProduct A₀ C A) (TensorProduct A₀ C A))) x = 0 := by
  have _hcompat := hψγ
  let : Algebra A (TensorProduct A₀ C A) := Algebra.TensorProduct.rightAlgebra
  let : Algebra A B := φ.toAlgebra
  have : Module.Flat A B := hflat
  let f : TensorProduct A₀ C A →ₗ[A] B :=
    { F.toAddMonoidHom with
      map_smul' := fun a x ↦ by
        change F ((1 ⊗ₜ[A₀] a) * x) = φ a * F x
        rw [map_mul, hF, map_one, one_mul] }
  have hclosed := finite_coefficient_tensor_kernel_closed_fiber α hα hres.2 γ hγ φ ψ
    F hF hker
  intro x hx
  apply (Submodule.Quotient.mk_eq_zero _).2
  have hxI : x ∈ (IsLocalRing.maximalIdeal A) •
      (⊤ : Submodule A (TensorProduct A₀ C A)) := by
    rw [Ideal.smul_top_eq_map]
    exact hclosed hx
  have hxK : x ∈ f.ker := hx
  have hxIK : x ∈ (IsLocalRing.maximalIdeal A) • f.ker := by
    rw [← LinearMap.ker_inf_smul_top_eq_smul_of_flat _ f hsurj]
    exact ⟨hxK, hxI⟩
  change x ∈ (((IsLocalRing.maximalIdeal A).map
    (algebraMap A (TensorProduct A₀ C A))) •
      (RingHom.ker F : Submodule (TensorProduct A₀ C A) (TensorProduct A₀ C A))).restrictScalars A
  rw [Ideal.smul_restrictScalars]
  exact hxIK

/-- Flatness and the correct closed-fibre kernel make K/m_A K vanish.
Source: Stacks Project, Remark 07NS (part (4)); Proposition 07NQ, tensor exactness argument.
(blueprint: lem-weil-pbc-finite-coefficient-tensor-kernel-reduction)

Proof:
1. The pure-tensor formula identifies the restrictions of F to A and C with φ and ψ.
   Put D = C ⊗[A₀] A and K = ker F. Surjectivity gives an exact sequence
   0 → K → D → B → 0 of A-modules, with B flat over A. Tensoring with k = A/m_A
   preserves injectivity at K by `LinearMap.lTensor_injective_of_exact_of_flat`.
   Identify the three tensor products with their quotients modulo m_A.
2. Residue surjectivity gives A = α(A₀) + m_A. Balancing reduces every pure tensor
   modulo m_A D to c ⊗ 1; sums do too. If this class maps to zero, ψ(c) lies in
   m_A B, so the given kernel equality implies c ∈ m₀C. Expand c as a finite
   sum γ(x_i)c_i, with x_i ∈ m₀. Then c ⊗ 1 = Σ c_i ⊗ α(x_i) lies in m_A D,
   since α is local. Hence D/m_A D → B/m_A B is injective.
3. Its kernel is zero; exactness and the injection from K/m_A K therefore force
   K/m_A K = 0. This means K = m_A K as A-submodules, equivalently
   K = (m_A D)K as D-submodules. In particular K ≤ (m_A D)K as asserted.
   Finiteness, Noetherianity, completeness, and formal smoothness are not used.
-/
theorem finite_coefficient_tensor_kernel_reduction
    {A₀ : Type u} {A : Type v} {B : Type w} {C : Type z}
    [CommRing A₀] [CommRing A] [CommRing B] [CommRing C]
    [Algebra A₀ A] [Algebra A₀ C]
    [IsLocalRing A₀] [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
    (α : A₀ →+* A) (hα : algebraMap A₀ A = α) [IsLocalHom α]
    (hres : Function.Bijective (IsLocalRing.ResidueField.map α))
    (γ : A₀ →+* C) (hγ : algebraMap A₀ C = γ) [IsLocalHom γ]
    (φ : A →+* B) [IsLocalHom φ]
    (ψ : C →+* B) [IsLocalHom ψ] (hψγ : ψ.comp γ = φ.comp α)
    (F : TensorProduct A₀ C A →+* B)
    (hF : ∀ c a, F (TensorProduct.tmul A₀ c a) = ψ c * φ a)
    (hflat : RingHom.Flat φ) (hsurj : Function.Surjective F)
    (hker : RingHom.ker
      ((Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A).map φ)).comp ψ) =
      (IsLocalRing.maximalIdeal A₀).map γ) :
    (RingHom.ker F : Submodule (TensorProduct A₀ C A) (TensorProduct A₀ C A)) ≤
      ((IsLocalRing.maximalIdeal A).map
        (Algebra.TensorProduct.includeRight (R := A₀) (A := C)).toRingHom) •
      (RingHom.ker F : Submodule (TensorProduct A₀ C A) (TensorProduct A₀ C A)) := by
  intro x hx
  have hq := finite_coefficient_tensor_kernel_reduction_quotient α hα hres γ hγ φ ψ hψγ F hF
    hflat hsurj hker x hx
  exact (Submodule.Quotient.mk_eq_zero _).mp hq

end RingHom
