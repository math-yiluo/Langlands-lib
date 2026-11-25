/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Injectivity on the closed fibre of the coefficient tensor map

Source: Stacks Project, Remark 07NS (4), the closed-fibre isomorphism.
(blueprint: lem-weil-pbc-finite-coefficient-tensor-kernel-closed-fiber)
-/

@[expose] public section

universe u v w z

/-- The tensor-map kernel is contained in the extended maximal ideal, without flatness.
Source: Stacks Project, Remark 07NS (4), the closed-fibre calculation preceding flatness.
(blueprint: lem-weil-pbc-finite-coefficient-tensor-kernel-closed-fiber)

Proof: put D = C ⊗[A₀] A and L = m_A D. For every a in A, surjectivity on
residue fields supplies a₀ in A₀ such that a - α(a₀) lies in m_A. Balancing
then gives c ⊗ a = c γ(a₀) ⊗ 1 modulo L. Tensor induction shows every x in D
is congruent to c ⊗ 1 for some c in C. The tensor formula implies F(L) ⊆ m_A B.
If F(x) = 0, therefore ψ(c) lies in m_A B. The kernel equality gives c ∈ m₀ C.
For each generator γ(r)c' with r ∈ m₀, balancing writes γ(r)c' ⊗ 1 as
c' ⊗ α(r), which lies in L because α is local. Additivity proves c ⊗ 1 ∈ L;
combining this with x - c ⊗ 1 ∈ L gives x ∈ L. Neither flatness nor
surjectivity of F is used.
-/
theorem RingHom.finite_coefficient_tensor_kernel_closed_fiber
    {A₀ : Type u} {A : Type v} {B : Type w} {C : Type z}
    [CommRing A₀] [CommRing A] [CommRing B] [CommRing C]
    [Algebra A₀ A] [Algebra A₀ C]
    [IsLocalRing A₀] [IsLocalRing A]
    (α : A₀ →+* A) (hα : algebraMap A₀ A = α) [IsLocalHom α]
    (hres : Function.Surjective (IsLocalRing.ResidueField.map α))
    (γ : A₀ →+* C) (hγ : algebraMap A₀ C = γ)
    (φ : A →+* B)
    (ψ : C →+* B)
    (F : TensorProduct A₀ C A →+* B)
    (hF : ∀ c a, F (TensorProduct.tmul A₀ c a) = ψ c * φ a)
    (hker : RingHom.ker
      ((Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A).map φ)).comp ψ) =
      (IsLocalRing.maximalIdeal A₀).map γ) :
    RingHom.ker F ≤ (IsLocalRing.maximalIdeal A).map
      (Algebra.TensorProduct.includeRight (R := A₀) (A := C)).toRingHom := by
  let D := TensorProduct A₀ C A
  let i : A →+* D := (Algebra.TensorProduct.includeRight (R := A₀) (A := C)).toRingHom
  let j : C →+* D := (Algebra.TensorProduct.includeLeft : C →ₐ[A₀] TensorProduct A₀ C A).toRingHom
  let L := (IsLocalRing.maximalIdeal A).map i
  let J := (IsLocalRing.maximalIdeal A).map φ
  have hbalance (c : C) (r : A₀) : j (c * γ r) = TensorProduct.tmul A₀ c (α r) := by
    change (c * γ r) ⊗ₜ[A₀] (1 : A) = c ⊗ₜ[A₀] α r
    rw [← hγ, ← hα, mul_comm c]
    simpa only [Algebra.smul_def, mul_one] using
      (TensorProduct.smul_tmul r c (1 : A))
  have hFL : L ≤ J.comap F := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change F (TensorProduct.tmul A₀ 1 a) ∈ J
    rw [hF, map_one, one_mul]
    exact Ideal.mem_map_of_mem φ ha
  have hCL : (IsLocalRing.maximalIdeal A₀).map γ ≤ L.comap j := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    change j (γ r) ∈ L
    have heq : j (γ r) = i (α r) := by
      change j (γ r) = (1 : C) ⊗ₜ[A₀] α r
      simpa only [one_mul] using hbalance 1 r
    rw [heq]
    exact Ideal.mem_map_of_mem i (map_nonunit α r hr)
  have happrox (a : A) : ∃ r : A₀, a - α r ∈ IsLocalRing.maximalIdeal A := by
    obtain ⟨rbar, hrbar⟩ := hres (IsLocalRing.residue A a)
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective rbar
    refine ⟨r, (IsLocalRing.residue_eq_zero_iff _).mp ?_⟩
    rw [map_sub, ← IsLocalRing.ResidueField.map_residue α, hrbar, sub_self]
  have hnormal (x : D) : ∃ c : C, x - j c ∈ L := by
    induction x using TensorProduct.inductionOn with
    | tmul c a =>
      obtain ⟨r, hr⟩ := happrox a
      refine ⟨c * γ r, ?_⟩
      rw [hbalance, ← TensorProduct.tmul_sub]
      have hm := L.mul_mem_left (j c) (Ideal.mem_map_of_mem i hr)
      change (c ⊗ₜ[A₀] (1 : A)) * ((1 : C) ⊗ₜ[A₀] (a - α r)) ∈ L at hm
      simpa only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] using hm
    | add x y hx hy =>
      obtain ⟨c, hc⟩ := hx
      obtain ⟨d, hd⟩ := hy
      refine ⟨c + d, ?_⟩
      simpa only [map_add, add_sub_add_comm] using L.add_mem hc hd
  intro x hx
  obtain ⟨c, hc⟩ := hnormal x
  have hcJ : ψ c ∈ J := by
    have hm := hFL hc
    change F (x - j c) ∈ J at hm
    have hx0 : F x = 0 := hx
    have hj : F (j c) = ψ c := by
      change F (c ⊗ₜ[A₀] (1 : A)) = ψ c
      simpa only [map_one, mul_one] using hF c 1
    rw [map_sub, hx0, zero_sub, hj] at hm
    simpa only [neg_neg] using J.neg_mem hm
  have hc0 : c ∈ (IsLocalRing.maximalIdeal A₀).map γ := by
    rw [← hker]
    change Ideal.Quotient.mk J (ψ c) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hcJ
  have hjc : j c ∈ L := hCL hc0
  have hm := L.add_mem hc hjc
  simpa only [sub_add_cancel] using hm
