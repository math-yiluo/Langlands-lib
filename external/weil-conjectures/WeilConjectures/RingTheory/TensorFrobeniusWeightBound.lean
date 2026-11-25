/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Weights
public import Mathlib.LinearAlgebra.TensorProduct.Basic
import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Tensor products add Frobenius weight bounds

Source: latest blueprint, sec-purity-real-sheaves/sk-p-real-semi/sk-p-real-semi.proof.md,
last paragraph: tensor powers have the multiplied punctual weight bound.
(blueprint: lem-wf-tensor-frobenius-weight-bound).
-/

@[expose] public section
set_option autoImplicit false

open AlgebraicGeometry

namespace LinearMap

variable {K V W : Type*} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]

omit [IsAlgClosed K] [FiniteDimensional K V] in
private theorem eigenvalue_ne_zero_of_bijective (f : V →ₗ[K] V) (hf : Function.Bijective f)
    {α : K} (hα : Module.End.HasEigenvalue f α) : α ≠ 0 := by
  obtain ⟨v, hv, hv0⟩ := hα.exists_hasEigenvector
  intro h
  apply hv0
  apply hf.injective
  simpa [h] using Module.End.mem_eigenspace_iff.mp hv

/-- Factor the tensor characteristic polynomial into products of eigenvalues, then use
logarithmic additivity for the two nonzero factors of each eigenvalue.
Source: latest blueprint, sk-p-real-semi.proof.md, tensor-power weight assertion
(blueprint: lem-wf-tensor-frobenius-weight-bound). -/
theorem tensor_frobeniusWeight_le
    (ι : K →+* ℂ) (q : ℕ) (f : V →ₗ[K] V) (g : W →ₗ[K] W)
    (hf : Function.Bijective f) (hg : Function.Bijective g) (a b : ℝ)
    (ha : ∀ α, Module.End.HasEigenvalue f α → WeilGroup.frobeniusWeight ι q α ≤ a)
    (hb : ∀ β, Module.End.HasEigenvalue g β → WeilGroup.frobeniusWeight ι q β ≤ b)
    (γ : K) (hγ : Module.End.HasEigenvalue (TensorProduct.map f g) γ) :
    WeilGroup.frobeniusWeight ι q γ ≤ a + b := by
  have hroot : γ ∈ (TensorProduct.map f g).charpoly.roots :=
    (Polynomial.mem_roots (LinearMap.charpoly_monic _).ne_zero).mpr
      ((Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mp hγ)
  rw [charpoly_roots_tensorProduct] at hroot
  obtain ⟨⟨α, β⟩, hαβ, rfl⟩ := Multiset.mem_map.mp hroot
  obtain ⟨hα, hβ⟩ := Multiset.mem_product.mp hαβ
  have heα : Module.End.HasEigenvalue f α :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr
      ((Polynomial.mem_roots f.charpoly_monic.ne_zero).mp hα)
  have heβ : Module.End.HasEigenvalue g β :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr
      ((Polynomial.mem_roots g.charpoly_monic.ne_zero).mp hβ)
  have hα0 := eigenvalue_ne_zero_of_bijective f hf heα
  have hβ0 := eigenvalue_ne_zero_of_bijective g hg heβ
  have hmul : WeilGroup.frobeniusWeight ι q (α * β) =
      WeilGroup.frobeniusWeight ι q α + WeilGroup.frobeniusWeight ι q β := by
    have hια : ‖ι α‖ ≠ 0 := by simpa using hα0
    have hιβ : ‖ι β‖ ≠ 0 := by simpa using hβ0
    simp only [WeilGroup.frobeniusWeight, map_mul, norm_mul, Real.log_mul hια hιβ]
    ring
  rw [hmul]
  exact add_le_add (ha α heα) (hb β heβ)

end LinearMap
