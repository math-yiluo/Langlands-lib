/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Hilbert 90 for the Amitsur complex of a field extension

Let `L` be a field extension of a field `K`. A unit `u` of `L ⊗_K L` is an *Amitsur
`1`-cocycle* if `u₁₃ = u₁₂ u₂₃` in `L ⊗_K L ⊗_K L`, where `uᵢⱼ` puts the two factors of `u` in
the slots `i` and `j` and `1` in the remaining slot. Every such cocycle is a coboundary:
`u = (1 ⊗ v) (v ⊗ 1)⁻¹` for a unit `v` of `L`. This is the descent of the invertible module
`L` along `K → L`, i.e. Čech `H¹` of `𝔾ₘ` for the covering `Spec L → Spec K`.

The proof avoids descent theory: for a `K`-linear form `λ` on `L`, contracting the third slot
of the cocycle identity for `u⁻¹` with `λ` produces an element `m = (id ⊗ λ)(u⁻¹)` of `L` with
`1 ⊗ m = (m ⊗ 1) u`, and `λ` can be chosen so that `m ≠ 0`; as `L` is a field, `m` is a unit.

## Main statements

- `Algebra.TensorProduct.exists_eq_of_cocycle`: an Amitsur `1`-cocycle in `(L ⊗_K L)ˣ` is a
  coboundary.
-/

@[expose] public section

open scoped TensorProduct

namespace Algebra.TensorProduct

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Contracting the third slot of `L ⊗_K (L ⊗_K L)` with a linear form `f`. -/
private noncomputable def contract3 (f : L →ₗ[K] K) : L ⊗[K] (L ⊗[K] L) →ₗ[K] L ⊗[K] L :=
  _root_.TensorProduct.map LinearMap.id
    ((_root_.TensorProduct.rid K L).toLinearMap ∘ₗ LinearMap.lTensor L f)

/-- `contract3 f` sends `x₂₃` to `1 ⊗ (id ⊗ f)(x)`. -/
private lemma contract3_includeRight (f : L →ₗ[K] K) (x : L ⊗[K] L) :
    contract3 f (includeRight x) =
      1 ⊗ₜ ((_root_.TensorProduct.rid K L) (LinearMap.lTensor L f x)) := by
  simp [contract3]

/-- `contract3 f` sends `x₁₃` to `(id ⊗ f)(x) ⊗ 1`. -/
private lemma contract3_map_includeRight (f : L →ₗ[K] K) (x : L ⊗[K] L) :
    contract3 f (map (AlgHom.id K L) (includeRight : L →ₐ[K] L ⊗[K] L) x) =
      ((_root_.TensorProduct.rid K L) (LinearMap.lTensor L f x)) ⊗ₜ 1 := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => simp [contract3, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  | add x y hx hy => simp only [map_add, hx, hy, TensorProduct.add_tmul]

/-- `contract3 f` commutes with right multiplication by `x₁₂`, acting on the target by `x`. -/
private lemma contract3_mul_map_includeLeft (f : L →ₗ[K] K) (y : L ⊗[K] (L ⊗[K] L))
    (x : L ⊗[K] L) :
    contract3 f (y * map (AlgHom.id K L) (includeLeft : L →ₐ[K] L ⊗[K] L) x) =
      contract3 f y * x := by
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    induction y using TensorProduct.inductionOn with
    | tmul c z =>
      induction z using TensorProduct.inductionOn with
      | tmul e g =>
        simp [contract3, TensorProduct.tmul_smul, TensorProduct.smul_tmul', mul_comm]
      | add z w hz hw => simp only [TensorProduct.tmul_add, add_mul, map_add, hz, hw]
    | add y w hy hw => simp only [add_mul, map_add, hy, hw]
  | add x w hx hw => simp only [mul_add, map_add, hx, hw]

/-- Coordinates of `equivFinsuppOfBasisRight b` are contractions with `b.coord i`. -/
private lemma equivFinsuppOfBasisRight_apply_eq_rid_lTensor {ι : Type*} [DecidableEq ι]
    (b : Module.Basis ι K L) (x : L ⊗[K] L) (i : ι) :
    _root_.TensorProduct.equivFinsuppOfBasisRight b x i =
      _root_.TensorProduct.rid K L (LinearMap.lTensor L (b.coord i) x) := by
  induction x using _root_.TensorProduct.inductionOn with
  | tmul a c => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

/-- A nonzero element of `L ⊗_K L` has a nonzero contraction of its second slot with some
linear form. -/
private lemma exists_rid_lTensor_ne_zero {x : L ⊗[K] L} (hx : x ≠ 0) :
    ∃ f : L →ₗ[K] K, _root_.TensorProduct.rid K L (LinearMap.lTensor L f x) ≠ 0 := by
  classical
  let b := Module.Basis.ofVectorSpace K L
  by_contra! h
  refine hx ((_root_.TensorProduct.equivFinsuppOfBasisRight b).map_eq_zero_iff.mp ?_)
  ext i
  rw [equivFinsuppOfBasisRight_apply_eq_rid_lTensor, h, Finsupp.zero_apply]

/-- **Hilbert 90 for the Amitsur complex.** Let `L` be a field extension of a field `K` and let
`u` be a unit of `L ⊗_K L` satisfying the cocycle identity `u₁₃ = u₁₂ u₂₃` in
`L ⊗_K (L ⊗_K L)`. Then `u = (1 ⊗ v) (v ⊗ 1)⁻¹` for a unit `v` of `L`.

This is the algebraic core of Hilbert 90 for the spectrum of a field.
(blueprint: `lemma-cohomology-multiplicative-group--3`, descent step, for `X = Spec K` and the
covering `Spec L → Spec K`) -/
theorem exists_eq_of_cocycle (u : (L ⊗[K] L)ˣ)
    (hu : map (AlgHom.id K L) (includeRight : L →ₐ[K] L ⊗[K] L) (u : L ⊗[K] L) =
      map (AlgHom.id K L) (includeLeft : L →ₐ[K] L ⊗[K] L) (u : L ⊗[K] L) *
        (includeRight : L ⊗[K] L →ₐ[K] L ⊗[K] (L ⊗[K] L)) (u : L ⊗[K] L)) :
    ∃ v : Lˣ, (u : L ⊗[K] L) =
      (includeRight : L →ₐ[K] L ⊗[K] L) (v : L) *
        (includeLeft : L →ₐ[K] L ⊗[K] L) ((v⁻¹ : Lˣ) : L) := by
  have hinv : (includeRight : L ⊗[K] L →ₐ[K] L ⊗[K] (L ⊗[K] L)) (u⁻¹ : (L ⊗[K] L)ˣ) =
      map (AlgHom.id K L) (includeRight : L →ₐ[K] L ⊗[K] L) (u⁻¹ : (L ⊗[K] L)ˣ) *
        map (AlgHom.id K L) (includeLeft : L →ₐ[K] L ⊗[K] L) (u : L ⊗[K] L) := by
    rw [← (u.isUnit.map (includeRight : L ⊗[K] L →ₐ[K] L ⊗[K] (L ⊗[K] L))).mul_left_inj,
      ← map_mul, Units.inv_mul, map_one, mul_assoc, ← hu, ← map_mul, Units.inv_mul, map_one]
  have hne : ((u⁻¹ : (L ⊗[K] L)ˣ) : L ⊗[K] L) ≠ 0 := by
    intro h
    have h1 := congrArg (lmul' K (S := L)) u.mul_inv
    rw [h, mul_zero, map_zero, map_one] at h1
    exact zero_ne_one h1
  obtain ⟨f, hf⟩ := exists_rid_lTensor_ne_zero hne
  have key := congrArg (contract3 f) hinv
  rw [contract3_includeRight, contract3_mul_map_includeLeft, contract3_map_includeRight] at key
  refine ⟨Units.mk0 _ hf, ?_⟩
  rw [Units.val_mk0, includeRight_apply, key, includeLeft_apply, mul_comm, ← mul_assoc,
    tmul_mul_tmul, Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_cancel₀ hf, mul_one,
    ← one_def, one_mul]

end Algebra.TensorProduct
