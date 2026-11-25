/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Unramified.Finite

/-!
# The diagonal of an unramified algebra over an intermediate ring

Let `R → P → A` be ring maps with `A` unramified and essentially of finite type over `P`. The
kernel of the multiplication `A ⊗[R] A → A` is, up to the idempotent of the diagonal of `A`
over `P`, the kernel of the projection `A ⊗[R] A → A ⊗[P] A`.

- `Algebra.TensorProduct.ker_mapOfCompatibleSMul_le`: the kernel of `A ⊗[R] A → A ⊗[P] A` lies
  in every ideal containing all `p ⊗ 1 - 1 ⊗ p` for `p : P`.
- `Algebra.FormallyUnramified.exists_lmul'_eq_one_mul_mem_ker`: there is `e : A ⊗[R] A` mapping
  to `1` in `A` such that `e` multiplies the kernel of `A ⊗[R] A → A` into the kernel of
  `A ⊗[R] A → A ⊗[P] A`.
-/

@[expose] public section

open TensorProduct

variable {R P A : Type*} [CommRing R] [CommRing P] [CommRing A] [Algebra R P] [Algebra P A]
  [Algebra R A] [IsScalarTower R P A]

namespace Algebra.TensorProduct

/-- The kernel of the canonical surjection `A ⊗[R] A → A ⊗[P] A` lies in every ideal `J`
containing the elements `p ⊗ 1 - 1 ⊗ p` for `p : P`: the quotient by `J` receives a map from
`A ⊗[P] A` inverting the surjection. -/
theorem ker_mapOfCompatibleSMul_le (J : Ideal (A ⊗[R] A))
    (hJ : ∀ p : P, algebraMap P A p ⊗ₜ[R] (1 : A) - 1 ⊗ₜ[R] algebraMap P A p ∈ J) :
    RingHom.ker (mapOfCompatibleSMul P R R A A) ≤ J := by
  let mk := Ideal.Quotient.mk J
  let : Algebra P (A ⊗[R] A ⧸ J) :=
    (mk.comp (includeLeftRingHom.comp (algebraMap P A))).toAlgebra
  let f₁ : A →ₐ[P] A ⊗[R] A ⧸ J :=
    { mk.comp includeLeftRingHom with commutes' := fun _ ↦ rfl }
  let f₂ : A →ₐ[P] A ⊗[R] A ⧸ J :=
    { mk.comp includeRight.toRingHom with
      commutes' := fun p ↦ ((Ideal.Quotient.eq).mpr (hJ p)).symm }
  let σ := productMap f₁ f₂
  have hσ (x : A ⊗[R] A) : σ (mapOfCompatibleSMul P R R A A x) = mk x := by
    induction x using TensorProduct.inductionOn with
    | tmul a b =>
      simp [σ, f₁, f₂, mk, ← map_mul]
    | add x y hx hy => simp only [map_add, hx, hy]
  intro x hx
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← hσ, RingHom.mem_ker.mp hx, map_zero]

end Algebra.TensorProduct

namespace Algebra.FormallyUnramified

/-- Let `A` be unramified and essentially of finite type over `P`, and `R → P`. Then there is
`e : A ⊗[R] A` with `e ↦ 1` under the multiplication `A ⊗[R] A → A` such that `e` multiplies
the kernel of the multiplication into the kernel of `A ⊗[R] A → A ⊗[P] A`: take for `e` a lift
of the idempotent of `A ⊗[P] A` cutting out the diagonal. -/
theorem exists_lmul'_eq_one_mul_mem_ker [FormallyUnramified P A] [EssFiniteType P A] :
    ∃ e : A ⊗[R] A, TensorProduct.lmul' R e = 1 ∧
      ∀ k ∈ RingHom.ker (TensorProduct.lmul' R (S := A)),
        e * k ∈ RingHom.ker (TensorProduct.mapOfCompatibleSMul P R R A A) := by
  obtain ⟨t, ht, ht₁⟩ := (iff_exists_tensorProduct (R := P) (S := A)).mp inferInstance
  obtain ⟨e, rfl⟩ := TensorProduct.mapOfCompatibleSMul_surjective P R R A A t
  have hlmul (x : A ⊗[R] A) :
      TensorProduct.lmul' P (TensorProduct.mapOfCompatibleSMul P R R A A x) =
        TensorProduct.lmul' R x := by
    induction x using TensorProduct.inductionOn with
    | tmul a b => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  refine ⟨e, by rwa [← hlmul], fun k hk ↦ ?_⟩
  have hk' : TensorProduct.mapOfCompatibleSMul P R R A A k ∈ KaehlerDifferential.ideal P A := by
    rw [KaehlerDifferential.ideal, RingHom.mem_ker, hlmul]
    exact hk
  rw [← KaehlerDifferential.span_range_eq_ideal] at hk'
  rw [RingHom.mem_ker, map_mul]
  generalize TensorProduct.mapOfCompatibleSMul P R R A A k = y at hk'
  induction hk' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    rw [mul_comm, ht]
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]
  | smul a x _ hx => rw [smul_eq_mul, mul_left_comm, hx, mul_zero]

end Algebra.FormallyUnramified
