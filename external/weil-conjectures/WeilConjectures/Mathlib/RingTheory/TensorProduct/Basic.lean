/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Generators of a tensor product of algebras

## Main results

- `Algebra.TensorProduct.closure_range_tmul_eq_top` — if `A` is generated as a ring by a family
  `a` containing `1` and `B` is generated as a ring by a family `b` containing `1`, then
  `A ⊗[R] B` is generated as a ring by the products `a i ⊗ₜ b j`.
-/

@[expose] public section

open scoped TensorProduct

namespace Algebra.TensorProduct

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- If the family `a` generates `A` as a ring and the family `b` generates `B` as a ring, and
both families take the value `1`, then the elementary tensors `a i ⊗ₜ b j` generate `A ⊗[R] B`
as a ring. -/
theorem closure_range_tmul_eq_top {ιA ιB : Type*} {a : ιA → A} {b : ιB → B}
    (ha : Subring.closure (Set.range a) = ⊤) (hb : Subring.closure (Set.range b) = ⊤)
    {ra : ιA} (hra : a ra = 1) {rb : ιB} (hrb : b rb = 1) :
    Subring.closure (Set.range fun p : ιA × ιB ↦ a p.1 ⊗ₜ[R] b p.2) = ⊤ := by
  set S := Subring.closure (Set.range fun p : ιA × ιB ↦ a p.1 ⊗ₜ[R] b p.2) with hS
  have hleft : ∀ x : A, x ⊗ₜ[R] (1 : B) ∈ S := by
    intro x
    have hx : x ⊗ₜ[R] (1 : B) ∈ Subring.map (includeLeftRingHom (R := R) (A := A) (B := B))
        (Subring.closure (Set.range a)) := by
      rw [ha]
      exact ⟨x, trivial, rfl⟩
    rw [RingHom.map_closure] at hx
    refine Subring.closure_le.mpr ?_ hx
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact Subring.subset_closure ⟨(i, rb), by simp [hrb]⟩
  have hright : ∀ y : B, (1 : A) ⊗ₜ[R] y ∈ S := by
    intro y
    have hy : (1 : A) ⊗ₜ[R] y ∈ Subring.map
        (includeRight (R := R) (A := A) (B := B)).toRingHom (Subring.closure (Set.range b)) := by
      rw [hb]
      exact ⟨y, trivial, rfl⟩
    rw [RingHom.map_closure] at hy
    refine Subring.closure_le.mpr ?_ hy
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact Subring.subset_closure ⟨(ra, i), by simp [hra]⟩
  have key : ∀ z : A ⊗[R] B, z ∈ S := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
        have hxy : x ⊗ₜ[R] y = (x ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] y) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul]; simp
        rw [hxy]
        exact mul_mem (hleft x) (hright y)
    | add x y hx hy => exact add_mem hx hy
  exact le_antisymm le_top fun z _ ↦ key z

end Algebra.TensorProduct
