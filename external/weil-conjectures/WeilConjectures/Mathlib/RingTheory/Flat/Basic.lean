/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.Flat.Basic

/-!
# Products of flat modules

The product `M × N` of two flat modules is flat: tensoring with it is the product of tensoring
with `M` and with `N` (`TensorProduct.prodRight`). A finite product of flat modules is flat.
-/

@[expose] public section

universe u v w

namespace Module.Flat

variable {R : Type u} {M : Type v} {N : Type w} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- The product of two flat modules is flat. -/
instance prod [Flat R M] [Flat R N] : Flat R (M × N) := by
  rw [iff_rTensor_preserves_injective_linearMap]
  intro P P' _ _ _ _ f hf
  have h : (TensorProduct.prodRight R R P' M N).toLinearMap ∘ₗ f.rTensor (M × N) =
      ((f.rTensor M).prodMap (f.rTensor N)) ∘ₗ (TensorProduct.prodRight R R P M N).toLinearMap :=
    TensorProduct.ext' fun p x ↦ by simp
  have hinj : Function.Injective ((f.rTensor M).prodMap (f.rTensor N)) :=
    Prod.map_injective.2 ⟨rTensor_preserves_injective_linearMap f hf,
      rTensor_preserves_injective_linearMap f hf⟩
  have := congrArg DFunLike.coe h
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe] at this
  rw [← (TensorProduct.prodRight R R P' M N).injective.of_comp_iff, this]
  exact hinj.comp (TensorProduct.prodRight R R P M N).injective

/-- A finite product of flat modules is flat. -/
instance pi {ι : Type*} [Finite ι] (P : ι → Type*) [∀ i, AddCommGroup (P i)]
    [∀ i, Module R (P i)] [∀ i, Flat R (P i)] : Flat R (∀ i, P i) := by
  classical
  have := Fintype.ofFinite ι
  exact of_linearEquiv (DirectSum.linearEquivFunOnFintype R ι P).symm

end Module.Flat
