/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Flat.Stability

/-!
# Flatness of a tensor product over an intermediate algebra

Let `S` be an `R`-algebra, `M` a flat `S`-module and `N` an `S`-module which is flat over `R`.
Then `M ⊗[S] N` is flat over `R`: tensoring over `R` with it is tensoring over `R` with `N`
followed by tensoring over `S` with `M`.
-/

@[expose] public section

universe u v w t

open TensorProduct

namespace Module.Flat

variable (R : Type u) (S : Type v) (M : Type w) (N : Type t) [CommRing R] [CommRing S]
  [Algebra R S] [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]
  [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- If `M` is a flat `S`-module and `N` an `S`-module flat over `R`, then `M ⊗[S] N` is flat over
`R`. -/
theorem tensorProduct_of_flat [Flat S M] [Flat R N] : Flat R (M ⊗[S] N) := by
  rw [Flat.iff_lTensor_injectiveₛ]
  intro P _ _ Q
  let e (P' : Type u) [AddCommMonoid P'] [Module R P'] :=
    AlgebraTensorModule.assoc R S S M N P'
  let g : N ⊗[R] Q →ₗ[S] N ⊗[R] P := AlgebraTensorModule.lTensor S N Q.subtype
  have key : (e P).toLinearMap.restrictScalars R ∘ₗ Q.subtype.lTensor (M ⊗[S] N) =
      (g.lTensor M).restrictScalars R ∘ₗ (e Q).toLinearMap.restrictScalars R := by
    refine LinearMap.ext fun x ↦ ?_
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]
    | tmul y q =>
      induction y using TensorProduct.inductionOn with
      | add y y' hy hy' =>
        simp only [LinearMap.coe_comp, Function.comp_apply, add_tmul, map_add] at hy hy' ⊢
        rw [hy, hy']
      | tmul m n => rfl
  have hinj : Function.Injective
      ((g.lTensor M).restrictScalars R ∘ₗ (e Q).toLinearMap.restrictScalars R) :=
    (Flat.lTensor_preserves_injective_linearMap g
      (Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective)).comp (e Q).injective
  rw [← key] at hinj
  intro a b hab
  exact hinj (by simp only [LinearMap.coe_comp, Function.comp_apply, hab])

end Module.Flat
