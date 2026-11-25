/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Bijectivity of a balanced map out of `O ⊗_R A` for `O` finite free

Let `O` be a finite free `R`-module with basis `(bⱼ)`, `A` an `R`-module and `μ : O × A → B` a
balanced biadditive map to an abelian group. The induced map `O ⊗_R A → B`
(`TensorProduct.liftOfBalanced`) is bijective as soon as there are additive maps `κⱼ : B → A`
with `∑ⱼ μ(bⱼ, κⱼ y) = y` and `κⱼ (μ(o, a)) = oⱼ a`
(`TensorProduct.bijective_liftOfBalanced`): `y ↦ ∑ⱼ bⱼ ⊗ κⱼ y` is an inverse.
-/

@[expose] public section

open TensorProduct

namespace TensorProduct

variable {R : Type*} [CommRing R] {O : Type*} [AddCommGroup O] [Module R O]
  {A : Type*} [AddCommGroup A] [Module R A] {B : Type*} [AddCommGroup B]
  {ι : Type*} [Fintype ι] (b : Module.Basis ι R O)
  (μ : O →+ A →+ B) (hμ : ∀ (r : R) (o : O) (a : A), μ (r • o) a = μ o (r • a))
  (κ : ι → B →+ A)

/-- The additive map `O ⊗_R A → B`, `o ⊗ a ↦ μ o a`, for a balanced biadditive `μ`. -/
noncomputable def liftOfBalanced : O ⊗[R] A →+ B :=
  TensorProduct.liftAddHom μ hμ

@[simp]
lemma liftOfBalanced_tmul (o : O) (a : A) : liftOfBalanced μ hμ (o ⊗ₜ a) = μ o a :=
  rfl

/-- **A balanced map out of `O ⊗_R A`, for `O` finite free, is bijective** as soon as there are
maps `κⱼ : B → A` with `∑ⱼ μ(bⱼ, κⱼ y) = y` and `κⱼ (μ(o, a)) = oⱼ a`, where `oⱼ` are the
coordinates of `o` in the basis `b`. -/
theorem bijective_liftOfBalanced (h₁ : ∀ y, ∑ j, μ (b j) (κ j y) = y)
    (h₂ : ∀ o a j, κ j (μ o a) = b.repr o j • a) :
    Function.Bijective (liftOfBalanced μ hμ) := by
  let inv : B →+ O ⊗[R] A :=
    ∑ j, (TensorProduct.mk R O A (b j)).toAddMonoidHom.comp (κ j)
  have hinv (y : B) : inv y = ∑ j, b j ⊗ₜ κ j y := by
    simp [inv]
  refine ⟨Function.LeftInverse.injective (g := inv) fun τ ↦ ?_,
    Function.RightInverse.surjective (g := inv) fun y ↦ ?_⟩
  · induction τ using TensorProduct.inductionOn with
    | add τ τ' hτ hτ' => rw [map_add, map_add, hτ, hτ']
    | tmul o a =>
      rw [hinv, liftOfBalanced_tmul]
      simp_rw [h₂, ← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul]
      congr 1
      conv_rhs => rw [← b.sum_repr o]
  · rw [hinv, map_sum]
    simp only [liftOfBalanced_tmul]
    exact h₁ y

end TensorProduct
