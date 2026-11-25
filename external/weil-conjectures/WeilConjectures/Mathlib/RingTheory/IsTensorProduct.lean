/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.IsTensorProduct

/-!
# Changing the base of a pushout square

If `B = A ⊗[R₀] B₀` and `A₁ → A` is a map of `R₀`-algebras, then `B = A ⊗[A₁] (A₁ ⊗[R₀] B₀)`.

## Main definitions and results

- `Algebra.IsPushout.tensorProductAlgebra`: the `A₁ ⊗[R₀] B₀`-algebra structure on `B`.
- `Algebra.IsPushout.tensorProduct`: the square `A₁ → A`, `A₁ ⊗[R₀] B₀ → B` is a pushout.
-/

@[expose] public section

open TensorProduct

namespace Algebra.IsPushout

variable (R₀ A₁ A B₀ B : Type*) [CommRing R₀] [CommRing A₁] [CommRing A] [CommRing B₀]
  [CommRing B] [Algebra R₀ A₁] [Algebra A₁ A] [Algebra R₀ A] [IsScalarTower R₀ A₁ A]
  [Algebra R₀ B₀] [Algebra A B] [Algebra B₀ B] [Algebra R₀ B] [IsScalarTower R₀ A B]
  [IsScalarTower R₀ B₀ B] [Algebra.IsPushout R₀ A B₀ B]

/-- If `B = A ⊗[R₀] B₀` and `A₁ → A` is a map of `R₀`-algebras, the `A₁ ⊗[R₀] B₀`-algebra
structure on `B` given by `A₁ ⊗[R₀] B₀ → A ⊗[R₀] B₀ ≅ B`. -/
noncomputable abbrev tensorProductAlgebra : Algebra (A₁ ⊗[R₀] B₀) B :=
  (((Algebra.IsPushout.equiv R₀ A B₀ B).toAlgHom.restrictScalars R₀).comp
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ A₁ A) (AlgHom.id R₀ B₀))).toAlgebra

lemma tensorProductAlgebra_algebraMap_tmul (a : A₁) (b : B₀) :
    letI := tensorProductAlgebra R₀ A₁ A B₀ B
    algebraMap (A₁ ⊗[R₀] B₀) B (a ⊗ₜ b) =
      algebraMap A B (algebraMap A₁ A a) * algebraMap B₀ B b := by
  simp [RingHom.algebraMap_toAlgebra, Algebra.IsPushout.equiv_tmul]

variable [Algebra A₁ B] [IsScalarTower A₁ A B]

lemma isScalarTower_tensorProductAlgebra :
    letI := tensorProductAlgebra R₀ A₁ A B₀ B
    IsScalarTower A₁ (A₁ ⊗[R₀] B₀) B := by
  let := tensorProductAlgebra R₀ A₁ A B₀ B
  refine .of_algebraMap_eq fun r ↦ ?_
  rw [Algebra.TensorProduct.algebraMap_apply, tensorProductAlgebra_algebraMap_tmul,
    Algebra.algebraMap_self, RingHom.id_apply, map_one, mul_one,
    ← IsScalarTower.algebraMap_apply]

/-- If `B = A ⊗[R₀] B₀` and `A₁ → A` is a map of `R₀`-algebras, then
`B = A ⊗[A₁] (A₁ ⊗[R₀] B₀)`. -/
theorem tensorProduct :
    letI := tensorProductAlgebra R₀ A₁ A B₀ B
    haveI := isScalarTower_tensorProductAlgebra R₀ A₁ A B₀ B
    Algebra.IsPushout A₁ A (A₁ ⊗[R₀] B₀) B := by
  let := tensorProductAlgebra R₀ A₁ A B₀ B
  have := isScalarTower_tensorProductAlgebra R₀ A₁ A B₀ B
  let : Algebra (A₁ ⊗[R₀] B₀) (A ⊗[A₁] (A₁ ⊗[R₀] B₀)) := Algebra.TensorProduct.rightAlgebra
  refine Algebra.IsPushout.of_equiv ((Algebra.TensorProduct.cancelBaseChange R₀ A₁ A A B₀).trans
    (Algebra.IsPushout.equiv R₀ A B₀ B)) (RingHom.ext fun x ↦ ?_)
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    simp [RingHom.algebraMap_toAlgebra, Algebra.IsPushout.equiv_tmul,
      Algebra.algebraMap_eq_smul_one]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end Algebra.IsPushout
