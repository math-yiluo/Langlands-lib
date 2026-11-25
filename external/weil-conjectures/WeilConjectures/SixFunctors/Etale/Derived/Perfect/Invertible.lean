/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Shift

/-!
# Dualizable and invertible étale complexes

Tensor products of dualizable complexes are dualizable, invertible complexes are dualizable,
and shifts of invertible complexes are invertible.

## Main statements

- `AlgebraicGeometry.Etale.DerivedCategory.isDualizable_derivedTensor`
- `AlgebraicGeometry.Etale.DerivedCategory.isDualizable_of_isInvertible`
- `AlgebraicGeometry.Etale.DerivedCategory.isInvertible_shift`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable (X : Scheme.{u})

namespace Etale.DerivedCategory

variable {A X}

/-- The derived tensor product of two dualizable complexes is dualizable. -/
theorem isDualizable_derivedTensor
    {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (hK : IsDualizable K)
    (hM : IsDualizable M) : IsDualizable (((derivedTensor A X).obj K).obj M) :=
  hK.tensorObj hM

/-- An invertible complex is dualizable. -/
theorem isDualizable_of_isInvertible
    {T : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (hT : IsInvertible T) :
    IsDualizable T :=
  hT.isDualizable

/-- A shift of an invertible complex is invertible: `T⟦n⟧ ⊗ᴸ M⟦-n⟧ ≅ (T ⊗ᴸ M)⟦0⟧ ≅ Λ_X`, and
symmetrically, for a tensor inverse `M` of `T`. -/
theorem isInvertible_shift
    {T : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (hT : IsInvertible T) (n : ℤ) :
    IsInvertible (T⟦n⟧) := by
  obtain ⟨M, ⟨e⟩, ⟨e'⟩⟩ := hT
  exact ⟨M⟦-n⟧, ⟨derivedTensorShiftIso A T M n (-n) ≪≫ (shiftFunctor _ (n + -n)).mapIso e ≪≫
    (shiftFunctorZero' _ (n + -n) (by simp)).app _⟩,
    ⟨derivedTensorShiftIso A M T (-n) n ≪≫ (shiftFunctor _ (-n + n)).mapIso e' ≪≫
    (shiftFunctorZero' _ (-n + n) (by simp)).app _⟩⟩

end Etale.DerivedCategory

end AlgebraicGeometry
