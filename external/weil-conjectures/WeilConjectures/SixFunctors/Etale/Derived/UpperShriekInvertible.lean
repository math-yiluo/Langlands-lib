/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure

/-!
# Tensor products of invertible objects

The derived tensor product of two `⊗`-invertible objects of `D(X_ét)` is invertible. Together
with the stability of invertible objects under derived pullback
(`AlgebraicGeometry.Etale.DerivedCategory.isInvertible.leftDerivedUpperStar`), this is used in
the composition law for cohomologically smooth morphisms (`lem-pur-co-smooth-composition`).

## Main statements

- `AlgebraicGeometry.Etale.isInvertible_derivedTensor`
- `AlgebraicGeometry.Etale.DerivedCategory.isInvertible.derivedTensor`
-/

@[expose] public section

universe u' u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

namespace Etale

section General

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X : Scheme.{u}}

/-- The tensor product of two invertible objects of `D(X_ét)` is invertible. -/
theorem isInvertible_derivedTensor
    {L L' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hL : IsInvertible L) (hL' : IsInvertible L') : IsInvertible (L ⊗ L') := by
  obtain ⟨M, ⟨e₁⟩, ⟨e₂⟩⟩ := hL
  obtain ⟨M', ⟨e₁'⟩, ⟨e₂'⟩⟩ := hL'
  exact ⟨M' ⊗ M, ⟨α_ L L' (M' ⊗ M) ≪≫ whiskerLeftIso L ((α_ L' M' M).symm ≪≫
      whiskerRightIso e₁' M ≪≫ λ_ M) ≪≫ e₁⟩,
    ⟨α_ M' M (L ⊗ L') ≪≫ whiskerLeftIso M' ((α_ M L L').symm ≪≫
      whiskerRightIso e₂ L' ≪≫ λ_ L') ≪≫ e₂'⟩⟩

end General

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

/-- The derived tensor product of two invertible objects is invertible. -/
theorem DerivedCategory.isInvertible.derivedTensor
    {L L' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hL : DerivedCategory.isInvertible Λ X L) (hL' : DerivedCategory.isInvertible Λ X L') :
    DerivedCategory.isInvertible Λ X
      (((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj L).obj L') :=
  (isInvertible_iff_exists_derivedTensor _).1 (isInvertible_derivedTensor
    ((isInvertible_iff_exists_derivedTensor _).2 hL)
    ((isInvertible_iff_exists_derivedTensor _).2 hL'))

end Etale

end AlgebraicGeometry
