/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

/-!
# Derived pullback of invertible complexes

The derived pullback `Lf^*` is monoidal, so it sends a `⊗`-invertible object of `D(Y_ét, Λ)` to
a `⊗`-invertible object of `D(X_ét, Λ)`, with inverse the pullback of the inverse.

## Main statements

- `AlgebraicGeometry.Etale.DerivedCategory.isInvertible.leftDerivedUpperStar`
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] {X Y : Scheme.{u}}

/-- The derived pullback of an invertible object is invertible: if `B ⊗ᴸ M ≅ Λ_Y` and
`M ⊗ᴸ B ≅ Λ_Y`, then `Lf^* B ⊗ᴸ Lf^* M ≅ Lf^*(B ⊗ᴸ M) ≅ Lf^* Λ_Y ≅ Λ_X`, and symmetrically. -/
theorem DerivedCategory.isInvertible.leftDerivedUpperStar (f : X ⟶ Y)
    {B : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hB : DerivedCategory.isInvertible Λ Y B) :
    DerivedCategory.isInvertible Λ X ((L((f)^*[ModuleCat.{u + 1} Λ])).obj B) := by
  obtain ⟨M, ⟨e⟩, ⟨e'⟩⟩ := hB
  exact ⟨(L((f)^*[ModuleCat.{u + 1} Λ])).obj M,
    ⟨(leftDerivedUpperStarTensorIso _ f B M).symm ≪≫ (L((f)^*[ModuleCat.{u + 1} Λ])).mapIso e ≪≫
      leftDerivedUpperStarUnitIso _ f⟩,
    ⟨(leftDerivedUpperStarTensorIso _ f M B).symm ≪≫ (L((f)^*[ModuleCat.{u + 1} Λ])).mapIso e' ≪≫
      leftDerivedUpperStarUnitIso _ f⟩⟩

end Etale

end AlgebraicGeometry
