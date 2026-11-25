/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Finite.Exact

/-!

# Cohomology of a finite pushforward

For a finite morphism `π : X ⟶ Y` the pushforward `π_*` on étale sheaves is exact, so its
right derived functor is `π_*` applied levelwise
(`AlgebraicGeometry.Etale.rightDerivedFunctorLowerStarIsoMapDerivedCategory`), and the Leray
isomorphism `RΓ(Y, Rπ_* K) ≅ RΓ(X, K)` becomes `RΓ(Y, π_* K) ≅ RΓ(X, K)`: in every degree
`H^q(Y, π_* F) ≅ H^q(X, F)`.

## Main definitions

- `AlgebraicGeometry.Etale.mapDerivedCategoryLowerStarCompRightDerivedGlobalSectionsIso`: the
  isomorphism `D(π_*) ⋙ RΓ_Y ≅ RΓ_X` for a finite `π`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (π : X ⟶ Y) [IsFinite π]

/-- **Cohomology of a finite pushforward.** For a finite morphism `π : X ⟶ Y`, the derived
global sections of `π_* K` are those of `K`: `RΓ(Y, π_* K) ≅ RΓ(X, K)`, so that
`H^q(Y, π_* F) ≅ H^q(X, F)` for every étale sheaf `F` of `Λ`-modules on `X` and every `q`. The
pushforward `π_*` is exact, so the Grothendieck spectral sequence of `Γ_Y ∘ π_*` degenerates:
this is the Leray isomorphism
`AlgebraicGeometry.Etale.rightDerivedLowerStarCompRightDerivedGlobalSectionsIso` with
`Rπ_* = π_*` (`AlgebraicGeometry.Etale.rightDerivedFunctorLowerStarIsoMapDerivedCategory`).
(blueprint: `lemma-finite-morphisms-cohomology--2`) -/
noncomputable def mapDerivedCategoryLowerStarCompRightDerivedGlobalSectionsIso :
    ((π)_*[ModuleCat.{u + 1} Λ]).mapDerivedCategory ⋙
        rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y ≅
      rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X :=
  Functor.isoWhiskerRight
      (Etale.rightDerivedFunctorLowerStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) π).symm _ ≪≫
    rightDerivedLowerStarCompRightDerivedGlobalSectionsIso (ModuleCat.{u + 1} Λ) π

end AlgebraicGeometry.Etale
