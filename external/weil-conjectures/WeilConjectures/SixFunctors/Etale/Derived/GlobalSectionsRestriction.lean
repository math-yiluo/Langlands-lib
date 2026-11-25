/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections

/-!
# Restriction maps on derived global sections

For a morphism of schemes `f : X' ⟶ X` and `K ∈ D(X_ét, Λ)`, the *restriction map*
`RΓ(X, K) ⟶ RΓ(X', Lf^* K)` is the derived global sections of the unit `K ⟶ Rf_* Lf^* K` of the
derived adjunction `Lf^* ⊣ Rf_*`, followed by the Leray identification
`RΓ(X, Rf_* -) ≅ RΓ(X', -)`.

## Main definitions

- `AlgebraicGeometry.Etale.derivedGlobalSectionsRestriction`: the restriction map.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The *restriction map* `RΓ(X, K) ⟶ RΓ(X', Lf^* K)` along a morphism `f : X' ⟶ X`: the
derived global sections of the unit `K ⟶ Rf_* Lf^* K` of the derived adjunction, followed by
the Leray identification `RΓ(X, Rf_* -) ≅ RΓ(X', -)`. -/
noncomputable def derivedGlobalSectionsRestriction {X X' : Scheme.{u}} (f : X' ⟶ X)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj K ⟶
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X').obj
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K) :=
  (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app K) ≫
    (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso (ModuleCat.{u + 1} Λ) f).hom.app _

end AlgebraicGeometry.Etale
