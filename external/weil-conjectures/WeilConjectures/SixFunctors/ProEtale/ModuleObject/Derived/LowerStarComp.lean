/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

/-!
# The composition isomorphism of derived pushforwards

For morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of schemes, the derived pushforwards of pro-étale
module objects satisfy `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*`
(`ProEtale.CondensedRing.rightDerivedLowerStarComp`), the conjugate of the composition isomorphism
`L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` of the derived pullbacks.

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The composition isomorphism `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*` of derived pushforwards, conjugate to
the composition isomorphism of derived pullbacks. -/
noncomputable abbrev rightDerivedLowerStarComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    R((f)_*⟦Λ⟧) ⋙ R((g)_*⟦Λ⟧) ≅ R((f ≫ g)_*⟦Λ⟧) :=
  conjugateIsoEquiv ((derivedUpperStarLowerStarAdjunction Λ g).comp
    (derivedUpperStarLowerStarAdjunction Λ f)) (derivedUpperStarLowerStarAdjunction Λ (f ≫ g))
    (leftDerivedUpperStarComp Λ f g)

end AlgebraicGeometry.ProEtale.CondensedRing
