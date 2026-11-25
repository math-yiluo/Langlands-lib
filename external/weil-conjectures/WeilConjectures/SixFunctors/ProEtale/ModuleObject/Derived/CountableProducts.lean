/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsExistence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarCoproducts

/-!

# Countable products in the derived categories of module objects

The derived category of module objects over a condensed coefficient ring on `X_proét` has
countable products (`ProEtale.CondensedRing.hasCountableProducts_derivedCategory_mod`): countable
products of module objects are exact (`ProEtale.CondensedRing.countableAB4Star_mod`), and
`CategoryTheory.derivedCategory_hasCountableProducts` applies.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (X : Scheme.{u}) (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
  [IsCommMonObj Λ]

/-- The derived category of module objects over a condensed coefficient ring on `X_proét` has
countable products: countable products of module objects are exact. -/
instance hasCountableProducts_derivedCategory_mod :
    HasCountableProducts (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :=
  derivedCategory_hasCountableProducts _

end AlgebraicGeometry.ProEtale.CondensedRing
