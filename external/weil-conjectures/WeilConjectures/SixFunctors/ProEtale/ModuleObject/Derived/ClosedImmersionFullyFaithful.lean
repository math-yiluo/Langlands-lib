/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.ClosedImmersion

/-!

# Full faithfulness of `Ri_*` on the ambient derived categories of module objects

Let `Λ` be a commutative condensed ring and `i : Z ⟶ X` a closed immersion. The derived
pushforward `Ri_*` is fully faithful, i.e. the counit `Li^* Ri_* ⟶ 𝟭` is an isomorphism, on
`D(Mod_{Λ_Z})`
(`ProEtale.CondensedRing.isIso_derivedUpperStarLowerStarAdjunction_counit_of_isClosedImmersion`).

The pushforward `i_*` on module objects is fully faithful
(`ProEtale.CondensedRing.fullyFaithfulLowerStarOfIsClosedImmersion`) and preserves K-injective
complexes, being right adjoint to the exact functor `i^*`, so its right derived functor is fully
faithful (`CategoryTheory.Functor.full_rightDerivedFunctor`).

The version on bounded constructible complexes is in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersion`. This file does not
import `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, so that
the latter can use this statement.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

instance : ((i)_*⟦Λ⟧).PreservesKInjectiveComplexes :=
  (upperStarLowerStarAdjunction Λ i).preservesKInjectiveComplexes

/-- The derived pushforward `Ri_*` along a closed immersion is fully faithful on module objects
over `Λ`: the counit `Li^* Ri_* ⟶ 𝟭` is an isomorphism. -/
instance isIso_derivedUpperStarLowerStarAdjunction_counit_of_isClosedImmersion :
    IsIso (derivedUpperStarLowerStarAdjunction Λ i).counit :=
  (derivedUpperStarLowerStarAdjunction Λ i).counit_isIso_of_R_fully_faithful

end AlgebraicGeometry.ProEtale.CondensedRing
