/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Triple
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionEssImage

/-!

# The derived pushforward along an open immersion is fully faithful

Let `Λ` be a commutative condensed ring and `j : U ⟶ X` an open immersion. On the unbounded
derived categories of module objects over `Λ`, the derived pushforward `Rj_*` is fully faithful:
the counit `Lj^* Rj_* ⟶ 𝟭` is an isomorphism
(`ProEtale.CondensedRing.isIso_derivedUpperStarLowerStarAdjunction_counit_of_isOpenImmersion`).
Indeed `Lj^* ≅ D(j^*)` sits in an adjoint triple `D(j_!) ⊣ D(j^*) ⊣ Rj_*`, and the unit of the
first adjunction is invertible because `j_!` is fully faithful on module objects.

The versions on bounded constructible complexes are in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerStar`. This file does
not import `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, so
that the latter can use this statement.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- For an open immersion `j`, the derived pushforward `Rj_*` on module objects over `Λ` is fully
faithful: the counit `Lj^* Rj_* ⟶ 𝟭` is an isomorphism. In the adjoint triple
`D(j_!) ⊣ D(j^*) ⊣ Rj_*` the unit of the first adjunction is invertible, `j_!` being fully
faithful, hence so is the counit of the second. -/
instance isIso_derivedUpperStarLowerStarAdjunction_counit_of_isOpenImmersion {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (derivedUpperStarLowerStarAdjunction Λ j).counit := by
  let adj := (derivedUpperStarLowerStarAdjunction Λ j).ofNatIsoLeft
    (leftDerivedUpperStarIsoMapDerivedCategory Λ j)
  have : IsIso (openImmersionLowerShriekUpperStarAdjunction Λ j).unit := inferInstance
  have : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).unit :=
    Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
  have : IsIso adj.counit :=
    (Adjunction.Triple.mk (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j)
      adj).isIso_unit_iff_isIso_counit.1 this
  have hff := adj.fullyFaithfulROfIsIsoCounit
  have := hff.full
  have := hff.faithful
  exact (derivedUpperStarLowerStarAdjunction Λ j).counit_isIso_of_R_fully_faithful

end AlgebraicGeometry.ProEtale.CondensedRing
