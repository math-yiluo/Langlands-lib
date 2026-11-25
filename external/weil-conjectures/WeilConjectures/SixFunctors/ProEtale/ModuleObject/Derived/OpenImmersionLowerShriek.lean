/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs

/-!

# The derived adjunction `j_! ⊣ j^*` along an open immersion, on module objects

This is the module-object counterpart of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek`, for
the coefficient ring objects `Λ_X = p_X^* Λ` of a commutative condensed ring `Λ`.

For an open immersion `j : U ⟶ X` both halves of the adjunction
`ProEtale.CondensedRing.openImmersionLowerShriekUpperStarAdjunction` on module objects are
*exact*: the extension by zero `j_!` by
`ProEtale.CondensedRing.preservesHomology_openImmersionLowerShriek`, and the pullback `j^*`
by `ProEtale.CondensedRing.preservesHomology_upperStar`, since the
coefficient morphism `α_j : j^* Λ_X ⟶ Λ_U` is an isomorphism. So each of them induces a
functor on derived categories by applying it levelwise, and the two levelwise functors are
again adjoint.

As in the finite-coefficient case the adjunction is obtained where the derived formalism
provides it, namely between the *total* derived functors
(`Adjunction.derivedAdjunction`), and exactness then identifies each total derived functor
with the corresponding levelwise functor; both steps are the general
`Adjunction.mapDerivedCategoryAdjunction` and `Adjunction.mapDerivedCategoryPlusAdjunction` of
`WeilConjectures.CategoryTheory.DerivedCategory.Adjunction`. In particular the derived pullback
`L((j)^*⟦Λ⟧)` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar` is,
for an open immersion, the levelwise functor `D((j)^*⟦Λ⟧)`
(`ProEtale.CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion`).

## Main results

- `ProEtale.CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion`:
  `L((j)^*⟦Λ⟧) ≅ D((j)^*⟦Λ⟧)` for an open immersion `j`.

- `ProEtale.CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction` and
  `ProEtale.CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus`: the
  derived adjunctions `D((j)_!open⟦Λ⟧) ⊣ D((j)^*⟦Λ⟧)` and `D+((j)_!open⟦Λ⟧) ⊣ D+((j)^*⟦Λ⟧)`.

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Abelian Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- For an open immersion `j : U ⟶ X`, the pullback `j^*` on module objects is exact, so its
total left derived functor `L((j)^*⟦Λ⟧)`, computed via K-flat resolutions, is canonically
isomorphic to the levelwise functor `D((j)^*⟦Λ⟧)`. -/
noncomputable def leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion :
    L((j)^*⟦Λ⟧) ≅ D((j)^*⟦Λ⟧) :=
  (j)^*⟦Λ⟧.leftDerivedFunctorIsoMapDerivedCategory

/-- The derived adjunction `j_! ⊣ j^*` along an open immersion `j : U ⟶ X` on the unbounded
derived categories of module objects over `Λ`: since both `j_!` and `j^*` are exact on
module objects, their total derived functors are the levelwise functors, and the adjunction
between the total left derived functor of `j_!` and the total right derived functor of `j^*`
becomes an adjunction between the levelwise functors. -/
noncomputable def derivedOpenImmersionLowerShriekUpperStarAdjunction :
    D((j)_!open⟦Λ⟧) ⊣ D((j)^*⟦Λ⟧) :=
  (openImmersionLowerShriekUpperStarAdjunction Λ j).mapDerivedCategoryAdjunction

/-- The bounded below version of
`ProEtale.CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction`: the derived
adjunction `j_! ⊣ j^*` along an open immersion on the bounded below derived categories of
module objects, obtained by restricting the unbounded one along the fully faithful inclusions,
which is legitimate since the exact functors `j_!` and `j^*` preserve bounded below objects. -/
noncomputable def derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus :
    D+((j)_!open⟦Λ⟧) ⊣ D+((j)^*⟦Λ⟧) :=
  (openImmersionLowerShriekUpperStarAdjunction Λ j).mapDerivedCategoryPlusAdjunction

instance : D((j)_!open⟦Λ⟧).IsLeftAdjoint :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).isLeftAdjoint

instance : D((j)^*⟦Λ⟧).IsRightAdjoint :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).isRightAdjoint

end AlgebraicGeometry.ProEtale.CondensedRing
