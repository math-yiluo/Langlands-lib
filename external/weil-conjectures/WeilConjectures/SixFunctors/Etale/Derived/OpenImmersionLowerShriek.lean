/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful

/-!
## The derived adjunction `j_! ⊣ j^*` along an open immersion

For an open immersion `j : U ⟶ X` both halves of the adjunction
`Etale.openImmersionLowerShriekUpperStarAdjunction` are *exact*: the extension by zero
`j_!` by `Etale.preservesFiniteLimits_openImmersionLowerShriek` together with its being a
left adjoint, and the pullback `j^*` by `Etale.preservesFiniteLimits_upperStar` together
with its being a left adjoint. So each of them induces a functor on derived categories by
applying it levelwise, and the two levelwise functors are again adjoint.

The adjunction is obtained where the derived formalism provides it, namely between the
*total* derived functors: `Adjunction.derivedAdjunction` gives
`(j_!).leftDerivedFunctor ⊣ (j^*).rightDerivedFunctor`, the left one computed by K-flat
resolutions and the right one by K-injective resolutions. Exactness then identifies each
with the corresponding levelwise functor
(`Functor.leftDerivedFunctorIsoMapDerivedCategory` and
`Functor.rightDerivedFunctorIsoMapDerivedCategory`), and the resulting adjunction on the
unbounded derived categories restricts along the fully faithful inclusions of the bounded
below ones. Both steps are the general
`Adjunction.mapDerivedCategoryAdjunction` and `Adjunction.mapDerivedCategoryPlusAdjunction`
of `WeilConjectures.CategoryTheory.DerivedCategory.Adjunction`.

In particular the K-flat and K-injective machinery, and with it the coefficient
hypotheses of the section `DerivedUpperStar`, are still needed even though the final
statement mentions only levelwise functors.

Since `j_!` is fully faithful, the unit of the derived adjunction is an isomorphism:
`Etale.isIso_derivedOpenImmersionLowerShriekUpperStarAdjunction_unit`.
-/

@[expose] public section

universe v'' u'' u' u

open CategoryTheory Abelian Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

open MonoidalCategory MonoidalClosed Etale

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/- The K-flat resolution package on the coefficient category `A`, as in the sections
`DerivedUpperStar` and `DerivedUpperLowerStarAdjunction`; it is what makes the total left
derived functor of `j_!` available. -/
variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The derived adjunction `j_! ⊣ j^*` along an open immersion `j : U ⟶ X` on the
unbounded derived categories of étale sheaves: since both `j_!` and `j^*` are exact, their
total derived functors are the levelwise functors, and the adjunction between the total
left derived functor of `j_!` and the total right derived functor of `j^*` becomes an
adjunction between the levelwise functors. -/
noncomputable def Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction :
    D((j)_!open[A]) ⊣ D((j)^*[A]) :=
  (Etale.openImmersionLowerShriekUpperStarAdjunction A j).mapDerivedCategoryAdjunction

/-- The unit of the derived adjunction `D(j_!) ⊣ D(j^*)` along an open immersion is an
isomorphism, i.e. `D(j^*) D(j_!) K ≅ K` naturally in `K`. -/
instance Etale.isIso_derivedOpenImmersionLowerShriekUpperStarAdjunction_unit :
    IsIso (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction A j).unit :=
  Adjunction.isIso_mapDerivedCategoryAdjunction_unit _

/-- The bounded below version of
`Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction`: the derived adjunction
`j_! ⊣ j^*` along an open immersion on the bounded below derived categories of étale
sheaves, obtained by restricting the unbounded one along the fully faithful inclusions,
which is legitimate since the exact functors `j_!` and `j^*` preserve bounded below
objects. -/
noncomputable def Etale.derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus :
    D+((j)_!open[A]) ⊣ D+((j)^*[A]) :=
  (Etale.openImmersionLowerShriekUpperStarAdjunction A j).mapDerivedCategoryPlusAdjunction

end AlgebraicGeometry
