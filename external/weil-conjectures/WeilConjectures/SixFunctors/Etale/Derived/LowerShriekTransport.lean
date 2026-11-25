/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp

/-!

# Transport of the derived lower shriek along isomorphisms of schemes

Let `f : X ⟶ Y` and `f' : X' ⟶ Y'` be morphisms of schemes and `eX : X ≅ X'`, `eY : Y ≅ Y'`
isomorphisms with `f ≫ eY.hom = eX.hom ≫ f'`. The derived lower shrieks attached to a
compactification `c` of `f` and to its transport `c.transport` (`Compactification.transport`)
are intertwined by the pullbacks along the isomorphisms:

`Rf'_!(c.transport) ⋙ D(eY^*) ≅ D(eX^*) ⋙ Rf_!(c)`.

This only uses that `eX` and `eY` are isomorphisms: the pushforward along an isomorphism `e`
is an exact equivalence, so `R(e_*) ≅ D(e_*)` is inverse to `D(e^*)`. Combined with the
independence of `Rf_!` of the compactification, this is what transports a Frobenius
structure through `Rf_!` when the Frobenius does not act on the chosen compactification.

## Main definitions

- `AlgebraicGeometry.Etale.mapDerivedLowerStarEquivalenceOfIso`: the equivalence
  `D(e_*) : D(Y_ét) ≌ D(Y'_ét)` for an isomorphism `e : Y ≅ Y'`.
- `AlgebraicGeometry.Etale.rightDerivedLowerStarCompMapDerivedUpperStarIso`:
  `R(e_*) ⋙ D(e^*) ≅ 𝟭`.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationTransportIso`:
  `Rf'_!(c.transport) ⋙ D(eY^*) ≅ D(eX^*) ⋙ Rf_!(c)`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

namespace Etale

section LowerStar

variable {Y Y' : Scheme.{u}} (e : Y ≅ Y')

instance : (lowerStarEquivalenceOfIso A e).functor.Additive :=
  inferInstanceAs ((e.hom)_*[A]).Additive

instance : (lowerStarEquivalenceOfIso A e).inverse.Additive :=
  inferInstanceAs ((e.inv)_*[A]).Additive

/-- The pushforward along an isomorphism `e : Y ≅ Y'` of schemes induces an equivalence
`D(e_*) : D(Y_ét) ≌ D(Y'_ét)` of derived categories, with inverse `D((e⁻¹)_*)`. -/
noncomputable def mapDerivedLowerStarEquivalenceOfIso :
    DerivedCategory (Sheaf Y.smallEtaleTopology A) ≌
      DerivedCategory (Sheaf Y'.smallEtaleTopology A) :=
  (lowerStarEquivalenceOfIso A e).mapDerivedCategory

/-- The derived pushforward along an isomorphism `e : Y ≅ Y'` of schemes followed by the
pullback along `e` is the identity:
```
D(Y) --R(e_*)--> D(Y')
    \              |
     \             | D(e^*)
      \            v
       ---𝟭-----> D(Y)
```
-/
noncomputable def rightDerivedLowerStarCompMapDerivedUpperStarIso :
    R((e.hom)_*[A]) ⋙ D((e.hom)^*[A]) ≅ 𝟭 _ :=
  -- `e_*` is exact, being an equivalence, so `R(e_*) ≅ D(e_*)`; and `e^* ≅ (e⁻¹)_*`, so this is
  -- the unit of `mapDerivedLowerStarEquivalenceOfIso`
  have : PreservesFiniteLimits (e.hom)_*[A] :=
    inferInstanceAs (PreservesFiniteLimits (lowerStarEquivalenceOfIso A e).functor)
  have : PreservesFiniteColimits (e.hom)_*[A] :=
    inferInstanceAs (PreservesFiniteColimits (lowerStarEquivalenceOfIso A e).functor)
  have : PreservesFiniteLimits (e.symm.hom)_*[A] :=
    inferInstanceAs (PreservesFiniteLimits (lowerStarEquivalenceOfIso A e).inverse)
  have : PreservesFiniteColimits (e.symm.hom)_*[A] :=
    inferInstanceAs (PreservesFiniteColimits (lowerStarEquivalenceOfIso A e).inverse)
  Functor.isoWhiskerRight (Functor.rightDerivedFunctorIsoMapDerivedCategory _) _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryNatIso
      (upperStarInvIsoLowerStarHom A e.symm)) ≪≫
    (mapDerivedLowerStarEquivalenceOfIso A e).unitIso.symm

end LowerStar

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} (eX : X ≅ X') (eY : Y ≅ Y')
  (w : f ≫ eY.hom = eX.hom ≫ f') (c : Compactification f)

/-- The derived lower shriek attached to the transported compactification `c.transport` of
`f'` is intertwined with the one attached to `c` by the pullbacks along `eX` and `eY`:
```
D(X') --Rf'_!(c.transport)--> D(Y')
  |                             |
D(eX^*)                       D(eY^*)
  v                             v
D(X)  ---------Rf_!(c)------> D(Y)
```
-/
noncomputable def rightDerivedLowerShriekOfCompactificationTransportIso :
    Rf_!(c.transport eX eY w)[A] ⋙ D((eY.hom)^*[A]) ≅ D((eX.hom)^*[A]) ⋙ Rf_!(c)[A] :=
  -- `(eX⁻¹ ≫ i)_! ≅ (eX⁻¹)_! ⋙ i_! ≅ eX^* ⋙ i_!`, `R((g ≫ eY)_*) ≅ R(g_*) ⋙ R(eY_*)` and
  -- `R(eY_*) ⋙ D(eY^*) ≅ 𝟭`
  Functor.isoWhiskerRight
      (Functor.isoWhiskerRight
          (Functor.mapDerivedCategoryNatIso
              (openImmersionLowerShriekComp A eX.inv c.i ≪≫
                Functor.isoWhiskerRight (upperStarIsoOpenImmersionLowerShriekInv A eX).symm _) ≪≫
            (Functor.mapDerivedCategoryCompIso _ _).symm) R((c.g ≫ eY.hom)_*[A]) ≪≫
        Functor.isoWhiskerLeft _
          (Functor.rightDerivedFunctorCompIso' (c.g)_*[A] (eY.hom)_*[A]
            (Etale.lowerStarComp A c.g eY.hom)).symm) D((eY.hom)^*[A]) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
      (Functor.isoWhiskerLeft _ (rightDerivedLowerStarCompMapDerivedUpperStarIso A eY) ≪≫
        Functor.rightUnitor _))


end Etale

end AlgebraicGeometry
