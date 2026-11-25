/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections

/-!
# Derived global sections of a pushforward and of a pullback along an isomorphism

For a morphism of schemes `f : X ⟶ Y`, the derived global sections of a derived pushforward
are the derived global sections: `RΓ(Y, Rf_* K) ≅ RΓ(X, K)` (the Leray isomorphism). For an
isomorphism `e : X ≅ Y`, this gives the invariance `RΓ(X, e^* K) ≅ RΓ(Y, K)` of derived global
sections under pullback.

## Main definitions

- `AlgebraicGeometry.Etale.commShiftRightDerivedGlobalSections`: `RΓ(X, -)` commutes with
  shifts.

- `AlgebraicGeometry.Etale.rightDerivedLowerStarCompRightDerivedGlobalSectionsIso`: the Leray
  isomorphism `R(f_*) ⋙ RΓ_Y ≅ RΓ_X`.
- `AlgebraicGeometry.Etale.upperStarCompRightDerivedGlobalSectionsIso`: the isomorphism
  `D(e^*) ⋙ RΓ_X ≅ RΓ_Y` for an isomorphism `e : X ≅ Y`.

## TODO

Derive the pullback map `AlgebraicGeometry.Etale.globalSectionsUpperStarMap` to a natural
transformation `RΓ_Y ⟶ D(f^*) ⋙ RΓ_X` for every `f : X ⟶ Y`, and show that for an isomorphism
`e` its inverse is `AlgebraicGeometry.Etale.upperStarCompRightDerivedGlobalSectionsIso`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

/-- The derived global sections `RΓ(X, -)` commute with shifts, as every right derived
functor does. -/
noncomputable instance commShiftRightDerivedGlobalSections (X : Scheme.{u}) :
    (rightDerivedGlobalSections A X).CommShift ℤ :=
  inferInstanceAs ((Sheaf.Γ X.smallEtaleTopology A).rightDerivedFunctor.CommShift ℤ)

/-- The Leray isomorphism `RΓ(Y, Rf_* K) ≅ RΓ(X, K)` for a morphism `f : X ⟶ Y`: the
composition of right derived functors applied to `f_* ⋙ Γ_Y ≅ Γ_X`, which is valid since `f_*`
preserves K-injective complexes (`AlgebraicGeometry.Etale.preservesKInjectiveComplexes_lowerStar`).
-/
noncomputable def rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((f)_*[A]).rightDerivedFunctor ⋙ rightDerivedGlobalSections A Y ≅
      rightDerivedGlobalSections A X :=
  Functor.rightDerivedFunctorCompIso' _ _ (lowerStarCompGlobalSectionsIso A f)

/-- Derived global sections are invariant under the pullback along an isomorphism
`e : X ≅ Y`: `RΓ(X, e^* K) ≅ RΓ(Y, K)`. It is the composite

```
            D(e^*)                RΓ_X
  D(Y) ──────────────▶ D(X) ──────────────▶ D(A)
    │      ≅ R(e^*) ≅ R((e⁻¹)_*)               ▲
    └──────────── R((e⁻¹)_*) ⋙ RΓ_X ≅ RΓ_Y ────┘
```

of `Functor.rightDerivedFunctorIsoMapDerivedCategory` (the pullback `e^*` is exact), of the
derived isomorphism `e^* ≅ (e⁻¹)_*` (`AlgebraicGeometry.Etale.upperStarInvIsoLowerStarHom`),
and of the Leray isomorphism
`AlgebraicGeometry.Etale.rightDerivedLowerStarCompRightDerivedGlobalSectionsIso` for `e⁻¹`. -/
noncomputable def upperStarCompRightDerivedGlobalSectionsIso {X Y : Scheme.{u}} (e : X ≅ Y) :
    ((e.hom)^*[A]).mapDerivedCategory ⋙ rightDerivedGlobalSections A X ≅
      rightDerivedGlobalSections A Y :=
  Functor.isoWhiskerRight (((e.hom)^*[A]).rightDerivedFunctorIsoMapDerivedCategory.symm ≪≫
      Functor.rightDerivedFunctorNatIso (upperStarInvIsoLowerStarHom A e.symm)) _ ≪≫
    rightDerivedLowerStarCompRightDerivedGlobalSectionsIso A e.inv

end AlgebraicGeometry.Etale
