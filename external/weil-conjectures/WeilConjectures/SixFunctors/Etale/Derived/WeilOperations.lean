/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.Etale.Derived.Adjunctions
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.SixFunctors.Etale.Derived.WeilComplexTensorHom
public import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius

/-!
# Weil structures on the six operations

Let `g : X ⟶ X` and `h : Y ⟶ Y` be automorphisms of schemes and `f : X ⟶ Y` a morphism with
`g ≫ f = f ≫ h`. In the `ℓ`-adic formalism `X = X₀ ×_{k₀} k̄`, `Y = Y₀ ×_{k₀} k̄`, `f` is the
base change of a morphism `f₀ : X₀ ⟶ Y₀` and `g`, `h` are the geometric Frobenius
automorphisms (`AlgebraicGeometry.Scheme.Hom.commSq_geometricGaloisFrobenius`); the square is
then cartesian
(`AlgebraicGeometry.Scheme.Hom.isPullback_geometricGaloisFrobenius_geometricFiberMap`).

A *Weil object* of `D(X_ét, Λ)` is an object `K` with an isomorphism `θ_K : Lg^* K ≅ K`; they
form the category `IsoAlgebra (Lg^*)` (`CategoryTheory.Endofunctor.IsoAlgebra`), whose morphisms
are the morphisms commuting with the `θ`'s. This file carries out the proof of
`prose-10-20`: the operations carry canonical Weil structures, transported through
the exchange isomorphisms of the Frobenius square, and the basic maps between them are
equivariant.

* **Pullback.** `Lf^*` is transported through `Lg^* Lf^* ≅ L(g ≫ f)^* = L(f ≫ h)^* ≅ Lf^* Lh^*`
  (`AlgebraicGeometry.Etale.weilUpperStar`).
* **Direct image.** `Rf_*` is transported through `Ex_* : Lh^* Rf_* ⟶ Rf_* Lg^*`, which is an
  isomorphism for an automorphism square: it is the mate of an isomorphism along the
  equivalences `Lg^*` and `Lh^*` (`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_of_isIso`,
  `AlgebraicGeometry.Etale.weilLowerStar`).
* **Compactly supported direct image.** `Rf_!` is transported through `Ex_!`, an isomorphism by
  compact-support base change (`AlgebraicGeometry.Etale.weilLowerShriek`).
* **Exceptional inverse image.** `Rf^!` is transported through the mate `Ex^!` of `Ex_!⁻¹`
  under `Rf_! ⊣ Rf^!` (`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`,
  `AlgebraicGeometry.Etale.weilUpperShriek`).
* **Adjunctions.** The units and counits of `Lf^* ⊣ Rf_*` and `Rf_! ⊣ Rf^!` are equivariant:
  both adjunctions lift to the Weil categories
  (`AlgebraicGeometry.Etale.weilUpperStarLowerStarAdjunction`,
  `AlgebraicGeometry.Etale.weilLowerShriekUpperShriekAdjunction`). For `Lf^* ⊣ Rf_*` this is
  the definition of `Ex_*` as a mate.

## Main definitions

- `AlgebraicGeometry.Etale.weilUpperStar`, `AlgebraicGeometry.Etale.weilLowerStar`,
  `AlgebraicGeometry.Etale.weilLowerShriek`, `AlgebraicGeometry.Etale.weilUpperShriek`.

## Main results

- `AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_of_isIso`,
  `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_isIso`.
- `AlgebraicGeometry.Etale.weilUpperStarLowerStarAdjunction`,
  `AlgebraicGeometry.Etale.weilLowerShriekUpperShriekAdjunction`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Endofunctor

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-! ### The exchange isomorphisms of an automorphism square -/

section Exchange

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

variable (Λ) in
/-- **The direct-image exchange of an automorphism square is an isomorphism.** For a
commutative square `g' ≫ f = f' ≫ g` whose horizontal maps `g` and `g'` are isomorphisms, the
exchange `Ex_* : Lg^* Rf_* ⟶ Rf'_* Lg'^*` is an isomorphism: it is the mate of the isomorphism
`Lf'^* Lg^* ≅ Lg'^* Lf^*` along the equivalences `Lg^*` and `Lg'^*`. -/
theorem isIso_derivedBaseChangeMap_of_isIso (sq : CommSq g' f' f g) [IsIso g] [IsIso g'] :
    IsIso (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq) :=
  have : IsIso (TwoSquare.mk _ _ _ _
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom) :=
    inferInstanceAs (IsIso (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom)
  isIso_mateEquiv_of_isEquivalence _ _ _

variable [Finite Λ]

variable (Λ) in
/-- The compact-support exchange `Ex_! : Lg^* Rf_! ≅ Rf'_! Lg'^*` of a cartesian square, as an
isomorphism (compact-support base change,
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap`). -/
noncomputable def rightDerivedLowerShriekBaseChangeNatIso [HasCompactification f]
    [HasCompactification f'] [QuasiCompact f'] (sq : IsPullback g' f' f g) :
    R(f)_![ModuleCat.{u + 1} Λ] ⋙ L((g)^*[ModuleCat.{u + 1} Λ]) ≅
      L((g')^*[ModuleCat.{u + 1} Λ]) ⋙ R(f')_![ModuleCat.{u + 1} Λ] :=
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  asIso (rightDerivedLowerShriekBaseChangeMap Λ sq)

@[simp]
lemma rightDerivedLowerShriekBaseChangeNatIso_hom [HasCompactification f]
    [HasCompactification f'] [QuasiCompact f'] (sq : IsPullback g' f' f g) :
    (rightDerivedLowerShriekBaseChangeNatIso Λ sq).hom =
      rightDerivedLowerShriekBaseChangeMap Λ sq :=
  rfl

/-- The unit form of the definition of `Ex^!` as a mate. -/
@[reassoc]
lemma map_unit_rightDerivedUpperShriekBaseChangeMap_app [HasCompactification f]
    [HasCompactification f'] [QuasiCompact f'] (sq : IsPullback g' f' f g)
    (K : DerivedCategoryModule Λ X) :
    L((g')^*[ModuleCat.{u + 1} Λ]).map ((rightDerivedUpperShriekAdjunction _ f).unit.app K) ≫
        (rightDerivedUpperShriekBaseChangeMap Λ sq).app ((R(f)_![ModuleCat.{u + 1} Λ]).obj K) =
      (rightDerivedUpperShriekAdjunction _ f').unit.app _ ≫
        (R(f')^![Λ]).map
          ((rightDerivedLowerShriekBaseChangeNatIso Λ sq).inv.app K) :=
  unit_mateEquiv _ _ _ K

/-- The counit form of the definition of `Ex^!` as a mate. -/
@[reassoc]
lemma map_rightDerivedUpperShriekBaseChangeMap_app_counit [HasCompactification f]
    [HasCompactification f'] [QuasiCompact f'] (sq : IsPullback g' f' f g)
    (M : DerivedCategoryModule Λ Y) :
    (R(f')_![ModuleCat.{u + 1} Λ]).map ((rightDerivedUpperShriekBaseChangeMap Λ sq).app M) ≫
        (rightDerivedUpperShriekAdjunction _ f').counit.app _ =
      (rightDerivedLowerShriekBaseChangeNatIso Λ sq).inv.app
          ((R(f)^![Λ]).obj M) ≫
        L((g)^*[ModuleCat.{u + 1} Λ]).map ((rightDerivedUpperShriekAdjunction _ f).counit.app M) :=
  mateEquiv_counit _ _ _ M

variable (Λ) in
/-- The exceptional-inverse-image exchange `Ex^!` of an automorphism square is an isomorphism,
being the mate of an isomorphism along the equivalences `Lg^*` and `Lg'^*`. -/
theorem isIso_rightDerivedUpperShriekBaseChangeMap_of_isIso [HasCompactification f]
    [HasCompactification f'] [QuasiCompact f'] (sq : IsPullback g' f' f g) [IsIso g]
    [IsIso g'] : IsIso (rightDerivedUpperShriekBaseChangeMap Λ sq) :=
  have : IsIso (TwoSquare.mk _ _ _ _
      (rightDerivedLowerShriekBaseChangeNatIso Λ sq).inv) :=
    inferInstanceAs (IsIso (rightDerivedLowerShriekBaseChangeNatIso Λ sq).inv)
  isIso_mateEquiv_of_isEquivalence _ _ _
end Exchange

/-! ### Weil structures on the operations -/

section Operations

variable {X Y : Scheme.{u}} {g : X ⟶ X} {h : Y ⟶ Y} {f : X ⟶ Y}

variable (Λ) in
/-- **Weil structure on the pullback.** For `g ≫ f = f ≫ h`, the derived pullback `Lf^*`
carries a Weil object `(M, θ_M)` of `D(Y_ét, Λ)` to the Weil object `(Lf^* M, θ)` of
`D(X_ét, Λ)`, with
```
  Lg^* Lf^* M ≅ Lf^* Lh^* M --Lf^* θ_M--> Lf^* M,
```
the first isomorphism being `AlgebraicGeometry.Etale.derivedSquareUpperStarIso`. -/
noncomputable def weilUpperStar (sq : CommSq g f f h) :
    IsoAlgebra L((h)^*[ModuleCat.{u + 1} Λ]) ⥤ IsoAlgebra L((g)^*[ModuleCat.{u + 1} Λ]) :=
  IsoAlgebra.mapOfNatIso (derivedSquareUpperStarIso _ sq).symm

variable (Λ) in
/-- **Weil structure on the direct image.** For `g ≫ f = f ≫ h` with `g` and `h` automorphisms,
the derived direct image `Rf_*` carries a Weil object `(K, θ_K)` of `D(X_ét, Λ)` to the Weil
object `(Rf_* K, θ)` of `D(Y_ét, Λ)`, with
```
  Lh^* Rf_* K --Ex_*--> Rf_* Lg^* K --Rf_* θ_K--> Rf_* K,
```
`Ex_*` being an isomorphism by `AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_of_isIso`.
Its structure morphism is `AlgebraicGeometry.Etale.lowerStarWeilDatum`. -/
noncomputable def weilLowerStar (sq : CommSq g f f h) [IsIso g] [IsIso h] :
    IsoAlgebra L((g)^*[ModuleCat.{u + 1} Λ]) ⥤ IsoAlgebra L((h)^*[ModuleCat.{u + 1} Λ]) :=
  have := isIso_derivedBaseChangeMap_of_isIso Λ sq
  IsoAlgebra.mapOfNatIso (asIso (derivedBaseChangeMap _ sq))

variable (Λ) in
/-- **The adjunction `Lf^* ⊣ Rf_*` is equivariant.** Its unit and counit are morphisms of Weil
objects, so that it lifts to an adjunction between the Weil pullback and the Weil direct image:
`Ex_*` is by definition the mate of `Lh^* Lf^* ≅ Lf^* Lg^*`. -/
noncomputable def weilUpperStarLowerStarAdjunction (sq : CommSq g f f h) [IsIso g] [IsIso h] :
    weilUpperStar Λ sq ⊣ weilLowerStar Λ sq :=
  have := isIso_derivedBaseChangeMap_of_isIso Λ sq
  IsoAlgebra.mapOfNatIsoAdjunction (derivedUpperStarLowerStarAdjunction _ f) _ _ rfl

variable [Finite Λ]

variable (Λ) in
/-- **Weil structure on the compactly supported direct image.** For a cartesian square
`g ≫ f = f ≫ h`, the derived lower shriek `Rf_!` carries a Weil object `(K, θ_K)` of
`D(X_ét, Λ)` to the Weil object `(Rf_! K, θ)` of `D(Y_ét, Λ)`, with
```
  Lh^* Rf_! K --Ex_!--> Rf_! Lg^* K --Rf_! θ_K--> Rf_! K,
```
`Ex_!` being an isomorphism by compact-support base change
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap`). Its structure morphism
is `AlgebraicGeometry.Etale.lowerShriekWeilDatum`. -/
noncomputable def weilLowerShriek [HasCompactification f] [QuasiCompact f]
    (sq : IsPullback g f f h) :
    IsoAlgebra L((g)^*[ModuleCat.{u + 1} Λ]) ⥤ IsoAlgebra L((h)^*[ModuleCat.{u + 1} Λ]) :=
  IsoAlgebra.mapOfNatIso (rightDerivedLowerShriekBaseChangeNatIso Λ sq)

variable (Λ) in
/-- **Weil structure on the exceptional inverse image.** For a cartesian square
`g ≫ f = f ≫ h` with `g` and `h` automorphisms, `Rf^!` carries a Weil object `(M, θ_M)` of
`D(Y_ét, Λ)` to the Weil object `(Rf^! M, θ)` of `D(X_ét, Λ)`, with
```
  Lg^* Rf^! M --Ex^!--> Rf^! Lh^* M --Rf^! θ_M--> Rf^! M,
```
`Ex^!` being the mate of `Ex_!⁻¹` under `Rf_! ⊣ Rf^!`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`). -/
noncomputable def weilUpperShriek [HasCompactification f] [QuasiCompact f]
    (sq : IsPullback g f f h) [IsIso g] [IsIso h] :
    IsoAlgebra L((h)^*[ModuleCat.{u + 1} Λ]) ⥤ IsoAlgebra L((g)^*[ModuleCat.{u + 1} Λ]) :=
  have := isIso_rightDerivedUpperShriekBaseChangeMap_of_isIso Λ sq
  IsoAlgebra.mapOfNatIso (asIso (rightDerivedUpperShriekBaseChangeMap Λ sq))

variable (Λ) in
/-- **The adjunction `Rf_! ⊣ Rf^!` is equivariant.** Its unit and counit are morphisms of Weil
objects, so that it lifts to an adjunction between the Weil compactly supported direct image
and the Weil exceptional inverse image: `Ex^!` is by definition the mate of `Ex_!⁻¹`. -/
noncomputable def weilLowerShriekUpperShriekAdjunction [HasCompactification f] [QuasiCompact f]
    (sq : IsPullback g f f h) [IsIso g] [IsIso h] :
    weilLowerShriek Λ sq ⊣ weilUpperShriek Λ sq :=
  have := isIso_rightDerivedUpperShriekBaseChangeMap_of_isIso Λ sq
  IsoAlgebra.mapOfNatIsoAdjunction (rightDerivedUpperShriekAdjunction _ f) _ _ rfl

end Operations

/-! ### Weil data and the equivariance of the adjunction maps

The equivariance statements below are phrased with Weil data, morphisms `ψ : Lh^* M ⟶ M` that
need not be invertible (`AlgebraicGeometry.Etale.IsWeilMorphism`), so that they also apply to
the Weil data used in the Frobenius statements of Poincaré duality. -/

section Data

variable {X Y : Scheme.{u}} {g : X ⟶ X} {h : Y ⟶ Y} {a : X ⟶ Y}

/-- The Weil datum on `La^* M` of a Weil datum `ψ : Lh^* M ⟶ M`, for `g ≫ a = a ≫ h`:
```
                ≅                     La^* ψ
  Lg^* La^* M ───▶ La^* Lh^* M ──────────▶ La^* M
```
the first map being `AlgebraicGeometry.Etale.derivedSquareUpperStarIso`. It is the structure
morphism of `AlgebraicGeometry.Etale.weilUpperStar`. -/
noncomputable def upperStarWeilDatum (sq : CommSq g a a h) {M : DerivedCategoryModule Λ Y}
    (ψ : (L((h)^*[ModuleCat.{u + 1} Λ])).obj M ⟶ M) :
    (L((g)^*[ModuleCat.{u + 1} Λ])).obj ((L((a)^*[ModuleCat.{u + 1} Λ])).obj M) ⟶
      (L((a)^*[ModuleCat.{u + 1} Λ])).obj M :=
  (derivedSquareUpperStarIso _ sq).inv.app M ≫ (L((a)^*[ModuleCat.{u + 1} Λ])).map ψ

/-- **The unit of `La^* ⊣ Ra_*` is equivariant**: for a Weil datum `ψ` on `M`, the unit
`M ⟶ Ra_* La^* M` is a morphism of Weil objects. This is the unit form of the definition of
`Ex_*` as a mate. -/
lemma isWeilMorphism_derivedUpperStarLowerStarAdjunction_unit (sq : CommSq g a a h)
    {M : DerivedCategoryModule Λ Y} (ψ : (L((h)^*[ModuleCat.{u + 1} Λ])).obj M ⟶ M) :
    IsWeilMorphism h ψ (lowerStarWeilDatum sq (upperStarWeilDatum sq ψ))
      ((derivedUpperStarLowerStarAdjunction _ a).unit.app M) := by
  unfold IsWeilMorphism lowerStarWeilDatum upperStarWeilDatum
  rw [map_unit_derivedBaseChangeMap_app_assoc, ← Functor.map_comp, Iso.hom_inv_id_app_assoc,
    Adjunction.unit_naturality]

/-- **The counit of `La^* ⊣ Ra_*` is equivariant**: for a Weil datum `φ` on `K`, the counit
`La^* Ra_* K ⟶ K` is a morphism of Weil objects. This is the counit form of the definition of
`Ex_*` as a mate. -/
lemma isWeilMorphism_derivedUpperStarLowerStarAdjunction_counit (sq : CommSq g a a h)
    {K : DerivedCategoryModule Λ X} (φ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K) :
    IsWeilMorphism g (upperStarWeilDatum sq (lowerStarWeilDatum sq φ)) φ
      ((derivedUpperStarLowerStarAdjunction _ a).counit.app K) := by
  unfold IsWeilMorphism lowerStarWeilDatum upperStarWeilDatum
  rw [Functor.map_comp, Category.assoc, Category.assoc, Adjunction.counit_naturality,
    derivedUpperStar_map_derivedBaseChangeMap_app_counit_assoc, Iso.inv_hom_id_app_assoc]

variable [Finite Λ] [HasCompactification a] [QuasiCompact a]

/-- The Weil datum on `Ra^! M` of a Weil datum `ψ : Lh^* M ⟶ M`, for a cartesian square
`g ≫ a = a ≫ h`:
```
                Ex^!                     Ra^! ψ
  Lg^* Ra^! M ───────▶ Ra^! Lh^* M ──────────▶ Ra^! M
```
with the exceptional-inverse-image exchange
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`). It is the structure morphism
of `AlgebraicGeometry.Etale.weilUpperShriek`. -/
noncomputable def upperShriekBaseChangeWeilDatum (sq : IsPullback g a a h)
    {M : DerivedCategoryModule Λ Y} (ψ : (L((h)^*[ModuleCat.{u + 1} Λ])).obj M ⟶ M) :
    (L((g)^*[ModuleCat.{u + 1} Λ])).obj ((R(a)^![Λ]).obj M) ⟶
      (R(a)^![Λ]).obj M :=
  (rightDerivedUpperShriekBaseChangeMap Λ sq).app M ≫ (R(a)^![Λ]).map ψ

/-- **The unit of `Ra_! ⊣ Ra^!` is equivariant**: for a Weil datum `φ` on `K`, the unit
`K ⟶ Ra^! Ra_! K` is a morphism of Weil objects, `Ex^!` being the mate of `Ex_!⁻¹`. -/
lemma isWeilMorphism_rightDerivedUpperShriekAdjunction_unit (sq : IsPullback g a a h)
    {K : DerivedCategoryModule Λ X} (φ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K) :
    IsWeilMorphism g φ (upperShriekBaseChangeWeilDatum sq (lowerShriekWeilDatum sq φ))
      ((rightDerivedUpperShriekAdjunction _ a).unit.app K) := by
  unfold IsWeilMorphism upperShriekBaseChangeWeilDatum lowerShriekWeilDatum
  rw [map_unit_rightDerivedUpperShriekBaseChangeMap_app_assoc, ← Functor.map_comp,
    ← rightDerivedLowerShriekBaseChangeNatIso_hom, Iso.inv_hom_id_app_assoc,
    Adjunction.unit_naturality]

/-- **The counit of `Ra_! ⊣ Ra^!` is equivariant**: for a Weil datum `ψ` on `M`, the counit
`Ra_! Ra^! M ⟶ M` is a morphism of Weil objects, `Ex^!` being the mate of `Ex_!⁻¹`. -/
lemma isWeilMorphism_rightDerivedUpperShriekAdjunction_counit (sq : IsPullback g a a h)
    {M : DerivedCategoryModule Λ Y} (ψ : (L((h)^*[ModuleCat.{u + 1} Λ])).obj M ⟶ M) :
    IsWeilMorphism h (lowerShriekWeilDatum sq (upperShriekBaseChangeWeilDatum sq ψ)) ψ
      ((rightDerivedUpperShriekAdjunction _ a).counit.app M) := by
  unfold IsWeilMorphism upperShriekBaseChangeWeilDatum lowerShriekWeilDatum
  rw [Functor.map_comp, Category.assoc, Category.assoc, Adjunction.counit_naturality,
    map_rightDerivedUpperShriekBaseChangeMap_app_counit_assoc,
    ← rightDerivedLowerShriekBaseChangeNatIso_hom, Iso.hom_inv_id_app_assoc]

end Data

end Etale

end AlgebraicGeometry
