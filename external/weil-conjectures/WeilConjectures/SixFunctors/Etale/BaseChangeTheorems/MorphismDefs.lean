/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie, Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.Mathlib.CategoryTheory.Functor.SquareTransport
import Mathlib.Tactic.IrreducibleDef

/-!

# The derived base-change morphism on bounded below derived categories

This file constructs the derived base-change morphism on the bounded below derived
categories (`DerivedCategory.Plus`). Fix a commutative square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

recorded as `sq : CommSq g' f' f g`.
This file constructs the *derived base-change morphism*

`BC_sq : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` (in diagrammatic `⋙`-order)

on the bounded below derived categories, as the composite of three named
transformations: unit insertion, square transport along the pullback comparison
`θ_sq : Lf'^* ∘ Lg^* ≅ Lg'^* ∘ Lf^*`, and counit contraction.

The square transport is an instance of the purely categorical construction
`CategoryTheory.Functor.squareTransport`: a natural isomorphism `θ : G₁ ⋙ G₂ ≅ G₃ ⋙ G₄`
is transported under `R` on the left and `R'` on the right (with the reassociations) to
`(R ⋙ G₁) ⋙ (G₂ ⋙ R') ≅ (R ⋙ G₃) ⋙ (G₄ ⋙ R')`, whose component at `K` is
`R'.mapIso (θ.app (R.obj K))`.

## Main definitions

- `CategoryTheory.Functor.squareTransport` (in
  `WeilConjectures.Mathlib.CategoryTheory.Functor.SquareTransport`): transport of a natural
  isomorphism under an outer functor on each side, with its component lemmas.
- `AlgebraicGeometry.Etale.pullbackSquareComparison`: the pullback comparison `θ_sq`
  of a commutative square on the bounded below derived categories.
- `AlgebraicGeometry.Etale.baseChangeUnitStep`, `Etale.baseChangeSquareStep`,
  `Etale.baseChangeCounitStep`: the three steps of the construction.
- `AlgebraicGeometry.Etale.baseChange`: the derived base-change morphism `BC_sq`.

## Implementation notes (@Edison Xie)

The component lemmas of `Etale.baseChangeSquareStep` are obtained from the component lemmas
of `Functor.squareTransport`, which are stated for arbitrary functors. A direct `simp` proof
on the unfolded concrete transformation elaborates quickly but produces a proof term whose
kernel check does not terminate in practice, because the kernel normalises the composite
transformation through the concrete derived functors `rightDerivedFunctorPlus` and
`mapDerivedCategoryPlus` into the localised category.

The isomorphism-level lemma `Etale.baseChangeSquareStep_app` is proved by `simp`: its
left-hand side is headed by the ordinary definition `Iso.app`, for which the kernel compares
arguments first, so nothing is unfolded. The morphism-level lemmas
`Etale.baseChangeSquareStep_hom_app` and `Etale.baseChangeSquareStep_inv_app` are instead
derived from it by `congrArg`. Instantiating `Functor.squareTransport_hom_app` at the
concrete functors directly (by `simp`, `rw` or `exact`) produces a syntactically matching
equation, but its kernel check was observed not to terminate: its left-hand side is headed by
the projection functions `NatTrans.app` and `Iso.hom`, which the kernel reduces by fully
normalising the underlying structure `squareTransport …` rather than by comparing
arguments.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory MonoidalClosed Abelian

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section PullbackComposition

/-- The composition isomorphism `L(h₁ ≫ h₂)^* ≅ Lh₂^* ⋙ Lh₁^*` of derived pullbacks on
the bounded below derived categories: since the pullbacks are exact, the derived
pullbacks are the levelwise functors `D+((h)^*[A])`, and the isomorphism is
obtained from the underived composition isomorphism `Etale.upperStarComp`. -/
noncomputable def Etale.upperStarPlusComp {T S R : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R) :
    D+((h₁ ≫ h₂)^*[A]) ≅ D+((h₂)^*[A]) ⋙ D+((h₁)^*[A]) :=
  Functor.mapDerivedCategoryPlusNatIso (Etale.upperStarComp A h₁ h₂) ≪≫
    Functor.mapDerivedCategoryPlusCompIso (h₂)^*[A] (h₁)^*[A]

variable {X Y X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The pullback comparison `θ_sq : Lf'^* ∘ Lg^* ≅ Lg'^* ∘ Lf^*` of a commutative
square `g' ≫ f = f' ≫ g` of schemes on the bounded below derived categories, obtained
from the composition isomorphisms of `Etale.upperStarPlusComp` and the commutativity of
the square. This comparison is the only square-specific categorical ingredient in the
construction of the base-change morphism. -/
noncomputable def Etale.pullbackSquareComparison (sq : CommSq g' f' f g) :
    D+((g)^*[A]) ⋙ D+((f')^*[A]) ≅ D+((f)^*[A]) ⋙ D+((g')^*[A]) :=
  (Etale.upperStarPlusComp A f' g).symm ≪≫
    eqToIso (by rw [← sq.w]) ≪≫ Etale.upperStarPlusComp A g' f

/-- The *square transport* step `s_sq` of the base-change morphism on the bounded
below derived categories: the natural transformation obtained by transporting along the
pullback comparison `θ_sq` of the square under `Rf_*` on the left and `Rf'_*` on the
right; the reassociations are the only other ingredient. This is
`Functor.squareTransport` applied to `θ_sq`. -/
noncomputable def Etale.baseChangeSquareStep (sq : CommSq g' f' f g) :
    (R+((f)_*[A]) ⋙ D+((g)^*[A])) ⋙ (D+((f')^*[A]) ⋙ R+((f')_*[A])) ≅
      (R+((f)_*[A]) ⋙ D+((f)^*[A])) ⋙ (D+((g')^*[A]) ⋙ R+((f')_*[A])) :=
  Functor.squareTransport R+((f)_*[A]) R+((f')_*[A])
    (Etale.pullbackSquareComparison A sq)

lemma Etale.baseChangeSquareStep_app (sq : CommSq g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    ((Etale.baseChangeSquareStep A sq).app K) =
      R+((f')_*[A]).mapIso ((pullbackSquareComparison A sq).app (R+((f)_*[A]).obj K)) := by
  simp [baseChangeSquareStep]

lemma Etale.baseChangeSquareStep_hom_app (sq : CommSq g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    (Etale.baseChangeSquareStep A sq).hom.app K =
      R+((f')_*[A]).map ((pullbackSquareComparison A sq).hom.app (R+((f)_*[A]).obj K)) :=
  congrArg Iso.hom (Etale.baseChangeSquareStep_app A sq K)

lemma Etale.baseChangeSquareStep_inv_app (sq : CommSq g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    (Etale.baseChangeSquareStep A sq).inv.app K =
      R+((f')_*[A]).map ((pullbackSquareComparison A sq).inv.app (R+((f)_*[A]).obj K)) :=
  congr(Iso.inv $(Etale.baseChangeSquareStep_app A sq K))

end PullbackComposition

section BaseChangeTransformation

/- The K-flat resolution package on the coefficient category `A`, as in the sections
`DerivedUpperStar` and `DerivedUpperLowerStarAdjunction` of
`WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar`; it enters here through the
bounded below derived adjunction `Etale.derivedUpperStarLowerStarAdjunctionPlus`, which is
obtained by restriction of the unbounded derived adjunction. -/
variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {X Y X' Y' : Scheme.{u}}
  (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)

/-- The *unit insertion* step `u_sq` of the base-change morphism on the bounded below
derived categories: the natural transformation
`Lg^* ∘ Rf_* ⟶ Rf'_* ∘ Lf'^* ∘ Lg^* ∘ Rf_*` obtained by inserting the unit of the
derived adjunction `Lf'^* ⊣ Rf'_*`. -/
noncomputable def Etale.baseChangeUnitStep :
    R+((f)_*[A]) ⋙ D+((g)^*[A]) ⟶
      (R+((f)_*[A]) ⋙ D+((g)^*[A])) ⋙ (D+((f')^*[A]) ⋙ R+((f')_*[A])) :=
  (Functor.rightUnitor _).inv ≫ Functor.whiskerLeft
  (R+((f)_*[A]) ⋙ D+((g)^*[A]))
  (Etale.derivedUpperStarLowerStarAdjunctionPlus A f').unit

lemma Etale.baseChangeUnitStep_app (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    (Etale.baseChangeUnitStep A f g f').app K =
      (derivedUpperStarLowerStarAdjunctionPlus A f').unit.app
        ((R+((f)_*[A]) ⋙ D+((g)^*[A])).obj K) := by
  simp [baseChangeUnitStep]

/-- The *counit contraction* step `c_sq` of the base-change morphism on the bounded
below derived categories: the natural transformation obtained by contracting the
counit of the derived adjunction `Lf^* ⊣ Rf_*`. -/
noncomputable def Etale.baseChangeCounitStep :
    (R+((f)_*[A]) ⋙ D+((f)^*[A])) ⋙ (D+((g')^*[A]) ⋙ R+((f')_*[A])) ⟶
      D+((g')^*[A]) ⋙ R+((f')_*[A]) :=
  Functor.whiskerRight
  (Etale.derivedUpperStarLowerStarAdjunctionPlus A f).counit
  (D+((g')^*[A]) ⋙ R+((f')_*[A]))
  ≫ (Functor.leftUnitor _).hom

lemma Etale.baseChangeCounitStep_app (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    (Etale.baseChangeCounitStep A f f' g').app K =
      R+((f')_*[A]).map (D+((g')^*[A]).map
        ((derivedUpperStarLowerStarAdjunctionPlus A f).counit.app K)) := by
  simp [baseChangeCounitStep]

-- Private-environment replay can unfold `no_expose` definitions. Use a checked opaque
-- wrapper to prevent projections from expanding the whole derived construction.
variable {f g f' g'} in
/-- The *derived base-change morphism* `BC_sq : Lg^* ∘ Rf_* ⟶ Rf'_* ∘ Lg'^*` of a
commutative square `g' ≫ f = f' ≫ g` of schemes on the bounded below derived
categories, assembled as the composite of the unit insertion, the square transport, and
the counit contraction.

Proper base change and smooth base change assert that this single morphism is an
isomorphism under two different sets of geometric hypotheses; no such hypothesis is
built into the definition. (blueprint: `definition-derived-base-change-map`) -/
noncomputable irreducible_def Etale.baseChange (sq : CommSq g' f' f g) :
    R+((f)_*[A]) ⋙ D+((g)^*[A]) ⟶ D+((g')^*[A]) ⋙ R+((f')_*[A]) :=
  (Etale.baseChangeUnitStep A f g f') ≫ (Etale.baseChangeSquareStep A sq).hom ≫
    (Etale.baseChangeCounitStep A f f' g')

lemma Etale.baseChange_app (sq : CommSq g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    (Etale.baseChange A sq).app K = (baseChangeUnitStep A f g f').app K ≫
      (baseChangeSquareStep A sq).hom.app K ≫ (baseChangeCounitStep A f f' g').app K := by
  simp [Etale.baseChange_def]

/-- Blueprint `lemma-naturality-pasting-comparison--1`: the derived base-change map is natural in
the complex: for `u : K ⟶ K'` the square formed by `BC_sq(K)`, `BC_sq(K')`, `g^* Rf_*(u)` and
`Rf'_* g'^*(u)` commutes, since `AlgebraicGeometry.Etale.baseChange` is a natural
transformation, being a composite of a unit, a natural isomorphism and a counit. -/
lemma Etale.baseChange_naturality (sq : CommSq g' f' f g)
    {K K' : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)} (u : K ⟶ K') :
    ((g)^*[A]).mapDerivedCategoryPlus.map (R+((f)_*[A]).map u) ≫
        (Etale.baseChange A sq).app K' =
      (Etale.baseChange A sq).app K ≫
        R+((f')_*[A]).map (((g')^*[A]).mapDerivedCategoryPlus.map u) :=
  (Etale.baseChange A sq).naturality u

end BaseChangeTransformation

end AlgebraicGeometry
