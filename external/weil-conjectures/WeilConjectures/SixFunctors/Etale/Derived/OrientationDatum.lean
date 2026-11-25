/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Orientation
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Duality

/-!
# Orientation data

An *orientation datum* (blueprint `theorem-smooth-purity-all-admissible-coefficients`) is a choice,
for every smooth separated morphism `f : X ⟶ Y` of finite type and of pure relative dimension `d`,
of an orientation `γ_f : Λ_X(d)[2d] ≅ Rf^! Λ_Y` (`AlgebraicGeometry.Etale.Orientation`), natural in
`Y`, compatible with composition, étale base change, finite reduction, scalar extension and
the pro-étale realization, and normalized on the affine line.

The blueprint places the definition in the setting of a six-functor datum (`def-sf-datum`),
whose comparison isomorphisms (the composition law and the base change of `R^!`, the
projection formula) are part of the datum. The compatibilities of an orientation datum are
equations between composites of these comparison isomorphisms. They are therefore stated
relative to the comparison isomorphisms they involve, which are bundled as
`AlgebraicGeometry.Etale.OrientationComparisonData` (one coefficient ring),
`AlgebraicGeometry.Etale.CoefficientChange` (two coefficient rings) and
`AlgebraicGeometry.Etale.ProEtaleRealization` (étale and pro-étale sheaves).

## Main definitions

- `AlgebraicGeometry.Etale.OrientationComparisonData`: the comparison isomorphisms of a
  six-functor datum that the compatibilities of an orientation datum refer to.
- `AlgebraicGeometry.Etale.OrientationDatum`: an orientation datum, i.e. a family of
  orientations natural in the base (in particular compatible with étale base change),
  compatible with composition and normalized on the affine line.
- `AlgebraicGeometry.Etale.OrientationDatum.nonempty_iso_dualizingComplex`: for the structure
  morphism an orientation datum reads `ω_X ≅ Λ_X(d)[2d]`.
- `AlgebraicGeometry.Etale.OrientationDatum.IsCompatibleCoefficientChange`: compatibility of
  two orientation data with a change of coefficients (finite reduction, scalar extension).
- `AlgebraicGeometry.Etale.OrientationDatum.IsCompatibleProEtaleRealization`: compatibility of
  an orientation datum with the pro-étale realization.

## Implementation notes

The comparison isomorphisms of a six-functor datum are canonical in the blueprint; in the
repository the composition law and the base change of `R^!` and the tensor formula of smooth
`R^!` are so far only known to exist
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_comp`,
`AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_comp_rightDerivedUpperShriek`,
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_obj_derivedTensor`). For this
reason they are parameters of the definitions here rather than fixed isomorphisms; once the
canonical isomorphisms are constructed they are the intended values of these parameters.
Each comparison isomorphism carries the hypotheses of the statement it stands in for; in
particular the exponent of `Λ` is invertible on the source, without which `Rf^!` of a smooth
`f` is not a twist of `Lf^*`.

TODO: replace `AlgebraicGeometry.Etale.OrientationComparisonData` by the canonical comparison
isomorphisms once they are constructed, so that an orientation datum no longer depends on `C`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ]

/-- Blueprint `theorem-smooth-purity-all-admissible-coefficients`: Orientation datum.

The comparison isomorphisms of the six-functor datum `def-sf-datum` in terms of which the
compatibilities of an orientation datum are stated:
* the composition law `R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!` (the mate of axiom (A4));
* the base change `Rf^! ⋙ Lg^* ≅ Lv^* ⋙ Rf'^!` of `R^!` along a cartesian square with `f`
  smooth (cohomological smoothness, `proposition-exceptional-inverse-image-smooth-morphism` (c));
* the tensor formula `Rf^!(Λ_Y(e)[2e]) ≅ Λ_X(e)[2e] ⊗ ω_f` for `f` smooth, the instance of
  `Rf^! K ≅ Lf^* K ⊗ ω_f` (`proposition-exceptional-inverse-image-smooth-morphism` (b)) at a
  twisting object, followed by `Lf^* Λ_Y(e)[2e] ≅ Λ_X(e)[2e]`;
* the canonical orientation `Λ(1)[2] ≅ Rπ^! Λ_Y` of the affine line `π : 𝔸¹_Y ⟶ Y`
  (`sk-prop-a1`). -/
structure OrientationComparisonData where
  /-- The composition law `R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!`. -/
  upperShriekComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [HasCompactification f]
    [HasCompactification g] [HasCompactification (f ≫ g)] :
    R(f ≫ g)^![Λ] ≅ R(g)^![Λ] ⋙ R(f)^![Λ]
  /-- The base change `Rf^! ⋙ Lg^* ≅ Lv^* ⋙ Rf'^!` of `R^!` along a cartesian square
  `g ≫ f = f' ≫ v` with `f` smooth of relative dimension `d`. -/
  upperShriekBaseChange {X Y X' Y' : Scheme.{u}} {g : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y}
    {v : Y' ⟶ Y} (sq : IsPullback g f' f v) (d : ℕ) [IsSeparated f]
    [SmoothOfRelativeDimension d f] [HasCompactification f] [HasInvertibleExponent Λ X]
    [HasCompactification f'] :
    R(f)^![Λ] ⋙ L((g)^*[ModuleCat.{u + 1} Λ]) ≅
      L((v)^*[ModuleCat.{u + 1} Λ]) ⋙ R(f')^![Λ]
  /-- The tensor formula `Rf^!(Λ_Y(e)[2e]) ≅ Λ_X(e)[2e] ⊗ ω_f` for `f` smooth of relative
  dimension `d`. -/
  upperShriekTateShift {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) [IsSeparated f]
    [SmoothOfRelativeDimension d f] [HasCompactification f] [HasInvertibleExponent Λ X]
    [HasInvertibleExponent Λ Y] (e : ℤ) :
    (R(f)^![Λ]).obj ((tateObject Λ Y e)⟦2 * e⟧) ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj ((tateObject Λ X e)⟦2 * e⟧)).obj
        (dualizingComplex Λ f)
  /-- The canonical orientation `Λ(1)[2] ≅ Rπ^! Λ_Y` of the affine line `π : 𝔸¹_Y ⟶ Y`. -/
  affineLine (Y : Scheme.{u}) [HasCompactification (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)]
    [HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin 1); Y)] :
    (tateObject Λ 𝔸(ULift.{u} (Fin 1); Y) (1 : ℕ))⟦(2 * (1 : ℕ) : ℤ)⟧ ≅
      dualizingComplex Λ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)

variable {Λ} in
/-- Blueprint `theorem-smooth-purity-all-admissible-coefficients`: Orientation datum.

The composite `Λ_X(d + e)[2(d + e)] ≅ R(f ≫ g)^! Λ_Z` built from orientations
`γ_f : Λ_X(d)[2d] ≅ Rf^! Λ_Y` and `γ_g : Λ_Y(e)[2e] ≅ Rg^! Λ_Z`:

`Λ_X(d + e)[2(d + e)] ≅ Λ_X(e)[2e] ⊗ Λ_X(d)[2d] ≅ Λ_X(e)[2e] ⊗ Rf^! Λ_Y ≅ Rf^!(Λ_Y(e)[2e])
  ≅ Rf^! Rg^! Λ_Z ≅ R(f ≫ g)^! Λ_Z`,

through the multiplicativity of the twists, `γ_f`, the tensor formula, `Rf^! γ_g` and the
composition law. Compatibility of an orientation datum with composition says that
`γ_{f ≫ g}` is this composite. -/
noncomputable def OrientationComparisonData.compIso (C : OrientationComparisonData Λ)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (d e : ℕ) [IsSeparated f]
    [SmoothOfRelativeDimension d f] [HasCompactification f] [HasInvertibleExponent Λ X]
    [HasInvertibleExponent Λ Y] [HasCompactification g] [HasCompactification (f ≫ g)]
    (γf : (tateObject Λ X d)⟦(2 * d : ℤ)⟧ ≅ dualizingComplex Λ f)
    (γg : (tateObject Λ Y e)⟦(2 * e : ℤ)⟧ ≅ dualizingComplex Λ g) :
    (tateObject Λ X (d + e : ℕ))⟦(2 * (d + e : ℕ) : ℤ)⟧ ≅
      dualizingComplex Λ (f ≫ g) :=
  eqToIso (by rw [Nat.cast_add, add_comm (d : ℤ)]) ≪≫ (shiftTateObjectAddIso Λ X e d).symm ≪≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj ((tateObject Λ X e)⟦2 * (e : ℤ)⟧)).mapIso γf ≪≫
    (C.upperShriekTateShift f d e).symm ≪≫ (R(f)^![Λ]).mapIso γg ≪≫
    ((C.upperShriekComp f g).app (𝟙_ _)).symm

variable {Λ} in
/-- Blueprint `theorem-smooth-purity-all-admissible-coefficients`: Orientation datum.

The base change `Λ_{X'}(d)[2d] ≅ Rf'^! Λ_{Y'}` of an orientation
`γ_f : Λ_X(d)[2d] ≅ Rf^! Λ_Y` along a cartesian square `g ≫ f = f' ≫ v`:

`Λ_{X'}(d)[2d] ≅ Lg^*(Λ_X(d)[2d]) ≅ Lg^* Rf^! Λ_Y ≅ Rf'^! Lv^* Λ_Y ≅ Rf'^! Λ_{Y'}`.

Naturality of an orientation datum in the base says that `γ_{f'}` is this composite. -/
noncomputable def OrientationComparisonData.baseChangeIso (C : OrientationComparisonData Λ)
    {X Y X' Y' : Scheme.{u}} {g : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {v : Y' ⟶ Y}
    (sq : IsPullback g f' f v) (d : ℕ) [IsSeparated f] [SmoothOfRelativeDimension d f]
    [HasCompactification f] [HasInvertibleExponent Λ X] [HasCompactification f']
    (γf : (tateObject Λ X d)⟦(2 * d : ℤ)⟧ ≅ dualizingComplex Λ f) :
    (tateObject Λ X' d)⟦(2 * d : ℤ)⟧ ≅ dualizingComplex Λ f' :=
  haveI : HasInvertibleExponent Λ X' := .of_hom g
  (leftDerivedUpperStarTateShiftIso Λ g d).symm ≪≫ (L((g)^*[ModuleCat.{u + 1} Λ])).mapIso γf ≪≫
    (C.upperShriekBaseChange sq d).app (𝟙_ _) ≪≫
    (R(f')^![Λ]).mapIso (leftDerivedUpperStarUnitIso _ v)

/-- Blueprint `theorem-smooth-purity-all-admissible-coefficients`: Orientation datum.

In the setting of a six-functor datum with comparison isomorphisms `C`, an *orientation
datum* consists of, for every smooth separated morphism `f : X ⟶ Y` of finite type and of
pure relative dimension `d` (along which the exponent of `Λ` is invertible), an orientation
`γ_f : Λ_X(d)[2d] ≅ Rf^! Λ_Y` (`AlgebraicGeometry.Etale.Orientation`), such that
* `γ` is natural in `Y`: for every cartesian square `g ≫ f = f' ≫ v`, `γ_{f'}` is the base
  change of `γ_f` (`AlgebraicGeometry.Etale.OrientationComparisonData.baseChangeIso`); for
  `v` étale this is the compatibility with étale base change;
* `γ` is compatible with composition: `γ_{f ≫ g}` is obtained from `γ_f` and `γ_g`
  (`AlgebraicGeometry.Etale.OrientationComparisonData.compIso`);
* `γ` is the canonical orientation of the affine line on the projection `𝔸¹_Y ⟶ Y`.

The compatibilities with finite reduction, scalar extension and the pro-étale realization
relate orientation data for different coefficients or sites; they are
`AlgebraicGeometry.Etale.OrientationDatum.IsCompatibleCoefficientChange` and
`AlgebraicGeometry.Etale.OrientationDatum.IsCompatibleProEtaleRealization`. For the
structure morphism `f = a_X` the orientation reads `ω_X ≅ Λ_X(d)[2d]`
(`AlgebraicGeometry.Etale.Orientation.nonempty_iso_dualizingComplex`). -/
structure OrientationDatum (C : OrientationComparisonData Λ) where
  /-- The orientation `γ_f` of a smooth separated `f` of finite type, of relative
  dimension `d`. -/
  orientation {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) [IsSeparated f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f] [HasCompactification f] [HasInvertibleExponent Λ X] :
    Orientation Λ f d
  /-- Naturality in the base, in particular compatibility with étale base change. -/
  orientation_baseChange {X Y X' Y' : Scheme.{u}} {g : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y}
    {v : Y' ⟶ Y} (sq : IsPullback g f' f v) (d : ℕ) [IsSeparated f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f] [HasCompactification f] [HasInvertibleExponent Λ X]
    [IsSeparated f'] [QuasiCompact f'] [SmoothOfRelativeDimension d f']
    [HasCompactification f'] [HasInvertibleExponent Λ X'] :
    (orientation f' d).purity = C.baseChangeIso sq d (orientation f d).purity
  /-- Compatibility with composition. -/
  orientation_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (d e : ℕ) [IsSeparated f]
    [QuasiCompact f] [SmoothOfRelativeDimension d f] [HasCompactification f]
    [HasInvertibleExponent Λ X] [IsSeparated g] [QuasiCompact g]
    [SmoothOfRelativeDimension e g] [HasCompactification g] [HasInvertibleExponent Λ Y]
    [SmoothOfRelativeDimension (d + e) (f ≫ g)] [HasCompactification (f ≫ g)] :
    (orientation (f ≫ g) (d + e)).purity =
      C.compIso f g d e (orientation f d).purity (orientation g e).purity
  /-- Normalization: on the projection of the affine line, the orientation is the canonical
  one. -/
  orientation_affineLine (Y : Scheme.{u})
    [SmoothOfRelativeDimension 1 (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)]
    [HasCompactification (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)]
    [HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin 1); Y)] :
    (orientation (𝔸(ULift.{u} (Fin 1); Y) ↘ Y) 1).purity = C.affineLine Y

variable {Λ} in
/-- Blueprint `theorem-smooth-purity-all-admissible-coefficients`: Orientation datum.

For the structure morphism `a : X ⟶ S` of a smooth separated `X` of finite type and pure
relative dimension `d` over `S`, an orientation datum reads `ω_X ≅ Λ_X(d)[2d]`: the dualizing
complex `ω_X = Ra^! Λ_S` is the shifted Tate twist. -/
theorem OrientationDatum.nonempty_iso_dualizingComplex {C : OrientationComparisonData Λ}
    (o : OrientationDatum Λ C) {X S : Scheme.{u}} (a : X ⟶ S) (d : ℕ) [IsSeparated a]
    [QuasiCompact a] [SmoothOfRelativeDimension d a] [HasCompactification a]
    [HasInvertibleExponent Λ X] :
    Nonempty (dualizingComplex Λ a ≅ (tateObject Λ X d)⟦(2 * d : ℤ)⟧) :=
  (o.orientation a d).nonempty_iso_dualizingComplex

variable (Λ' : Type (u + 1)) [CommRing Λ'] [Finite Λ'] [HasTateTwist Λ']

/-- Blueprint `theorem-smooth-purity-all-admissible-coefficients`: Orientation datum.

A change of coefficients from `Λ` to `Λ'`, such as the finite reduction
`A_{E,n+1} → A_{E,n}` or the scalar extension `A_{E,n} → A_{E',n}` of `def-sf-datum` (A5):
functors `D(X_ét, Λ) ⥤ D(X_ét, Λ')` together with their identifications
`Λ_X(d)[2d] ↦ Λ'_X(d)[2d]` on the twisting objects and `ω_f ↦ ω'_f` on the dualizing
complexes (the compatibility of `R^!` with the change of coefficients). -/
structure CoefficientChange where
  /-- The change of coefficients on `D(X_ét)`. -/
  functor (X : Scheme.{u}) : DerivedCategoryModule Λ X ⥤ DerivedCategoryModule Λ' X
  /-- The change of coefficients of the shifted twisting objects. -/
  tateShiftIso (X : Scheme.{u}) (d : ℤ) :
    (functor X).obj ((tateObject Λ X d)⟦2 * d⟧) ≅ (tateObject Λ' X d)⟦2 * d⟧
  /-- The change of coefficients of the dualizing complexes. -/
  dualizingComplexIso {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    (functor X).obj (dualizingComplex Λ f) ≅
      dualizingComplex Λ' f

variable {Λ Λ'} in
/-- Blueprint `theorem-smooth-purity-all-admissible-coefficients`: Orientation datum.

Compatibility of orientation data over `Λ` and `Λ'` with a change of coefficients `F`: for
every smooth `f`, the change of coefficients of `γ_f` is `γ'_f`. -/
def OrientationDatum.IsCompatibleCoefficientChange {C : OrientationComparisonData Λ}
    {C' : OrientationComparisonData Λ'} (o : OrientationDatum Λ C) (o' : OrientationDatum Λ' C')
    (F : CoefficientChange Λ Λ') : Prop :=
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) [IsSeparated f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f] [HasCompactification f] [HasInvertibleExponent Λ X]
    [HasInvertibleExponent Λ' X],
    (F.functor X).mapIso (o.orientation f d).purity ≪≫ F.dualizingComplexIso f =
      F.tateShiftIso X d ≪≫ (o'.orientation f d).purity

open scoped AlgebraicGeometry.ProEtale in
/-- Blueprint `theorem-smooth-purity-all-admissible-coefficients`: Orientation datum.

The pro-étale realization `D(ν^*) : D(X_ét, Λ) ⥤ D(X_proét, Λ)` on dualizing complexes: the
identification `D(ν^*) ω_f ≅ ω_f^{proét}` of the étale dualizing complex with the pro-étale
one, for `f` smooth of relative dimension `d`. -/
structure ProEtaleRealization where
  /-- The realization of the étale dualizing complex is the pro-étale one. -/
  dualizingComplexIso {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) [IsSeparated f]
    [SmoothOfRelativeDimension d f] [HasCompactification f] [HasInvertibleExponent Λ X]
    [CompactSpace Y] :
    D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj (dualizingComplex Λ f) ≅
      ProEtale.dualizingComplex Λ f

open scoped AlgebraicGeometry.ProEtale in
variable {Λ} in
/-- Blueprint `theorem-smooth-purity-all-admissible-coefficients`: Orientation datum.

Compatibility of an orientation datum `o` with the pro-étale realization `ν`: the pro-étale
orientations `γ^{proét}_f : ν^*(Λ_X(d)[2d]) ≅ ω_f^{proét}` are the realizations of the
étale ones. -/
def OrientationDatum.IsCompatibleProEtaleRealization {C : OrientationComparisonData Λ}
    (o : OrientationDatum Λ C) (ν : ProEtaleRealization Λ)
    (γ : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) [IsSeparated f] [QuasiCompact f]
      [SmoothOfRelativeDimension d f] [HasCompactification f] [HasInvertibleExponent Λ X]
      [CompactSpace Y],
      D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj ((tateObject Λ X d)⟦(2 * d : ℤ)⟧) ≅
        ProEtale.dualizingComplex Λ f) : Prop :=
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) [IsSeparated f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f] [HasCompactification f] [HasInvertibleExponent Λ X]
    [CompactSpace Y],
    γ f d = D(ν^*(X)[ModuleCat.{u + 1} Λ]).mapIso (o.orientation f d).purity ≪≫
      ν.dualizingComplexIso f d

end Etale

end AlgebraicGeometry
