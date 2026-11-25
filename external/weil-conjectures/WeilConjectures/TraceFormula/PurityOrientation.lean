/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothRelativeDimensionCover
public import WeilConjectures.CategoryTheory.Monoidal.Closed.IhomUnitTensorComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleOpenCoverIsIso
public import WeilConjectures.TraceFormula.PurityBaseChangeRestriction
public import WeilConjectures.TraceFormula.PurityOrientationPure
public import WeilConjectures.SmoothPurity.UpperShriekSmoothBaseChange

/-!

# The relative dualizing complex of a smooth morphism

For a smooth morphism `f : X ⟶ Y` of separated `k`-schemes of finite type, the *relative
dualizing complex* `ω_f = Rf^! ℚ̄_ℓ` on `X` is the object through which smooth purity is
expressed: `Rf^! K ≅ Lf^* K ⊗ ω_f` (`ProEtale.CondensedRing.upperShriekUnitTensorMap`). This file
records the two properties of `ω_f` (its *orientation*, blueprint
`proposition-relative-dualizing-complex`, `proposition-exceptional-inverse-image-smooth-morphism`)
which the proof of smooth purity for `ℚ̄_ℓ`-coefficients takes as input:

- `ProEtale.CondensedRing.isDualizable_upperShriek_unit_of_smooth`: `ω_f` is dualizable, proved in
  `WeilConjectures.SmoothPurity.UpperShriekUnitDualizable` from the integral dualizing complex;
- `ProEtale.CondensedRing.isIso_upperShriekBaseChange_unit_of_smooth`: the formation of `ω_f`
  commutes with base change.

Both are consequences of the trace isomorphism `ω_f ≅ ℚ̄_ℓ(d)[2d]` of a morphism smooth of pure
relative dimension `d` (`ProEtale.CondensedRing.isIso_smoothPurityMap`, built from the smooth trace
`ProEtale.CondensedRing.smoothTrace` of `WeilConjectures.SmoothPurity.Defs`), of the invertibility
of the Tate twists `ℚ̄_ℓ(d)` (blueprint `definition-tate-twists`: "each `Λ_X(1)` is locally free of
rank one") and of the compatibility of the smooth trace with base change (SGA 4, Exposé XVIII,
Théorème 2.9 (Var 4)). Neither the smooth trace nor the comparison isomorphisms of Tate twists
along pullbacks are available (see the module docstring of `WeilConjectures.SmoothPurity.Defs`
and of `WeilConjectures.TateTwist.ProEtale`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]

/-- **The formation of the relative dualizing complex of a smooth morphism commutes with base
change** (blueprint `proposition-exceptional-inverse-image-smooth-morphism`, (G12) at the unit: "it
identifies `g'^* ω_f` with `ω_{f'}`"; `proposition-compatibility-purity-base-change` (1); SGA 4,
Exposé XVIII, Théorème 2.9 (Var 4), the compatibility of the smooth trace with base change): for a
cartesian square with `f` smooth, the exceptional base change map at the unit
`Lg'^* Rf^! ℚ̄_ℓ ⟶ Rf'^! Lg^* ℚ̄_ℓ` is an isomorphism. -/
theorem isIso_upperShriekBaseChange_unit_of_smooth {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} (sq : IsPullback g' f' f g) [Smooth f.left] :
    IsIso (upperShriekBaseChange ℓ sq (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧))) := by
  refine isIso_upperShriekBaseChange_of_forall_smoothOfRelativeDimension ℓ sq _ fun U d hd ↦ ?_
  have : SmoothOfRelativeDimension d (pullback.snd (overRestrictι X U ≫ f) g).left :=
    have := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
    MorphismProperty.of_isPullback (isPullback_pullback_left _ g) hd
  exact isIso_upperShriekBaseChange_unit_of_smoothOfRelativeDimension ℓ
    (IsPullback.of_hasPullback (overRestrictι X U ≫ f) g) d

end AlgebraicGeometry.ProEtale.CondensedRing
