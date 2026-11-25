/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.QuotPowTriangle
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionUnit
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
public import WeilConjectures.SixFunctors.Etale.Derived.TensorRightUnitor
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekTensorRight
import WeilConjectures.SixFunctors.Etale.Derived.ConstantTensorProjection
import WeilConjectures.AlgebraicGeometry.CompactificationUpperShriek.CompactificationUpperShriek

/-!
# Compact-support base change, the projection formula and finite reduction

The two theorems of the six-functor formalism attached to `Rf_!` that the purity chapter
consumes: compact-support base change for a cartesian square, and the projection formula.
Alongside them, the compatibilities of `Rf_!`, `Lf^*` and `Rf_*` with the reduction
`K ↦ K ⊗ᴸ (Λ/J)` of the coefficients modulo an ideal `J`.

## Implementation notes

Compact-support base change is stated as `IsIso Ex_!` for the exchange
`Ex_! : Lg^* Rf_! ⟶ Rf'_! Lg'^*` of the framework chapter's `sk-def-sf-exchanges`, on the
unbounded derived categories. The main form is for the exchange map
`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationBaseChangeMap` computed with
an arbitrary compactification `c` of `f`: it reduces to unbounded proper base change for the
proper map of `c`. The blueprint states it on `D⁺` instead.

The statement for the canonical exchange map
`AlgebraicGeometry.Etale.rightDerivedLowerShriekBaseChangeMap` is a corollary. That map is only
defined for `f'` quasi-compact, and it goes through the comparison isomorphism
`AlgebraicGeometry.Etale.rightDerivedLowerShriekIso`, which is defined for torsion coefficients
and rests on unbounded proper base change. The hypothesis `[QuasiCompact f']` should disappear
once `Ex_!` is constructed on `D⁺`.

The projection formula is stated as the invertibility of the projection map
`PF : Rf_! K ⊗^L L ⟶ Rf_!(K ⊗^L Lf^* L)` of `AlgebraicGeometry.Etale.projectionMap`
(`AlgebraicGeometry.Etale.hasProjectionFormula_of_finite`, in
`WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula`); its case of `sk-thm-sf-pf-finite`,
for `K` bounded constructible and `L` in `Dᵇctf`, is
`AlgebraicGeometry.Etale.hasProjectionFormula_of_boundedConstructible`.

The exchange `Ex_*` for `Rf_*` does already exist in this repository, as
`AlgebraicGeometry.Etale.baseChange` and `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_of_finite`
- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap`
- `AlgebraicGeometry.Etale.hasProjectionFormula_of_boundedConstructible`
- `AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerShriek_of_finite`,
  `AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerStar`
- `AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_leftDerivedUpperStar`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}

section Exchange

variable {X' Y' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- **Compact-support base change along a compactification.** For a cartesian square

```
  X' --g'--> X
  |          |
  f'         f
  ↓          ↓
  Y' --g---> Y
```

with `g` arbitrary, a compactification `c` of `f` and `Λ` finite, the exchange transformation
`Ex_!(c) : Lg^* Rf_!(c) ⟶ Rf'_!(c ×_Y Y') Lg'^*` of `sk-def-sf-exchanges`, computed with `c`
and its base change, is an isomorphism of functors `D(X_ét, Λ) ⥤ D(Y'_ét, Λ)`.

This is the blueprint's raw finite compact-support base change theorem, stated on the
unbounded derived categories rather than on `D⁺`. By
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap` it
reduces to the invertibility of the derived base change map `Ex_*` for the proper map `c.g`,
which is unbounded proper base change
`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring`. -/
theorem isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_of_finite [Finite Λ]
    (sq : IsPullback g' f' f g) (c : Compactification f) :
    IsIso (rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} Λ) sq c) :=
  have := isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring Λ isAddTorsion_of_finite
    (IsPullback.of_hasPullback c.g g)
  isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap _ sq c

/-- Blueprint `proposition-composition-base-change-rf-shriek--4`: Compact-support base change

**Compact-support base change.** For `f : X ⟶ Y` admitting a compactification, `g : Y' ⟶ Y`
arbitrary, a cartesian square

```
  X' --g'--> X
  |          |
  f'         f
  ↓          ↓
  Y' --g---> Y
```

with `f'` quasi-compact and admitting a compactification, and `Λ` finite, the exchange
transformation `Ex_! : Lg^* Rf_! ⟶ Rf'_! Lg'^*` of
`proposition-composition-base-change-rf-shriek--4` is an isomorphism of functors
`D(X_ét, Λ) ⥤ D(Y'_ét, Λ)`.

`Ex_!` is `Ex_!(c)` for the chosen compactification `c` of `f`, followed by the comparison
isomorphism `AlgebraicGeometry.Etale.rightDerivedLowerShriekIso` for `f'`, so this follows from
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_of_finite`.
That comparison isomorphism is
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekOfCompactificationComparison`, which rests
on unbounded proper base change; the blueprint states this theorem on `D⁺`. If `f` is
quasi-compact, `[QuasiCompact f']` is obtained from `sq` by `MorphismProperty.of_isPullback`. -/
-- TODO: state this for the `D⁺` exchange map built from `derivedBaseChangeMapPlus`, and drop
-- `[QuasiCompact f']` once `Ex_!` is constructed without it.
theorem isIso_rightDerivedLowerShriekBaseChangeMap [Finite Λ] [HasCompactification f]
    [HasCompactification f'] [QuasiCompact f'] (sq : IsPullback g' f' f g) :
    IsIso (rightDerivedLowerShriekBaseChangeMap Λ sq) := by
  have := isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_of_finite Λ sq
    (HasCompactification.compactification f)
  unfold rightDerivedLowerShriekBaseChangeMap
  infer_instance

end Exchange

section Projection

variable (f : X ⟶ Y) [HasCompactification f]

/-- Blueprint `sk-thm-sf-pf-finite`: Projection formula, finite coefficients

Blueprint `thm-sf-pf-finite`: Finite coefficients on the étale site

This is also blueprint `thm-sf-pf-finite` (Finite coefficients on the étale site), the same
statement in the setting of the six-functor datum `def-sf-datum`.

**The projection formula at finite coefficients.** For `Λ` a finite coefficient ring whose
exponent is invertible on `Y`, `f : X ⟶ Y` separated of finite type, `K` bounded constructible
on `X` and `L` bounded constructible *of finite Tor amplitude* on `Y`, the projection map

`PF : Rf_! K ⊗^L L ⟶ Rf_!(K ⊗^L Lf^* L)`

is an isomorphism, naturally in `K` and `L`: the projection map is a natural transformation, and
it is invertible at every such `K` and `L`. It is the case of
`AlgebraicGeometry.Etale.hasProjectionFormula_of_finite` treated by the fibrewise argument of
the blueprint, which represents the stalks of `L` by bounded complexes of finite free modules;
the hypotheses on `K` and `L` are not needed for the conclusion. -/
theorem hasProjectionFormula_of_boundedConstructible [Finite Λ]
    [HasInvertibleExponent Λ Y] [LocallyOfFiniteType f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (_hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (_hL : DerivedCategory.boundedConstructibleFiniteTor Λ Y L) :
    HasProjectionFormula (ModuleCat.{u + 1} Λ) f K L :=
  hasProjectionFormula_of_finite Λ f K L

/-- Blueprint `sk-prop-sf-pf-reduction`: Projection formula: compatibility with finite
reduction

**`Rf_!` commutes with finite reduction.** For a finite coefficient ring `Λ` (the blueprint's
`A_{E,n}`) and an ideal `J` of `Λ`,

`Rf_!(K ⊗^L (Λ/J)_X) ≅ (Rf_! K) ⊗^L (Λ/J)_Y`.

This is one of the three compatibilities out of which the comparison square of
`sk-prop-sf-pf-reduction` (`AlgebraicGeometry.Etale.projectionMapOfCompactification_constantSingle`)
is built, and the only one that is not formal; it is what reduces the projection formula at
level `n` to the projection formula at level `m ≤ n`. The isomorphism is the comparison
`AlgebraicGeometry.Etale.rightDerivedLowerShriekReductionModIdealMap`, the projection map at
`(K, (Λ/J)_Y)` followed by `Lf^*(Λ/J)_Y ≅ (Λ/J)_X`, invertible by the projection formula at
finite coefficients. -/
theorem nonempty_iso_reductionModIdeal_rightDerivedLowerShriek_of_finite [Finite Λ]
    (J : Ideal Λ) :
    Nonempty (R(f)_![ModuleCat.{u + 1} Λ] ⋙ reductionModIdeal Λ Y J ≅
      reductionModIdeal Λ X J ⋙ R(f)_![ModuleCat.{u + 1} Λ]) :=
  ⟨asIso (rightDerivedLowerShriekReductionModIdealMap Λ J
    (HasCompactification.compactification f))⟩

omit [HasCompactification f] in
/-- Blueprint `sk-prop-sf-pf-reduction`: Projection formula: compatibility with finite
reduction

**`Lf^*` commutes with finite reduction.** For an ideal `J` of `Λ`,

`Lf^*(L ⊗^L (Λ/J)_Y) ≅ (Lf^* L) ⊗^L (Λ/J)_X`,

because `Lf^*` is monoidal and carries the constant complex on `Λ/J` to the constant complex
on `Λ/J`. Together with the associativity of `⊗^L` and
`AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerShriek_of_finite` this
is what makes the comparison square of the blueprint commute. -/
theorem nonempty_iso_reductionModIdeal_leftDerivedUpperStar (J : Ideal Λ) :
    Nonempty (reductionModIdeal Λ Y J ⋙ L((f)^*[ModuleCat.{u + 1} Λ]) ≅
      L((f)^*[ModuleCat.{u + 1} Λ]) ⋙ reductionModIdeal Λ X J) :=
  ⟨leftDerivedUpperStarReductionModIdealIso Λ J f⟩

end Projection

section LowerStar

/-- Blueprint `proposition-six-operations-change-coefficients`: Basic operations and coefficient
reduction; the ordinary direct image. Used in blueprint `lemma-perfect-complexes-geometric-point`.

**`Rf_*` commutes with reduction modulo a principal ideal.** For `f : X ⟶ Y` arbitrary and a
principal ideal `J` of a domain `Λ`, the square

```
  D(X_ét, Λ) ---Rf_*---> D(Y_ét, Λ)
      |                      |
  – ⊗ᴸ (Λ/J)_X           – ⊗ᴸ (Λ/J)_Y
      ↓                      ↓
  D(X_ét, Λ) ---Rf_*---> D(Y_ét, Λ)
```

commutes up to isomorphism:

`R(f)_* ⋙ reductionModIdeal Λ Y J ≅ reductionModIdeal Λ X J ⋙ R(f)_*`.

The hypotheses only serve to make `Λ/J` a perfect `Λ`-module, which is all the proof uses:
for `J = (π)` with `π ≠ 0`, the module `Λ/J` is the cokernel of `π : Λ → Λ`, and for `J = 0` it
is `Λ`. So the constant complex `(Λ/J)_Y` is dualizable, and the comparison
`AlgebraicGeometry.Etale.rightDerivedLowerStarReductionModIdealMap` (the projection map of `Rf_*`
at `(Λ/J)_Y`) is an isomorphism
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarReductionModIdealMap_span_pow`).
This is the reduction `𝒪_E → 𝒪_E/𝔪_Eⁿ` that carries `lemma-perfect-complexes-geometric-point` from
the finite stages to the integral stage `𝒪_E`, and the input of
`AlgebraicGeometry.Etale.derivedComplete_rightDerivedLowerStar`. -/
theorem nonempty_iso_reductionModIdeal_rightDerivedLowerStar (f : X ⟶ Y) [IsDomain Λ]
    (J : Ideal Λ) (hJ : J.IsPrincipal) :
    Nonempty (R((f)_*[ModuleCat.{u + 1} Λ]) ⋙ reductionModIdeal Λ Y J ≅
      reductionModIdeal Λ X J ⋙ R((f)_*[ModuleCat.{u + 1} Λ])) := by
  obtain ⟨π, rfl⟩ := hJ.principal
  by_cases hπ : π = 0
  · have hbot : (Submodule.span Λ {π} : Ideal Λ) = ⊥ := by
      rw [hπ]
      exact Ideal.span_singleton_eq_bot.mpr rfl
    rw [hbot]
    have := isIso_rightDerivedLowerStarReductionModIdealMap_bot Λ f
    exact ⟨asIso (rightDerivedLowerStarReductionModIdealMap Λ ⊥ f)⟩
  · have hpow : (Submodule.span Λ {π} : Ideal Λ) = Ideal.span {π} ^ 1 := (pow_one _).symm
    rw [hpow]
    have := isIso_rightDerivedLowerStarReductionModIdealMap_span_pow
      (mem_nonZeroDivisors_of_ne_zero hπ) 1 f
    exact ⟨asIso (rightDerivedLowerStarReductionModIdealMap Λ (Ideal.span {π} ^ 1) f)⟩

/-- **`Rf_!` commutes with reduction modulo a principal ideal of a domain.** This is the
analogue of
`AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerShriek_of_finite`
where `Λ/J` is a perfect `Λ`-module. For a compactification `f = g ∘ j`, the extension by zero
`j_!` commutes with tensoring by any constant complex (the projection formula for an open
immersion), and `Rg_*` commutes with the reduction by
`AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerStar`. -/
theorem nonempty_iso_reductionModIdeal_rightDerivedLowerShriek_of_isPrincipal (f : X ⟶ Y)
    [HasCompactification f] [IsDomain Λ] (J : Ideal Λ) (hJ : J.IsPrincipal) :
    Nonempty (R(f)_![ModuleCat.{u + 1} Λ] ⋙ reductionModIdeal Λ Y J ≅
      reductionModIdeal Λ X J ⋙ R(f)_![ModuleCat.{u + 1} Λ]) := by
  let c := HasCompactification.compactification f
  obtain ⟨e⟩ := nonempty_iso_reductionModIdeal_rightDerivedLowerStar Λ c.g J hJ
  let eo : reductionModIdeal Λ X J ⋙ D((c.i)_!open[ModuleCat.{u + 1} Λ]) ≅
      D((c.i)_!open[ModuleCat.{u + 1} Λ]) ⋙ reductionModIdeal Λ c.Z J :=
    Functor.isoWhiskerRight ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).flip.mapIso
        (leftDerivedUpperStarSingleConstantSheafIso _ c.i (ModuleCat.of Λ (Λ ⧸ J)))).symm _ ≪≫
      derivedTensorRightCompOpenImmersionLowerShriekIso _ c.i _
  exact ⟨Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ e ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eo.symm _ ≪≫
    Functor.associator _ _ _⟩

end LowerStar

end Etale

end AlgebraicGeometry
