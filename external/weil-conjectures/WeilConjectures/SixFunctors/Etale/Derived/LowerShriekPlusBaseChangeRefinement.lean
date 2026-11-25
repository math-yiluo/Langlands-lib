/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange
public import WeilConjectures.SixFunctors.LowerShriek.Formalism.BaseChange

/-!
# Base change for `Rf_!` along a compactification

For a cartesian square
```
X' --u--> X
|f'       |f
Y' --v--> Y
```
a compactification `c = (X ⟶[j] Z ⟶[p] Y)` of `f` and its base change
`c ×_Y Y' = (X' ⟶[j'] Z' ⟶[p'] Y')`, with `v' : Z' ⟶ Z`, this file records the three statements
of blueprint `proposition-composition-base-change-rf-shriek--4` for the compactly supported direct
images of the compact support formalism `AlgebraicGeometry.Etale.derivedPlusFormalism` of the
bounded below derived categories `D⁺(-_ét, Λ)`, `Λ` finite:

1. the base change map `j'_! u^* ⟶ v'^* j_!` of the extension by zero is an isomorphism;
2. the composite `β : v^* Rp_* j_! ⟶ Rp'_* v'^* j_! ⟶ Rp'_* j'_! u^*` of proper base change and
   (1), i.e. the exchange map `Ex_!(c)`, is an isomorphism;
3. `β` is compatible with the comparison maps along refinements of compactifications of `f`
   and of `f'`.

The canonical composition law of `Rf_!` with its unit and associativity constraints is also
stated on `D⁺` (`AlgebraicGeometry.Etale.rightDerivedLowerShriekPlusCompIso`). On the
unbounded derived categories, (1) is
`AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekBaseChangeIso` and (2) is
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_of_finite`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {v : Y' ⟶ Y} {u' : X' ⟶ X}

/-- Blueprint `proposition-composition-base-change-rf-shriek--4`, parts (1) and (2): Base change for
`Rf_!` on the localizing category.

For a cartesian square `u ≫ f = f' ≫ v`, a compactification `c = (X ⟶[j] Z ⟶[p] Y)` of `f` with
base change `c ×_Y Y' = (X' ⟶[j'] Z' ⟶[p'] Y')` (`AlgebraicGeometry.Compactification.ofIsPullback`)
and `Λ` finite, on the bounded below derived categories `D⁺(-_ét, Λ)`:

1. the base change map `u^* ⋙ j'_! ⟶ j_! ⋙ v'^*` of the extension by zero, for the cartesian
   square `AlgebraicGeometry.Compactification.isPullback_i_ofIsPullback`, is an isomorphism;
2. the exchange map `β = Ex_!(c) : v^* Rp_* j_! ⟶ Rp'_* j'_! u^*`
   (`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap`), the
   composite of proper base change for `p` and the inverse of (1), is an isomorphism.

Part (3), the compatibility of `β` with refinements of compactifications, is
`AlgebraicGeometry.Etale.derivedPlusFormalism_shriekBaseChange_refinementComparison`. -/
theorem isIso_derivedPlusFormalism_baseChange_and_shriekBaseChange
    (sq : IsPullback u' f' f v) (c : Compactification f) :
    IsIso ((derivedPlusFormalism (ModuleCat.{u + 1} Λ)).baseChange u' (c.ofIsPullback sq).i c.i
        (pullback.fst c.g v) (c.isPullback_i_ofIsPullback sq).w) ∧
      IsIso (rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap Λ sq c) :=
  ⟨isIso_derivedPlusFormalism_baseChange Λ (c.isPullback_i_ofIsPullback sq), inferInstance⟩

omit [Finite Λ] in
/-- Blueprint `proposition-composition-base-change-rf-shriek--4`, part (3): **the base change
isomorphism `β` is compatible with the comparisons between compactifications**. Let `r : c ⟶ d` and
`r' : c' ⟶ d'` be refinements of compactifications of `f` and of `f'` (with cartesian squares
over `X` and `X'`), and let `hc : c'.Z ⟶ c.Z`, `hd : d'.Z ⟶ d.Z` exhibit `c'` and `d'` as base
changes of `c` and `d`, compatibly with `r` and `r'`. Then the exchange maps of `c` and `d` are
intertwined by the comparison maps `Rf_!(d) ⟶ Rf_!(c)` and `Rf'_!(d') ⟶ Rf'_!(c')`, on
`D⁺(-_ét, Λ)` for `Λ` finite. -/
theorem derivedPlusFormalism_shriekBaseChange_refinementComparison {c d : Compactification f}
    {c' d' : Compactification f'} (r : c.Refinement d) (hr : IsPullback c.i (𝟙 X) r.hom d.i)
    (r' : c'.Refinement d') (hr' : IsPullback c'.i (𝟙 X') r'.hom d'.i) (hc : c'.Z ⟶ c.Z)
    (hci : IsPullback u' c'.i c.i hc) (hcp : IsPullback hc c'.g c.g v) (hd : d'.Z ⟶ d.Z)
    (hdi : IsPullback u' d'.i d.i hd) (hdp : IsPullback hd d'.g d.g v)
    (hcomm : hc ≫ r.hom = r'.hom ≫ hd) :
    Functor.whiskerRight ((derivedPlusFormalism (ModuleCat.{u + 1} Λ)).refinementComparison r hr)
        ((derivedPlusFormalism (ModuleCat.{u + 1} Λ)).pb v) ≫
        ((derivedPlusFormalism (ModuleCat.{u + 1} Λ)).shriekBaseChange c c' hc hci hcp) =
      ((derivedPlusFormalism (ModuleCat.{u + 1} Λ)).shriekBaseChange d d' hd hdi hdp) ≫
        Functor.whiskerLeft ((derivedPlusFormalism (ModuleCat.{u + 1} Λ)).pb u')
          ((derivedPlusFormalism (ModuleCat.{u + 1} Λ)).refinementComparison r' hr') :=
  CompactSupportFormalism.shriekBaseChange_refinementComparison _ r hr r' hr' hc hci hcp hd hdi
    hdp hcomm

end Etale

end AlgebraicGeometry
