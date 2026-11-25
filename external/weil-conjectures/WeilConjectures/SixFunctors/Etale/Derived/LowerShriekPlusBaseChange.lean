/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism
public import WeilConjectures.SixFunctors.LowerShriek.Formalism.BaseChange

/-!
# Compact-support base change on the bounded below étale derived categories

For a finite coefficient ring `Λ`, a cartesian square
```
X' --g'--> X
|f'        |f
Y' --g---> Y
```
with `g` arbitrary and a compactification `c = (X ⟶[c.i] c.Z ⟶[c.g] Y)` of `f`, the
compact-support exchange map (blueprint `prose-05-31`)

`Ex_!(c) : g^* Rf_!(c) ⟶ Rf'_!(c ×_Y Y') g'^*`

on `D⁺(X_ét, Λ)` is the exchange map `CompactSupportFormalism.shriekBaseChange` of the compact
support formalism `AlgebraicGeometry.Etale.derivedPlusFormalism` of the bounded below étale
derived categories: the derived base change map `Ex_*` of the proper `c.g`
(`AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`, blueprint
`definition-derived-base-change-map`), applied to `(c.i)_! K`, composed with the base change
isomorphism of the extension by zero (blueprint
`proposition-extension-zero-restriction-closed-subscheme--11`). It is an isomorphism: the first
factor by the bounded below proper base change theorem
(`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring`, blueprint
`theorem-proper-base-change-classical-pro`), the second by base change for the extension by zero
(blueprint `proposition-composition-base-change-rf-shriek`).

## Main definitions

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap`: the
  exchange map `Ex_!(c)` on `D⁺`.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekPlusBaseChangeMap`: the exchange map
  `Ex_! : g^* R(f)_! ⟶ R(f')_! g'^*` of the canonical compactly supported direct images on `D⁺`.

## Main statements

- `AlgebraicGeometry.Etale.derivedPlusFormalism_pfBaseChange`: the base change map of the
  formalism is `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`.
- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap`
  and `AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekPlusBaseChangeMap`: compact-support
  base change on `D⁺` (blueprint `proposition-composition-base-change-rf-shriek`). Naturality in `K`
  holds since the exchange maps are natural transformations; the identity and pasting laws and the
  independence of the compactification are `CompactSupportFormalism.shriekBaseChange_id`,
  `CompactSupportFormalism.shriekBaseChange_paste_horiz`,
  `CompactSupportFormalism.lowerShriekBaseChange_paste_vert` and
  `CompactSupportFormalism.lowerShriekBaseChange_eq`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Formalism

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A] [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
  [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]

variable {U' U Z' Z : Scheme.{u}}

/-- The square isomorphism of the compact support formalism `derivedPlusFormalism A` is the
pullback comparison `θ_sq` of `AlgebraicGeometry.Etale.pullbackSquareComparison`, inverted. -/
lemma derivedPlusFormalism_sqIso (t : U' ⟶ U) (l : U' ⟶ Z') (r : U ⟶ Z) (b : Z' ⟶ Z)
    (w : t ≫ r = l ≫ b) :
    (derivedPlusFormalism A).sqIso t l r b w =
      (pullbackSquareComparison A (CommSq.mk w)).symm := by
  rw [pullbackSquareComparison_eq]
  ext M
  have key : ∀ (d : U' ⟶ Z) (hd : d = l ≫ b)
      (h : (derivedPlusFormalism A).pb d = (derivedPlusFormalism A).pb (l ≫ b)),
      (eqToIso h).hom.app M ≫ (upperStarCompDerivedPlus A l b (l ≫ b) rfl).hom.app M =
        (upperStarCompDerivedPlus A l b d hd).hom.app M := by
    intro d hd h
    subst hd
    simp
  simp only [ExchangeFormalism.sqIso, ExchangeFormalism.pbComp',
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Iso.trans_inv, Iso.symm_inv]
  simp only [eqToIso_refl, Iso.refl_inv, NatTrans.id_app, Category.comp_id]
  exact congrArg _ (key (t ≫ r) w _)

/-- The adjunctions `f^* ⊣ f_*` of the compact support formalism `derivedPlusFormalism A` are the
bounded below derived adjunctions. -/
lemma derivedPlusFormalism_adj {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (derivedPlusFormalism A).adj f = (upperStarLowerStarAdjunction A f).derivedPlus := rfl

/-- The base change map of pushforwards of the compact support formalism of `D⁺`, as a mate. -/
lemma derivedPlusFormalism_pfBaseChange_eq_mateEquiv (t : U' ⟶ U) (l : U' ⟶ Z') (r : U ⟶ Z)
    (b : Z' ⟶ Z) (w : t ≫ r = l ≫ b) :
    (derivedPlusFormalism A).pfBaseChange t l r b w =
      mateEquiv (upperStarLowerStarAdjunction A r).derivedPlus
        (upperStarLowerStarAdjunction A l).derivedPlus
        (TwoSquare.mk _ _ _ _ (pullbackSquareComparison A (CommSq.mk w)).hom) := by
  rw [ExchangeFormalism.pfBaseChange, derivedPlusFormalism_sqIso]
  rfl

/-- **The base change map of pushforwards of the compact support formalism of `D⁺`** is the
derived base change map `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus` (blueprint
`definition-derived-base-change-map`). -/
lemma derivedPlusFormalism_pfBaseChange (t : U' ⟶ U) (l : U' ⟶ Z') (r : U ⟶ Z) (b : Z' ⟶ Z)
    (w : t ≫ r = l ≫ b) :
    ((derivedPlusFormalism A).pfBaseChange t l r b w) =
      derivedBaseChangeMapPlus A (CommSq.mk w) := by
  rw [← baseChange_eq_derivedBaseChangeMapPlus, derivedPlusFormalism_pfBaseChange_eq_mateEquiv]
  ext K
  rw [baseChange_app_eq_mateEquiv]

end Formalism

section Torsion

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **Proper base change in the compact support formalism of `D⁺`** for finite coefficients:
the derived base change map of a cartesian square with proper right side is an isomorphism
(`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring`, blueprint
`theorem-proper-base-change-classical-pro`). -/
instance [Finite Λ] : (derivedPlusFormalism (ModuleCat.{u + 1} Λ)).HasProperBaseChange where
  isIso_pfBaseChange {U' U Z' Z t l r b} _ h := by
    rw [derivedPlusFormalism_pfBaseChange, ← baseChange_eq_derivedBaseChangeMapPlus]
    exact isIso_baseChange_of_isProper_of_isAddTorsion_ring Λ isAddTorsion_of_finite h

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme--11`: Derived
extension-by-zero base change.

For a cartesian square
```
U' --t--> U
|l        |r
Z' --b--> Z
```
with `l` and `r` open immersions and `Λ` finite, the base change map `t^* ⋙ l_! ⟶ r_! ⋙ b^*`,
i.e. `l_! t^* K ⟶ b^* r_! K`, of the extension by zero on `D⁺(-_ét, Λ)` is an isomorphism; its
inverse is the map `b^{-1} r_! K ⟶ l_! t^{-1} K` of the blueprint. It is natural, being a
natural transformation; it is the identity for an identity square
(`ExchangeFormalism.baseChange_id_horiz`, `ExchangeFormalism.baseChange_id_vert`)
and compatible with pasting (`ExchangeFormalism.baseChange_paste_horiz`,
`ExchangeFormalism.baseChange_paste_vert`). On sheaves this is
`AlgebraicGeometry.Etale.isIso_openImmersionLowerShriekBaseChangeMap`
(`proposition-extension-zero-restriction-closed-subscheme--11`), and on the unbounded derived
categories `AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekBaseChangeIso`. -/
theorem isIso_derivedPlusFormalism_baseChange [Finite Λ] {U' U Z' Z : Scheme.{u}}
    {t : U' ⟶ U} {l : U' ⟶ Z'} {r : U ⟶ Z} {b : Z' ⟶ Z} [IsOpenImmersion l] [IsOpenImmersion r]
    (h : IsPullback t l r b) :
    IsIso ((derivedPlusFormalism (ModuleCat.{u + 1} Λ)).baseChange t l r b h.w) :=
  CompactSupportFormalism.HasBaseChange.isIso_baseChange h

/-- Blueprint `prose-05-31`: Compact-support exchange map.

**The compact-support exchange map on `D⁺` along a compactification** `Ex_!(c)`: for a
cartesian square `g' ≫ f = f' ≫ g`, a compactification `c` of `f` and `Λ` finite, the natural
transformation `g^* Rf_!(c) ⟶ Rf'_!(c ×_Y Y') g'^*` of functors
`D⁺(X_ét, Λ) ⥤ D⁺(Y'_ét, Λ)`, where `c ×_Y Y' = c.ofIsPullback sq` is the base changed
compactification of `f'` (blueprint `remark-base-change-compactification--1`). It is the derived
base change map `derivedBaseChangeMapPlus` of the proper map `c.g`
(`AlgebraicGeometry.Etale.derivedPlusFormalism_pfBaseChange`), applied after `(c.i)_!`,
followed by the inverse of the base change isomorphism of the extension by zero. -/
noncomputable def rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap [Finite Λ]
    (sq : IsPullback g' f' f g) (c : Compactification f) :
    Rf_!(c)[ModuleCat.{u + 1} Λ]+ ⋙ D+((g)^*[ModuleCat.{u + 1} Λ]) ⟶
      D+((g')^*[ModuleCat.{u + 1} Λ]) ⋙ Rf_!(c.ofIsPullback sq)[ModuleCat.{u + 1} Λ]+ :=
  ((derivedPlusFormalism (ModuleCat.{u + 1} Λ)).shriekBaseChangeOfIsPullback sq c)

/-- Blueprint `proposition-composition-base-change-rf-shriek`: Compact-support base change at finite
coefficients.

**Compact-support base change on `D⁺`**: for a cartesian square
```
X' --g'--> X
|f'        |f
Y' --g---> Y
```
with `g` arbitrary, a compactification `c` of `f` and a finite coefficient ring `Λ`, the
exchange map `Ex_!(c) : g^* Rf_!(c) K ⟶ Rf'_!(c ×_Y Y') g'^* K` is an isomorphism in
`D⁺(Y'_ét, Λ)` for every `K ∈ D⁺(X_ét, Λ)`.

It is natural in `K`, being a natural transformation. Its identity and horizontal pasting laws
are `CompactSupportFormalism.shriekBaseChange_id` and
`CompactSupportFormalism.shriekBaseChange_paste_horiz`, its compatibility with the comparisons
along refinements of compactifications is
`CompactSupportFormalism.shriekBaseChange_refinementComparison`, and the independence of the
compactification and vertical pasting for the canonical exchange map
`AlgebraicGeometry.Etale.rightDerivedLowerShriekPlusBaseChangeMap` are
`CompactSupportFormalism.lowerShriekBaseChange_eq` and
`CompactSupportFormalism.lowerShriekBaseChange_paste_vert`. -/
instance isIso_rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap [Finite Λ]
    (sq : IsPullback g' f' f g) (c : Compactification f) :
    IsIso (rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap Λ sq c) :=
  CompactSupportFormalism.isIso_shriekBaseChange _ c (c.ofIsPullback sq) _
    (c.isPullback_i_ofIsPullback sq) (c.isPullback_g_ofIsPullback sq).flip

/-- **The compact-support exchange map** `Ex_! : g^* R(f)_! ⟶ R(f')_! g'^*` of the canonical
compactly supported direct images on `D⁺(-_ét, Λ)`, for `Λ` finite: the exchange map along the
chosen compactification of `f`, followed by the comparison isomorphism with the chosen
compactification of `f'`. (blueprint: `prose-05-31`) -/
noncomputable def rightDerivedLowerShriekPlusBaseChangeMap [Finite Λ] [HasCompactification f]
    [HasCompactification f'] [QuasiCompact f'] (sq : IsPullback g' f' f g) :
    R(f)_![ModuleCat.{u + 1} Λ]+ ⋙ D+((g)^*[ModuleCat.{u + 1} Λ]) ⟶
      D+((g')^*[ModuleCat.{u + 1} Λ]) ⋙ R(f')_![ModuleCat.{u + 1} Λ]+ :=
  ((derivedPlusFormalism (ModuleCat.{u + 1} Λ)).lowerShriekBaseChange sq)

/-- Blueprint `sk-prop-sf-cbc`: Compact-support base change, clause (a) on the small étale site.

**Compact-support base change on `D⁺(X_ét, Λ)`**: for `f` admitting a compactification, `g`
arbitrary, a cartesian square with `f'` quasi-compact and admitting a compactification, and `Λ`
finite, the exchange transformation `Ex_! : g^* Rf_! ⟶ Rf'_! g'^*` is an isomorphism of
functors `D⁺(X_ét, Λ) ⥤ D⁺(Y'_ét, Λ)`. This is `proposition-composition-base-change-rf-shriek` for
the chosen compactifications. The unbounded form is
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap`. -/
instance isIso_rightDerivedLowerShriekPlusBaseChangeMap [Finite Λ] [HasCompactification f]
    [HasCompactification f'] [QuasiCompact f'] (sq : IsPullback g' f' f g) :
    IsIso (rightDerivedLowerShriekPlusBaseChangeMap Λ sq) :=
  CompactSupportFormalism.isIso_lowerShriekBaseChange _ _

end Torsion

end Etale

end AlgebraicGeometry
