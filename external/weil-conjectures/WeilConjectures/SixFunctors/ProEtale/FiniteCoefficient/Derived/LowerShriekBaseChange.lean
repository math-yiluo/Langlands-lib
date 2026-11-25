/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.BaseChange

/-!
# Compact-support base change on the pro-étale site, finite coefficients

Consider a cartesian square of schemes
```
X' --g'--> X
|f'        |f
Y' --g---> Y
```
and a compactification `c = (X ⟶[c.i] c.Z ⟶[c.g] Y)` of `f`, with base change
`c' = c.ofIsPullback sq` (blueprint `remark-base-change-compactification--1`), whose compactifying
scheme is `c.Z ×_Y Y'` with projection `h : c'.Z ⟶ c.Z`. The *pro-étale compact-support exchange
map* (blueprint `prose-05-31`, transported to the pro-étale site)

`Ex_!(c) : Lg^* Rf_!(c) ⟶ Rf'_!(c') Lg'^*`

on the unbounded derived categories of pro-étale sheaves is the derived base change map
`Lg^* R(c.g)_* ⟶ R(c'.g)_* Lh^*` of the proper `c.g`
(`AlgebraicGeometry.ProEtale.derivedBaseChangeMap`)
applied after `(c.i)_!`, followed by the inverse of the base change isomorphism
`(c'.i)_! g'^* ≅ h^* (c.i)_!` of the extension by zero
(`AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekBaseChangeIso`, blueprint
`proposition-extension-zero-restriction-closed-subscheme--11`).

For a finite coefficient ring, it is an isomorphism on every complex `K` of étale origin
(`K ≅ ν_X^* L` with `L ∈ D⁺(X_ét)`, blueprint
`proposition-proper-direct-image-constructible-complexes--5`), blueprint
`proposition-composition-base-change-rf-shriek--4`. The extension by zero
`(c.i)_! K ≅ ν^* (c.i)_!^{ét} L` is again of
étale origin (blueprint `proposition-comparison-immersions--1`), so the claim reduces to the
pro-étale proper base change for complexes of étale origin (blueprint
`proposition-proper-direct-image-constructible-complexes--5`), which is the étale proper base change
(`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring`) transported along
the site comparison (`AlgebraicGeometry.ProEtale.comparison_derivedBaseChangeMap`, blueprint
`lemma-naturality-pasting-comparison--3`).

## Main definitions

- `AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap`: the
  exchange map `Ex_!(c)`.

## Main statements

- `AlgebraicGeometry.ProEtale.isIso_derivedBaseChangeMap_app_of_isProper`: pro-étale proper base
  change for complexes of étale origin
  (`proposition-proper-direct-image-constructible-complexes--5`).
- `AlgebraicGeometry.ProEtale.isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_app`:
  pro-étale compact-support base change for complexes of étale origin
  (`proposition-composition-base-change-rf-shriek--4`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

section EtaleOrigin

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable {A} in
/-- The extension by zero along an open immersion of a complex bounded below of étale origin is
bounded below of étale origin: `j_! ν_U^* L ≅ ν_X^* j_!^{ét} L`
(`AlgebraicGeometry.ProEtale.openImmersionLowerShriekComparisonUpperStarIso`, blueprint
`proposition-comparison-immersions--1`), and `j_!^{ét}` is exact. -/
lemma plusEtaleOrigin_mapDerivedCategory_openImmersionLowerShriek {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology U) A)}
    (hK : DerivedCategory.plusEtaleOrigin A U K) :
    DerivedCategory.plusEtaleOrigin A X (D((j)_!open[A]).obj K) := by
  obtain ⟨L, ⟨n, hn⟩, ⟨e⟩⟩ := hK
  refine ⟨D(Etale.openImmersionLowerShriek A j).obj L,
    ⟨n, (Etale.openImmersionLowerShriek A j).isGE_mapDerivedCategory_obj L n⟩,
    ⟨(Functor.mapDerivedCategoryCompIso _ _ ≪≫
      Functor.mapDerivedCategoryNatIso (openImmersionLowerShriekComparisonUpperStarIso A j) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm).app L ≪≫ D((j)_!open[A]).mapIso e⟩⟩

end EtaleOrigin

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

section Proper

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `proposition-proper-direct-image-constructible-complexes--5`: Finite-level pro-etale
proper base change.

For a finite coefficient ring `Λ`, a cartesian square
```
X' --g'--> X
|f'        |f
Y' --g---> Y
```
with `f` proper and `g` arbitrary, and a complex `K` of pro-étale sheaves on `X` bounded below of
étale origin (`K ≅ ν_X^* L` with `L ∈ D⁺(X_ét, Λ)`, an étale-origin witness of blueprint
`proposition-proper-direct-image-constructible-complexes--5`), the pro-étale exchange map
`Lg^* Rf_* K ⟶ Rf'_* Lg'^* K` is an isomorphism. Being a statement about a component of a natural
transformation, it does not depend on the choice of the witness.

The proof conjugates the étale proper base change isomorphism
(`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring`) by the site
comparison (`AlgebraicGeometry.ProEtale.comparison_derivedBaseChangeMap`). -/
theorem isIso_derivedBaseChangeMap_app_of_isProper [Finite Λ] [IsProper f]
    (sq : IsPullback g' f' f g)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X K) :
    IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) := by
  obtain ⟨K', hK', ⟨eK⟩⟩ := hK
  let L : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    ⟨K', hK'⟩
  let eK' : (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj
      (_root_.DerivedCategory.Plus.ι.obj L) ≅ K := eK
  rw [← NatTrans.isIso_app_iff_of_iso _ eK']
  have : IsIso (Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq) :=
    Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring Λ isAddTorsion_of_finite sq
  have : IsProper f' := MorphismProperty.of_isPullback (P := @IsProper) sq inferInstance
  have hαβ := ProEtale.comparison_derivedBaseChangeMap Λ sq L
  have : IsIso ((comparisonUpperStar (ModuleCat.{u + 1} Λ) Y').mapDerivedCategory.map
      (_root_.DerivedCategory.Plus.ι.map
        ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app L))) :=
    inferInstance
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (Arrow.isoMk ((ProEtale.baseChangeSourceComparisonIso f g Λ).app L)
      ((ProEtale.baseChangeTargetComparisonIso g' f' Λ).app L) hαβ.symm)).1 this

end Proper

section Exchange

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The isomorphism `R(c'.g)_* Lh^* (c.i)_! ≅ R(c'.g)_* (c'.i)_! Lg'^*` closing the pro-étale
compact-support exchange map: the derived pullbacks are computed degreewise
(`AlgebraicGeometry.ProEtale.leftDerivedUpperStarIsoMapDerivedCategory`) and the extension by zero
commutes with base change
(`AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekBaseChangeIso`,
blueprint `proposition-extension-zero-restriction-closed-subscheme--11`). -/
noncomputable def rightDerivedLowerShriekOfCompactificationBaseChangeIso
    (sq : IsPullback g' f' f g) (c : Compactification f) :
    (D((c.i)_!open[A]) ⋙ L((pullback.fst c.g g)^*[A])) ⋙ R(((c.ofIsPullback sq).g)_*[A]) ≅
      L((g')^*[A]) ⋙ Rf_!(c.ofIsPullback sq)[A] :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft D((c.i)_!open[A])
          (leftDerivedUpperStarIsoMapDerivedCategory A (pullback.fst c.g g)) ≪≫
        (derivedOpenImmersionLowerShriekBaseChangeIso A
          (c.isPullback_i_ofIsPullback sq)).symm ≪≫
        Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory A g').symm
          D(((c.ofIsPullback sq).i)_!open[A]))
      R(((c.ofIsPullback sq).g)_*[A]) ≪≫
    Functor.associator _ _ _

/-- Blueprint `prose-05-31`: Compact-support exchange map, on the pro-étale site.

**The pro-étale compact-support exchange map along a compactification** `Ex_!(c)`: for a
cartesian square `g' ≫ f = f' ≫ g` and a compactification `c` of `f`, the natural
transformation `Lg^* Rf_!(c) ⟶ Rf'_!(c ×_Y Y') Lg'^*` of functors
`D(X_proét) ⥤ D(Y'_proét)`, where `c ×_Y Y' = c.ofIsPullback sq` is the base changed
compactification of `f'` (blueprint `remark-base-change-compactification--1`), with
`h : c.Z ×_Y Y' ⟶ c.Z` the projection. It is the composite
```
Lg^* R(c.g)_* (c.i)_! ⟶ R(c'.g)_* Lh^* (c.i)_! ≅ R(c'.g)_* h^* (c.i)_!
  ≅ R(c'.g)_* (c'.i)_! g'^*
  ≅ R(c'.g)_* (c'.i)_! Lg'^*
```
of the derived base change map of the proper `c.g`
(`AlgebraicGeometry.ProEtale.derivedBaseChangeMap`)
and the inverse of the base change isomorphism of the extension by zero
(`AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekBaseChangeIso`), the derived
pullbacks of the exact pullbacks being computed degreewise
(`AlgebraicGeometry.ProEtale.leftDerivedUpperStarIsoMapDerivedCategory`). -/
noncomputable def rightDerivedLowerShriekOfCompactificationBaseChangeMap
    (sq : IsPullback g' f' f g) (c : Compactification f) :
    Rf_!(c)[A] ⋙ L((g)^*[A]) ⟶ L((g')^*[A]) ⋙ Rf_!(c.ofIsPullback sq)[A] :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft D((c.i)_!open[A])
      (ProEtale.derivedBaseChangeMap A (c.isPullback_g_ofIsPullback sq).flip.toCommSq) ≫
    ((Functor.associator _ _ _).symm ≪≫
      rightDerivedLowerShriekOfCompactificationBaseChangeIso A sq c).hom

/-- **Derived base change for the extension by zero**, with derived pullbacks: the isomorphism
`Lg'^* ⋙ Dj'_! ≅ Dj_! ⋙ Lg''^*` on the unbounded derived categories of pro-étale sheaves, for a
cartesian square `g' ≫ j = j' ≫ g''` with `j`, `j'` open immersions. Its inverse is the
canonical identification `Lḡ'^* j_! ≅ j'_! Lg'^*` of blueprint `def-exchange-projection`. -/
noncomputable def leftDerivedOpenImmersionLowerShriekBaseChangeIso {U' U Z' Z : Scheme.{u}}
    {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z} [IsOpenImmersion j]
    [IsOpenImmersion j'] (hsq : IsPullback g' j' j g'') :
    L((g')^*[A]) ⋙ D((j')_!open[A]) ≅ D((j)_!open[A]) ⋙ L((g'')^*[A]) :=
  Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory A g') _ ≪≫
    derivedOpenImmersionLowerShriekBaseChangeIso A hsq ≪≫
    Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory A g'').symm

/-- `Ex_!(c)` is an isomorphism if and only if `Ex_*` for the proper part of `c`, whiskered by
`Dj_!`, is one: the other factors are isomorphisms. -/
theorem isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_iff
    (sq : IsPullback g' f' f g) (c : Compactification f) :
    IsIso (rightDerivedLowerShriekOfCompactificationBaseChangeMap A sq c) ↔
      IsIso (Functor.whiskerLeft D((c.i)_!open[A])
        (derivedBaseChangeMap A (c.isPullback_g_ofIsPullback sq).flip.toCommSq)) := by
  simp only [rightDerivedLowerShriekOfCompactificationBaseChangeMap, isIso_comp_left_iff,
    isIso_comp_right_iff]

/-- Blueprint `sk-def-sf-exchanges`: Exchange and projection transformations, typed (the
compact-support exchange `Ex_!` on the pro-étale sites, at finite coefficient stages; blueprint
`def-exchange-projection`).

The compact-support exchange `Ex_! : Lg^* Rf_! ⟶ Rf'_!(c ×_Y Y') Lg'^*` for the chosen
compactification `c` of `f`. -/
noncomputable def rightDerivedLowerShriekBaseChangeMap [HasCompactification f]
    (sq : IsPullback g' f' f g) :
    R(f)_![A] ⋙ L((g)^*[A]) ⟶
      L((g')^*[A]) ⋙ Rf_!((HasCompactification.compactification f).ofIsPullback sq)[A] :=
  rightDerivedLowerShriekOfCompactificationBaseChangeMap A sq
    (HasCompactification.compactification f)

end Exchange

section Finite

/-- A component of a composite `a ≫ F ◁ β ≫ b` of natural transformations is an isomorphism as
soon as the components of `a`, of `β` at `F.obj K` and of `b` are. Stated abstractly so that the
kernel does not have to unfold the concrete functors when checking instances. -/
lemma _root_.CategoryTheory.NatTrans.isIso_app_comp_whiskerLeft_comp {C D E : Type*}
    [Category* C] [Category* D] [Category* E] {F : C ⥤ D} {G H : D ⥤ E} {P Q : C ⥤ E}
    (a : P ⟶ F ⋙ G) (β : G ⟶ H) (b : F ⋙ H ⟶ Q) (K : C) [IsIso (a.app K)]
    [IsIso (β.app (F.obj K))] [IsIso (b.app K)] :
    IsIso ((a ≫ Functor.whiskerLeft F β ≫ b).app K) := by
  rw [NatTrans.comp_app, NatTrans.comp_app, Functor.whiskerLeft_app]
  infer_instance

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

omit [Finite Λ] in
lemma isIso_derivedBaseChangeMap_app_openImmersionLowerShriek_of_compactification [Finite Λ]
    (sq : IsPullback g' f' f g) (c : Compactification f)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X K) :
    IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
      (c.isPullback_g_ofIsPullback sq).flip.toCommSq).app
        (D((c.i)_!open[ModuleCat.{u + 1} Λ]).obj K)) :=
  isIso_derivedBaseChangeMap_app_of_isProper Λ (c.isPullback_g_ofIsPullback sq).flip _
    (plusEtaleOrigin_mapDerivedCategory_openImmersionLowerShriek c.i hK)

/-- Blueprint `proposition-composition-base-change-rf-shriek--4`: Finite-level pro-etale
compact-support base change.

For a finite coefficient ring `Λ`, a cartesian square
```
X' --g'--> X
|f'        |f
Y' --g---> Y
```
with `g` arbitrary, a compactification `c` of `f` (`f` separated of finite type) with base change
`c ×_Y Y'` (blueprint `remark-base-change-compactification--1`), and a complex `K` of pro-étale
sheaves on `X` bounded below of étale origin (`K ≅ ν_X^* L` with `L ∈ D⁺(X_ét, Λ)`, an étale-origin
witness
of blueprint `proposition-proper-direct-image-constructible-complexes--5`), the pro-étale exchange
map `Ex_!(c) : Lg^* Rf_!(c) K ⟶ Rf'_!(c ×_Y Y') Lg'^* K` of
`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap` is an
isomorphism. As the statement concerns a component of a natural transformation, it is
independent of the witness.

Its first factor is the pro-étale proper base change map of `c.g` at `(c.i)_! K`, which is again
of étale origin
(`AlgebraicGeometry.ProEtale.plusEtaleOrigin_mapDerivedCategory_openImmersionLowerShriek`),
an isomorphism by `AlgebraicGeometry.ProEtale.isIso_derivedBaseChangeMap_app_of_isProper`; the
other factors are isomorphisms. -/
theorem isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_app
    (sq : IsPullback g' f' f g) (c : Compactification f)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X K) :
    IsIso ((rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} Λ) sq
      c).app K) := by
  have := isIso_derivedBaseChangeMap_app_openImmersionLowerShriek_of_compactification Λ sq c K hK
  exact NatTrans.isIso_app_comp_whiskerLeft_comp _ _ _ K

end Finite

end AlgebraicGeometry.ProEtale
