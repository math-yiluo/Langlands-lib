/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FieldBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.TensorBaseChange
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FlatSingle.Devissage

/-!
# Base change for a pushforward tensored with a flat sheaf

Let `K` be a field, `Λ` a finite ring whose exponent is invertible in `K`, and consider a diagram

```
  X <--p-- X' <--h-- Y
  |        |         |
  a        f'        e
  v        v         v
Spec K <-b- S' <--g-- T
```

with both squares cartesian, `X` of finite type over `K` and `g` quasi-compact and
quasi-separated. For a flat sheaf `𝓔` of `Λ`-modules on `X_ét` and a sheaf `𝓕` of
`Λ`-modules on `T_ét`, both placed in degree `0`, the base change map
(`AlgebraicGeometry.Etale.tensorBaseChangeMap`)

`Lp^* 𝓔 ⊗ᴸ Lf'^* Rg_* 𝓕 ⟶ Rh_* (Lh^* Lp^* 𝓔 ⊗ᴸ Le^* 𝓕)`

is an isomorphism (`AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap_singleFunctor_of_flat`).
This is the case of single sheaves in the proof of blueprint `lemma-kunneth-field-coefficients--1`,
to which the general case is reduced in
`WeilConjectures.SixFunctors.Etale.Derived.Kunneth.SingleReduction`.

Following the blueprint, the coefficients are reduced to residue fields of `Λ`, the sheaf `𝓔`
is written as a filtered colimit of constructible sheaves, each of which embeds into a finite
sum of pushforwards of constant sheaves along finite morphisms, and for those the statement is
the base change theorem towards spectra of fields (blueprint `lemma-kunneth-field-coefficients--1`,
`AlgebraicGeometry.Etale.universalBaseChangeProperty_of_field`) for a scheme finite over `X`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `lemma-kunneth-field-coefficients--1`, for single sheaves: base change for a
pushforward tensored with a flat sheaf.

Let `K` be a field and `Λ` a finite ring whose exponent is invertible in `K`. For a diagram

```
  X <--p-- X' <--h-- Y
  |        |         |
  a        f'        e
  v        v         v
Spec K <-b- S' <--g-- T
```

with both squares cartesian, `X` of finite type over `K` and `g` quasi-compact and
quasi-separated, the base change map

`Lp^* 𝓔 ⊗ᴸ Lf'^* Rg_* 𝓕 ⟶ Rh_* (Lh^* Lp^* 𝓔 ⊗ᴸ Le^* 𝓕)`

is an isomorphism for every flat sheaf `𝓔` of `Λ`-modules on `X_ét` and every sheaf `𝓕` of
`Λ`-modules on `T_ét`, both placed in degree `0`. -/
theorem isIso_tensorBaseChangeMap_singleFunctor_of_flat [Finite Λ] {K : Type u} [Field K]
    [HasInvertibleExponent Λ (Spec (.of K))] {X X' S' T Y : Scheme.{u}}
    (a : X ⟶ Spec (.of K)) (b : S' ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a]
    (p : X' ⟶ X) (f' : X' ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T) (g : T ⟶ S') [QuasiCompact g]
    [QuasiSeparated g] (sq₁ : IsPullback p f' a b) (sq₂ : IsPullback h e f' g)
    (𝓔 : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (h𝓔 : ObjectProperty.flat 𝓔)
    (𝓕 : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (tensorBaseChangeMap (ModuleCat.{u + 1} Λ) h e f' g sq₂.w
      ((L((p)^*[ModuleCat.{u + 1} Λ])).obj ((DerivedCategory.singleFunctor _ 0).obj 𝓔))
      ((DerivedCategory.singleFunctor _ 0).obj 𝓕)) := by
  have : QuasiCompact h := MorphismProperty.of_isPullback sq₂.flip inferInstance
  have : QuasiSeparated h := MorphismProperty.of_isPullback sq₂.flip inferInstance
  exact isIso_tensorBaseChangeMap_singleFunctor_of_flat_of_lowerStar Λ a p f' h e g sq₂.w
    (fun π _ 𝓕 ↦ isIso_tensorBaseChangeMap_lowerStar_unit Λ a b p f' h e g sq₁ sq₂ π 𝓕) 𝓔 h𝓔 𝓕

end Etale

end AlgebraicGeometry
