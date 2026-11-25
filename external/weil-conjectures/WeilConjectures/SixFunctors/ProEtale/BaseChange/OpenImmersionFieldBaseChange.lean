/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OpenImmersionBaseChange

/-!
# Base change for open direct images over a field, finite coefficients

Let `K` be a field, `j : U ⟶ X` an open immersion of schemes of finite type over `K`, `Y` a
scheme of finite type over `K`, `W = X ×_K Y` and `V = U ×_X W`, with the cartesian square

```
  V --h--> W
  |        |
  e        q₁
  v        v
  U --j--> X
```

and let `Λ` be a coefficient ring killed by an integer `n` invertible in `K`. This file proves
blueprint `corollary-open-direct-image-over-field--2` (section `chap-Construction-of-f`): the
derived base-change map `q₁^* Rj_* L ⟶ Rh_* e^* L` is an isomorphism for every bounded constructible
complex `L`,

* on the small étale sites
  (`AlgebraicGeometry.Etale.isIso_baseChange_app_of_isOpenImmersion_of_field`),
  from the case of sheaves, blueprint `corollary-open-direct-image-over-field--2`
  (`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isOpenImmersion_of_field`), by the
  hypercohomology spectral sequence comparison
  (`AlgebraicGeometry.Etale.isIso_baseChange_app_of_isGE_of_isLE`);
* on the pro-étale sites, for complexes of étale origin
  (`AlgebraicGeometry.ProEtale.isIso_derivedBaseChangeMap_app_of_isOpenImmersion_of_field`), by
  conjugating the étale statement by the site comparison
  (`AlgebraicGeometry.ProEtale.comparison_derivedBaseChangeMap`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

variable {K : Type u} [Field K] {X U Y W V : Scheme.{u}} (aX : X ⟶ Spec (.of K))
  (aY : Y ⟶ Spec (.of K)) [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY]
  [QuasiCompact aY] (j : U ⟶ X) [IsOpenImmersion j] {q₁ : W ⟶ X} {q₂ : W ⟶ Y}
  (hW : IsPullback q₁ q₂ aX aY) {e : V ⟶ U} {h : V ⟶ W} (sq : IsPullback e h j q₁)

include hW in
/-- Blueprint `corollary-open-direct-image-over-field--2` on the small étale sites: for an open
immersion `j : U ⟶ X` of schemes of finite type over a field `K`, its base change `h` along the
projection `q₁ : X ×_K Y ⟶ X` and a coefficient ring `Λ` killed by an integer `n` invertible in
`K`, the derived base-change map `q₁^* Rj_* L ⟶ Rh_* e^* L` is an isomorphism for every bounded
constructible complex `L` of étale sheaves of `Λ`-modules on `U`. -/
theorem Etale.isIso_baseChange_app_of_isOpenImmersion_of_field (n : ℕ) (hn : IsUnit (n : K))
    (hΛ : (n : Λ) = 0) (L : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hL : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) U L) :
    IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app ⟨L, hL.1.1⟩) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hL.1
  have : DerivedCategory.Plus.IsGE (⟨L, hL.1.1⟩ : DerivedCategory.Plus _) a := ⟨ha.1⟩
  have : DerivedCategory.Plus.IsLE (⟨L, hL.1.1⟩ : DerivedCategory.Plus _) b := ⟨hb.1⟩
  exact Etale.isIso_baseChange_app_of_isGE_of_isLE Λ sq _ a b fun i _ ↦
    Etale.isIso_baseChangeHomologyMap_of_isOpenImmersion_of_field Λ aX aY j q₁ q₂ hW e h sq n hn
      hΛ i _

include hW in
/-- Blueprint `corollary-open-direct-image-over-field--2` on the pro-étale sites, finite
coefficients: for an open immersion `j : U ⟶ X` of schemes of finite type over a field `K`, its base
change `h` along the projection `q₁ : X ×_K Y ⟶ X` and a coefficient ring `Λ` killed by an integer
`n` invertible in `K`, the pro-étale derived base-change map `q₁^* Rj_* L ⟶ Rh_* e^* L` is an
isomorphism for every bounded constructible pro-étale complex `L`, that is, one of étale origin.
It is the étale statement `Etale.isIso_baseChange_app_of_isOpenImmersion_of_field` conjugated by
the site comparison (`ProEtale.comparison_derivedBaseChangeMap`). -/
theorem ProEtale.isIso_derivedBaseChangeMap_app_of_isOpenImmersion_of_field (n : ℕ)
    (hn : IsUnit (n : K)) (hΛ : (n : Λ) = 0)
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} Λ)))
    (hL : ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) U L) :
    IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app L) := by
  obtain ⟨L', hL', ⟨eL⟩⟩ := hL
  let M : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) := ⟨L', hL'.1.1⟩
  let eL' : (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategory.obj
      (DerivedCategory.Plus.ι.obj M) ≅ L := eL
  rw [← NatTrans.isIso_app_iff_of_iso _ eL']
  have hBC : IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app M) :=
    Etale.isIso_baseChange_app_of_isOpenImmersion_of_field Λ aX aY j hW sq n hn hΛ L' hL'
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  have : QuasiCompact j := inferInstance
  have : QuasiCompact h := MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
  have : QuasiSeparated h :=
    MorphismProperty.of_isPullback (P := @QuasiSeparated) sq inferInstance
  have hαβ := ProEtale.comparison_derivedBaseChangeMap Λ sq M
  have : IsIso ((comparisonUpperStar (ModuleCat.{u + 1} Λ) W).mapDerivedCategory.map
      (DerivedCategory.Plus.ι.map ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app M))) :=
    inferInstance
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (Arrow.isoMk ((ProEtale.baseChangeSourceComparisonIso j q₁ Λ).app M)
      ((ProEtale.baseChangeTargetComparisonIso e h Λ).app M) hαβ.symm)).1 this

end AlgebraicGeometry
