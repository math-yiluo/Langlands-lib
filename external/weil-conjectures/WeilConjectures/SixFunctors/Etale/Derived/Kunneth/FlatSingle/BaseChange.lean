/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FieldBaseChange
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived
public import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnboundedPlus
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne.ChangeOfBase

/-!
# Base change towards spectra of fields on the unbounded derived category

Let `K` be a field, `Λ` a finite ring whose exponent is invertible in `K`, `X` of finite type over
`K`, `X' = X ×_K S'` and `Y = X' ×_{S'} T` for a quasi-compact quasi-separated `g : T ⟶ S'`. The
unbounded derived base change map `Lf'^* Rg_* F ⟶ Rh_* Le^* F` is an isomorphism at every sheaf
`F` placed in degree `0` (`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_app_singleFunctor`):
this is blueprint `lemma-kunneth-field-coefficients--1`
(`AlgebraicGeometry.Etale.universalBaseChangeProperty_of_field`), transported from the bounded below
derived categories.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The exponent of `Λ` is a natural number invertible in `K` and killing `Λ`. -/
lemma exists_isUnit_natCast_of_hasInvertibleExponent {K : Type u} [Field K]
    [HasInvertibleExponent Λ (Spec (.of K))] :
    ∃ n : ℕ, IsUnit (n : K) ∧ (n : Λ) = 0 := by
  obtain ⟨n, -, hΛ, hu⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ)
    (X := Spec (.of K))
  exact ⟨n, by simpa using hu.map (Scheme.ΓSpecIso (.of K)).hom.hom, hΛ⟩

/-- Blueprint `lemma-kunneth-field-coefficients--1` on the bounded below derived categories: the
derived base change map of `Y = X' ×_{S'} T` over `X' = X ×_K S'` is an isomorphism at every sheaf
placed in degree `0`. -/
lemma isIso_derivedBaseChangeMapPlus_app_singleFunctor {K : Type u} [Field K]
    [HasInvertibleExponent Λ (Spec (.of K))] {X X' S' T Y : Scheme.{u}}
    (a : X ⟶ Spec (.of K)) (b : S' ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a]
    (p : X' ⟶ X) (f' : X' ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T) (g : T ⟶ S') [QuasiCompact g]
    [QuasiSeparated g] (sq₁ : IsPullback p f' a b) (sq₂ : IsPullback h e f' g)
    (𝓕 : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq₂.flip.toCommSq).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj 𝓕)) := by
  obtain ⟨n, hn, hΛ⟩ := exists_isUnit_natCast_of_hasInvertibleExponent Λ (K := K)
  have hBC (q : ℤ) := universalBaseChangeProperty_of_field Λ a n hn hΛ q b p f' sq₁ g e h
    sq₂.flip 𝓕
  have h1 := (Etale.isIso_baseChange_app_singleFunctor_obj_iff Λ sq₂.flip 𝓕).2 hBC
  rwa [Etale.baseChange_eq_derivedBaseChangeMapPlus] at h1

/-- Blueprint `lemma-kunneth-field-coefficients--1` on the unbounded derived categories: the derived
base change map `Lf'^* Rg_* F ⟶ Rh_* Le^* F` of `Y = X' ×_{S'} T` over `X' = X ×_K S'` is an
isomorphism at every sheaf `F` placed in degree `0`. -/
lemma isIso_derivedBaseChangeMap_app_singleFunctor {K : Type u} [Field K]
    [HasInvertibleExponent Λ (Spec (.of K))] {X X' S' T Y : Scheme.{u}}
    (a : X ⟶ Spec (.of K)) (b : S' ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a]
    (p : X' ⟶ X) (f' : X' ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T) (g : T ⟶ S') [QuasiCompact g]
    [QuasiSeparated g] (sq₁ : IsPullback p f' a b) (sq₂ : IsPullback h e f' g)
    (𝓕 : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) (CommSq.mk sq₂.w.symm)).app
      ((DerivedCategory.singleFunctor _ 0).obj 𝓕)) :=
  (isIso_derivedBaseChangeMap_app_ι_obj_iff (ModuleCat.{u + 1} Λ) sq₂.flip.toCommSq _).2
    (isIso_derivedBaseChangeMapPlus_app_singleFunctor Λ a b p f' h e g sq₁ sq₂ 𝓕)

/-- Blueprint `lemma-kunneth-field-coefficients--1` for a scheme finite over `X`: for a finite
`π : Xᵢ ⟶ X` with base changes `π' : X'ᵢ ⟶ X'` and `ρ : Yᵢ ⟶ Y`, the derived base change map
`Lπ'^* Rh_* Le^* F ⟶ Rhᵢ_* Lρ^* Le^* F` is an isomorphism at every sheaf `F` placed in degree `0`:
the base change maps along `X'ᵢ ⟶ S'` and `X' ⟶ S'` are isomorphisms, and the derived base change
maps compose. -/
lemma isIso_derivedBaseChangeMap_app_upperStar_singleFunctor {K : Type u} [Field K]
    [HasInvertibleExponent Λ (Spec (.of K))] {X X' S' T Y Xᵢ X'ᵢ Yᵢ : Scheme.{u}}
    (a : X ⟶ Spec (.of K)) (b : S' ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a]
    (p : X' ⟶ X) (f' : X' ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T) (g : T ⟶ S') [QuasiCompact g]
    [QuasiSeparated g] (sq₁ : IsPullback p f' a b) (sq₂ : IsPullback h e f' g)
    (π : Xᵢ ⟶ X) [IsFinite π] (pᵢ : X'ᵢ ⟶ Xᵢ) (π' : X'ᵢ ⟶ X') (sqπ : IsPullback pᵢ π' π p)
    (hᵢ : Yᵢ ⟶ X'ᵢ) (ρ : Yᵢ ⟶ Y) (sq : IsPullback hᵢ ρ π' h)
    (𝓕 : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) (CommSq.mk sq.w.symm)).app
      (L((e)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.singleFunctor _ 0).obj 𝓕))) := by
  have hBC₁ := isIso_derivedBaseChangeMapPlus_app_singleFunctor Λ a b p f' h e g sq₁ sq₂ 𝓕
  have hBC := isIso_derivedBaseChangeMapPlus_app_singleFunctor Λ (π ≫ a) b pᵢ (π' ≫ f') hᵢ
    (ρ ≫ e) g (sqπ.paste_vert sq₁) (sq.paste_vert sq₂) 𝓕
  have hsq := isIso_derivedBaseChangeMapPlus_app_of_paste_horiz sq₂.flip.toCommSq
    sq.flip.toCommSq (sq.paste_vert sq₂).flip.toCommSq _ inferInstance hBC
  have hu := (isIso_derivedBaseChangeMap_app_ι_obj_iff (ModuleCat.{u + 1} Λ)
    sq.flip.toCommSq _).2 hsq
  refine (NatTrans.isIso_app_iff_of_iso (derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
    (CommSq.mk sq.w.symm)) ?_).1 hu
  exact ((e)^*[ModuleCat.{u + 1} Λ].mapDerivedCategoryPlusCompatibility.app _) ≪≫
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) e).symm.app _

end Etale

end AlgebraicGeometry
