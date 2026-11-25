/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne.ChangeOfBase

/-!
# Restricting the base of the generic constructibility property to an open

For an open `U₀ ⊆ S` and `S`-schemes `X ⟶ Y`, the generic constructibility and base change
property over a subset of `U₀` is the same whether `X ⟶ Y` is viewed over `S` or restricted to a
morphism of `U₀`-schemes `X_{U₀} ⟶ Y_{U₀}`
(`AlgebraicGeometry.Etale.HasDirectImageBaseChangeOnPlus.of_restrict_base`,
`AlgebraicGeometry.Etale.HasDirectImageBaseChangeOnPlus.restrict_base`): a morphism `T ⟶ S` with
image in `U₀` factors through `U₀`, and the base changes agree.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- **From an open of the base to the base**: if over `V ⊆ U₀` the direct image along the
restriction `X_{U₀} ⟶ Y_{U₀}` of `j` over `U₀` has the generic constructibility property, then
so has the direct image along `j` over `V`, as a subset of `S`. -/
theorem HasDirectImageBaseChangeOnPlus.of_restrict_base {S X Y : Scheme.{u}} {fY : Y ⟶ S}
    (j : X ⟶ Y) (U₀ : S.Opens)
    {K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {V : Set U₀}
    (h : HasDirectImageBaseChangeOnPlus Λ (fY ∣_ U₀) (j ∣_ (fY ⁻¹ᵁ U₀))
      ((((j ⁻¹ᵁ (fY ⁻¹ᵁ U₀)).ι)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K) V) :
    HasDirectImageBaseChangeOnPlus Λ fY j K (U₀.ι '' V) := by
  intro T _ t ht YT XT gT fT gXT jT hYT sqT
  have htU : Set.range t ⊆ Set.range U₀.ι := ht.trans (Set.image_subset_range _ _)
  let t' : T ⟶ U₀ := IsOpenImmersion.lift U₀.ι t htU
  have ht' : t' ≫ U₀.ι = t := IsOpenImmersion.lift_fac _ _ _
  have ht'V : Set.range t' ⊆ V := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy, hyx⟩ := ht ⟨x, rfl⟩
    rw [← ht', Scheme.Hom.comp_apply] at hyx
    rwa [← U₀.ι.isOpenEmbedding.injective hyx]
  -- the restriction squares
  have hRY : IsPullback (fY ⁻¹ᵁ U₀).ι (fY ∣_ U₀) fY U₀.ι :=
    (isPullback_morphismRestrict fY U₀).flip
  obtain ⟨gT', hgT', hgT'eq⟩ : ∃ gT' : YT ⟶ fY ⁻¹ᵁ U₀, IsPullback gT' fT (fY ∣_ U₀) t' ∧
      gT' ≫ (fY ⁻¹ᵁ U₀).ι = gT :=
    ⟨_, IsPullback.of_right' (ht' ▸ hYT) hRY, hRY.lift_fst _ _ _⟩
  have hRX : IsPullback (j ⁻¹ᵁ (fY ⁻¹ᵁ U₀)).ι (j ∣_ (fY ⁻¹ᵁ U₀)) j (fY ⁻¹ᵁ U₀).ι :=
    (isPullback_morphismRestrict j (fY ⁻¹ᵁ U₀)).flip
  obtain ⟨gXT', hgXT', hgXT'eq⟩ : ∃ gXT' : XT ⟶ j ⁻¹ᵁ (fY ⁻¹ᵁ U₀),
      IsPullback gXT' jT (j ∣_ (fY ⁻¹ᵁ U₀)) gT' ∧ gXT' ≫ (j ⁻¹ᵁ (fY ⁻¹ᵁ U₀)).ι = gXT :=
    ⟨_, IsPullback.of_right' (hgT'eq ▸ sqT) hRX, hRX.lift_fst _ _ _⟩
  obtain ⟨c, i⟩ := h T t' ht'V YT XT gT' fT gXT' jT hgT' hgXT'
  refine ⟨ObjectProperty.prop_of_iso _ (_root_.DerivedCategory.Plus.ι.mapIso
    ((jT)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.mapIso
      ((upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) gXT' (j ⁻¹ᵁ (fY ⁻¹ᵁ U₀)).ι gXT
        hgXT'eq.symm).app K).symm)) c, ?_⟩
  have := isIso_derivedBaseChangeMapPlus_of_etale (Λ := Λ) hRX
  have hsq := (isIso_derivedBaseChangeMapPlus_app_paste_horiz_iff hRX.toCommSq hgXT'.toCommSq
    (⟨by rw [Category.assoc, hRX.w, ← Category.assoc, hgXT'.w, Category.assoc]⟩ :
      CommSq (gXT' ≫ (j ⁻¹ᵁ (fY ⁻¹ᵁ U₀)).ι) jT j (gT' ≫ (fY ⁻¹ᵁ U₀).ι)) K i).2 inferInstance
  exact (isIso_derivedBaseChangeMapPlus_app_congr hgXT'eq hgT'eq _ _ K).1 hsq

/-- **From the base to an open of the base**: if over `U₀.ι '' V` the direct image along `j` has
the generic constructibility property, then so has the direct image along the restriction
`X_{U₀} ⟶ Y_{U₀}` of `j` over `U₀`, over `V`. -/
theorem HasDirectImageBaseChangeOnPlus.restrict_base {S X Y : Scheme.{u}} {fY : Y ⟶ S}
    (j : X ⟶ Y) (U₀ : S.Opens)
    {K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {V : Set U₀} (h : HasDirectImageBaseChangeOnPlus Λ fY j K (U₀.ι '' V)) :
    HasDirectImageBaseChangeOnPlus Λ (fY ∣_ U₀) (j ∣_ (fY ⁻¹ᵁ U₀))
      ((((j ⁻¹ᵁ (fY ⁻¹ᵁ U₀)).ι)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K) V := by
  intro T _ t ht YT XT gT fT gXT jT hYT sqT
  have hRY : IsPullback (fY ⁻¹ᵁ U₀).ι (fY ∣_ U₀) fY U₀.ι :=
    (isPullback_morphismRestrict fY U₀).flip
  have hRX : IsPullback (j ⁻¹ᵁ (fY ⁻¹ᵁ U₀)).ι (j ∣_ (fY ⁻¹ᵁ U₀)) j (fY ⁻¹ᵁ U₀).ι :=
    (isPullback_morphismRestrict j (fY ⁻¹ᵁ U₀)).flip
  have ht' : Set.range (t ≫ U₀.ι) ⊆ U₀.ι '' V := by
    rintro _ ⟨x, rfl⟩
    exact ⟨t x, ht ⟨x, rfl⟩, rfl⟩
  obtain ⟨c, i⟩ := h T (t ≫ U₀.ι) ht' YT XT (gT ≫ (fY ⁻¹ᵁ U₀).ι) fT
    (gXT ≫ (j ⁻¹ᵁ (fY ⁻¹ᵁ U₀)).ι) jT (hYT.paste_horiz hRY) (sqT.paste_horiz hRX)
  refine ⟨ObjectProperty.prop_of_iso _ (_root_.DerivedCategory.Plus.ι.mapIso
    ((jT)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.mapIso
      ((upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) gXT (j ⁻¹ᵁ (fY ⁻¹ᵁ U₀)).ι).app K))) c,
    ?_⟩
  have := isIso_derivedBaseChangeMapPlus_of_etale (Λ := Λ) hRX
  exact isIso_derivedBaseChangeMapPlus_app_of_paste_horiz hRX.toCommSq sqT.toCommSq _ K
    inferInstance i

end Etale

end AlgebraicGeometry
