/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne.ChangeOfBase
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne.ClosedImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne.OpenCover

/-!
# Transport of the generic constructibility property

The conclusion of `AlgebraicGeometry.Etale.HasDirectImageBaseChangeOnPlus` for a given base change
`T ⟶ S` does not depend on the chosen cartesian squares
(`AlgebraicGeometry.Etale.HasDirectImageBaseChangeOnPlus.conclusion_congr`). Consequently the
property is invariant under isomorphisms of the data
(`AlgebraicGeometry.Etale.HasDirectImageBaseChangeOnPlus.of_iso_data`), and it passes to the
restriction of `j : X ⟶ Y` over an open of `Y`
(`AlgebraicGeometry.Etale.HasDirectImageBaseChangeOnPlus.restrict`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The conclusion of the generic constructibility property for a base change `T ⟶ S`: the
direct image after base change is bounded constructible and the derived base change map is an
isomorphism. -/
def HasDirectImageBaseChangeOnPlus.Conclusion {S X Y : Scheme.{u}} {fY : Y ⟶ S} {j : X ⟶ Y}
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    {T YT XT : Scheme.{u}} {t : T ⟶ S} {gT : YT ⟶ Y} {fT : YT ⟶ T} {gXT : XT ⟶ X}
    {jT : XT ⟶ YT} (_hYT : IsPullback gT fT fY t) (sqT : IsPullback gXT jT j gT) : Prop :=
  DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) YT
      (_root_.DerivedCategory.Plus.ι.obj ((jT)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.obj
        (((gXT)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K))) ∧
    IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sqT.toCommSq).app K)

/-- **The conclusion does not depend on the choice of the cartesian squares.** -/
lemma HasDirectImageBaseChangeOnPlus.conclusion_congr {S X Y : Scheme.{u}} {fY : Y ⟶ S}
    {j : X ⟶ Y}
    {K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {T : Scheme.{u}} {t : T ⟶ S}
    {YT₁ XT₁ : Scheme.{u}} {gT₁ : YT₁ ⟶ Y} {fT₁ : YT₁ ⟶ T} {gXT₁ : XT₁ ⟶ X} {jT₁ : XT₁ ⟶ YT₁}
    (hY₁ : IsPullback gT₁ fT₁ fY t) (sq₁ : IsPullback gXT₁ jT₁ j gT₁)
    {YT₂ XT₂ : Scheme.{u}} {gT₂ : YT₂ ⟶ Y} {fT₂ : YT₂ ⟶ T} {gXT₂ : XT₂ ⟶ X} {jT₂ : XT₂ ⟶ YT₂}
    (hY₂ : IsPullback gT₂ fT₂ fY t) (sq₂ : IsPullback gXT₂ jT₂ j gT₂)
    (h : Conclusion (Λ := Λ) K hY₁ sq₁) : Conclusion (Λ := Λ) K hY₂ sq₂ := by
  obtain ⟨c, i⟩ := h
  -- the comparison isomorphisms of the two base changes
  let e : YT₂ ≅ YT₁ := hY₂.isoIsPullback _ _ hY₁
  have he₁ : e.hom ≫ gT₁ = gT₂ := IsPullback.isoIsPullback_hom_fst _ _ _ _
  have hsq₂' : IsPullback gXT₂ (jT₂ ≫ e.hom) j gT₁ := by
    refine IsPullback.of_iso sq₂ (Iso.refl _) (Iso.refl _) e (Iso.refl _) ?_ ?_ ?_ ?_ <;>
      simp [he₁]
  let eX : XT₂ ≅ XT₁ := hsq₂'.isoIsPullback _ _ sq₁
  have heX₁ : eX.hom ≫ gXT₁ = gXT₂ := IsPullback.isoIsPullback_hom_fst _ _ _ _
  have heX₂ : eX.hom ≫ jT₁ = jT₂ ≫ e.hom := IsPullback.isoIsPullback_hom_snd _ _ _ _
  have hiso : IsPullback eX.hom jT₂ jT₁ e.hom :=
    IsPullback.of_horiz_isIso ⟨heX₂⟩
  have iiso := isIso_derivedBaseChangeMapPlus_of_etale (Λ := Λ) hiso
  refine ⟨ObjectProperty.prop_of_iso _ ?_ (c.mapDerivedCategory_upperStar e.hom), ?_⟩
  · exact _root_.DerivedCategory.Plus.ι.mapIso
      (asIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) hiso.toCommSq).app
          (((gXT₁)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K)) ≪≫
        (jT₂)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.mapIso
          ((upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) eX.hom gXT₁ gXT₂ heX₁.symm).app
            K).symm)
  · have hpaste := (isIso_derivedBaseChangeMapPlus_app_paste_horiz_iff sq₁.toCommSq
      hiso.toCommSq (⟨by rw [Category.assoc, sq₁.w, ← Category.assoc, hiso.w,
        Category.assoc]⟩ : CommSq (eX.hom ≫ gXT₁) jT₂ j (e.hom ≫ gT₁)) K inferInstance).2
      inferInstance
    exact (isIso_derivedBaseChangeMapPlus_app_congr' heX₁ rfl rfl he₁ _ _ K).1 hpaste

/-- **Invariance under isomorphisms of the data**: if `Y₁ ≅ Y₂` over `S` and `X₁ ≅ X₂`
compatibly with `j₁` and `j₂`, and `K₁ ≅ eX^* K₂`, then the generic constructibility property for
`(j₂, K₂)` implies that for `(j₁, K₁)`. -/
theorem HasDirectImageBaseChangeOnPlus.of_iso_data {S X₁ X₂ Y₁ Y₂ : Scheme.{u}} {fY₁ : Y₁ ⟶ S}
    {fY₂ : Y₂ ⟶ S} {j₁ : X₁ ⟶ Y₁} {j₂ : X₂ ⟶ Y₂} (e : Y₁ ⟶ Y₂) [IsIso e] (eX : X₁ ⟶ X₂)
    [IsIso eX] (hfY : e ≫ fY₂ = fY₁) (hj : j₁ ≫ e = eX ≫ j₂)
    {K₁ : _root_.DerivedCategory.Plus (Sheaf X₁.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {K₂ : _root_.DerivedCategory.Plus (Sheaf X₂.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (eK : K₁ ≅ ((eX)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K₂) {U : Set S}
    (h : HasDirectImageBaseChangeOnPlus Λ fY₂ j₂ K₂ U) :
    HasDirectImageBaseChangeOnPlus Λ fY₁ j₁ K₁ U := by
  intro T _ t ht YT XT gT fT gXT jT hYT sqT
  have hY₂ : IsPullback (gT ≫ e) fT fY₂ t := by
    have := hYT.paste_horiz (IsPullback.of_horiz_isIso ⟨by simp [hfY]⟩ :
      IsPullback e fY₁ fY₂ (𝟙 S))
    simpa using this
  have he : IsPullback eX j₁ j₂ e := IsPullback.of_horiz_isIso ⟨hj.symm⟩
  have hX₂ : IsPullback (gXT ≫ eX) jT j₂ (gT ≫ e) := sqT.paste_horiz he
  obtain ⟨c, i⟩ := h T t ht YT XT (gT ≫ e) fT (gXT ≫ eX) jT hY₂ hX₂
  have ie := isIso_derivedBaseChangeMapPlus_of_etale (Λ := Λ) he
  refine ⟨ObjectProperty.prop_of_iso _ (_root_.DerivedCategory.Plus.ι.mapIso
    ((jT)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.mapIso
      ((upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) gXT eX).app K₂ ≪≫
        (((gXT)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.mapIso eK).symm))) c, ?_⟩
  refine (NatTrans.isIso_app_iff_of_iso _ eK).2 ?_
  exact isIso_derivedBaseChangeMapPlus_app_of_paste_horiz he.toCommSq sqT.toCommSq _ K₂
    inferInstance i

/-- **Restriction to an open of the target**: if the direct image along `j : X ⟶ Y` has the
generic constructibility property over `U`, so has the direct image along its restriction
`j⁻¹(V) ⟶ V` over an open `V ⊆ Y`. -/
theorem HasDirectImageBaseChangeOnPlus.restrict {S X Y : Scheme.{u}} {fY : Y ⟶ S} (j : X ⟶ Y)
    (V : Y.Opens)
    {K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {U : Set S} (h : HasDirectImageBaseChangeOnPlus Λ fY j K U) :
    HasDirectImageBaseChangeOnPlus Λ (V.ι ≫ fY) (j ∣_ V)
      ((((j ⁻¹ᵁ V).ι)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K) U := by
  intro T _ t ht VT XVT gV fVT gXV jVT hVT sqV
  -- the canonical base change of `Y` and its open `W = V_T`
  let YT := pullback fY t
  let gT : YT ⟶ Y := pullback.fst fY t
  let fT : YT ⟶ T := pullback.snd fY t
  have hYT : IsPullback gT fT fY t := IsPullback.of_hasPullback fY t
  let XT := pullback j gT
  let gXT : XT ⟶ X := pullback.fst j gT
  let jT : XT ⟶ YT := pullback.snd j gT
  have sqT : IsPullback gXT jT j gT := IsPullback.of_hasPullback j gT
  obtain ⟨c, i⟩ := h T t ht YT XT gT fT gXT jT hYT sqT
  let W : YT.Opens := gT ⁻¹ᵁ V
  have hle : jT ⁻¹ᵁ W ≤ gXT ⁻¹ᵁ (j ⁻¹ᵁ V) := by
    intro x hx
    change j (gXT x) ∈ V
    rw [← Scheme.Hom.comp_apply, sqT.w, Scheme.Hom.comp_apply]
    exact hx
  let gX' : (jT ⁻¹ᵁ W).toScheme ⟶ (j ⁻¹ᵁ V).toScheme := gXT.resLE (j ⁻¹ᵁ V) (jT ⁻¹ᵁ W) hle
  have hgX' : gX' ≫ (j ⁻¹ᵁ V).ι = (jT ⁻¹ᵁ W).ι ≫ gXT := Scheme.Hom.resLE_comp_ι _ _
  have hA : IsPullback (gT ∣_ V) (W.ι ≫ fT) (V.ι ≫ fY) t :=
    (isPullback_morphismRestrict gT V).paste_vert hYT
  have hR : IsPullback (jT ⁻¹ᵁ W).ι (jT ∣_ W) jT W.ι := (isPullback_morphismRestrict jT W).flip
  have hRj : IsPullback (j ⁻¹ᵁ V).ι (j ∣_ V) j V.ι := (isPullback_morphismRestrict j V).flip
  have hB : IsPullback gX' (jT ∣_ W) (j ∣_ V) (gT ∣_ V) := by
    refine IsPullback.of_right ?_ ?_ hRj
    · rw [hgX', morphismRestrict_ι]
      exact hR.paste_horiz sqT
    · rw [← cancel_mono V.ι]
      simp only [Category.assoc, morphismRestrict_ι]
      rw [← Category.assoc, hgX', Category.assoc, sqT.w, ← Category.assoc (jT ∣_ W),
        morphismRestrict_ι, Category.assoc]
  refine conclusion_congr (Λ := Λ) hA hB hVT sqV ⟨?_, ?_⟩
  · have iR := isIso_derivedBaseChangeMapPlus_of_etale (Λ := Λ) hR
    let eK := ((upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (jT ⁻¹ᵁ W).ι gXT).app K).symm ≪≫
      (upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) gX' (j ⁻¹ᵁ V).ι
        ((jT ⁻¹ᵁ W).ι ≫ gXT) hgX'.symm).app K
    refine ObjectProperty.prop_of_iso _ ?_ (c.mapDerivedCategory_upperStar W.ι)
    exact _root_.DerivedCategory.Plus.ι.mapIso
      (asIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) hR.toCommSq).app
        (((gXT)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K)) ≪≫
        (jT ∣_ W)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.mapIso eK)
  · have iR := isIso_derivedBaseChangeMapPlus_of_etale (Λ := Λ) hR
    have iRj := isIso_derivedBaseChangeMapPlus_of_etale (Λ := Λ) hRj
    have h₁ := (isIso_derivedBaseChangeMapPlus_app_paste_horiz_iff sqT.toCommSq hR.toCommSq
      (⟨by rw [Category.assoc, sqT.w, ← Category.assoc, hR.w, Category.assoc]⟩ :
        CommSq ((jT ⁻¹ᵁ W).ι ≫ gXT) (jT ∣_ W) j (W.ι ≫ gT)) K inferInstance).2 inferInstance
    have h₂ := (isIso_derivedBaseChangeMapPlus_app_congr hgX' (morphismRestrict_ι gT V)
      (⟨by rw [Category.assoc, hRj.w, ← Category.assoc, hB.w, Category.assoc]⟩ :
        CommSq (gX' ≫ (j ⁻¹ᵁ V).ι) (jT ∣_ W) j ((gT ∣_ V) ≫ V.ι)) _ K).2 h₁
    exact isIso_derivedBaseChangeMapPlus_app_of_paste_horiz hRj.toCommSq hB.toCommSq _ K
      inferInstance h₂

end Etale

end AlgebraicGeometry
