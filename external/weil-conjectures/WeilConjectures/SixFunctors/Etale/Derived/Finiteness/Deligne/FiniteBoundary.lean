/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteBoundary
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne.ChangeOfBase
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne.OpenCover
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne.ClosedImmersion

/-!
# Generic constructibility across a finite boundary

Let `b : Y ⟶ S` be proper over a scheme `S` of finite type over a field, `j : X ⟶ Y` a morphism,
`G ⊆ Y` open with closed complement `i : Z ⟶ Y` finite over `S`, and `K` a bounded below complex
on `X`. If the direct image of `K` along the restriction `j⁻¹(G) ⟶ G` and the direct image along
`a = j ≫ b` are bounded constructible and commute with base change, then so is the direct image
along `j` (`AlgebraicGeometry.Etale.HasDirectImageBaseChangeOnPlus.of_finite_boundary`).

This is the core of the second step of the proof of
`theorem-generic-constructibility-base-change-rj`. Over `S`, `Rj_* K` is bounded constructible by
`lemma-detection-proper-direct-image--1`, its restriction to `G` and its direct image
`Rb_* Rj_* K = Ra_* K` being so. After a base change `T ⟶ S`, the derived base change map `c` for
`j` is an isomorphism over `G_T`, and so is `Rb_{T,*} c`, which proper base change for `b` and the
composition law identify with the derived base change map for `a`; hence `c` is an isomorphism by
`lemma-detection-proper-direct-image--2`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- **Vertical pasting, at an object, the third way**: for two squares pasted vertically, if the
derived base change map of the pasted square is an isomorphism at `K` and that of the lower square
is an isomorphism at `Rf_* K`, then `Re'_*` of that of the upper square is an isomorphism at
`K`. -/
lemma isIso_rightDerivedFunctorPlus_map_derivedBaseChangeMapPlus_app_of_paste_vert
    {X' X Y' Y Z' Z : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} {e' : Y' ⟶ Z'} {e : Y ⟶ Z}
    {k : Z' ⟶ Z} (sq₁ : CommSq g' f' f g) (sq₂ : CommSq g e' e k)
    (sq : CommSq g' (f' ≫ e') (f ≫ e) k)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (h₂ : IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq₂).app
      ((f)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.obj K)))
    (hsq : IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq).app K)) :
    IsIso ((e')_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.map
      ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq₁).app K)) := by
  have e := NatTrans.congr_app
    (derivedBaseChangeMapPlus_paste_vert (ModuleCat.{u + 1} Λ) sq₁ sq₂ sq) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Functor.comp_obj] at e
  rw [e, isIso_comp_left_iff, isIso_comp_left_iff, isIso_comp_right_iff] at hsq
  exact hsq

variable [Finite Λ]


/-- **Generic constructibility across a finite boundary**: let `b : Y ⟶ S` be proper over a scheme
`S` of finite type over a field `k` on which the exponent of the finite ring `Λ` is invertible,
`j : X ⟶ Y`, `G ⊆ Y` open with closed complement `i : Z ⟶ Y` finite over the open `U ⊆ S`, and
`K` a bounded below complex on `X`. If over `U` the direct image of `K` along the restriction
`j⁻¹(G) ⟶ G`, and the direct image along `j ≫ b`, are bounded constructible and commute with
every base change from a noetherian scheme, then so is the direct image of `K` along `j`. -/
theorem HasDirectImageBaseChangeOnPlus.of_finite_boundary {k : Type u} [Field k]
    {S X Y Z : Scheme.{u}} (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    [HasInvertibleExponent Λ S] (b : Y ⟶ S) [IsProper b] (j : X ⟶ Y) (G : Y.Opens) (i : Z ⟶ Y)
    [IsClosedImmersion i] (hGi : Set.range i = (G : Set Y)ᶜ) (U : S.Opens)
    [IsFinite ((i ≫ b) ∣_ U)]
    {K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hG : HasDirectImageBaseChangeOnPlus Λ (G.ι ≫ b) (j ∣_ G)
      ((((j ⁻¹ᵁ G).ι)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K) U)
    (ha : HasDirectImageBaseChangeOnPlus Λ (𝟙 S) (j ≫ b) K U) :
    HasDirectImageBaseChangeOnPlus Λ b j K U := by
  have : IsNoetherian S :=
    { __ := LocallyOfFiniteType.isLocallyNoetherian aS
      __ := QuasiCompact.compactSpace_of_compactSpace aS }
  have hΛ : IsAddTorsion Λ := isAddTorsion_of_finite
  have : IsFinite i := ((IsClosedImmersion.iff_isFinite_and_mono i).1 inferInstance).1
  -- the closed complement is finite over every base change factoring through `U`
  have hfin : ∀ {T ZT YT : Scheme.{u}} (t : T ⟶ S) (_ : Set.range t ⊆ U) {gT : YT ⟶ Y}
      {fT : YT ⟶ T} (_ : IsPullback gT fT b t) {gZ : ZT ⟶ Z} {iT : ZT ⟶ YT}
      (_ : IsPullback gZ iT i gT), IsFinite (iT ≫ fT) := by
    intro T ZT YT t ht gT fT hYT gZ iT hZ
    let t' : T ⟶ U := IsOpenImmersion.lift U.ι t (by rwa [Opens.range_ι])
    have ht' : t' ≫ U.ι = t := IsOpenImmersion.lift_fac _ _ _
    have hR : IsPullback ((i ≫ b) ⁻¹ᵁ U).ι ((i ≫ b) ∣_ U) (i ≫ b) U.ι :=
      (isPullback_morphismRestrict (i ≫ b) U).flip
    have hbig : IsPullback gZ (iT ≫ fT) (i ≫ b) (t' ≫ U.ι) := by
      rw [ht']
      exact hZ.paste_vert hYT
    exact MorphismProperty.of_isPullback (IsPullback.of_right' hbig hR).flip.flip inferInstance
  -- the canonical base change to `U`
  have : IsNoetherian U := isNoetherian_opens U
  have : HasInvertibleExponent Λ U := HasInvertibleExponent.of_hom U.ι
  let YU := b ⁻¹ᵁ U
  have hYU : IsPullback YU.ι (b ∣_ U) b U.ι := (isPullback_morphismRestrict b U).flip
  let XU := pullback j YU.ι
  let gXU : XU ⟶ X := pullback.fst j YU.ι
  let jU : XU ⟶ YU := pullback.snd j YU.ι
  have sqU : IsPullback gXU jU j YU.ι := IsPullback.of_hasPullback j YU.ι
  have hUr : Set.range U.ι ⊆ (U : Set S) := by rw [Opens.range_ι]
  -- over `U`, the direct image along `j` is bounded constructible
  have hcU : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) YU
      (_root_.DerivedCategory.Plus.ι.obj ((jU)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.obj
        (((gXU)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K))) := by
    have hG₀ := hG.restrict_apply j G U.ι hUr hYU sqU
    obtain ⟨ha₀, -⟩ := ha U U.ι hUr U XU U.ι (𝟙 U.toScheme) gXU (jU ≫ (b ∣_ U))
      (IsPullback.id_horiz U.ι).flip (sqU.paste_vert hYU)
    let ZU := pullback i YU.ι
    let iU : ZU ⟶ YU := pullback.snd i YU.ι
    have : IsClosedImmersion iU := MorphismProperty.pullback_snd i YU.ι inferInstance
    have : IsFinite (iU ≫ (b ∣_ U)) := hfin U.ι hUr hYU (IsPullback.of_hasPullback i YU.ι)
    refine boundedConstructible_of_upperStar_of_rightDerivedLowerStar Λ (U.ι ≫ aS) (b ∣_ U)
      (YU.ι ⁻¹ᵁ G).ι iU ?_ _
      ((jU)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.obj
        (((gXU)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K)).2 hG₀.1 ?_
    · rw [Opens.range_ι, Scheme.Pullback.range_snd, hGi]
      rfl
    · refine ObjectProperty.prop_of_iso _ ?_ ha₀
      exact _root_.DerivedCategory.Plus.ι.mapIso
          ((Functor.rightDerivedFunctorPlusCompIso' (jU)_*[ModuleCat.{u + 1} Λ]
            (b ∣_ U)_*[ModuleCat.{u + 1} Λ]
            (lowerStarComp (ModuleCat.{u + 1} Λ) jU (b ∣_ U))).symm.app _) ≪≫
        (b ∣_ U)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlusCompatibility.app _
  have iU := isIso_derivedBaseChangeMapPlus_of_etale (Λ := Λ) sqU
  intro T _ t ht YT XT gT fT gXT jT hYT sqT
  -- the base change of the closed complement, finite over `T`
  let ZT := pullback i gT
  let iT : ZT ⟶ YT := pullback.snd i gT
  have : IsClosedImmersion iT := MorphismProperty.pullback_snd i gT inferInstance
  have : IsFinite (iT ≫ fT) := hfin t ht hYT (IsPullback.of_hasPullback i gT)
  have hrange : Set.range iT = (Set.range (gT ⁻¹ᵁ G).ι)ᶜ := by
    rw [Opens.range_ι, Scheme.Pullback.range_snd, hGi]
    rfl
  -- the derived base change map for `j`, restricted to `G_T`
  have hres := hG.restrict_apply j G t ht hYT sqT
  -- the derived base change map for `j ≫ b`
  obtain ⟨-, iab⟩ := ha T t ht T XT t (𝟙 T) gXT (jT ≫ fT) (IsPullback.id_horiz t).flip
    (sqT.paste_vert hYT)
  have hb : IsIso (derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) hYT.toCommSq) := by
    rw [← baseChange_eq_derivedBaseChangeMapPlus]
    exact isIso_baseChange_of_isProper_of_isAddTorsion_ring Λ hΛ hYT
  have hbc := isIso_rightDerivedFunctorPlus_map_derivedBaseChangeMapPlus_app_of_paste_vert
    sqT.toCommSq hYT.toCommSq (sqT.paste_vert hYT).toCommSq K inferInstance
    ((isIso_derivedBaseChangeMapPlus_app_congr' rfl rfl rfl rfl _ _ K).1 iab)
  -- hence the derived base change map for `j` is an isomorphism
  have hiso : IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sqT.toCommSq).app K) := by
    have : IsIso (_root_.DerivedCategory.Plus.ι.map
        ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sqT.toCommSq).app K)) := by
      refine isIso_of_isIso_upperStar_map_of_isIso_rightDerivedLowerStar_map Λ fT
        (gT ⁻¹ᵁ G).ι iT hrange _ ?_ ?_
      · have := hres.2
        exact Functor.map_isIso _root_.DerivedCategory.Plus.ι
          ((((gT ⁻¹ᵁ G).ι)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.map
            ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sqT.toCommSq).app K))
      · exact (NatIso.isIso_map_iff
          (fT)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlusCompatibility
          ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sqT.toCommSq).app K)).1
          (Functor.map_isIso _root_.DerivedCategory.Plus.ι
            ((fT)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.map
              ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sqT.toCommSq).app K)))
    exact isIso_of_fully_faithful _root_.DerivedCategory.Plus.ι _
  refine ⟨?_, hiso⟩
  -- `Y_T ⟶ Y` factors through `Y_U`, over which `Rj_* K` is bounded constructible
  have hgT : Set.range gT ⊆ Set.range YU.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Opens.range_ι]
    change b (gT y) ∈ U
    rw [← Scheme.Hom.comp_apply, hYT.w, Scheme.Hom.comp_apply]
    exact ht ⟨_, rfl⟩
  let gT' : YT ⟶ YU := IsOpenImmersion.lift YU.ι gT hgT
  have hgT' : gT' ≫ YU.ι = gT := IsOpenImmersion.lift_fac _ _ _
  have hc := hcU.mapDerivedCategory_upperStar gT'
  refine ObjectProperty.prop_of_iso _ ?_ hc
  let e₁ := ((gT')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.mapIso
    (asIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sqU.toCommSq).app K)).symm
  let e₂ := ((upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) gT' YU.ι gT hgT'.symm).app
    ((j)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.obj K)).symm
  let e₃ := asIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sqT.toCommSq).app K)
  exact _root_.DerivedCategory.Plus.ι.mapIso (e₁ ≪≫ e₂ ≪≫ e₃)

end Etale

end AlgebraicGeometry
