/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne.Transport

/-!
# Generic constructibility from a cover by open immersions

Let `j : X ⟶ Y` be a morphism of `S`-schemes, `Y` locally of finite type over `S`, and let
`aᵢ : Vᵢ ⟶ Y` be finitely many open immersions covering `Y`, with base changes
`jᵢ : Xᵢ ⟶ Vᵢ` of `j`. If the direct image of the restriction of `K` along each `jᵢ` is bounded
constructible and commutes with base change over `U`, then so is the direct image of `K` along
`j` (`AlgebraicGeometry.Etale.HasDirectImageBaseChangeOnPlus.of_cover`). This is the form of
`AlgebraicGeometry.Etale.HasDirectImageBaseChangeOnPlus.of_openCover` in which the members of
the cover need not be presented as open subschemes of `Y`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- Bounded constructibility is local for finite covers by open immersions of a locally
noetherian scheme. -/
lemma boundedConstructible_of_finite_cover {X : Scheme.{u}} [IsLocallyNoetherian X]
    {ι : Type u} [Finite ι] {V : ι → Scheme.{u}} (a : ∀ i, V i ⟶ X) [∀ i, IsOpenImmersion (a i)]
    (ha : ∀ x : X, ∃ (i : ι) (y : V i), a i y = x)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (h : ∀ i, DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) (V i)
      (D((a i)^*[ModuleCat.{u + 1} Λ]).obj K)) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K := by
  refine boundedConstructible_of_finite_openCover (fun i ↦ (a i).opensRange) ?_ fun i ↦ ?_
  · refine eq_top_iff.2 fun x _ ↦ ?_
    obtain ⟨i, y, rfl⟩ := ha x
    exact (TopologicalSpace.Opens.mem_iSup).2 ⟨i, ⟨y, rfl⟩⟩
  · have e := (a i).isoOpensRange_hom_ι
    have hc := (h i).mapDerivedCategory_upperStar (a i).isoOpensRange.inv
    refine ObjectProperty.prop_of_iso _ ?_ hc
    exact (Functor.mapDerivedCategoryCompIso _ _).app K ≪≫
      (Functor.mapDerivedCategoryNatIso ((upperStarComp (ModuleCat.{u + 1} Λ)
        (a i).isoOpensRange.inv (a i) ((a i).opensRange.ι)
        (by rw [← cancel_epi (a i).isoOpensRange.hom, Iso.hom_inv_id_assoc]; exact e)).symm)).app
        K

/-- **Generic constructibility from a cover by open immersions**: for `j : X ⟶ Y` over `S`, `Y`
locally of finite type over `S`, finitely many open immersions `aᵢ : Vᵢ ⟶ Y` covering `Y`, base
changes `jᵢ : Xᵢ ⟶ Vᵢ` of `j` along `aᵢ` with projections `bᵢ : Xᵢ ⟶ X`, and complexes
`Kᵢ ≅ bᵢ^* K`: if each direct image `Rjᵢ_* Kᵢ` is bounded constructible and commutes with base
change over `U`, then so is `Rj_* K`. -/
theorem HasDirectImageBaseChangeOnPlus.of_cover {S X Y : Scheme.{u}} {fY : Y ⟶ S}
    [LocallyOfFiniteType fY] (j : X ⟶ Y) {ι : Type u} [Finite ι] {V Xi : ι → Scheme.{u}}
    (a : ∀ i, V i ⟶ Y) [∀ i, IsOpenImmersion (a i)] (ha : ∀ y : Y, ∃ (i : ι) (x : V i), a i x = y)
    (b : ∀ i, Xi i ⟶ X) (ji : ∀ i, Xi i ⟶ V i) (hb : ∀ i, IsPullback (b i) (ji i) j (a i))
    {K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {Ki : ∀ i, _root_.DerivedCategory.Plus (Sheaf (Xi i).smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (eK : ∀ i, Ki i ≅ (((b i))^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K) {U : Set S}
    (h : ∀ i, HasDirectImageBaseChangeOnPlus Λ (a i ≫ fY) (ji i) (Ki i) U) :
    HasDirectImageBaseChangeOnPlus Λ fY j K U := by
  intro T _ t ht YT XT gT fT gXT jT hYT sqT
  have : LocallyOfFiniteType fT := MorphismProperty.of_isPullback hYT inferInstance
  have : IsLocallyNoetherian YT := LocallyOfFiniteType.isLocallyNoetherian fT
  -- the restrictions of the base change to the members of the cover
  let WT (i : ι) := pullback (a i) gT
  let gW (i : ι) : WT i ⟶ V i := pullback.fst (a i) gT
  let aT (i : ι) : WT i ⟶ YT := pullback.snd (a i) gT
  have hW (i : ι) : IsPullback (gW i) (aT i) (a i) gT := IsPullback.of_hasPullback (a i) gT
  have : ∀ i, IsOpenImmersion (aT i) := fun i ↦ MorphismProperty.pullback_snd _ _ inferInstance
  let XW (i : ι) := pullback (ji i) (gW i)
  let gXW (i : ι) : XW i ⟶ Xi i := pullback.fst (ji i) (gW i)
  let jW (i : ι) : XW i ⟶ WT i := pullback.snd (ji i) (gW i)
  have sqW (i : ι) : IsPullback (gXW i) (jW i) (ji i) (gW i) :=
    IsPullback.of_hasPullback (ji i) (gW i)
  have hc (i : ι) := h i T t ht (WT i) (XW i) (gW i) (aT i ≫ fT) (gXW i) (jW i)
    ((hW i).paste_vert hYT) (sqW i)
  -- the comparison of the restricted base change with the restriction of the base change
  have htot (i : ι) : IsPullback (gXW i ≫ b i) (jW i) j (aT i ≫ gT) := by
    rw [← (hW i).w]
    exact (sqW i).paste_horiz (hb i)
  have hex : ∀ i, ∃ c : XW i ⟶ XT, IsPullback c (jW i) jT (aT i) ∧
      c ≫ gXT = gXW i ≫ b i := fun i ↦
    ⟨_, IsPullback.of_right' (htot i) sqT, sqT.lift_fst _ _ _⟩
  choose cX hcX hcX₁ using hex
  have iR (i : ι) := isIso_derivedBaseChangeMapPlus_of_etale (Λ := Λ) (hcX i)
  have ib (i : ι) := isIso_derivedBaseChangeMapPlus_of_etale (Λ := Λ) (hb i)
  have hcov (y : YT) : ∃ (i : ι) (w : WT i), aT i w = y := by
    obtain ⟨i, x, hx⟩ := ha (gT y)
    obtain ⟨w, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback x y hx
    exact ⟨i, w, hw₂⟩
  refine ⟨boundedConstructible_of_finite_cover aT hcov fun i ↦ ?_, ?_⟩
  · refine ObjectProperty.prop_of_iso _ ?_ (hc i).1
    exact _root_.DerivedCategory.Plus.ι.mapIso
      ((jW i)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.mapIso
          ((((gXW i))^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.mapIso (eK i) ≪≫
            ((upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (gXW i) (b i)).app K).symm ≪≫
            (upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (cX i) gXT (gXW i ≫ b i)
              (hcX₁ i).symm).app K) ≪≫
        (asIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) (hcX i).toCommSq).app
          (((gXT)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K))).symm)
  · refine isIso_of_isIso_mapDerivedCategoryPlus_map_of_jointlySurjective aT hcov _ fun i ↦ ?_
    have h₂ : IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) (sqW i).toCommSq).app
        ((((b i))^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K)) :=
      (NatTrans.isIso_app_iff_of_iso _ (eK i)).1 (hc i).2
    have h₁ := (isIso_derivedBaseChangeMapPlus_app_paste_horiz_iff (hb i).toCommSq
      (sqW i).toCommSq (⟨by rw [Category.assoc, (hb i).w, ← Category.assoc, (sqW i).w,
        Category.assoc]⟩ : CommSq (gXW i ≫ b i) (jW i) j (gW i ≫ a i)) K h₂).2 inferInstance
    have h₁' := (isIso_derivedBaseChangeMapPlus_app_congr' (hcX₁ i).symm rfl rfl (hW i).w
      _ (⟨by rw [Category.assoc, sqT.w, ← Category.assoc, (hcX i).w,
        Category.assoc]⟩ : CommSq (cX i ≫ gXT) (jW i) j (aT i ≫ gT)) K).1 h₁
    exact (isIso_derivedBaseChangeMapPlus_app_paste_horiz_iff sqT.toCommSq (hcX i).toCommSq _ K
      inferInstance).1 h₁'

end Etale

end AlgebraicGeometry
