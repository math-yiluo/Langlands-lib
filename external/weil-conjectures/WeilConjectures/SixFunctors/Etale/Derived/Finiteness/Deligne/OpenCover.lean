/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.FiniteOpenCover
public import WeilConjectures.SixFunctors.BaseChange.EtaleDerived
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne.RadicialDescent
public import WeilConjectures.SixFunctors.OpenClosed.Conservative

/-!
# Generic constructibility of a direct image is local on the target

Let `j : X ⟶ Y` be a morphism of `S`-schemes, `Y` locally of finite type over `S`, and let
`Y = ⋃ᵢ Vᵢ` be a finite open cover. If for each `i` the direct image along the restriction
`j⁻¹(Vᵢ) ⟶ Vᵢ` of the restriction of `K` is bounded constructible and commutes with base change
over `U`, then so is `Rj_* K`
(`AlgebraicGeometry.Etale.HasDirectImageBaseChangeOnPlus.of_openCover`).

After a base change `T ⟶ S`, the restriction of `Rj_{T,*} K_T` to `V_{i,T}` is the direct image
along the restriction, by étale base change, and both bounded constructibility and the
invertibility of a morphism can be checked on a finite open cover of a locally noetherian scheme
(`AlgebraicGeometry.Etale.boundedConstructible_of_finite_openCover`). The comparison of the base
change maps is the pasting law.
-/

@[expose] public section

universe u

open CategoryTheory Limits ZeroObject

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- Isomorphisms of `D⁺(X_ét, Λ)` can be checked after restriction to the members of a jointly
surjective family. -/
lemma isIso_of_isIso_mapDerivedCategoryPlus_map_of_jointlySurjective {X : Scheme.{u}}
    {ι : Type u} {V : ι → Scheme.{u}} (a : ∀ i, V i ⟶ X)
    (ha : ∀ x : X, ∃ (i : ι) (y : V i), (a i).base y = x)
    {M N : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : M ⟶ N) (h : ∀ i, IsIso (((a i)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.map φ)) :
    IsIso φ := by
  rw [_root_.DerivedCategory.Plus.isIso_iff]
  intro n
  refine Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} Λ) a ha _
    fun i ↦ ?_
  exact (NatIso.isIso_map_iff
    (((a i)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso n) φ).2
    (Functor.map_isIso (_root_.DerivedCategory.Plus.homologyFunctor _ n)
      (((a i)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.map φ))

/-- **Bounded constructibility is local for finite open covers** of a locally noetherian
scheme. -/
lemma boundedConstructible_of_finite_openCover {X : Scheme.{u}} [IsLocallyNoetherian X]
    {ι : Type u} [Finite ι] (V : ι → X.Opens) (hV : ⨆ i, V i = ⊤)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (h : ∀ i, DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) (V i)
      (D(((V i).ι)^*[ModuleCat.{u + 1} Λ]).obj K)) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K := by
  have := Fintype.ofFinite ι
  have hcov : ∀ x : X, ∃ (i : ι) (y : V i), (V i).ι.base y = x := fun x ↦ by
    have hx : x ∈ (⊤ : X.Opens) := trivial
    rw [← hV] at hx
    obtain ⟨i, hi⟩ := (TopologicalSpace.Opens.mem_iSup).1 hx
    exact ⟨i, ⟨x, hi⟩, rfl⟩
  -- the homology sheaves of `K` restrict to those of the restrictions
  let e (i : ι) (q : ℤ) : (_root_.DerivedCategory.homologyFunctor _ q).obj
      (D(((V i).ι)^*[ModuleCat.{u + 1} Λ]).obj K) ≅
        ((V i).ι)^*[ModuleCat.{u + 1} Λ].obj ((_root_.DerivedCategory.homologyFunctor _ q).obj K) :=
    ((((V i).ι)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso q).symm.app K
  have hz (q : ℤ) (hq : ∀ i, IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
      (D(((V i).ι)^*[ModuleCat.{u + 1} Λ]).obj K))) :
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj K) :=
    have : IsIso (0 : (_root_.DerivedCategory.homologyFunctor _ q).obj K ⟶ 0) :=
      Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} Λ)
        (fun i ↦ (V i).ι) hcov _ fun i ↦ by
          rw [Functor.map_zero]
          exact ⟨0, ((hq i).of_iso (e i q).symm).eq_of_src _ _,
            (Functor.map_isZero _ (isZero_zero _)).eq_of_src _ _⟩
    (isZero_zero _).of_iso (asIso (0 : (_root_.DerivedCategory.homologyFunctor _ q).obj K ⟶ 0))
  choose a b hab using fun i ↦
    (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded _).2 (h i).1
  let A : ℤ := -∑ i, |a i|
  let B : ℤ := ∑ i, |b i|
  have hA (i : ι) : A ≤ a i := by
    have := Finset.single_le_sum (f := fun i ↦ |a i|) (fun _ _ ↦ abs_nonneg _)
      (Finset.mem_univ i)
    have := neg_abs_le (a i)
    simp only [A]
    lia
  have hB (i : ι) : b i ≤ B := by
    have := Finset.single_le_sum (f := fun i ↦ |b i|) (fun _ _ ↦ abs_nonneg _)
      (Finset.mem_univ i)
    have := le_abs_self (b i)
    simp only [B]
    lia
  refine ⟨(_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded K).1
    ⟨A, B, ⟨(_root_.DerivedCategory.isGE_iff _ A).2 fun q hq ↦ hz q fun i ↦
      (_root_.DerivedCategory.isGE_iff _ (a i)).1 (hab i).1 q (by linarith [hA i]),
      (_root_.DerivedCategory.isLE_iff _ B).2 fun q hq ↦ hz q fun i ↦
      (_root_.DerivedCategory.isLE_iff _ (b i)).1 (hab i).2 q (by linarith [hB i])⟩⟩,
    fun q ↦ ?_⟩
  refine Scheme.IsConstructibleSheaf.of_finite_openCover V hV _ fun i ↦ ?_
  have : IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ q).obj
      (D(((V i).ι)^*[ModuleCat.{u + 1} Λ]).obj K)) := (h i).2 q
  exact IsConstructibleSheaf.of_iso (e i q)

/-- **Restriction to an open of the target**: if the direct image along the restriction
`j⁻¹(V) ⟶ V` of `j : X ⟶ Y` to an open `V ⊆ Y` has the generic constructibility property over
`U`, then for every base change `T ⟶ S` with image in `U` the restriction to `V_T` of
`Rj_{T,*} K_T` is bounded constructible and the restriction to `V_T` of the derived base change
map is an isomorphism. -/
lemma HasDirectImageBaseChangeOnPlus.restrict_apply {S X Y : Scheme.{u}} {fY : Y ⟶ S}
    (j : X ⟶ Y) (V : Y.Opens)
    {K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {U : Set S}
    (h : HasDirectImageBaseChangeOnPlus Λ (V.ι ≫ fY) (j ∣_ V)
      ((((j ⁻¹ᵁ V).ι)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K) U)
    {T : Scheme.{u}} [IsNoetherian T] (t : T ⟶ S) (ht : Set.range t ⊆ U)
    {YT XT : Scheme.{u}} {gT : YT ⟶ Y} {fT : YT ⟶ T} {gXT : XT ⟶ X} {jT : XT ⟶ YT}
    (hYT : IsPullback gT fT fY t) (sqT : IsPullback gXT jT j gT) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) (gT ⁻¹ᵁ V)
        (D(((gT ⁻¹ᵁ V).ι)^*[ModuleCat.{u + 1} Λ]).obj (_root_.DerivedCategory.Plus.ι.obj
          ((jT)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.obj
            (((gXT)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K)))) ∧
      IsIso ((((gT ⁻¹ᵁ V).ι)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.map
        ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sqT.toCommSq).app K)) := by
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
  obtain ⟨c, i⟩ := h T t ht W _ (gT ∣_ V) (W.ι ≫ fT) gX' (jT ∣_ W) hA hB
  have iR := isIso_derivedBaseChangeMapPlus_of_etale (Λ := Λ) hR
  have iRj := isIso_derivedBaseChangeMapPlus_of_etale (Λ := Λ) hRj
  let eK := ((upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (jT ⁻¹ᵁ W).ι gXT).app K).symm ≪≫
    (upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) gX' (j ⁻¹ᵁ V).ι
      ((jT ⁻¹ᵁ W).ι ≫ gXT) hgX'.symm).app K
  refine ⟨ObjectProperty.prop_of_iso _ ?_ c, ?_⟩
  · exact _root_.DerivedCategory.Plus.ι.mapIso
      ((jT ∣_ W)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.mapIso eK.symm ≪≫
        (asIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) hR.toCommSq).app
          (((gXT)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K))).symm)
  · have h₁ : IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ)
        (⟨by rw [Category.assoc, hRj.w, ← Category.assoc, hB.w, Category.assoc]⟩ :
          CommSq (gX' ≫ (j ⁻¹ᵁ V).ι) (jT ∣_ W) j ((gT ∣_ V) ≫ V.ι))).app K) :=
      (isIso_derivedBaseChangeMapPlus_app_paste_horiz_iff hRj.toCommSq hB.toCommSq _ K i).2
        inferInstance
    have h₂ : IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ)
        (⟨by rw [Category.assoc, sqT.w, ← Category.assoc, hR.w, Category.assoc]⟩ :
          CommSq ((jT ⁻¹ᵁ W).ι ≫ gXT) (jT ∣_ W) j (W.ι ≫ gT))).app K) :=
      (isIso_derivedBaseChangeMapPlus_app_congr hgX' (morphismRestrict_ι gT V) _ _ K).1 h₁
    exact (isIso_derivedBaseChangeMapPlus_app_paste_horiz_iff sqT.toCommSq hR.toCommSq _ K
      inferInstance).1 h₂

/-- **Generic constructibility of a direct image is local on the target**: for a morphism
`j : X ⟶ Y` of `S`-schemes, `Y` locally of finite type over `S`, and a finite open cover
`Y = ⋃ᵢ Vᵢ`, if the direct image along each restriction `j⁻¹(Vᵢ) ⟶ Vᵢ` of the restriction of `K`
is bounded constructible and commutes with base change over `U`, then so is `Rj_* K`. -/
theorem HasDirectImageBaseChangeOnPlus.of_openCover {S X Y : Scheme.{u}} {fY : Y ⟶ S}
    [LocallyOfFiniteType fY] (j : X ⟶ Y) {ι : Type u} [Finite ι] (V : ι → Y.Opens)
    (hV : ⨆ i, V i = ⊤)
    {K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {U : Set S}
    (h : ∀ i, HasDirectImageBaseChangeOnPlus Λ ((V i).ι ≫ fY) (j ∣_ V i)
      ((((j ⁻¹ᵁ V i).ι)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K) U) :
    HasDirectImageBaseChangeOnPlus Λ fY j K U := by
  intro T _ t ht YT XT gT fT gXT jT hYT sqT
  have : LocallyOfFiniteType fT := MorphismProperty.of_isPullback hYT inferInstance
  have : IsLocallyNoetherian YT := LocallyOfFiniteType.isLocallyNoetherian fT
  have hW : ⨆ i, gT ⁻¹ᵁ V i = ⊤ := by
    simp only [← Scheme.Hom.preimage_iSup, hV, Scheme.Hom.preimage_top]
  have hr (i : ι) := (h i).restrict_apply j (V i) t ht hYT sqT
  refine ⟨boundedConstructible_of_finite_openCover _ hW fun i ↦ (hr i).1, ?_⟩
  refine isIso_of_isIso_mapDerivedCategoryPlus_map_of_jointlySurjective (fun i ↦ (gT ⁻¹ᵁ V i).ι)
    (fun x ↦ ?_) _ fun i ↦ (hr i).2
  have hx : x ∈ (⊤ : YT.Opens) := trivial
  rw [← hW] at hx
  obtain ⟨i, hi⟩ := (TopologicalSpace.Opens.mem_iSup).1 hx
  exact ⟨i, ⟨x, hi⟩, rfl⟩

end Etale

end AlgebraicGeometry
