/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationSpace.BaseChangeClosedImmersion
public import WeilConjectures.TraceFormula.Specialization.DefectCentreMap
public import WeilConjectures.TraceFormula.Specialization.TraitBaseChangeModel

/-!

# Deformation models along a change of the base field

Let `k ⟶ K₀` be a field extension, `k'` an extension of `k` and `K` a common extension of `K₀`
and `k'` (compatibly over `k`). Let `Y` be a `k`-scheme, `Y₀` a `K₀`-scheme and `h : Y₀ ⟶ Y` a
morphism over `Spec K₀ ⟶ Spec k`, with ideal sheaves `J` on `Y` and `J₀ ⊇ h^* J` on `Y₀`. The
morphism of deformation spaces `D_{J₀} Y₀ ⟶ D_J Y` lies over `𝔸¹_{K₀} ⟶ 𝔸¹_k`, and the change of
trait `Spec K⟦t⟧ ⟶ Spec k'⟦t⟧` lies over it as well; this gives a morphism of nearby cycles models
`deformationModel Y₀ J₀ K ⟶ deformationModel Y J k'`
(`ProEtale.CondensedRing.deformationModelBaseFieldHom`).

If `Y₀ = Y ×_k K₀` and `D_{J₀} Y₀ = Y₀ ×_Y D_J Y` (e.g. `h` flat and `J₀ = h⁻¹ J`, or `J`, `J₀`
the zero ideals), then `D_{J₀} Y₀ = D_J Y ×_{𝔸¹_k} 𝔸¹_{K₀}`, the total space of the model of
`Y₀` is the base change of the one of `Y` along the change of trait, and the special fibre of the
model of `Y₀` is the base change of the one of `Y` along `Spec K ⟶ Spec k'`.

## Main definitions

- `ProEtale.CondensedRing.deformationTotalBaseFieldMap`,
  `ProEtale.CondensedRing.deformationGenericBaseFieldMap`,
  `ProEtale.CondensedRing.deformationSpecialBaseFieldMap`: the maps of total spaces, geometric
  generic fibres and special fibres.
- `ProEtale.CondensedRing.deformationModelBaseFieldHom`: the morphism of nearby cycles models.

## Main results

- `ProEtale.CondensedRing.isPullback_deformationSpaceMap_affineLine`:
  `D_{J₀} Y₀ = D_J Y ×_{𝔸¹_k} 𝔸¹_{K₀}`.
- `ProEtale.CondensedRing.isPullback_deformationTotalBaseFieldMap`: the total spaces form a
  cartesian square over the change of trait.
- `ProEtale.CondensedRing.isPullback_deformationSpecialBaseFieldMap`: the special fibres form a
  cartesian square over `Spec K ⟶ Spec k'`.
- `ProEtale.CondensedRing.zeroSection_deformationSpecialBaseFieldMap`: compatibility with the zero
  sections.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (k K₀ : Type u) [Field k] [Field K₀] [Algebra k K₀] (k' K : Type u) [Field k'] [Field K]
  [Algebra k k'] [Algebra K₀ K] [Algebra k' K] [Algebra k K] [IsScalarTower k K₀ K]
  [IsScalarTower k k' K]

/-- The change of trait `Spec K⟦t⟧ ⟶ Spec k'⟦t⟧` lies over the change of affine lines
`𝔸¹_{K₀} ⟶ 𝔸¹_k`. -/
@[reassoc]
lemma traitToAffineLine_map_eq_traitMap_traitToAffineLine :
    traitToAffineLine K₀ K ≫
        AffineSpace.map (ULift.{u} (Fin 1)) (Spec.map (CommRingCat.ofHom (algebraMap k K₀))) =
      traitMap k' K ≫ traitToAffineLine k k' := by
  refine AffineSpace.hom_ext ?_ fun i ↦ ?_
  · rw [Category.assoc, AffineSpace.map_over, traitToAffineLine_over_assoc, Category.assoc,
      traitToAffineLine_over, traitToBase, traitToBase, traitMap, ← Spec.map_comp,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a : 1
    simp [PowerSeries.algebraMap_apply, ← IsScalarTower.algebraMap_apply k K₀ K,
      ← IsScalarTower.algebraMap_apply k k' K]
  · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply, AffineSpace.map_appTop_coord, traitToAffineLine,
      AffineSpace.homOfVector_appTop_coord, traitToAffineLine, AffineSpace.homOfVector_appTop_coord,
      traitMap, ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
      CommRingCat.comp_apply]
    simp

end AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {k K₀ : Type u} [Field k] [Field K₀] [Algebra k K₀] (k' K : Type u) [Field k'] [Field K]
  [Algebra k k'] [Algebra K₀ K] [Algebra k' K] [Algebra k K] [IsScalarTower k K₀ K]
  [IsScalarTower k k' K]
  {Y : Over (Spec (.of k))} {Y₀ : Over (Spec (.of K₀))} (h : Y₀.left ⟶ Y.left)
  (hh : h ≫ Y.hom = Y₀.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k K₀)))
  {J : Y.left.IdealSheafData} {J₀ : Y₀.left.IdealSheafData}
  (hJ : ∀ ⦃U' : Y₀.left.AffineZariskiSite⦄ ⦃U : Y.left.AffineZariskiSite⦄
    (hU : U'.1 ≤ h ⁻¹ᵁ U.1), (J.siteIdeal U).map (h.appLE U.1 U'.1 hU).hom ≤ J₀.siteIdeal U')

include hh in
/-- The morphism of deformation spaces `D_{J₀} Y₀ ⟶ D_J Y` lies over `𝔸¹_{K₀} ⟶ 𝔸¹_k`. -/
@[reassoc]
lemma deformationSpaceMap_deformationSpaceToAffineLine_of_base :
    IdealSheafData.deformationSpaceMap h J J₀ hJ ≫ deformationSpaceToAffineLine Y J =
      deformationSpaceToAffineLine Y₀ J₀ ≫
        AffineSpace.map _ (Spec.map (CommRingCat.ofHom (algebraMap k K₀))) :=
  IdealSheafData.deformationSpaceMap_proj h J J₀ hJ Y.hom Y₀.hom _ hh

/-- **The deformation space along a change of base field**: if `Y₀ = Y ×_k K₀` and
`D_{J₀} Y₀ = Y₀ ×_Y D_J Y`, then `D_{J₀} Y₀ = D_J Y ×_{𝔸¹_k} 𝔸¹_{K₀}`. -/
lemma isPullback_deformationSpaceMap_affineLine
    (hY : IsPullback h Y₀.hom Y.hom (Spec.map (CommRingCat.ofHom (algebraMap k K₀))))
    (hD : IsPullback (IdealSheafData.deformationSpaceMap h J J₀ hJ) J₀.deformationSpaceProj
      J.deformationSpaceProj h) :
    IsPullback (IdealSheafData.deformationSpaceMap h J J₀ hJ) (deformationSpaceToAffineLine Y₀ J₀)
      (deformationSpaceToAffineLine Y J)
      (AffineSpace.map _ (Spec.map (CommRingCat.ofHom (algebraMap k K₀)))) := by
  refine IsPullback.of_bot ?_
    (deformationSpaceMap_deformationSpaceToAffineLine_of_base h hY.w hJ)
    (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) _)
  rw [deformationSpaceToAffineLine, deformationSpaceToAffineLine,
    IdealSheafData.deformationSpaceProj_over', IdealSheafData.deformationSpaceProj_over']
  exact hD.paste_vert hY

/-- The morphism of total spaces `𝒳₀ = D_{J₀} Y₀ ×_{𝔸¹_{K₀}} Spec K⟦t⟧ ⟶
𝒳 = D_J Y ×_{𝔸¹_k} Spec k'⟦t⟧` along a change of base field. -/
noncomputable def deformationTotalBaseFieldMap :
    deformationTotal Y₀ J₀ K ⟶ deformationTotal Y J k' :=
  pullback.map _ _ _ _ (IdealSheafData.deformationSpaceMap h J J₀ hJ) (traitMap k' K)
    (AffineSpace.map _ (Spec.map (CommRingCat.ofHom (algebraMap k K₀))))
    (deformationSpaceMap_deformationSpaceToAffineLine_of_base h hh hJ).symm
    (traitToAffineLine_map_eq_traitMap_traitToAffineLine k K₀ k' K)

@[reassoc (attr := simp)]
lemma deformationTotalBaseFieldMap_toSpace :
    deformationTotalBaseFieldMap k' K h hh hJ ≫ deformationTotalToSpace Y J k' =
      deformationTotalToSpace Y₀ J₀ K ≫ IdealSheafData.deformationSpaceMap h J J₀ hJ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma deformationTotalBaseFieldMap_toTrait :
    deformationTotalBaseFieldMap k' K h hh hJ ≫ deformationTotalToTrait Y J k' =
      deformationTotalToTrait Y₀ J₀ K ≫ traitMap k' K :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma deformationTotalBaseFieldMap_toBase :
    deformationTotalBaseFieldMap k' K h hh hJ ≫ deformationTotalToBase Y J k' =
      deformationTotalToBase Y₀ J₀ K ≫ h := by
  rw [deformationTotalToBase, deformationTotalBaseFieldMap_toSpace_assoc,
    IdealSheafData.deformationSpaceMap_toBase, deformationTotalToBase, Category.assoc]

/-- If `D_{J₀} Y₀ = D_J Y ×_{𝔸¹_k} 𝔸¹_{K₀}`, the total space of the model of `Y₀` is the base
change of the one of `Y` along the change of trait `Spec K⟦t⟧ ⟶ Spec k'⟦t⟧`. -/
lemma isPullback_deformationTotalBaseFieldMap
    (hD : IsPullback (IdealSheafData.deformationSpaceMap h J J₀ hJ)
      (deformationSpaceToAffineLine Y₀ J₀) (deformationSpaceToAffineLine Y J)
      (AffineSpace.map _ (Spec.map (CommRingCat.ofHom (algebraMap k K₀))))) :
    IsPullback (deformationTotalBaseFieldMap k' K h hh hJ) (deformationTotalToTrait Y₀ J₀ K)
      (deformationTotalToTrait Y J k') (traitMap k' K) := by
  refine IsPullback.of_right ?_ (deformationTotalBaseFieldMap_toTrait k' K h hh hJ)
    (isPullback_deformationTotal Y J k')
  rw [deformationTotalBaseFieldMap_toSpace,
    ← traitToAffineLine_map_eq_traitMap_traitToAffineLine k K₀ k' K]
  exact (isPullback_deformationTotal Y₀ J₀ K).paste_horiz hD

/-- The morphism of geometric generic fibres along a change of base field. -/
noncomputable def deformationGenericBaseFieldMap :
    deformationGeneric Y₀ J₀ K ⟶ deformationGeneric Y J k' :=
  pullback.map _ _ _ _ (deformationTotalBaseFieldMap k' K h hh hJ) (traitGenericPointMap k' K)
    (traitMap k' K) (deformationTotalBaseFieldMap_toTrait k' K h hh hJ).symm
    (traitGenericPoint_traitMap k' K)

@[reassoc (attr := simp)]
lemma deformationGenericBaseFieldMap_toTotal :
    deformationGenericBaseFieldMap k' K h hh hJ ≫ deformationGenericToTotal Y J k' =
      deformationGenericToTotal Y₀ J₀ K ≫ deformationTotalBaseFieldMap k' K h hh hJ :=
  pullback.lift_fst _ _ _

/-- The morphism of geometric generic fibres lies over `Spec Ω_K ⟶ Spec Ω_{k'}`. -/
@[reassoc]
lemma deformationGenericBaseFieldMap_snd :
    deformationGenericBaseFieldMap k' K h hh hJ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (traitGenericFieldMap k' K)) :=
  pullback.lift_snd _ _ _

/-- The morphism of special fibres `𝒳₀,s ⟶ 𝒳_s` along a change of base field, over
`Spec K ⟶ Spec k'`. -/
noncomputable def deformationSpecialBaseFieldMap :
    (deformationSpecialFibre Y₀ J₀ K).left ⟶ (deformationSpecialFibre Y J k').left :=
  pullback.map _ _ _ _ (deformationTotalBaseFieldMap k' K h hh hJ)
    (Spec.map (CommRingCat.ofHom (algebraMap k' K))) (traitMap k' K)
    (deformationTotalBaseFieldMap_toTrait k' K h hh hJ).symm (traitClosedPoint_traitMap k' K)

@[reassoc (attr := simp)]
lemma deformationSpecialBaseFieldMap_toTotal :
    deformationSpecialBaseFieldMap k' K h hh hJ ≫ deformationSpecialToTotal Y J k' =
      deformationSpecialToTotal Y₀ J₀ K ≫ deformationTotalBaseFieldMap k' K h hh hJ :=
  pullback.lift_fst _ _ _

/-- The morphism of special fibres lies over `Spec K ⟶ Spec k'`. -/
@[reassoc]
lemma deformationSpecialBaseFieldMap_hom :
    deformationSpecialBaseFieldMap k' K h hh hJ ≫ (deformationSpecialFibre Y J k').hom =
      (deformationSpecialFibre Y₀ J₀ K).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k' K)) :=
  pullback.lift_snd _ _ _

/-- The morphism of special fibres is compatible with the projections to `Y₀` and `Y`. -/
@[reassoc]
lemma deformationSpecialBaseFieldMap_toBase :
    deformationSpecialBaseFieldMap k' K h hh hJ ≫ deformationSpecialToTotal Y J k' ≫
        deformationTotalToBase Y J k' =
      (deformationSpecialToTotal Y₀ J₀ K ≫ deformationTotalToBase Y₀ J₀ K) ≫ h := by
  rw [deformationSpecialBaseFieldMap_toTotal_assoc, deformationTotalBaseFieldMap_toBase,
    Category.assoc]

/-- If the total space of the model of `Y₀` is the base change of the one of `Y` along the change
of trait, the special fibre of the model of `Y₀` is the base change of the one of `Y` along
`Spec K ⟶ Spec k'`: `𝒳₀,s = 𝒳_s ⊗_{k'} K`. -/
lemma isPullback_deformationSpecialBaseFieldMap
    (hT : IsPullback (deformationTotalBaseFieldMap k' K h hh hJ) (deformationTotalToTrait Y₀ J₀ K)
      (deformationTotalToTrait Y J k') (traitMap k' K)) :
    IsPullback (deformationSpecialBaseFieldMap k' K h hh hJ) (deformationSpecialFibre Y₀ J₀ K).hom
      (deformationSpecialFibre Y J k').hom (Spec.map (CommRingCat.ofHom (algebraMap k' K))) := by
  refine IsPullback.of_right ?_ (deformationSpecialBaseFieldMap_hom k' K h hh hJ)
    (isPullback_deformationSpecialFibre Y J k')
  rw [deformationSpecialBaseFieldMap_toTotal, ← traitClosedPoint_traitMap]
  exact (isPullback_deformationSpecialFibre Y₀ J₀ K).paste_horiz hT

/-- The morphism of nearby cycles models `deformationModel Y₀ J₀ K ⟶ deformationModel Y J k'`
along a change of base field, over `h : Y₀ ⟶ Y` and the morphism of special fibres. -/
noncomputable def deformationModelBaseFieldHom :
    (deformationModel Y₀ J₀ K).Hom (deformationModel Y J k') h
      (deformationSpecialBaseFieldMap k' K h hh hJ) where
  total := deformationTotalBaseFieldMap k' K h hh hJ
  generic := deformationGenericBaseFieldMap k' K h hh hJ
  comm_j := deformationGenericBaseFieldMap_toTotal k' K h hh hJ
  comm_i := deformationSpecialBaseFieldMap_toTotal k' K h hh hJ
  comm_ε := by
    rw [deformationModel_ε, deformationModel_ε, deformationGenericBaseFieldMap_toTotal_assoc,
      deformationTotalBaseFieldMap_toBase, Category.assoc]

@[simp]
lemma deformationModelBaseFieldHom_total :
    (deformationModelBaseFieldHom k' K h hh hJ).total = deformationTotalBaseFieldMap k' K h hh hJ :=
  rfl

@[simp]
lemma deformationModelBaseFieldHom_generic :
    (deformationModelBaseFieldHom k' K h hh hJ).generic =
      deformationGenericBaseFieldMap k' K h hh hJ :=
  rfl

/-! ### The zero sections -/

omit [Algebra k K] [IsScalarTower k K₀ K] [IsScalarTower k k' K] in
/-- The zero ideal of a scheme `Z₀` contains the pullback of an ideal `J'` along `f : Z₀ ⟶ Y'` as
soon as `J' ⊆ ker f`. -/
lemma siteIdeal_map_appLE_le_bot_of_le_ker {Z₀ Y' : Scheme.{u}} {J' : Y'.IdealSheafData}
    (f : Z₀ ⟶ Y') (hf : J' ≤ f.ker) ⦃U' : Z₀.AffineZariskiSite⦄ ⦃U : Y'.AffineZariskiSite⦄
    (hU : U'.1 ≤ f ⁻¹ᵁ U.1) :
    (J'.siteIdeal U).map (f.appLE U.1 U'.1 hU).hom ≤
      (⊥ : Z₀.IdealSheafData).siteIdeal U' :=
  IdealSheafData.siteIdeal_map_appLE_le_of_le_map (by rwa [IdealSheafData.map_bot]) hU

variable (πZ : (centre Y₀ J₀).left ⟶ (centre Y J).left)
  (hπ : πZ ≫ J.subschemeι = J₀.subschemeι ≫ h)

include hπ hh in
/-- The restriction `π_Z : Z₀ ⟶ Z` of `h` to the centres lies over `Spec K₀ ⟶ Spec k`. -/
lemma centre_hom_of_subschemeι :
    πZ ≫ (centre Y J).hom =
      (centre Y₀ J₀).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k K₀)) :=
  ((reassoc_of% hπ) Y.hom).trans ((J₀.subschemeι ≫= hh).trans (Category.assoc _ _ _).symm)

omit [Algebra k K₀] [Algebra k K] [IsScalarTower k K₀ K] [IsScalarTower k k' K] in
include hπ in
/-- The ideal `J` is contained in the kernel of `Z₀ ⟶ Y₀ ⟶ Y`. -/
lemma le_ker_subschemeι_comp_of_subschemeι : J ≤ (J₀.subschemeι ≫ h).ker := by
  rw [← hπ]
  exact J.ker_subschemeι.ge.trans (Scheme.Hom.le_ker_comp _ _)

include hπ in
/-- The zero sections are compatible with the morphisms of total spaces along a change of base
field: `Z₀ × S_K ⟶ 𝒳₀ ⟶ 𝒳` equals `Z₀ × S_K ⟶ Z × S_{k'} ⟶ 𝒳`. -/
lemma deformationTotalMap_centreι_baseField :
    deformationTotalMap (centreι Y₀ J₀) (siteIdeal_map_appLE_le_bot Y₀ J₀) K ≫
        deformationTotalBaseFieldMap k' K h hh hJ =
      deformationTotalBaseFieldMap k' K πZ (centre_hom_of_subschemeι h hh πZ hπ)
          (IdealSheafData.siteIdeal_map_appLE_le_of_le_map bot_le) ≫
        deformationTotalMap (centreι Y J) (siteIdeal_map_appLE_le_bot Y J) k' := by
  refine pullback.hom_ext (?_ : _ ≫ deformationTotalToSpace Y J k' =
    _ ≫ deformationTotalToSpace Y J k') (?_ : _ ≫ deformationTotalToTrait Y J k' =
    _ ≫ deformationTotalToTrait Y J k')
  · rw [Category.assoc, deformationTotalBaseFieldMap_toSpace, deformationTotalMap_toSpace_assoc,
      Category.assoc, deformationTotalMap_toSpace, deformationTotalBaseFieldMap_toSpace_assoc]
    congr 1
    exact (IdealSheafData.deformationSpaceMap_comp (centreι Y₀ J₀).left h _ _
      (siteIdeal_map_appLE_le_bot_of_le_ker _
        (le_ker_subschemeι_comp_of_subschemeι h πZ hπ))).trans
      ((IdealSheafData.deformationSpaceMap_eq_of_eq hπ.symm _ _).trans
        (IdealSheafData.deformationSpaceMap_comp πZ (centreι Y J).left _ _
          (siteIdeal_map_appLE_le_bot_of_le_ker _ (hπ ▸
            le_ker_subschemeι_comp_of_subschemeι h πZ hπ))).symm)
  · rw [Category.assoc, deformationTotalBaseFieldMap_toTrait, deformationTotalMap_toTrait_assoc,
      Category.assoc, deformationTotalMap_toTrait, deformationTotalBaseFieldMap_toTrait]

include hπ in
/-- **The zero sections along a change of base field**: the zero section
`e₀ : N_⊥ Z₀ ⟶ 𝒳₀,s` followed by the map of special fibres `𝒳₀,s ⟶ 𝒳_s` equals the map
`σ : N_⊥ Z₀ ⟶ N_⊥ Z` of special fibres of the constant families followed by the zero section
`e : N_⊥ Z ⟶ 𝒳_s`. -/
lemma zeroSection_deformationSpecialBaseFieldMap :
    (zeroSectionSpecialFibreMap Y₀ J₀ K).left ≫ deformationSpecialBaseFieldMap k' K h hh hJ =
      deformationSpecialBaseFieldMap k' K πZ (centre_hom_of_subschemeι h hh πZ hπ)
          (IdealSheafData.siteIdeal_map_appLE_le_of_le_map bot_le) ≫
        (zeroSectionSpecialFibreMap Y J k').left := by
  refine pullback.hom_ext (?_ : _ ≫ deformationSpecialToTotal Y J k' =
    _ ≫ deformationSpecialToTotal Y J k') (?_ : _ ≫ (deformationSpecialFibre Y J k').hom =
    _ ≫ (deformationSpecialFibre Y J k').hom)
  · rw [Category.assoc, deformationSpecialBaseFieldMap_toTotal, zeroSectionSpecialFibreMap,
      deformationSpecialFibreMap_toTotal_assoc, Category.assoc, zeroSectionSpecialFibreMap,
      deformationSpecialFibreMap_toTotal, deformationSpecialBaseFieldMap_toTotal_assoc,
      deformationTotalMap_centreι_baseField k' K h hh hJ πZ hπ]
  · rw [Category.assoc, deformationSpecialBaseFieldMap_hom, Over.w_assoc, Category.assoc,
      Over.w, deformationSpecialBaseFieldMap_hom]

end AlgebraicGeometry.ProEtale.CondensedRing
