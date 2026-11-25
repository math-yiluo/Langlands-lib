/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpaceEmbedding
public import WeilConjectures.TraceFormula.Specialization.DefectCentreMap

/-!
# Special fibres of deformations along open immersions and constant families

Geometric facts used to show that the vanishing of the defect of the specialization is local
(`WeilConjectures.TraceFormula.Specialization.DefectLocal`):

* along an open immersion `h : X' ⟶ X`, the total spaces and the special fibres over the trait of
  the deformation of `h^* I` are base changes of those of `I`
  (`ProEtale.CondensedRing.isPullback_deformationSpecialFibreMap_toBase`); in particular the map of
  special fibres is an open immersion
  (`ProEtale.CondensedRing.isOpenImmersion_deformationSpecialFibreMap_of_isOpenImmersion`);
* the special fibre of a constant family is a base change
  (`ProEtale.CondensedRing.isPullback_deformationSpecialFibreMap_bot`).
-/

@[expose] public section

universe u

open CategoryTheory Limits ZeroObject

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Base change of the total space and of the special fibre -/

section Map

variable {k : Type u} [Field k] {X Y : Over (Spec (.of k))} (f : X ⟶ Y)
  {I : Y.left.IdealSheafData} {J : X.left.IdealSheafData}
  (hJ : ∀ ⦃U' : X.left.AffineZariskiSite⦄ ⦃U : Y.left.AffineZariskiSite⦄
    (hU : U'.1 ≤ f.left ⁻¹ᵁ U.1), (I.siteIdeal U).map (f.left.appLE U.1 U'.1 hU).hom ≤
      J.siteIdeal U')
  (k' : Type u) [Field k'] [Algebra k k']

/-- Along an open immersion `f : X ⟶ Y` and for `J = f^* I`, the special fibre `𝒳_s` of the
deformation of `J` is the base change `X ×_Y 𝒴_s` of the special fibre of the deformation of
`I`:
```
𝒳_s ⟶ 𝒴_s
 │      │
 X  ⟶   Y
```
-/
lemma isPullback_deformationSpecialFibreMap_toBase [IsOpenImmersion f.left]
    (hJI : J = I.comap f.left) :
    IsPullback (deformationSpecialFibreMap f hJ k').left
      (deformationSpecialToTotal X J k' ≫ deformationTotalToBase X J k')
      (deformationSpecialToTotal Y I k' ≫ deformationTotalToBase Y I k') f.left :=
  (isPullback_deformationSpecialFibreMap_toTotal f hJ k').paste_vert
    ((isPullback_deformationTotalMap_toSpace f hJ k').paste_vert
      (IdealSheafData.isPullback_deformationSpaceMap_of_isOpenImmersion f.left I J hJ hJI))

/-- Along an open immersion `f : X ⟶ Y` and for `J = f^* I`, the map of special fibres
`𝒳_s ⟶ 𝒴_s` is an open immersion. -/
lemma isOpenImmersion_deformationSpecialFibreMap_of_isOpenImmersion [IsOpenImmersion f.left]
    (hJI : J = I.comap f.left) : IsOpenImmersion (deformationSpecialFibreMap f hJ k').left :=
  (isPullback_deformationSpecialFibreMap_toBase f hJ k' hJI).isOpenImmersion_fst

/-- Along an open immersion `f : X ⟶ Y` and for `J = f^* I`, the image of the map of special
fibres `𝒳_s ⟶ 𝒴_s` is the inverse image of the image of `f` under `𝒴_s ⟶ Y`. -/
lemma range_deformationSpecialFibreMap_of_isOpenImmersion [IsOpenImmersion f.left]
    (hJI : J = I.comap f.left) :
    Set.range (deformationSpecialFibreMap f hJ k').left =
      (deformationSpecialToTotal Y I k' ≫ deformationTotalToBase Y I k') ⁻¹'
        Set.range f.left :=
  Scheme.range_snd_of_isPullback (isPullback_deformationSpecialFibreMap_toBase f hJ k' hJI).flip

end Map

/-! ### The restriction to the centre -/

section Centre

variable {k : Type u} [Field k] {X X' : Over (Spec (.of k))} (f : X' ⟶ X)
  (I : X.left.IdealSheafData) (k' : Type u) [Field k'] [Algebra k k']

instance [IsOpenImmersion f.left] : IsOpenImmersion (centreMap f I).left :=
  (isPullback_centreMap f I).isOpenImmersion_fst

/-- The image of the restriction `f_Z : V(f^* I) ⟶ V(I)` is the inverse image of the image
of `f`. -/
lemma range_centreMap :
    Set.range (centreMap f I).left = I.subschemeι ⁻¹' Set.range f.left :=
  Scheme.range_snd_of_isPullback (isPullback_centreMap f I).flip

instance [IsClosedImmersion f.left] : IsClosedImmersion (centreMap f I).left :=
  MorphismProperty.of_isPullback (isPullback_centreMap f I).flip ‹_›

/-- For a closed immersion `f`, the map `N_⊥ Z' ⟶ N_⊥ Z` of special fibres of the constant
families is a closed immersion. -/
lemma isClosedImmersion_centreSpecialFibreMap [IsClosedImmersion f.left] :
    IsClosedImmersion (centreSpecialFibreMap f I k').left := by
  have := IdealSheafData.isClosedImmersion_deformationSpaceMap_bot (centreMap f I).left
    (siteIdeal_map_appLE_le_bot_centreMap f I)
  have : IsClosedImmersion
      (deformationTotalMap (centreMap f I) (siteIdeal_map_appLE_le_bot_centreMap f I) k') :=
    MorphismProperty.of_isPullback (isPullback_deformationTotalMap_toSpace _ _ k').flip this
  exact MorphismProperty.of_isPullback
    (isPullback_deformationSpecialFibreMap_toTotal _ _ k').flip this

instance [IsOpenImmersion f.left] : IsOpenImmersion (centreSpecialFibreMap f I k').left :=
  isOpenImmersion_deformationSpecialFibreMap_of_isOpenImmersion _ _ k'
    (IdealSheafData.comap_bot _).symm

instance [QuasiCompact X'.hom] [IsSeparated X.hom] :
    QuasiCompact (centreSpecialFibreMap f I k').left := by
  have : QuasiCompact ((centreSpecialFibreMap f I k').left ≫
      (deformationSpecialFibre (centre X I) ⊥ k').hom) := by
    rw [Over.w (centreSpecialFibreMap f I k')]
    infer_instance
  exact QuasiCompact.of_comp _ (deformationSpecialFibre (centre X I) ⊥ k').hom

/-- For an open immersion `f`, the image of the map `N_⊥ Z' ⟶ N_⊥ Z` of special fibres of the
constant families is the inverse image of the image of `f` under `N_⊥ Z ⟶ Z ⟶ X`. -/
lemma range_centreSpecialFibreMap [IsOpenImmersion f.left] :
    Set.range (centreSpecialFibreMap f I k').left =
      (deformationSpecialToTotal (centre X I) ⊥ k' ≫
        deformationTotalToBase (centre X I) ⊥ k' ≫ I.subschemeι) ⁻¹' Set.range f.left := by
  rw [centreSpecialFibreMap, range_deformationSpecialFibreMap_of_isOpenImmersion _ _ k'
    (IdealSheafData.comap_bot _).symm, range_centreMap]
  rfl

/-- The maps `N_⊥ (V(g_a^* I)) ⟶ N_⊥ V(I)` of special fibres of the constant families, for
open immersions `g_a` covering `X`, are jointly surjective. -/
lemma exists_mem_range_centreSpecialFibreMap {ι : Type*} {V : ι → Over (Spec (.of k))}
    (g : ∀ a, V a ⟶ X) [∀ a, IsOpenImmersion (g a).left]
    (hg : ⋃ a, Set.range (g a).left.base = Set.univ)
    (p : (deformationSpecialFibre (centre X I) ⊥ k').left) :
    ∃ a, p ∈ Set.range (centreSpecialFibreMap (g a) I k').left.base := by
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (hg.symm ▸ Set.mem_univ
    ((deformationSpecialToTotal (centre X I) ⊥ k' ≫
      deformationTotalToBase (centre X I) ⊥ k' ≫ I.subschemeι) p))
  refine ⟨a, ?_⟩
  have := range_centreSpecialFibreMap (g a) I k'
  exact this.symm ▸ ha

end Centre

/-! ### The special fibre of a constant family is a base change -/

section ConstantFamily

variable {k : Type u} [Field k] (k' : Type u) [Field k'] [Algebra k k']

/-- The projection `N_⊥ Z ⟶ Z` from the special fibre `N_⊥ Z ≅ Z ⊗ k'` of the constant family of
a `k`-scheme `Z`. -/
noncomputable abbrev constantSpecialFibreProj (Z : Over (Spec (.of k))) :
    (deformationSpecialFibre Z ⊥ k').left ⟶ Z.left :=
  deformationSpecialToTotal Z ⊥ k' ≫ deformationTotalToBase Z ⊥ k'

variable {A B : Over (Spec (.of k))} (g : A ⟶ B)
  (hg : ∀ ⦃U' : A.left.AffineZariskiSite⦄ ⦃U : B.left.AffineZariskiSite⦄
    (hU : U'.1 ≤ g.left ⁻¹ᵁ U.1), ((⊥ : B.left.IdealSheafData).siteIdeal U).map
      (g.left.appLE U.1 U'.1 hU).hom ≤ (⊥ : A.left.IdealSheafData).siteIdeal U')

/-- The special fibre of the constant family is a base change: for `g : A ⟶ B`, the square
```
N_⊥ A ⟶ N_⊥ B
  │        │
  A   ⟶    B
```
is a pullback, that is, `A ⊗ k' = A ×_B (B ⊗ k')`. -/
lemma isPullback_deformationSpecialFibreMap_bot :
    IsPullback (deformationSpecialFibreMap g hg k').left (constantSpecialFibreProj k' A)
      (constantSpecialFibreProj k' B) g.left :=
  (isPullback_deformationSpecialFibreMap_toTotal g hg k').paste_vert
    ((isPullback_deformationTotalMap_toSpace g hg k').paste_vert
      (IdealSheafData.isPullback_deformationSpaceMap_bot g.left hg))

variable {X X' : Over (Spec (.of k))} (f : X' ⟶ X) (I : X.left.IdealSheafData)

/-- The map `N_⊥ Z' ⟶ N_⊥ Z` of special fibres of the constant families of the centres is the base
change of the restriction `f_Z : Z' ⟶ Z`. -/
lemma isPullback_centreSpecialFibreMap :
    IsPullback (centreSpecialFibreMap f I k').left
      (constantSpecialFibreProj k' (centre X' (I.comap f.left)))
      (constantSpecialFibreProj k' (centre X I)) (centreMap f I).left :=
  isPullback_deformationSpecialFibreMap_bot k' _ _

@[reassoc]
lemma centreSpecialFibreMap_constantSpecialFibreProj :
    (centreSpecialFibreMap f I k').left ≫ constantSpecialFibreProj k' (centre X I) =
      constantSpecialFibreProj k' (centre X' (I.comap f.left)) ≫ (centreMap f I).left :=
  (isPullback_centreSpecialFibreMap k' f I).w

/-- The image of `N_⊥ Z' ⟶ N_⊥ Z` is the inverse image of the image of `f_Z : Z' ⟶ Z`. -/
lemma range_centreSpecialFibreMap_eq_preimage :
    Set.range (centreSpecialFibreMap f I k').left =
      constantSpecialFibreProj k' (centre X I) ⁻¹' Set.range (centreMap f I).left :=
  Scheme.range_snd_of_isPullback (isPullback_centreSpecialFibreMap k' f I).flip

/-- For `f₁ : X'' ⟶ X'` and `f₂ : X' ⟶ X` with `f₁ ≫ f₂` finite, the composite of the maps of
special fibres of the constant families of the centres `N_⊥ Z'' ⟶ N_⊥ Z' ⟶ N_⊥ Z` is finite. -/
lemma isFinite_centreSpecialFibreMap_comp {X'' : Over (Spec (.of k))} (f₁ : X'' ⟶ X')
    [IsFinite (f₁ ≫ f).left] :
    IsFinite ((centreSpecialFibreMap f₁ (I.comap f.left) k').left ≫
      (centreSpecialFibreMap f I k').left) := by
  have hc : (centreMap f₁ (I.comap f.left) ≫ centreMap f I) ≫ centreι X I =
      centreι X'' ((I.comap f.left).comap f₁.left) ≫ f₁ ≫ f := by
    simp [centreMap_centreι, centreMap_centreι_assoc]
  have : IsFinite (f₁.left ≫ f.left) := ‹IsFinite (f₁ ≫ f).left›
  have : IsFinite (((centreMap f₁ (I.comap f.left)).left ≫ (centreMap f I).left) ≫
      (centreι X I).left) := by
    have h := congrArg (fun φ ↦ φ.left) hc
    simp only [Over.comp_left] at h
    rw [h]
    infer_instance
  have : IsFinite ((centreMap f₁ (I.comap f.left)).left ≫ (centreMap f I).left) :=
    IsFinite.of_comp _ (centreι X I).left
  exact MorphismProperty.of_isPullback
    ((isPullback_centreSpecialFibreMap k' f₁ (I.comap f.left)).paste_horiz
      (isPullback_centreSpecialFibreMap k' f I)).flip this

end ConstantFamily

section Complement

variable {k : Type u} [Field k] {X : Over (Spec (.of k))} (I : X.left.IdealSheafData)

/-- The complement `X ∖ Z` of the centre and the centre are complementary. -/
lemma isCompl_range_overRestrictι_centreι :
    IsCompl (Set.range (overRestrictι X I.support.compl).left.base)
      (Set.range (centreι X I).left.base) := by
  have h : Set.range (centreι X I).left.base = I.support := IdealSheafData.range_subschemeι I
  rw [range_overRestrictι, h]
  exact isCompl_compl.symm

end Complement

end AlgebraicGeometry.ProEtale.CondensedRing
