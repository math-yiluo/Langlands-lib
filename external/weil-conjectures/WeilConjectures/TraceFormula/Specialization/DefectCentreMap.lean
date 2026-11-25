/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.Defect
public import WeilConjectures.TraceFormula.Specialization.DeformationModelGeneric
public import WeilConjectures.TraceFormula.Specialization.DeformationSpecialFibreComp
public import WeilConjectures.TraceFormula.Specialization.OpenExchange

/-!

# The deformation to the normal cone along a morphism and the zero section

Let `f : X' ⟶ X` be a morphism of `k`-schemes, `Z = V(I) ⊆ X` a closed subscheme and
`Z' = f⁻¹ Z = V(f^* I)` its schematic inverse image, with the restriction `f_Z : Z' ⟶ Z`
(`ProEtale.CondensedRing.centreMap`). The deformation of `f_Z` maps the special fibre
`N_⊥ Z' ≅ Z' ⊗ k'` of the constant family of `Z'` to that of `Z`
(`ProEtale.CondensedRing.centreSpecialFibreMap`).

This file proves the geometric inputs of the proper and smooth exchanges for the defect of the
specialization (blueprint `lemma-base-change-cone-x-z`), following blueprint
`lemma-functoriality-deformation`:

* the squares of geometric generic fibres of the morphisms of deformation models are cartesian
  (`ProEtale.CondensedRing.isPullback_deformationModel_ε_deformationGenericMap`);
* for `f` proper (resp. smooth), the morphism of total spaces `𝒟_{Z'} X' ⟶ 𝒟_Z X` is proper
  (resp. smooth) (`ProEtale.CondensedRing.isProper_deformationTotalMap`,
  `ProEtale.CondensedRing.smooth_deformationTotalMap`);
* the special fibre of the deformation of `f` pulls the zero section of `N_Z X` back to the zero
  section of `N_{Z'} X'`: the square of zero sections is cartesian
  (`ProEtale.CondensedRing.isPullback_zeroSectionSpecialFibreMap`);
* the morphisms of models `𝒟_{Z'} X' ⟶ 𝒟_Z X` and `Z' × S ⟶ Z × S` are compatible with the zero
  sections `ẽ` (`ProEtale.CondensedRing.zeroSectionDeformationModelHom_total_comp`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k] {X X' : Over (Spec (.of k))} (f : X' ⟶ X)
  (I : X.left.IdealSheafData) (k' : Type u) [Field k'] [Algebra k k']

/-! ### The restriction to the centre -/

/-- The restriction `f_Z : Z' = V(f^* I) ⟶ Z = V(I)` of `f : X' ⟶ X` to the inverse image of the
centre. -/
noncomputable def centreMap : centre X' (I.comap f.left) ⟶ centre X I :=
  Over.homMk (IdealSheafData.subschemeMap _ _ f.left (I.le_map_comap f.left)) (by
    change _ ≫ I.subschemeι ≫ X.hom = (I.comap f.left).subschemeι ≫ X'.hom
    rw [IdealSheafData.subschemeMap_subschemeι_assoc, Over.w f])

@[reassoc (attr := simp)]
lemma centreMap_centreι : centreMap f I ≫ centreι X I = centreι X' (I.comap f.left) ≫ f :=
  Over.OverMorphism.ext (IdealSheafData.subschemeMap_subschemeι _ _ _ (I.le_map_comap f.left))

/-- The zero ideal of `Z'` contains the pullback of the zero ideal of `Z`. -/
lemma siteIdeal_map_appLE_le_bot_centreMap
    ⦃U' : (centre X' (I.comap f.left)).left.AffineZariskiSite⦄
    ⦃U : (centre X I).left.AffineZariskiSite⦄ (hU : U'.1 ≤ (centreMap f I).left ⁻¹ᵁ U.1) :
    ((⊥ : (centre X I).left.IdealSheafData).siteIdeal U).map
        ((centreMap f I).left.appLE U.1 U'.1 hU).hom ≤
      (⊥ : (centre X' (I.comap f.left)).left.IdealSheafData).siteIdeal U' :=
  IdealSheafData.siteIdeal_map_appLE_le_of_le_map bot_le hU

/-- The map `N_⊥ Z' ⟶ N_⊥ Z` of special fibres of the constant families, the deformation of
`f_Z`; under `N_⊥ Z ≅ Z ⊗ k'` it is `f_Z ⊗ k'`. -/
noncomputable abbrev centreSpecialFibreMap :
    deformationSpecialFibre (centre X' (I.comap f.left)) ⊥ k' ⟶
      deformationSpecialFibre (centre X I) ⊥ k' :=
  deformationSpecialFibreMap (centreMap f I) (siteIdeal_map_appLE_le_bot_centreMap f I) k'

/-- The morphism of constant families `Z' × S ⟶ Z × S` induced by `f_Z : Z' ⟶ Z`. -/
noncomputable abbrev centreDeformationModelHom :
    (deformationModel (centre X' (I.comap f.left)) ⊥ k').Hom
      (deformationModel (centre X I) ⊥ k') (centreMap f I).left
      (centreSpecialFibreMap f I k').left :=
  deformationModelHom (centreMap f I) (siteIdeal_map_appLE_le_bot_centreMap f I) k'

/-! ### The deformation along `f` -/

/-- The ideal `f^* I` contains the pullback of `I`, chart by chart. -/
lemma siteIdeal_map_appLE_le_comap ⦃U' : X'.left.AffineZariskiSite⦄
    ⦃U : X.left.AffineZariskiSite⦄ (hU : U'.1 ≤ f.left ⁻¹ᵁ U.1) :
    (I.siteIdeal U).map (f.left.appLE U.1 U'.1 hU).hom ≤ (I.comap f.left).siteIdeal U' :=
  IdealSheafData.siteIdeal_map_appLE_le_of_le_map (I.le_map_comap f.left) hU

/-- The map `N_{Z'} X' ⟶ N_Z X` of special fibres of the deformations to the normal cones induced
by `f`, for `Z' = f⁻¹ Z`. -/
noncomputable abbrev comapSpecialFibreMap :
    deformationSpecialFibre X' (I.comap f.left) k' ⟶ deformationSpecialFibre X I k' :=
  deformationSpecialFibreMap f (siteIdeal_map_appLE_le_comap f I) k'

/-- The morphism of deformation models `𝒟_{Z'} X' ⟶ 𝒟_Z X` induced by `f`, for `Z' = f⁻¹ Z`
(blueprint `lemma-functoriality-deformation` (1)). -/
noncomputable abbrev comapDeformationModelHom :
    (deformationModel X' (I.comap f.left) k').Hom (deformationModel X I k') f.left
      (comapSpecialFibreMap f I k').left :=
  deformationModelHom f (siteIdeal_map_appLE_le_comap f I) k'

/-! ### Geometric generic fibres -/

section Generic

variable {Y : Over (Spec (.of k))} (g : X ⟶ Y) {I : Y.left.IdealSheafData}
  {J : X.left.IdealSheafData}
  (hJ : ∀ ⦃U' : X.left.AffineZariskiSite⦄ ⦃U : Y.left.AffineZariskiSite⦄
    (hU : U'.1 ≤ g.left ⁻¹ᵁ U.1), (I.siteIdeal U).map (g.left.appLE U.1 U'.1 hU).hom ≤
      J.siteIdeal U')

/-- The morphism of geometric generic fibres lies over `Spec Ω`. -/
@[reassoc (attr := simp)]
lemma deformationGenericMap_toPoint :
    deformationGenericMap g hJ k' ≫ deformationGenericToPoint Y I k' =
      deformationGenericToPoint X J k' :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The square of identifications `ε` of the geometric generic fibres of a morphism of deformation
models is cartesian: `𝒳_Ω = X ×_Y 𝒴_Ω`, since both are base changes to `Ω`. -/
lemma isPullback_deformationModel_ε_deformationGenericMap :
    IsPullback (deformationModel X J k').ε (deformationGenericMap g hJ k') g.left
      (deformationModel Y I k').ε := by
  refine (IsPullback.of_right ?_ (deformationModelHom g hJ k').comm_ε
    (isPullback_deformationModel_ε k' (X := Y) I).flip).flip
  rw [deformationModelHom_generic, deformationGenericMap_toPoint, Over.w g]
  exact (isPullback_deformationModel_ε k' (X := X) J).flip

/-- The morphisms of geometric generic fibres of deformation models compose. -/
lemma deformationGenericMap_comp {W : Over (Spec (.of k))} (h : W ⟶ X)
    {K : W.left.IdealSheafData}
    (hK : ∀ ⦃U' : W.left.AffineZariskiSite⦄ ⦃U : X.left.AffineZariskiSite⦄
      (hU : U'.1 ≤ h.left ⁻¹ᵁ U.1), (J.siteIdeal U).map (h.left.appLE U.1 U'.1 hU).hom ≤
        K.siteIdeal U')
    (hKI : ∀ ⦃U' : W.left.AffineZariskiSite⦄ ⦃U : Y.left.AffineZariskiSite⦄
      (hU : U'.1 ≤ (h ≫ g).left ⁻¹ᵁ U.1),
      (I.siteIdeal U).map ((h ≫ g).left.appLE U.1 U'.1 hU).hom ≤ K.siteIdeal U') :
    deformationGenericMap h hK k' ≫ deformationGenericMap g hJ k' =
      deformationGenericMap (h ≫ g) hKI k' := by
  refine pullback.hom_ext (?_ : _ ≫ deformationGenericToTotal Y I k' =
    _ ≫ deformationGenericToTotal Y I k') (?_ : _ ≫ deformationGenericToPoint Y I k' =
    _ ≫ deformationGenericToPoint Y I k')
  · rw [Category.assoc, deformationGenericMap_toTotal, deformationGenericMap_toTotal_assoc,
      deformationTotalMap_comp k' h g hK hJ hKI, deformationGenericMap_toTotal]
  · rw [Category.assoc, deformationGenericMap_toPoint, deformationGenericMap_toPoint,
      deformationGenericMap_toPoint]

/-- For `f` proper and `J = f⁻¹ I`, the morphism of total spaces `𝒳 ⟶ 𝒴` of the deformation
models is proper (blueprint `lemma-functoriality-deformation` (3)). -/
lemma isProper_deformationTotalMap [IsProper g.left] (hJI : J = I.comap g.left) :
    IsProper (deformationTotalMap g hJ k') := by
  have := IdealSheafData.isProper_deformationSpaceMap g.left I J hJ hJI
  exact MorphismProperty.of_isPullback (isPullback_deformationTotalMap g hJ k').flip
    inferInstance

/-- For `f` smooth and `J = f⁻¹ I`, the morphism of total spaces `𝒳 ⟶ 𝒴` of the deformation
models is smooth: it is the base change of `f` (blueprint `lemma-functoriality-deformation` (3)). -/
lemma smooth_deformationTotalMap [Smooth g.left] (hJI : J = I.comap g.left) :
    Smooth (deformationTotalMap g hJ k') := by
  have : Smooth (IdealSheafData.deformationSpaceMap g.left I J hJ) :=
    MorphismProperty.of_isPullback
      (IdealSheafData.isPullback_deformationSpaceMap_of_flat g.left I J hJ hJI).flip
      inferInstance
  exact MorphismProperty.of_isPullback (isPullback_deformationTotalMap g hJ k').flip
    inferInstance

end Generic

/-- The restriction `f_Z : V(f^* I) ⟶ V(I)` is the base change of `f` along `V(I) ⟶ X`. -/
lemma isPullback_centreMap :
    IsPullback (centreMap f I).left (I.comap f.left).subschemeι I.subschemeι f.left := by
  have := (I.isPullback_comap f.left).flip
  rwa [IdealSheafData.comapIso_hom_snd] at this

instance [IsProper f.left] : IsProper (centreMap f I).left :=
  MorphismProperty.of_isPullback (isPullback_centreMap f I).flip ‹_›

instance [Smooth f.left] : Smooth (centreMap f I).left :=
  MorphismProperty.of_isPullback (isPullback_centreMap f I).flip ‹_›

/-! ### The zero sections -/

/-- The morphism of deformation spaces depends only on the underlying morphism. -/
lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.deformationSpaceMap_eq_of_eq
    {Y Y' : Scheme.{u}} {h h' : Y' ⟶ Y} (e : h = h') {I : Y.IdealSheafData}
    {J : Y'.IdealSheafData}
    (hJ : ∀ ⦃U' : Y'.AffineZariskiSite⦄ ⦃U : Y.AffineZariskiSite⦄ (hU : U'.1 ≤ h ⁻¹ᵁ U.1),
      (I.siteIdeal U).map (h.appLE U.1 U'.1 hU).hom ≤ J.siteIdeal U')
    (hJ' : ∀ ⦃U' : Y'.AffineZariskiSite⦄ ⦃U : Y.AffineZariskiSite⦄ (hU : U'.1 ≤ h' ⁻¹ᵁ U.1),
      (I.siteIdeal U).map (h'.appLE U.1 U'.1 hU).hom ≤ J.siteIdeal U') :
    IdealSheafData.deformationSpaceMap h I J hJ =
      IdealSheafData.deformationSpaceMap h' I J hJ' := by
  subst e
  rfl

/-- The morphism of total spaces of deformation models depends only on the underlying
morphism. -/
lemma deformationTotalMap_eq_of_eq {Y Y' : Over (Spec (.of k))} {h h' : Y' ⟶ Y} (e : h = h')
    {I : Y.left.IdealSheafData} {J : Y'.left.IdealSheafData}
    (hJ : ∀ ⦃U' : Y'.left.AffineZariskiSite⦄ ⦃U : Y.left.AffineZariskiSite⦄
      (hU : U'.1 ≤ h.left ⁻¹ᵁ U.1), (I.siteIdeal U).map (h.left.appLE U.1 U'.1 hU).hom ≤
        J.siteIdeal U')
    (hJ' : ∀ ⦃U' : Y'.left.AffineZariskiSite⦄ ⦃U : Y.left.AffineZariskiSite⦄
      (hU : U'.1 ≤ h'.left ⁻¹ᵁ U.1), (I.siteIdeal U).map (h'.left.appLE U.1 U'.1 hU).hom ≤
        J.siteIdeal U') :
    deformationTotalMap h hJ k' = deformationTotalMap h' hJ' k' := by
  subst e
  rfl

/-- The morphism of geometric generic fibres of deformation models depends only on the underlying
morphism. -/
lemma deformationGenericMap_eq_of_eq {Y Y' : Over (Spec (.of k))} {h h' : Y' ⟶ Y} (e : h = h')
    {I : Y.left.IdealSheafData} {J : Y'.left.IdealSheafData}
    (hJ : ∀ ⦃U' : Y'.left.AffineZariskiSite⦄ ⦃U : Y.left.AffineZariskiSite⦄
      (hU : U'.1 ≤ h.left ⁻¹ᵁ U.1), (I.siteIdeal U).map (h.left.appLE U.1 U'.1 hU).hom ≤
        J.siteIdeal U')
    (hJ' : ∀ ⦃U' : Y'.left.AffineZariskiSite⦄ ⦃U : Y.left.AffineZariskiSite⦄
      (hU : U'.1 ≤ h'.left ⁻¹ᵁ U.1), (I.siteIdeal U).map (h'.left.appLE U.1 U'.1 hU).hom ≤
        J.siteIdeal U') :
    deformationGenericMap h hJ k' = deformationGenericMap h' hJ' k' := by
  subst e
  rfl

/-- The zero ideal of `Z'` contains the pullback of `I` along `Z' ⟶ Z ⟶ X`. -/
lemma siteIdeal_map_appLE_le_bot_centreMap_comp
    ⦃U' : (centre X' (I.comap f.left)).left.AffineZariskiSite⦄
    ⦃U : X.left.AffineZariskiSite⦄ (hU : U'.1 ≤ (centreMap f I ≫ centreι X I).left ⁻¹ᵁ U.1) :
    (I.siteIdeal U).map ((centreMap f I ≫ centreι X I).left.appLE U.1 U'.1 hU).hom ≤
      (⊥ : (centre X' (I.comap f.left)).left.IdealSheafData).siteIdeal U' :=
  IdealSheafData.siteIdeal_map_appLE_le_of_le_map (by
    rw [IdealSheafData.map_bot, Over.comp_left, centreι_left]
    exact I.ker_subschemeι.ge.trans (Scheme.Hom.le_ker_comp _ _)) hU

/-- The zero ideal of `Z'` contains the pullback of `I` along `Z' ⟶ X' ⟶ X`. -/
lemma siteIdeal_map_appLE_le_bot_centreι_comp
    ⦃U' : (centre X' (I.comap f.left)).left.AffineZariskiSite⦄
    ⦃U : X.left.AffineZariskiSite⦄
    (hU : U'.1 ≤ (centreι X' (I.comap f.left) ≫ f).left ⁻¹ᵁ U.1) :
    (I.siteIdeal U).map ((centreι X' (I.comap f.left) ≫ f).left.appLE U.1 U'.1 hU).hom ≤
      (⊥ : (centre X' (I.comap f.left)).left.IdealSheafData).siteIdeal U' :=
  IdealSheafData.siteIdeal_map_appLE_le_of_le_map (by
    rw [← centreMap_centreι, IdealSheafData.map_bot, Over.comp_left, centreι_left]
    exact I.ker_subschemeι.ge.trans (Scheme.Hom.le_ker_comp _ _)) hU

/-- If `m` is a monomorphism and the square with top edge `t ≫ m` and right edge `r` is a pullback,
then so is the square with top edge `t` and right edge `m ≫ r`. -/
lemma _root_.CategoryTheory.IsPullback.of_comp_mono_top {C : Type*} [Category C]
    {P A B D E : C} {t : P ⟶ A} {l : P ⟶ B} {m : A ⟶ E} {r : E ⟶ D} {b : B ⟶ D} [Mono m]
    (h : IsPullback (t ≫ m) l r b) : IsPullback t l (m ≫ r) b := by
  have hw : t ≫ m ≫ r = l ≫ b := by rw [← Category.assoc, h.w]
  refine IsPullback.of_isLimit' ⟨hw⟩
    (PullbackCone.IsLimit.mk _ (fun s ↦ h.lift (s.fst ≫ m) s.snd (by rw [Category.assoc,
      s.condition])) (fun s ↦ ?_) (fun s ↦ h.lift_snd _ _ _) fun s u h₁ h₂ ↦ h.hom_ext ?_ ?_)
  · rw [← cancel_mono m, Category.assoc, h.lift_fst]
  · rw [h.lift_fst, ← h₁, Category.assoc]
  · rw [h.lift_snd, h₂]

/-- The square of deformation spaces of the zero sections is cartesian:
`D_⊥ Z' = D_⊥ Z ×_{D_I X} D_{f^* I} X'`. -/
lemma isPullback_zeroSection_deformationSpaceMap :
    IsPullback
      (IdealSheafData.deformationSpaceMap (centreι X' (I.comap f.left)).left (I.comap f.left) ⊥
        (siteIdeal_map_appLE_le_bot X' (I.comap f.left)))
      (IdealSheafData.deformationSpaceMap (centreMap f I).left ⊥ ⊥
        (siteIdeal_map_appLE_le_bot_centreMap f I))
      (IdealSheafData.deformationSpaceMap f.left I (I.comap f.left)
        (siteIdeal_map_appLE_le_comap f I))
      (IdealSheafData.deformationSpaceMap (centreι X I).left I ⊥
        (siteIdeal_map_appLE_le_bot X I)) := by
  have hw := (IdealSheafData.deformationSpaceMap_comp _ _
    (siteIdeal_map_appLE_le_bot X' (I.comap f.left)) (siteIdeal_map_appLE_le_comap f I)
    (siteIdeal_map_appLE_le_bot_centreι_comp f I)).trans
    ((IdealSheafData.deformationSpaceMap_eq_of_eq
      (congrArg CommaMorphism.left (centreMap_centreι f I).symm) _ _).trans
      (IdealSheafData.deformationSpaceMap_comp _ _ (siteIdeal_map_appLE_le_bot_centreMap f I)
        (siteIdeal_map_appLE_le_bot X I) (siteIdeal_map_appLE_le_bot_centreMap_comp f I)).symm)
  have := IdealSheafData.isClosedImmersion_deformationSpaceToPullback f.left I (I.comap f.left)
    (siteIdeal_map_appLE_le_comap f I) rfl
  rw [← IdealSheafData.deformationSpaceToPullback_fst f.left I (I.comap f.left)
    (siteIdeal_map_appLE_le_comap f I)]
  refine IsPullback.of_comp_mono_top (IsPullback.of_right ?_ ?_
    (IsPullback.of_hasPullback I.deformationSpaceProj f.left).flip)
  · rw [Category.assoc, IdealSheafData.deformationSpaceToPullback_snd,
      IdealSheafData.deformationSpaceMap_toBase, IdealSheafData.deformationSpaceMap_toBase]
    exact (IdealSheafData.isPullback_deformationSpaceMap_bot _
      (siteIdeal_map_appLE_le_bot_centreMap f I)).flip.paste_horiz
      (isPullback_centreMap f I).flip
  · rw [Category.assoc, IdealSheafData.deformationSpaceToPullback_fst]
    exact hw

/-- The morphisms of total spaces of `Z' × S ⟶ 𝒟_{Z'} X' ⟶ 𝒟_Z X` and `Z' × S ⟶ Z × S ⟶ 𝒟_Z X`
agree. -/
lemma deformationTotalMap_centreι_comp :
    deformationTotalMap (centreι X' (I.comap f.left))
        (siteIdeal_map_appLE_le_bot X' (I.comap f.left)) k' ≫
        deformationTotalMap f (siteIdeal_map_appLE_le_comap f I) k' =
      deformationTotalMap (centreMap f I) (siteIdeal_map_appLE_le_bot_centreMap f I) k' ≫
        deformationTotalMap (centreι X I) (siteIdeal_map_appLE_le_bot X I) k' :=
  (deformationTotalMap_comp k' _ _ _ _ (siteIdeal_map_appLE_le_bot_centreι_comp f I)).trans
    ((deformationTotalMap_eq_of_eq k' (centreMap_centreι f I).symm _ _).trans
      (deformationTotalMap_comp k' _ _ _ _ (siteIdeal_map_appLE_le_bot_centreMap_comp f I)).symm)

/-- The square of total spaces of the zero sections is cartesian. -/
lemma isPullback_zeroSection_deformationTotalMap :
    IsPullback
      (deformationTotalMap (centreι X' (I.comap f.left))
        (siteIdeal_map_appLE_le_bot X' (I.comap f.left)) k')
      (deformationTotalMap (centreMap f I) (siteIdeal_map_appLE_le_bot_centreMap f I) k')
      (deformationTotalMap f (siteIdeal_map_appLE_le_comap f I) k')
      (deformationTotalMap (centreι X I) (siteIdeal_map_appLE_le_bot X I) k') := by
  refine IsPullback.of_right ?_ (deformationTotalMap_centreι_comp f I k')
    (isPullback_deformationTotalMap_toSpace f (siteIdeal_map_appLE_le_comap f I) k').flip
  rw [deformationTotalMap_toSpace, deformationTotalMap_toSpace]
  exact (isPullback_deformationTotalMap_toSpace (centreMap f I)
    (siteIdeal_map_appLE_le_bot_centreMap f I) k').flip.paste_horiz
    (isPullback_zeroSection_deformationSpaceMap f I)

/-- **The zero sections are compatible with the deformation of `f`** (blueprint
`lemma-functoriality-deformation` (2)): the special fibre `N_{Z'} X' ⟶ N_Z X` of the deformation of
`f` pulls the zero section `e : N_⊥ Z ⟶ N_Z X` back to the zero section `e' : N_⊥ Z' ⟶ N_{Z'} X'`,
that is, `f̃_s⁻¹(Z) = Z'` schematically. -/
lemma isPullback_zeroSectionSpecialFibreMap :
    IsPullback (zeroSectionSpecialFibreMap X' (I.comap f.left) k').left
      (centreSpecialFibreMap f I k').left (comapSpecialFibreMap f I k').left
      (zeroSectionSpecialFibreMap X I k').left := by
  have hc : (zeroSectionSpecialFibreMap X' (I.comap f.left) k').left ≫
      (comapSpecialFibreMap f I k').left =
      (centreSpecialFibreMap f I k').left ≫ (zeroSectionSpecialFibreMap X I k').left := by
    rw [← Over.comp_left, ← Over.comp_left, zeroSectionSpecialFibreMap, comapSpecialFibreMap,
      centreSpecialFibreMap, zeroSectionSpecialFibreMap,
      deformationSpecialFibreMap_comp k' _ _ _ _ (siteIdeal_map_appLE_le_bot_centreι_comp f I),
      deformationSpecialFibreMap_comp k' _ _ _ _ (siteIdeal_map_appLE_le_bot_centreMap_comp f I),
      deformationSpecialFibreMap_eq_of_eq k' _ _ (centreMap_centreι f I).symm]
  refine IsPullback.of_right ?_ hc
    (isPullback_deformationSpecialFibreMap_toTotal f (siteIdeal_map_appLE_le_comap f I) k').flip
  rw [zeroSectionSpecialFibreMap, zeroSectionSpecialFibreMap, deformationSpecialFibreMap_toTotal,
    deformationSpecialFibreMap_toTotal]
  exact (isPullback_deformationSpecialFibreMap_toTotal (centreMap f I)
    (siteIdeal_map_appLE_le_bot_centreMap f I) k').flip.paste_horiz
    (isPullback_zeroSection_deformationTotalMap f I k')

/-- The morphisms of total spaces of `Z' × S ⟶ 𝒟_{Z'} X' ⟶ 𝒟_Z X` and `Z' × S ⟶ Z × S ⟶ 𝒟_Z X`
agree. -/
lemma zeroSectionDeformationModelHom_total_comp :
    (zeroSectionDeformationModelHom X' (I.comap f.left) k').total ≫
        (comapDeformationModelHom f I k').total =
      (centreDeformationModelHom f I k').total ≫ (zeroSectionDeformationModelHom X I k').total :=
  deformationTotalMap_centreι_comp f I k'

/-- The morphisms of geometric generic fibres of `Z' × S ⟶ 𝒟_{Z'} X' ⟶ 𝒟_Z X` and
`Z' × S ⟶ Z × S ⟶ 𝒟_Z X` agree. -/
lemma zeroSectionDeformationModelHom_generic_comp :
    (zeroSectionDeformationModelHom X' (I.comap f.left) k').generic ≫
        (comapDeformationModelHom f I k').generic =
      (centreDeformationModelHom f I k').generic ≫
        (zeroSectionDeformationModelHom X I k').generic :=
  (deformationGenericMap_comp k' _ _ _ _ (siteIdeal_map_appLE_le_bot_centreι_comp f I)).trans
    ((deformationGenericMap_eq_of_eq k' (centreMap_centreι f I).symm _ _).trans
      (deformationGenericMap_comp k' _ _ _ _ (siteIdeal_map_appLE_le_bot_centreMap_comp f I)).symm)

/-- For the zero ideal, the morphism of total spaces `Z × S ⟶ 𝒟_⊥ X` of the zero section is an
isomorphism: the centre `V(⊥)` is `X`. -/
instance isIso_zeroSectionDeformationModelHom_bot_total :
    IsIso (zeroSectionDeformationModelHom X ⊥ k').total := by
  have : IsIso (centreι X ⊥).left := by
    rw [centreι_left]
    infer_instance
  have := (IdealSheafData.isPullback_deformationSpaceMap_bot (centreι X ⊥).left
    (siteIdeal_map_appLE_le_bot X ⊥)).isIso_fst_of_isIso
  exact (isPullback_deformationTotalMap (centreι X ⊥) (siteIdeal_map_appLE_le_bot X ⊥)
    k').isIso_fst_of_isIso

/-- For the zero ideal, the morphism of geometric generic fibres of the zero section is an
isomorphism. -/
instance isIso_zeroSectionDeformationModelHom_bot_generic :
    IsIso (zeroSectionDeformationModelHom X ⊥ k').generic :=
  (isPullback_deformationGenericMap (centreι X ⊥) (siteIdeal_map_appLE_le_bot X ⊥)
    k').isIso_fst_of_isIso (isIso_zeroSectionDeformationModelHom_bot_total (X := X) k')

end AlgebraicGeometry.ProEtale.CondensedRing
