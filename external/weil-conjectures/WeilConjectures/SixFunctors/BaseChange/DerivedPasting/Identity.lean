/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Vertical

/-!
# The derived base change map of the identity square

For the identity square on `f` the derived base change map is the identity, modulo the identity
isomorphisms of the derived pullbacks (`AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_id`);
with the horizontal pasting law this is blueprint `lemma-identity-pasting--1`.
The file also records how the composition isomorphisms
`AlgebraicGeometry.Etale.upperStarCompDerivedPlus` behave on identities.

The pasting laws are collected in `WeilConjectures.SixFunctors.BaseChange.DerivedPasting`.
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

open Etale

section Identity

variable {X Y : Scheme.{u}}

omit [HasSmallSiteSheafify A] in
/-- The composition isomorphism `AlgebraicGeometry.Etale.upperStarComp` along two equal
diagonals `d = d'` agree up to the induced identification of the pullbacks. -/
lemma Etale.upperStarComp_congr {T S R : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R) (d d' : T ⟶ R)
    (hd : d = h₁ ≫ h₂) (hd' : d' = h₁ ≫ h₂) (h : d = d') :
    Etale.upperStarComp A h₁ h₂ d hd =
      eqToIso (by rw [h]) ≪≫ Etale.upperStarComp A h₁ h₂ d' hd' := by
  subst h
  simp

/-- The square isomorphism of the identity square on `f` is built from the identity
isomorphisms `(𝟙 _)^* ≅ 𝟭`. -/
lemma Etale.squareUpperStarIso_id (f : X ⟶ Y) (sq : CommSq (𝟙 X) f f (𝟙 Y)) :
    Etale.squareUpperStarIso A sq =
      Functor.isoWhiskerRight (Etale.upperStarId A Y) (f)^*[A] ≪≫ Functor.leftUnitor _ ≪≫
        (Functor.rightUnitor _).symm ≪≫
          Functor.isoWhiskerLeft (f)^*[A] (Etale.upperStarId A X).symm := by
  rw [Etale.squareUpperStarIso, Etale.upperStarComp_congr A f (𝟙 Y) _ f sq.w
      (Category.comp_id f).symm (Category.id_comp f),
    Etale.upperStarComp_congr A (𝟙 X) f _ f rfl (Category.id_comp f).symm (Category.id_comp f),
    Etale.upperStarComp_id_left, Etale.upperStarComp_id_right]
  ext M
  simp

/-- **The underived base change map of the identity square** is the identity, modulo the
identity isomorphisms `(𝟙 _)^* ≅ 𝟭` of the pullbacks. -/
lemma Etale.baseChangeMap_id (f : X ⟶ Y) (sq : CommSq (𝟙 X) f f (𝟙 Y)) :
    Etale.baseChangeMap A sq =
      Functor.whiskerLeft (f)_*[A] (Etale.upperStarId A Y).hom ≫ (Functor.rightUnitor _).hom ≫
        (Functor.leftUnitor _).inv ≫ Functor.whiskerRight (Etale.upperStarId A X).inv (f)_*[A] := by
  ext F : 2
  simp only [Etale.baseChangeMap, Etale.squareUpperStarIso_id, mateEquiv_apply]
  simp only [Functor.comp_obj, Functor.id_obj, NatTrans.comp_app, Functor.rightUnitor_inv_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.leftUnitor_hom_app,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app, Category.id_comp,
    Category.comp_id, Functor.map_comp, Category.assoc]
  have h₁ := (Etale.upperStarLowerStarAdjunction A f).unit.naturality
    ((Etale.upperStarId A Y).hom.app (((f)_*[A]).obj F))
  have h₂ := (Etale.upperStarId A X).inv.naturality
    ((Etale.upperStarLowerStarAdjunction A f).counit.app F)
  simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map] at h₁ h₂
  rw [← reassoc_of% h₁, Functor.comp_map, ← Functor.map_comp, ← h₂,
    Functor.map_comp, Adjunction.right_triangle_components_assoc]

/-- Blueprint `lemma-identity-pasting--1` (identity part): **the derived
exchange morphism of the identity square is the identity**, modulo the identity isomorphisms
`D(𝟙 _)^*⁺ ≅ 𝟭` of the derived pullbacks. The composition part of that blueprint lemma is the
horizontal pasting law `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_paste_horiz`.
(blueprint: `lemma-identity-pasting`,
`lemma-identity-pasting`) -/
lemma Etale.derivedBaseChangeMapPlus_id (f : X ⟶ Y) (sq : CommSq (𝟙 X) f f (𝟙 Y)) :
    Etale.derivedBaseChangeMapPlus A sq =
      Functor.whiskerLeft (f)_*[A].rightDerivedFunctorPlus (Etale.upperStarIdDerivedPlus A Y).hom ≫
        (Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv ≫
        Functor.whiskerRight (Etale.upperStarIdDerivedPlus A X).inv
          (f)_*[A].rightDerivedFunctorPlus := by
  symm
  refine Etale.derivedBaseChangeMapPlus_ext A sq _ fun K => ?_
  rw [Etale.baseChangeMap_id]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app, Category.id_comp,
    NatTrans.mapHomotopyCategoryPlus_comp, NatTrans.mapHomotopyCategoryPlus_rightUnitor_hom_app,
    NatTrans.mapHomotopyCategoryPlus_leftUnitor_inv_app,
    NatTrans.mapHomotopyCategoryPlus_whiskerLeft_app,
    NatTrans.mapHomotopyCategoryPlus_whiskerRight_app, Functor.map_comp]
  have n₁ := (Etale.upperStarIdDerivedPlus A Y).hom.naturality
    ((f)_*[A].rightDerivedFunctorPlusUnith.app K)
  have e₁ := Etale.upperStarIdDerivedPlus_hom_app A Y ((f)_*[A].mapHomotopyCategoryPlus.obj K)
  have n₂ := (f)_*[A].rightDerivedFunctorPlusUnith.naturality
    ((NatTrans.mapHomotopyCategoryPlus (Etale.upperStarId A X).inv).app K)
  have e₂ : DerivedCategory.Plus.Qh.map
        ((NatTrans.mapHomotopyCategoryPlus (Etale.upperStarId A X).inv).app K) ≫
      ((𝟙 X)^*[A]).mapDerivedCategoryPlusFactorsh.inv.app K =
      (Etale.upperStarIdDerivedPlus A X).inv.app (DerivedCategory.Plus.Qh.obj K) := by
    rw [← cancel_epi ((Etale.upperStarIdDerivedPlus A X).hom.app (DerivedCategory.Plus.Qh.obj K)),
      Iso.hom_inv_id_app,
      Etale.upperStarIdDerivedPlus_hom_app, Category.assoc, ← Functor.map_comp_assoc,
      ← NatTrans.comp_app, ← NatTrans.mapHomotopyCategoryPlus_comp, Iso.hom_inv_id,
      NatTrans.mapHomotopyCategoryPlus_id, NatTrans.id_app, CategoryTheory.Functor.map_id,
      Category.id_comp, Iso.hom_inv_id_app]
    rfl
  simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map] at n₁ n₂
  rw [reassoc_of% n₁, e₁]
  simp only [Category.assoc]
  erw [reassoc_of% n₂]
  rw [← Functor.map_comp, e₂]
  erw [Category.id_comp]
  rfl

/-- The right unit law for the composition isomorphisms of the derived pullbacks: the
composition isomorphism `D(h ≫ 𝟙)^*⁺ ≅ D(𝟙)^*⁺ ⋙ D(h)^*⁺` along the diagonal `h`, followed by
the identity isomorphism `D(𝟙)^*⁺ ≅ 𝟭`, is the unitor. -/
lemma Etale.upperStarCompDerivedPlus_id_right (h : Y ⟶ X) :
    (upperStarCompDerivedPlus A h (𝟙 X) h (Category.comp_id h).symm).hom ≫
        Functor.whiskerRight (upperStarIdDerivedPlus A X).hom ((h)^*[A]).mapDerivedCategoryPlus =
      (Functor.leftUnitor _).inv := by
  refine Localization.natTrans_ext DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso _) (fun K => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_inv_app]
  rw [← cancel_mono (((h)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app K),
    upperStarIdDerivedPlus_hom_app, Functor.map_comp, Category.assoc]
  have hn := ((h)^*[A]).mapDerivedCategoryPlusFactorsh.hom.naturality
    ((NatTrans.mapHomotopyCategoryPlus (Etale.upperStarId A X).hom).app K)
  simp only [Functor.comp_obj, Functor.comp_map] at hn
  simp only [Category.assoc]
  erw [hn]
  rw [upperStarCompDerivedPlus_hom_app_factorsh_assoc A h (𝟙 X) h _ K,
    ← Functor.map_comp, ← NatTrans.mapHomotopyCategoryPlus_whiskerRight_app,
    ← NatTrans.comp_app, ← NatTrans.mapHomotopyCategoryPlus_comp,
    Etale.upperStarComp_id_right]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom, Category.assoc,
    ← Functor.whiskerRight_comp, Iso.inv_hom_id, Functor.whiskerRight_id', Category.comp_id,
    NatTrans.mapHomotopyCategoryPlus_leftUnitor_inv_app, Category.id_comp]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- The componentwise inverse form of `AlgebraicGeometry.Etale.upperStarCompDerivedPlus_id_right`.
-/
lemma Etale.upperStarCompDerivedPlus_id_right_inv_app (h : Y ⟶ X)
    (M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    ((h)^*[A]).mapDerivedCategoryPlus.map ((upperStarIdDerivedPlus A X).inv.app M) ≫
        (upperStarCompDerivedPlus A h (𝟙 X) h (Category.comp_id h).symm).inv.app M =
      𝟙 _ := by
  have hiso : upperStarCompDerivedPlus A h (𝟙 X) h (Category.comp_id h).symm ≪≫
      Functor.isoWhiskerRight (upperStarIdDerivedPlus A X) ((h)^*[A]).mapDerivedCategoryPlus =
      (Functor.leftUnitor _).symm :=
    Iso.ext (upperStarCompDerivedPlus_id_right A h)
  exact NatTrans.congr_app (congrArg Iso.inv hiso) M

/-- The left unit law for the composition isomorphisms of the derived pullbacks: the
composition isomorphism `D(𝟙 ≫ p)^*⁺ ≅ D(p)^*⁺ ⋙ D(𝟙)^*⁺` along the diagonal `p`, followed by
the identity isomorphism `D(𝟙)^*⁺ ≅ 𝟭`, is the unitor. -/
lemma Etale.upperStarCompDerivedPlus_id_left (p : X ⟶ Y) :
    (upperStarCompDerivedPlus A (𝟙 X) p p (Category.id_comp p).symm).hom ≫
        Functor.whiskerLeft ((p)^*[A]).mapDerivedCategoryPlus (upperStarIdDerivedPlus A X).hom =
      (Functor.rightUnitor _).inv := by
  refine Localization.natTrans_ext DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso _) (fun K => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_inv_app]
  have hn := (upperStarIdDerivedPlus A X).hom.naturality
    (((p)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app K)
  simp only [Functor.id_map, Functor.comp_obj] at hn
  rw [← cancel_mono (((p)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app K), Category.assoc, ← hn,
    upperStarIdDerivedPlus_hom_app,
    upperStarCompDerivedPlus_hom_app_factorsh_assoc A (𝟙 X) p p _ K,
    ← Functor.map_comp, ← NatTrans.mapHomotopyCategoryPlus_whiskerLeft_app,
    ← NatTrans.comp_app, ← NatTrans.mapHomotopyCategoryPlus_comp,
    Etale.upperStarComp_id_left]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom, Category.assoc,
    ← Functor.whiskerLeft_comp, Iso.inv_hom_id, Functor.whiskerLeft_id', Category.comp_id,
    NatTrans.mapHomotopyCategoryPlus_rightUnitor_inv_app, Category.id_comp]
  exact (congrArg _ (DerivedCategory.Plus.Qh.map_id _)).trans (Category.comp_id _)

/-- The componentwise inverse form of `AlgebraicGeometry.Etale.upperStarCompDerivedPlus_id_left`.
-/
lemma Etale.upperStarCompDerivedPlus_id_left_inv_app (p : X ⟶ Y)
    (M : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A)) :
    (upperStarIdDerivedPlus A X).inv.app (((p)^*[A]).mapDerivedCategoryPlus.obj M) ≫
        (upperStarCompDerivedPlus A (𝟙 X) p p (Category.id_comp p).symm).inv.app M =
      𝟙 (((p)^*[A]).mapDerivedCategoryPlus.obj M) := by
  have hiso : upperStarCompDerivedPlus A (𝟙 X) p p (Category.id_comp p).symm ≪≫
      Functor.isoWhiskerLeft ((p)^*[A]).mapDerivedCategoryPlus (upperStarIdDerivedPlus A X) =
      (Functor.rightUnitor _).symm :=
    Iso.ext (upperStarCompDerivedPlus_id_left A p)
  exact NatTrans.congr_app (congrArg Iso.inv hiso) M

end Identity

end AlgebraicGeometry
