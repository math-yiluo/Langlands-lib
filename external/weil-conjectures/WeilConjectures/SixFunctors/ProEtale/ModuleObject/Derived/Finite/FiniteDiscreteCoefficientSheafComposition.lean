/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientPullbackIso
import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientRestrictionCoherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence

/-! # Composition coherence before derivation -/

@[expose] public section
open CategoryTheory Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private noncomputable def inverseRestriction
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (E : C ≌ D) (E' : C' ≌ D') (P : C ⥤ C') (R : D ⥤ D')
    (r : E.functor ⋙ R ≅ P ⋙ E'.functor) : R ⋙ E'.inverse ≅ E.inverse ⋙ P :=
  ((Functor.associator E.functor R E'.inverse).symm ≪≫ r.compInverseIso).isoInverseComp

private theorem inverseRestriction_hom
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (E : C ≌ D) (E' : C' ≌ D') (P : C ⥤ C') (R : D ⥤ D')
    (r : E.functor ⋙ R ≅ P ⋙ E'.functor) (M : D) :
    E'.functor.map ((inverseRestriction E E' P R r).hom.app M) =
      E'.counitIso.hom.app (R.obj M) ≫ R.map (E.counitIso.inv.app M) ≫
        r.hom.app (E.inverse.obj M) := by
  simp only [inverseRestriction, Iso.isoInverseComp, Iso.compInverseIso,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.leftUnitor_inv_app,
    Functor.rightUnitor_hom_app, Functor.map_comp, Functor.comp_map, Category.id_comp,
    Iso.symm_hom]
  rw [← E'.counit_app_functor]
  rw [← E'.functor.map_comp_assoc, ← E'.inverse.map_comp]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  simpa only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj,
    Category.assoc] using E'.counitIso.hom.naturality
      (R.map (E.counitIso.inv.app M) ≫ r.hom.app (E.inverse.obj M))

private theorem inverseRestriction_comp
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    (E₀ : C₀ ≌ D₀) (E₁ : C₁ ≌ D₁) (E₂ : C₂ ≌ D₂)
    (P₁ : C₀ ⥤ C₁) (P₂ : C₁ ⥤ C₂) (P₁₂ : C₀ ⥤ C₂)
    (R₁ : D₀ ⥤ D₁) (R₂ : D₁ ⥤ D₂) (R₁₂ : D₀ ⥤ D₂)
    (r₁ : E₀.functor ⋙ R₁ ≅ P₁ ⋙ E₁.functor)
    (r₂ : E₁.functor ⋙ R₂ ≅ P₂ ⋙ E₂.functor)
    (r₁₂ : E₀.functor ⋙ R₁₂ ≅ P₁₂ ⋙ E₂.functor)
    (cP : P₁ ⋙ P₂ ≅ P₁₂) (cR : R₁ ⋙ R₂ ≅ R₁₂)
    (h : ∀ N, R₂.map (r₁.hom.app N) ≫ r₂.hom.app (P₁.obj N) ≫
      E₂.functor.map (cP.hom.app N) = cR.hom.app (E₀.functor.obj N) ≫ r₁₂.hom.app N)
    (M : D₀) :
    (inverseRestriction E₁ E₂ P₂ R₂ r₂).hom.app (R₁.obj M) ≫
      P₂.map ((inverseRestriction E₀ E₁ P₁ R₁ r₁).hom.app M) ≫
      cP.hom.app (E₀.inverse.obj M) =
    E₂.inverse.map (cR.hom.app M) ≫
      (inverseRestriction E₀ E₂ P₁₂ R₁₂ r₁₂).hom.app M := by
  apply E₂.functor.map_injective
  simp only [Functor.map_comp, inverseRestriction_hom, Category.assoc]
  have hn := r₂.hom.naturality ((inverseRestriction E₀ E₁ P₁ R₁ r₁).hom.app M)
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  simp only [inverseRestriction_hom, Functor.map_comp, Category.assoc]
  rw [← R₂.map_comp_assoc, Iso.inv_hom_id_app]
  erw [R₂.map_id, Category.id_comp]
  rw [h (E₀.inverse.obj M)]
  have hc := cR.hom.naturality (E₀.counitIso.inv.app M)
  dsimp only [Functor.comp_map] at hc
  rw [reassoc_of% hc]
  have he := E₂.counitIso.hom.naturality (cR.hom.app M)
  dsimp only [Functor.comp_map, Functor.id_map] at he
  rw [reassoc_of% he]

private theorem inverseRestriction_comp_iso
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    (E₀ : C₀ ≌ D₀) (E₁ : C₁ ≌ D₁) (E₂ : C₂ ≌ D₂)
    (P₁ : C₀ ⥤ C₁) (P₂ : C₁ ⥤ C₂) (P₁₂ : C₀ ⥤ C₂)
    (R₁ : D₀ ⥤ D₁) (R₂ : D₁ ⥤ D₂) (R₁₂ : D₀ ⥤ D₂)
    (r₁ : E₀.functor ⋙ R₁ ≅ P₁ ⋙ E₁.functor)
    (r₂ : E₁.functor ⋙ R₂ ≅ P₂ ⋙ E₂.functor)
    (r₁₂ : E₀.functor ⋙ R₁₂ ≅ P₁₂ ⋙ E₂.functor)
    (cP : P₁ ⋙ P₂ ≅ P₁₂) (cR : R₁ ⋙ R₂ ≅ R₁₂)
    (h : ∀ N, R₂.map (r₁.hom.app N) ≫ r₂.hom.app (P₁.obj N) ≫
      E₂.functor.map (cP.hom.app N) = cR.hom.app (E₀.functor.obj N) ≫ r₁₂.hom.app N) :
    inverseRestriction E₀ E₂ P₁₂ R₁₂ r₁₂ =
      isoWhiskerRight cR.symm E₂.inverse ≪≫ associator R₁ R₂ E₂.inverse ≪≫
      isoWhiskerLeft R₁ (inverseRestriction E₁ E₂ P₂ R₂ r₂) ≪≫
      (associator R₁ E₁.inverse P₂).symm ≪≫
      isoWhiskerRight (inverseRestriction E₀ E₁ P₁ R₁ r₁) P₂ ≪≫
      associator E₀.inverse P₁ P₂ ≪≫ isoWhiskerLeft E₀.inverse cP := by
  ext M
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerRight_hom, isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app,
    associator_hom_app, associator_inv_app, Category.id_comp]
  rw [← cancel_epi (E₂.inverse.map (cR.hom.app M))]
  rw [← E₂.inverse.map_comp_assoc, Iso.hom_inv_id_app]
  erw [E₂.inverse.map_id, Category.id_comp]
  exact (inverseRestriction_comp E₀ E₁ E₂ P₁ P₂ P₁₂ R₁ R₂ R₁₂ r₁ r₂ r₁₂ cP cR h M).symm

private theorem mate_composition_components
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    (E₀ : C₀ ≌ D₀) (E₁ : C₁ ≌ D₁) (E₂ : C₂ ≌ D₂)
    (F : C₁ ⥤ C₀) (G : C₂ ⥤ C₁) (FG : C₂ ⥤ C₀)
    (P : C₀ ⥤ C₁) (Q : C₁ ⥤ C₂) (PQ : C₀ ⥤ C₂)
    (I : D₁ ⥤ D₀) (J : D₂ ⥤ D₁) (IJ : D₂ ⥤ D₀)
    (R : D₀ ⥤ D₁) (V : D₁ ⥤ D₂) (RV : D₀ ⥤ D₂)
    (aF : F ⊣ P) (aG : G ⊣ Q) (aFG : FG ⊣ PQ)
    (aI : I ⊣ R) (aJ : J ⊣ V) (aIJ : IJ ⊣ RV)
    (r₁ : E₀.functor ⋙ R ≅ P ⋙ E₁.functor)
    (r₂ : E₁.functor ⋙ V ≅ Q ⋙ E₂.functor)
    (r₁₂ : E₀.functor ⋙ RV ≅ PQ ⋙ E₂.functor)
    (p₁ : F ⋙ E₀.functor ≅ E₁.functor ⋙ I)
    (p₂ : G ⋙ E₁.functor ≅ E₂.functor ⋙ J)
    (p₁₂ : FG ⋙ E₀.functor ≅ E₂.functor ⋙ IJ)
    (cP : P ⋙ Q ≅ PQ) (cR : R ⋙ V ≅ RV)
    (cF : FG ≅ G ⋙ F) (cI : IJ ≅ J ⋙ I)
    (hp₁ : conjugateIsoEquiv (aF.comp E₀.toAdjunction)
      (E₁.toAdjunction.comp aI) p₁.symm = (inverseRestriction E₀ E₁ P R r₁).symm)
    (hp₂ : conjugateIsoEquiv (aG.comp E₁.toAdjunction)
      (E₂.toAdjunction.comp aJ) p₂.symm = (inverseRestriction E₁ E₂ Q V r₂).symm)
    (hp₁₂ : conjugateIsoEquiv (aFG.comp E₀.toAdjunction)
      (E₂.toAdjunction.comp aIJ) p₁₂.symm =
        (inverseRestriction E₀ E₂ PQ RV r₁₂).symm)
    (hμ : conjugateIsoEquiv (aG.comp aF) aFG cF = cP)
    (hκ : conjugateIsoEquiv (aJ.comp aI) aIJ cI = cR)
    (hr : ∀ N, V.map (r₁.hom.app N) ≫ r₂.hom.app (P.obj N) ≫
      E₂.functor.map (cP.hom.app N) = cR.hom.app (E₀.functor.obj N) ≫ r₁₂.hom.app N)
    (N : C₂) :
    E₀.functor.map (cF.hom.app N) ≫ p₁.hom.app (G.obj N) ≫
      I.map (p₂.hom.app N) = p₁₂.hom.app N ≫ cI.hom.app (E₂.functor.obj N) := by
  have H := adjunctionSquareComposition
    E₂.toAdjunction E₁.toAdjunction E₀.toAdjunction
    aG aF aFG aJ aI aIJ
    (inverseRestriction E₁ E₂ Q V r₂)
    (inverseRestriction E₀ E₁ P R r₁)
    (inverseRestriction E₀ E₂ PQ RV r₁₂)
    cP.symm cR p₂.symm p₁.symm p₁₂.symm cF cI.symm
    hp₂ hp₁ hp₁₂ hμ
    (by rw [conjugateIsoEquiv_iso_symm, hκ])
    (inverseRestriction_comp_iso E₀ E₁ E₂ P Q PQ R V RV r₁ r₂ r₁₂ cP cR hr)
  have H := congrArg (fun t ↦ t.inv.app N) H
  simp only [Iso.trans_inv, Iso.symm_inv, isoWhiskerRight_inv, isoWhiskerLeft_inv,
    whiskerRight_app, whiskerLeft_app, associator_inv_app, associator_hom_app,
    NatTrans.comp_app, Category.id_comp, Category.comp_id, Category.assoc] at H
  rw [H, ← E₀.functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

universe u

open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.Functor

attribute [local instance] coefficientProfiniteEssentiallySmall

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

variable
  (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B)
  [IsMonHom eR.hom]
  (G : Mod Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} B)) ⥤
    ModuleCat.{u + 1} (ULift.{u + 1} B)) [G.IsEquivalence]
  (hG : G ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1} =
    Mod.forget (AddCommGrpCat.of (ULift.{u + 1} B)))

private theorem site_restriction_hom
    (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    {S T : Scheme.{u}} (f : S ⟶ T) (N : Sheaf (ProEt.topology S) A)
    (V : T.Etaleᵒᵖ) :
    ((lowerStarCompComparisonLowerStarIso f A).hom.app N).hom.app V = 𝟙 _ := by
  change 𝟙 _ ≫ N.obj.map (𝟙 _) ≫ 𝟙 _ = 𝟙 _
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]

private theorem etale_map_op
    (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    {S T : Scheme.{u}} (f : S ⟶ T) {N N' : Sheaf S.smallEtaleTopology A}
    (φ : N ⟶ N') (V : T.Etaleᵒᵖ) :
    ((Etale.lowerStar A f).map φ).hom.app V =
      φ.hom.app ((MorphismProperty.Over.pullback @Etale ⊤ f).op.obj V) := rfl

private theorem comparison_map
    (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    (T : Scheme.{u}) {N N' : Sheaf (ProEt.topology T) A} (φ : N ⟶ N') (V : T.Etaleᵒᵖ) :
    ((comparisonLowerStar A T).map φ).hom.app V = φ.hom.app ((toProEt T).op.obj V) := rfl

private theorem comparison_obj_map
    (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    (T : Scheme.{u}) (N : Sheaf (ProEt.topology T) A) {V W : T.Etaleᵒᵖ} (φ : V ⟶ W) :
    ((comparisonLowerStar A T).obj N).obj.map φ = N.obj.map ((toProEt T).op.map φ) := rfl

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] lowerStarCompComparisonLowerStarIso
  Etale.lowerStarComp ProEtale.lowerStarComp

private theorem site_restriction_comp
    (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    {S T U : Scheme.{u}} (f : S ⟶ T) (g : T ⟶ U)
    (N : Sheaf (ProEt.topology S) A) :
    (lowerStarCompComparisonLowerStarIso g A).hom.app ((ProEtale.lowerStar A f).obj N) ≫
      (Etale.lowerStar A g).map ((lowerStarCompComparisonLowerStarIso f A).hom.app N) ≫
      (Etale.lowerStarComp A f g).hom.app ((comparisonLowerStar A S).obj N) =
    (comparisonLowerStar A U).map ((ProEtale.lowerStarComp A f g).hom.app N) ≫
      (lowerStarCompComparisonLowerStarIso (f ≫ g) A).hom.app N := by
  ext V
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    etale_map_op, comparison_map, site_restriction_hom]
  erw [Category.id_comp, Category.id_comp, Category.comp_id]
  rw [Etale.lowerStarComp_hom_app_hom_app, comparison_obj_map,
    ProEtale.lowerStarComp_hom_app_hom_app]
  congr 1

private theorem site_comp
    (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [HasSmallSiteSheafify A]
    {S T U : Scheme.{u}} (f : S ⟶ T) (g : T ⟶ U)
    (N : Sheaf U.smallEtaleTopology A) :
    (comparisonUpperStar A S).map ((Etale.upperStarComp A f g).hom.app N) ≫
      (comparisonUpperStarCompUpperStarIso A f).inv.app ((Etale.upperStar A g).obj N) ≫
      (ProEtale.upperStar A f).map ((comparisonUpperStarCompUpperStarIso A g).inv.app N) =
    (comparisonUpperStarCompUpperStarIso A (f ≫ g)).inv.app N ≫
      (ProEtale.upperStarComp A f g).hom.app ((comparisonUpperStar A U).obj N) := by
  let r := fun {X Y : Scheme.{u}} (h : X ⟶ Y) ↦ lowerStarCompComparisonLowerStarIso h A
  let p := fun {X Y : Scheme.{u}} (h : X ⟶ Y) ↦ comparisonUpperStarCompUpperStarIso A h
  have hp {X Y : Scheme.{u}} (h : X ⟶ Y) :
      conjugateIsoEquiv
        ((Etale.upperStarLowerStarAdjunction A h).comp (comparisonAdjunction A X))
        ((comparisonAdjunction A Y).comp (ProEtale.upperStarLowerStarAdjunction A h))
        (p h) = (r h).symm := by
    unfold p comparisonUpperStarCompUpperStarIso
    exact (conjugateIsoEquiv _ _).apply_symm_apply _
  have hr : r (f ≫ g) =
      isoWhiskerRight (ProEtale.lowerStarComp A f g).symm (comparisonLowerStar A U) ≪≫
      associator (ProEtale.lowerStar A f) (ProEtale.lowerStar A g)
        (comparisonLowerStar A U) ≪≫
      isoWhiskerLeft (ProEtale.lowerStar A f) (r g) ≪≫
      (associator (ProEtale.lowerStar A f) (comparisonLowerStar A T)
        (Etale.lowerStar A g)).symm ≪≫
      isoWhiskerRight (r f) (Etale.lowerStar A g) ≪≫
      associator (comparisonLowerStar A S) (Etale.lowerStar A f) (Etale.lowerStar A g) ≪≫
      isoWhiskerLeft (comparisonLowerStar A S) (Etale.lowerStarComp A f g) := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      isoWhiskerRight_hom, isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app,
      associator_hom_app, associator_inv_app, Category.id_comp]
    rw [← cancel_epi ((comparisonLowerStar A U).map
      ((ProEtale.lowerStarComp A f g).hom.app M))]
    rw [← (comparisonLowerStar A U).map_comp_assoc, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
    exact (site_restriction_comp A f g M).symm
  have hκ : conjugateIsoEquiv (ProEtale.upperStarLowerStarAdjunction A (f ≫ g))
      ((ProEtale.upperStarLowerStarAdjunction A g).comp
        (ProEtale.upperStarLowerStarAdjunction A f))
      (ProEtale.upperStarComp A f g).symm = (ProEtale.lowerStarComp A f g).symm := by
    rw [conjugateIsoEquiv_iso_symm, ProEtale.conjugateIsoEquiv_upperStarComp]
  have H := adjunctionSquareComposition
    (comparisonAdjunction A U) (comparisonAdjunction A T) (comparisonAdjunction A S)
    (Etale.upperStarLowerStarAdjunction A g) (Etale.upperStarLowerStarAdjunction A f)
    (Etale.upperStarLowerStarAdjunction A (f ≫ g))
    (ProEtale.upperStarLowerStarAdjunction A g) (ProEtale.upperStarLowerStarAdjunction A f)
    (ProEtale.upperStarLowerStarAdjunction A (f ≫ g))
    (r g) (r f) (r (f ≫ g)) (Etale.lowerStarComp A f g).symm
    (ProEtale.lowerStarComp A f g) (p g) (p f) (p (f ≫ g))
    (Etale.upperStarComp A f g) (ProEtale.upperStarComp A f g).symm
    (hp g) (hp f) (hp (f ≫ g)) (Etale.conjugateIsoEquiv_upperStarComp A f g) hκ hr
  have H := congrArg (fun t ↦ t.inv.app N) H
  simp only [Iso.trans_inv, Iso.symm_inv, isoWhiskerRight_inv, isoWhiskerLeft_inv,
    whiskerRight_app, whiskerLeft_app, associator_inv_app, associator_hom_app,
    NatTrans.comp_app, Category.id_comp, Category.comp_id, Category.assoc] at H
  rw [H, ← (comparisonUpperStar A S).map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

private theorem pro_mate {X Y : Scheme.{u}} (h : X ⟶ Y) :
    conjugateIsoEquiv
      ((ProEtale.upperStarLowerStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1} B)) h).comp
          (finiteDiscreteCoefficientEquivalence B eR G hG X).toAdjunction)
      ((finiteDiscreteCoefficientEquivalence B eR G hG Y).toAdjunction.comp
        (upperStarLowerStarAdjunction (Profinite.continuousMapRingObj B) h))
      (finiteDiscreteCoefficientProEtalePullbackIso B eR G hG h).symm =
    (inverseRestriction (finiteDiscreteCoefficientEquivalence B eR G hG X)
      (finiteDiscreteCoefficientEquivalence B eR G hG Y)
      (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h)
      (lowerStar (Profinite.continuousMapRingObj B) h)
      (finiteDiscreteCoefficientRestrictionIso B eR G hG h)).symm := by
  rw [conjugateIsoEquiv_iso_symm]
  congr 1
  unfold finiteDiscreteCoefficientProEtalePullbackIso inverseRestriction
  exact (conjugateIsoEquiv _ _).apply_symm_apply _

private theorem pro_comp {S T U : Scheme.{u}} (f : S ⟶ T) (g : T ⟶ U)
    (N : FiniteDiscreteProEtaleSheaves B U) :
    (finiteDiscreteCoefficientEquivalence B eR G hG S).functor.map
        ((ProEtale.upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} B)) f g).hom.app N) ≫
      (finiteDiscreteCoefficientProEtalePullbackIso B eR G hG f).hom.app
        ((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) g).obj N) ≫
      (upperStar (Profinite.continuousMapRingObj B) f).map
        ((finiteDiscreteCoefficientProEtalePullbackIso B eR G hG g).hom.app N) =
    (finiteDiscreteCoefficientProEtalePullbackIso B eR G hG (f ≫ g)).hom.app N ≫
      (upperStarComp (Profinite.continuousMapRingObj B) f g).hom.app
        ((finiteDiscreteCoefficientEquivalence B eR G hG U).functor.obj N) := by
  exact mate_composition_components
    (finiteDiscreteCoefficientEquivalence B eR G hG S)
    (finiteDiscreteCoefficientEquivalence B eR G hG T)
    (finiteDiscreteCoefficientEquivalence B eR G hG U)
    (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) f)
    (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) g)
    (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B))
    (f ≫ g))
    (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) f)
    (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) g)
    (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B))
    (f ≫ g))
    (upperStar (Profinite.continuousMapRingObj B) f)
    (upperStar (Profinite.continuousMapRingObj B) g)
    (upperStar (Profinite.continuousMapRingObj B)
    (f ≫ g))
    (lowerStar (Profinite.continuousMapRingObj B) f)
    (lowerStar (Profinite.continuousMapRingObj B) g)
    (lowerStar (Profinite.continuousMapRingObj B)
    (f ≫ g))
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} B)) f)
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} B)) g)
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} B))
    (f ≫ g))
    (upperStarLowerStarAdjunction (Profinite.continuousMapRingObj B) f)
    (upperStarLowerStarAdjunction (Profinite.continuousMapRingObj B) g)
    (upperStarLowerStarAdjunction (Profinite.continuousMapRingObj B)
    (f ≫ g))
    (finiteDiscreteCoefficientRestrictionIso B eR G hG f)
    (finiteDiscreteCoefficientRestrictionIso B eR G hG g)
    (finiteDiscreteCoefficientRestrictionIso B eR G hG (f ≫ g))
    (finiteDiscreteCoefficientProEtalePullbackIso B eR G hG f)
    (finiteDiscreteCoefficientProEtalePullbackIso B eR G hG g)
    (finiteDiscreteCoefficientProEtalePullbackIso B eR G hG (f ≫ g))
    (ProEtale.lowerStarComp (ModuleCat.{u + 1} (ULift.{u + 1} B)) f g)
    (lowerStarComp (Profinite.continuousMapRingObj B) f g)
    (ProEtale.upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} B)) f g)
    (upperStarComp (Profinite.continuousMapRingObj B) f g)
    (pro_mate B eR G hG f)
    (pro_mate B eR G hG g)
    (pro_mate B eR G hG (f ≫ g))
    (ProEtale.conjugateIsoEquiv_upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} B)) f g)
    (conjugateIsoEquiv_upperStarComp (Profinite.continuousMapRingObj B) f g)
    (finiteDiscreteCoefficientRestrictionIso_comp B eR G hG f g) N

private theorem sheaf_pullback_hom {S T : Scheme.{u}} (f : S ⟶ T)
    (N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} B))) :
    (finiteDiscreteCoefficientSheafPullbackIso B eR G hG f).hom.app N =
      (finiteDiscreteCoefficientEquivalence B eR G hG S).functor.map
        ((comparisonUpperStarCompUpperStarIso
          (ModuleCat.{u + 1} (ULift.{u + 1} B)) f).inv.app N) ≫
      (finiteDiscreteCoefficientProEtalePullbackIso B eR G hG f).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) T).obj N) := by
  unfold finiteDiscreteCoefficientSheafPullbackIso
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerRight_hom, isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app,
    associator_hom_app, associator_inv_app, Category.id_comp, Category.comp_id]

/-- The canonical ordinary coefficient pullback comparisons commute with composition.
Source: Bhatt--Scholze, Proposition 5.3.2 and Lemma 5.4.1; the normalized restriction
comparison (blueprint: lem-weil-pbc-finite-discrete-sheaf-pullback-composition).

Proof in words. First apply finiteDiscreteCoefficientRestrictionIso_comp to the
normalized restriction comparisons. Cancel the encoding equivalences on the two
right adjoints using their unit and counit isomorphisms. Conjugate the resulting
identity through the composite pullback adjunctions that define
finiteDiscreteCoefficientProEtalePullbackIso. The conjugation composition and
whiskering laws reverse its order and identify the two pullback composition maps.
For the etale/pro-etale site comparison, restriction along the composite base-change
functor is the composite restriction; its comparison is natural in the sheaf. Apply
the same conjugation laws to this identity, using comparisonAdjunction. Finally
expand finiteDiscreteCoefficientSheafPullbackIso as the paste of the site comparison
and the coefficient comparison. Move the site composition map through the coefficient
comparison by naturality. Cancel the intermediate associators, whose components are
identities. The two composition identities give exactly the displayed equation.
This argument also applies when either morphism is an identity, and requires no
cartesian or finiteness hypothesis on the morphisms.
-/
theorem finiteDiscreteCoefficientSheafPullbackIso_comp {S T U : Scheme.{u}}
    (f : S ⟶ T) (g : T ⟶ U)
    (N : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} B))) :
    (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) S ⋙
      (finiteDiscreteCoefficientEquivalence B eR G hG S).functor).map
        ((Etale.upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} B)) f g).hom.app N) ≫
      (finiteDiscreteCoefficientSheafPullbackIso B eR G hG f).hom.app
        ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) g).obj N) ≫
      (upperStar (Profinite.continuousMapRingObj B) f).map
        ((finiteDiscreteCoefficientSheafPullbackIso B eR G hG g).hom.app N) =
    (finiteDiscreteCoefficientSheafPullbackIso B eR G hG (f ≫ g)).hom.app N ≫
      (upperStarComp (Profinite.continuousMapRingObj B) f g).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) U ⋙
          (finiteDiscreteCoefficientEquivalence B eR G hG U).functor).obj N) := by
  let A := ModuleCat.{u + 1} (ULift.{u + 1} B)
  let E := fun X ↦ finiteDiscreteCoefficientEquivalence B eR G hG X
  let p := fun {X Y : Scheme.{u}} (h : X ⟶ Y) ↦
    finiteDiscreteCoefficientProEtalePullbackIso B eR G hG h
  let c := fun {X Y : Scheme.{u}} (h : X ⟶ Y) ↦ comparisonUpperStarCompUpperStarIso A h
  simp only [sheaf_pullback_hom, Functor.comp_map, Functor.map_comp, Category.assoc]
  have hn := (p f).hom.naturality ((c g).inv.app N)
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  rw [← (E S).functor.map_comp_assoc, ← (E S).functor.map_comp_assoc]
  simp only [Category.assoc]
  rw [site_comp A f g N]
  rw [(E S).functor.map_comp, Category.assoc, pro_comp B eR G hG f g]
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
