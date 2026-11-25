/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SixFunctors.Supporting.SixFunctorOperationDatumStages
public import WeilConjectures.AlgebraicGeometry.SixFunctors.IdentityFactorFixedSupport
import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicDirectImageUnitNormalization
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionIdIso
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars

/-! # Coefficient realization respects the two identity-factor unit maps -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  AlgebraicGeometry.ProEtale
namespace WeilConjectures.FixProjectionCompactification

private theorem left_id_normalization {B : Type*} [Category B] {L R : B ⥤ B}
    (a : L ⊣ R) (r : R ≅ 𝟭 B) :
      (a.ofNatIsoRight r).leftAdjointUniq Adjunction.id = a.leftAdjointIdIso r := by
  apply Iso.ext_inv
  ext N
  simp [Adjunction.leftAdjointUniq, Adjunction.leftAdjointIdIso,
    conjugateIsoEquiv, conjugateEquiv_symm_apply_app, Adjunction.ofNatIsoRight]

private theorem transported_left_id
    {C D : Type*} [Category C] [Category D] (e : C ≌ D)
    {L R : C ⥤ C} (a : L ⊣ R) (r : R ≅ 𝟭 C) :
    (((e.symm.toAdjunction.comp a).comp e.toAdjunction).ofNatIsoRight
      (Functor.isoWhiskerLeft e.inverse (Functor.isoWhiskerRight r e.functor) ≪≫
        e.counitIso)).leftAdjointUniq Adjunction.id =
      Functor.isoWhiskerLeft e.inverse
        (Functor.isoWhiskerRight
          ((a.ofNatIsoRight r).leftAdjointUniq Adjunction.id) e.functor) ≪≫
        e.counitIso := by
  rw [left_id_normalization, left_id_normalization]
  apply Iso.ext_inv
  ext M
  simp only [Adjunction.leftAdjointIdIso_inv_app, Adjunction.comp_unit_app, Iso.trans_hom,
    Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.id_obj,
    Equivalence.symm_functor, Equivalence.symm_inverse, Equivalence.toAdjunction_unit,
    Equivalence.symm_unit, Functor.comp_map, Functor.map_comp, Category.assoc]
  dsimp only [Functor.comp_obj]
  have hn := congrArg e.functor.map (r.hom.naturality
    (e.unit.app (L.obj (e.inverse.obj M))))
  dsimp only [Functor.id_map] at hn
  simp only [e.functor.map_comp] at hn
  rw [reassoc_of% hn]
  simp only [e.functor_unit_comp, Category.comp_id]

private theorem right_id_app
    {C : Type*} [Category C] {L R : C ⥤ C} (a : L ⊣ R) (l : L ≅ 𝟭 C) (N : C) :
    ((a.ofNatIsoLeft l).rightAdjointUniq Adjunction.id).hom.app N =
      l.inv.app (R.obj N) ≫ a.counit.app N := by
  have h := Adjunction.rightAdjointUniq_hom_app_counit
    (a.ofNatIsoLeft l) Adjunction.id N
  change ((a.ofNatIsoLeft l).rightAdjointUniq Adjunction.id).hom.app N ≫ 𝟙 _ =
    l.inv.app (R.obj N) ≫ a.counit.app N at h
  simpa only [Category.comp_id] using h

private theorem derived_right_id
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Abelian.HasKInjectiveResolutions C]
    {L R : C ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (a : L ⊣ R) (l : L ≅ 𝟭 C) :
    ((a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoLeft
      (Functor.mapDerivedCategoryNatIso l ≪≫ Functor.mapDerivedCategoryIdIso C)).rightAdjointUniq
        Adjunction.id) =
      Functor.rightDerivedFunctorNatIso ((a.ofNatIsoLeft l).rightAdjointUniq Adjunction.id) ≪≫
        Functor.rightDerivedFunctorIdIso C := by
  let r := (a.ofNatIsoLeft l).rightAdjointUniq Adjunction.id
  have : R.IsEquivalence := Functor.isEquivalence_of_iso r.symm
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Qh (HomotopyCategory.quasiIso C (.up ℤ))
  intro K
  rw [right_id_app]
  apply (cancel_epi (R.rightDerivedFunctorUnit.app K)).mp
  simp only [Iso.trans_hom, NatTrans.comp_app]
  erw [Functor.rightDerivedFunctorNatTrans_app_assoc,
    Functor.rightDerivedFunctorIdIso_fac_app, Category.comp_id]
  have hn := (Functor.mapDerivedCategoryNatIso l ≪≫
    Functor.mapDerivedCategoryIdIso C).inv.naturality (R.rightDerivedFunctorUnit.app K)
  dsimp only [Functor.id_map, Functor.comp_obj, Functor.comp_map, Functor.id_obj] at hn
  rw [← Category.assoc, hn, Category.assoc]
  have hc := (a.mapHomotopyCategory (.up ℤ)).derivedε_fac_app
    (HomotopyCategory.quasiIso C (.up ℤ))
    L.mapDerivedCategoryFactorsh.hom R.rightDerivedFunctorUnit K
  change L.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app K) ≫
    a.mapDerivedCategoryRightDerivedAdjunction.counit.app (DerivedCategory.Qh.obj K) = _ at hc
  erw [hc,
    Adjunction.mapDerivedCategoryNatIso_trans_idIso_inv_app_Qh_obj_assoc]
  erw [← DerivedCategory.Qh.map_comp]
  congr 1
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  rw [Adjunction.mapHomotopyCategory_counit_app_quotient]
  change (HomotopyCategory.quotient C (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient C (.up ℤ)).map _ =
    (HomotopyCategory.quotient C (.up ℤ)).map _
  rw [← Functor.map_comp]
  congr 1
  ext n
  exact (right_id_app a l (P.X n)).symm

private theorem transported_right_id
    {C D : Type*} [Category C] [Category D] (e : C ≌ D)
    {L R : C ⥤ C} (a : L ⊣ R) (l : L ≅ 𝟭 C) (H : D ⥤ D)
    (d : e.functor ⋙ H ≅ R ⋙ e.functor) (M : C) :
    d.hom.app M ≫ e.functor.map
        (((a.ofNatIsoLeft l).rightAdjointUniq Adjunction.id).hom.app M) =
      (((((e.symm.toAdjunction.comp a).comp e.toAdjunction).ofNatIsoRight
        (Functor.isoWhiskerLeft e.inverse d.symm ≪≫
          (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight e.counitIso H ≪≫ Functor.leftUnitor H)).ofNatIsoLeft
        (Functor.isoWhiskerLeft e.inverse (Functor.isoWhiskerRight l e.functor) ≪≫
          e.counitIso)).rightAdjointUniq Adjunction.id).hom.app (e.functor.obj M) := by
  simp only [right_id_app, Adjunction.ofNatIsoRight_counit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.trans_inv,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Functor.associator_hom_app,
    Functor.leftUnitor_inv_app, Iso.symm_inv, Functor.map_comp, Category.id_comp,
    Adjunction.comp_counit_app, Equivalence.toAdjunction_counit, Equivalence.symm_counit,
    Functor.comp_obj, Functor.comp_map, Equivalence.symm_functor,
    Equivalence.symm_inverse, Category.assoc]
  have hm {S T : C} (f : S ⟶ T) :
      e.functor.map (l.inv.app S) ≫ e.functor.map (L.map f) =
        e.functor.map f ≫ e.functor.map (l.inv.app T) := by
    rw [← e.functor.map_comp, ← l.inv.naturality]
    simp only [Functor.id_map, e.functor.map_comp]
  erw [reassoc_of% hm, reassoc_of% hm, reassoc_of% hm]
  simp only [← Functor.comp_map, ← e.counit_app_functor]
  erw [← e.counitIso.inv.naturality_assoc, ← e.counitIso.inv.naturality_assoc]
  simp only [Iso.inv_hom_id_app_assoc]
  simp only [Functor.id_map, ← e.functor.map_comp_assoc, ← right_id_app]
  erw [e.counitInv_app_functor, d.hom.naturality_assoc]
  dsimp only [Functor.comp_map, Functor.id_obj]
  erw [← e.functor.map_comp_assoc (R.map (e.unit.app M))
    (((a.ofNatIsoLeft l).rightAdjointUniq Adjunction.id).hom.app _),
    ((a.ofNatIsoLeft l).rightAdjointUniq Adjunction.id).hom.naturality]
  simp only [Functor.id_map, e.functor.map_comp, Category.assoc,
    e.functor_unit_comp, Category.comp_id, right_id_app, Functor.id_obj]

private theorem right_id_conjugate
    {C : Type*} [Category C] {L R : C ⥤ C} (a : L ⊣ R) (l : L ≅ 𝟭 C) :
    (a.ofNatIsoLeft l).rightAdjointUniq Adjunction.id =
      ((conjugateIsoEquiv Adjunction.id a) l).symm := by
  apply Iso.ext_inv
  ext M
  simp [Adjunction.rightAdjointUniq, conjugateIsoEquiv, conjugateEquiv_apply_app,
    Adjunction.ofNatIsoLeft]

private theorem left_id_fixed
    {C : Type*} [Category C] {L R : C ⥤ C} (a : L ⊣ R) (r : R ≅ 𝟭 C) :
    (a.ofNatIsoRight r).leftAdjointUniq Adjunction.id =
      a.leftAdjointUniq (Adjunction.id.ofNatIsoRight r.symm) := by
  apply Iso.ext_inv
  ext M
  simp [Adjunction.leftAdjointUniq, conjugateIsoEquiv, conjugateEquiv_symm_apply_app,
    Adjunction.ofNatIsoRight]

private theorem right_derived_id_unitQ
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Abelian.HasKInjectiveResolutions C]
    (R : C ⥤ C) [R.Additive] (r : R ≅ 𝟭 C) (J : CochainComplex C ℤ) :
    R.rightDerivedFunctorUnitQ J ≫
        (Functor.rightDerivedFunctorNatIso r ≪≫ Functor.rightDerivedFunctorIdIso C).hom.app
          (DerivedCategory.Q.obj J) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex r.hom (.up ℤ)).app J) := by
  have h := Functor.rightDerivedFunctorNatTrans_app r.hom
    ((HomotopyCategory.quotient C (.up ℤ)).obj J)
  have h' := congrArg (fun f => f ≫ (Functor.rightDerivedFunctorIdIso C).hom.app
    (DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (.up ℤ)).obj J))) h
  simp only [Category.assoc, Functor.rightDerivedFunctorIdIso_fac_app] at h'
  dsimp only [Functor.rightDerivedFunctorUnitQ,
    DerivedCategory.quotientCompQhIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Quotient.lift.isLift_hom, Quotient.lift.isLift_inv]
  erw [R.rightDerivedFunctor.map_id, Category.comp_id, Category.id_comp]
  erw [Category.comp_id] at h'
  exact h'

private theorem derived_identity_square
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (E : C ⥤ D) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (F : C ⥤ C) (G : D ⥤ D) [F.Additive] [G.Additive]
    (r : F ≅ 𝟭 C) (s : G ≅ 𝟭 D) (c : E ⋙ G ≅ F ⋙ E)
    (d : E.mapDerivedCategory ⋙ G.rightDerivedFunctor ≅
      F.rightDerivedFunctor ⋙ E.mapDerivedCategory)
    (hn : ∀ J : CochainComplex C ℤ,
      E.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ J) ≫
          d.inv.app (DerivedCategory.Q.obj J) ≫
          G.rightDerivedFunctor.map (E.mapDerivedCategoryFactors.hom.app J) =
        E.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj J) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c.inv (.up ℤ)).app J) ≫
          G.rightDerivedFunctorUnitQ ((E.mapHomologicalComplex (.up ℤ)).obj J))
    (hc : ∀ N, c.inv.app N ≫ s.hom.app (E.obj N) = E.map (r.hom.app N)) :
    d.inv ≫ Functor.whiskerLeft E.mapDerivedCategory
        (Functor.rightDerivedFunctorNatIso s ≪≫ Functor.rightDerivedFunctorIdIso D).hom =
      Functor.whiskerRight
        (Functor.rightDerivedFunctorNatIso r ≪≫ Functor.rightDerivedFunctorIdIso C).hom
        E.mapDerivedCategory := by
  have : F.IsEquivalence := Functor.isEquivalence_of_iso r.symm
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
  intro J
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  have hu : IsIso (F.rightDerivedFunctorUnitQ J) := by
    dsimp only [Functor.rightDerivedFunctorUnitQ]
    infer_instance
  apply (cancel_epi (E.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ J))).mp
  apply (cancel_mono (E.mapDerivedCategoryFactors.hom.app J)).mp
  have hg := (Functor.rightDerivedFunctorNatIso s ≪≫
    Functor.rightDerivedFunctorIdIso D).hom.naturality
      (E.mapDerivedCategoryFactors.hom.app J)
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hg
  simp only [Category.assoc]
  rw [← hg, reassoc_of% (hn J), right_derived_id_unitQ,
    ← DerivedCategory.Q.map_comp]
  have hcJ : (NatTrans.mapHomologicalComplex c.inv (.up ℤ)).app J ≫
      (NatTrans.mapHomologicalComplex s.hom (.up ℤ)).app
        ((E.mapHomologicalComplex (.up ℤ)).obj J) =
    (E.mapHomologicalComplex (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex r.hom (.up ℤ)).app J) := by
    ext n
    exact hc (J.X n)
  rw [hcJ]
  erw [← E.mapDerivedCategoryFactors.hom.naturality]
  erw [← E.mapDerivedCategory.map_comp_assoc, right_derived_id_unitQ]
  rfl

attribute [local implicit_reducible] sfIntrinsicCompactSupport sfAmbientCompactSupportCandidate
  sfIntrinsicDerivedEquivalence
attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian HasDerivedCategory.ofHasKInjectiveResolutions
  sfIntrinsicModuleEquivalence sfIntrinsicCompactSupportComparison
  Functor.mapDerivedCategory Functor.rightDerivedFunctor

private theorem direct_identity_square (A : Type u) [CommRing A] [Finite A] (X : Scheme.{u})
    (M : DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} A)))) :
    (sfIntrinsicDerivedDirectImageComparison (𝟙 X) A).hom.app M ≫
      (sfIntrinsicDerivedEquivalence X A).functor.map
        ((rightDerivedLowerStarId (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).hom.app M) =
      (WeilConjectures.sixFunctorDirectIdentity A X).hom.app
        ((sfIntrinsicDerivedEquivalence X A).functor.obj M) := by
  let s := ((sfIntrinsicConstantModuleAdjunction (𝟙 X) A).ofNatIsoLeft
    (sfIntrinsicPullbackId A X)).rightAdjointUniq Adjunction.id
  have hr : ((upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) (𝟙 X)).ofNatIsoLeft
        (upperStarId (ModuleCat.{u + 1} (ULift.{u + 1} A)) X)).rightAdjointUniq
        Adjunction.id = lowerStarId (ModuleCat.{u + 1} (ULift.{u + 1} A)) X := by
    rw [right_id_conjugate, conjugateIsoEquiv_upperStarId, Iso.symm_symm_eq]
  have hc (N : Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1} A))) :
      (sfIntrinsicDirectImageComparison (𝟙 X) A).inv.app N ≫
        s.hom.app ((sfIntrinsicModuleEquivalence X A).functor.obj N) =
      (sfIntrinsicModuleEquivalence X A).functor.map
        ((lowerStarId (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).hom.app N) := by
    have h := transported_right_id (sfIntrinsicModuleEquivalence X A)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} A)) (𝟙 X))
      (upperStarId (ModuleCat.{u + 1} (ULift.{u + 1} A)) X)
      (proEtaleConstantModuleDirectImage (𝟙 X) A)
      (sfIntrinsicDirectImageComparison (𝟙 X) A) N
    rw [hr] at h
    apply (cancel_epi ((sfIntrinsicDirectImageComparison (𝟙 X) A).hom.app N)).mp
    dsimp only [s, sfIntrinsicConstantModuleAdjunction, sfIntrinsicPullbackId,
      sfIntrinsicTransportIso]
    simpa only [Iso.hom_inv_id_app_assoc] using h.symm
  have hs : WeilConjectures.sixFunctorDirectIdentity A X =
      Functor.rightDerivedFunctorNatIso s ≪≫ Functor.rightDerivedFunctorIdIso _ := by
    exact derived_right_id (sfIntrinsicConstantModuleAdjunction (𝟙 X) A)
      (sfIntrinsicPullbackId A X)
  have h := derived_identity_square (sfIntrinsicModuleEquivalence X A).functor
    (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) (𝟙 X))
    (proEtaleConstantModuleDirectImage (𝟙 X) A)
    (lowerStarId (ModuleCat.{u + 1} (ULift.{u + 1} A)) X) s
    (sfIntrinsicDirectImageComparison (𝟙 X) A)
    (sfIntrinsicDerivedDirectImageComparison (𝟙 X) A)
    (sfIntrinsicDerivedDirectImageComparison_inv_unitQ_factors A (𝟙 X)) hc
  rw [← hs] at h
  have hM := NatTrans.congr_app h M
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app] at hM
  apply (cancel_epi ((sfIntrinsicDerivedDirectImageComparison (𝟙 X) A).inv.app M)).mp
  rw [Iso.inv_hom_id_app_assoc]
  exact hM.symm

private theorem open_identity (A : Type u) [CommRing A] [Finite A] (X : Scheme.{u}) :
    sfIntrinsicOpenId A X =
      Functor.isoWhiskerLeft (sfIntrinsicModuleEquivalence X A).inverse
        (Functor.isoWhiskerRight
          (openImmersionLowerShriekIdIso (ModuleCat.{u + 1} (ULift.{u + 1} A)) X)
          (sfIntrinsicModuleEquivalence X A).functor) ≪≫
        (sfIntrinsicModuleEquivalence X A).counitIso := by
  have h := transported_left_id (sfIntrinsicModuleEquivalence X A)
    (openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) (𝟙 X))
    (upperStarId (ModuleCat.{u + 1} (ULift.{u + 1} A)) X)
  rw [left_id_fixed (openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) (𝟙 X))] at h
  exact h

private theorem open_identity_square (A : Type u) [CommRing A] [Finite A] (X : Scheme.{u})
    (M : DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} A)))) :
    (Functor.mapDerivedCategorySquareIso
      (sfIntrinsicOpenExtensionComparison A (𝟙 X))).hom.app M ≫
      (sfIntrinsicDerivedEquivalence X A).functor.map
        ((Functor.mapDerivedCategoryNatIso
          (openImmersionLowerShriekIdIso (ModuleCat.{u + 1} (ULift.{u + 1} A)) X) ≪≫
          Functor.mapDerivedCategoryIdIso _).hom.app M) =
      (Functor.mapDerivedCategoryNatIso (sfIntrinsicOpenId A X) ≪≫
        Functor.mapDerivedCategoryIdIso _).hom.app
        ((sfIntrinsicDerivedEquivalence X A).functor.obj M) := by
  apply Functor.mapDerivedCategorySquareIso_hom_app_id
  intro N
  rw [open_identity]
  dsimp only [sfIntrinsicOpenExtensionComparison, Iso.trans_hom,
    sfIntrinsicExtensionByZero, Iso.symm_hom,
    NatTrans.comp_app, Functor.associator_inv_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app]
  dsimp only [Functor.comp_map]
  erw [Category.id_comp, Category.comp_id]
  rw [← Functor.map_comp]
  erw [(openImmersionLowerShriekIdIso
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).hom.naturality]
  rw [Functor.map_comp]
  simp only [Functor.id_map]
  erw [(sfIntrinsicModuleEquivalence X A).counit_app_functor N]
  rfl

private def openRealization (A : Type u) [CommRing A] [Finite A]
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] :
    (sfIntrinsicDerivedEquivalence U A).functor ⋙
        (sfIntrinsicExtensionByZero j A).mapDerivedCategory ≅
      (openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).mapDerivedCategory ⋙
        (sfIntrinsicDerivedEquivalence V A).functor :=
  Functor.mapDerivedCategorySquareIso (sfIntrinsicOpenExtensionComparison A j)

private theorem supportComparison_app (A : Type u) [CommRing A] [Finite A]
    {U V : Scheme.{u}} {f : U ⟶ V} (c : Compactification f)
    (N : DerivedCategory
      (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} (ULift.{u + 1} A)))) :
    (sfIntrinsicCompactSupportComparison A c).hom.app N =
      (proEtaleConstantDerivedDirectImage c.g A).map
        ((openRealization A c.i).hom.app N) ≫
      (sfIntrinsicDerivedDirectImageComparison c.g A).hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} A))
          c.i).mapDerivedCategory.obj N) := by
  unfold sfIntrinsicCompactSupportComparison
  dsimp only [openRealization,
    Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
    Functor.associator_hom_app]
  simp only [Category.id_comp, Category.comp_id]
  erw [Category.id_comp]

attribute [local irreducible] openRealization

private theorem paste_identity_units
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (E : C ⥤ D) (E' : C' ⥤ D') (G : C ⥤ C') (H : D ⥤ D')
    (P Q : C ⥤ C) (p q : D ⥤ D)
    (a : P ≅ 𝟭 C) (b : Q ≅ 𝟭 C) (a' : p ≅ 𝟭 D) (b' : q ≅ 𝟭 D)
    (s : E ⋙ p ≅ P ⋙ E) (t : E ⋙ q ≅ Q ⋙ E) (d : E ⋙ H ≅ G ⋙ E')
    (hs : ∀ M, s.hom.app M ≫ E.map (a.hom.app M) = a'.hom.app (E.obj M))
    (ht : ∀ M, t.hom.app M ≫ E.map (b.hom.app M) = b'.hom.app (E.obj M))
    {N : D} {M : C} (v : N ⟶ E.obj M) :
    H.map (p.map (q.map v ≫ t.hom.app M)) ≫ H.map (s.hom.app (Q.obj M)) ≫
        d.hom.app (P.obj (Q.obj M)) ≫
        E'.map (G.map (a.hom.app (Q.obj M) ≫ b.hom.app M)) =
      H.map (a'.hom.app (q.obj N)) ≫ H.map (b'.hom.app N) ≫ H.map v ≫ d.hom.app M := by
  have hp : p.map (q.map v ≫ t.hom.app M) ≫ s.hom.app (Q.obj M) ≫
      E.map (a.hom.app (Q.obj M) ≫ b.hom.app M) =
      a'.hom.app (q.obj N) ≫ b'.hom.app N ≫ v := by
    rw [E.map_comp, reassoc_of% (hs (Q.obj M))]
    erw [a'.hom.naturality_assoc]
    dsimp only [Functor.id_map]
    erw [Category.assoc, ht, b'.hom.naturality]
    rfl
  have hd := d.hom.naturality (a.hom.app (Q.obj M) ≫ b.hom.app M)
  dsimp only [Functor.comp_map, Functor.id_obj] at hd
  calc
    _ = H.map (p.map (q.map v ≫ t.hom.app M) ≫ s.hom.app (Q.obj M) ≫
        E.map (a.hom.app (Q.obj M) ≫ b.hom.app M)) ≫ d.hom.app M := by
      simp only [H.map_comp, Category.assoc]
      rw [hd]
    _ = _ := by rw [hp]; simp only [H.map_comp, Category.assoc]

private theorem properCandidate_app (A : Type u) [CommRing A] [Finite A]
    {U V : Scheme.{u}} (p : U ⟶ V) [IsProper p]
    (N : proEtaleDerivedCategory U A) :
    (sixFunctorProperCandidateIso A p).hom.app N =
      (proEtaleConstantDerivedDirectImage p A).map
        ((Functor.mapDerivedCategoryNatIso (sfIntrinsicOpenId A U) ≪≫
          Functor.mapDerivedCategoryIdIso _).hom.app N) := by
  unfold sixFunctorProperCandidateIso
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app]
  exact Category.comp_id _

private theorem openCandidate_app (A : Type u) [CommRing A] [Finite A]
    {U V : Scheme.{u}} (i : U ⟶ V) [IsOpenImmersion i]
    (N : proEtaleDerivedCategory U A) :
    (sixFunctorOpenCandidateIso A i).hom.app N =
      (sixFunctorDirectIdentity A V).hom.app
        ((sfIntrinsicExtensionByZero i A).mapDerivedCategory.obj N) := by
  unfold sixFunctorOpenCandidateIso
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
  exact Category.comp_id _

private theorem fixedIdentity_app (A : Type u) [CommRing A]
    {U V W : Scheme.{u}} (i : U ⟶ V) (p : V ⟶ W) [IsOpenImmersion i] [IsProper p]
    (N : DerivedCategory
      (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} (ULift.{u + 1} A)))) :
    (identityFactorFixedIso (ULift.{u + 1} A) i p).hom.app N =
      (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) p).rightDerivedFunctor.map
        ((Functor.mapDerivedCategoryNatIso
            (openImmersionLowerShriekIdIso (ModuleCat.{u + 1} (ULift.{u + 1} A)) V) ≪≫
          Functor.mapDerivedCategoryIdIso _).hom.app
          ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) (𝟙 V)).rightDerivedFunctor.obj
            ((openImmersionLowerShriek
              (ModuleCat.{u + 1} (ULift.{u + 1} A)) i).mapDerivedCategory.obj N)) ≫
        (rightDerivedLowerStarId (ModuleCat.{u + 1} (ULift.{u + 1} A)) V).hom.app
          ((openImmersionLowerShriek
            (ModuleCat.{u + 1} (ULift.{u + 1} A)) i).mapDerivedCategory.obj N)) := by
  unfold identityFactorFixedIso identityFactorFixedProper identityFactorFixedOpen
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_hom_app]
  simp only [Functor.map_comp]
  erw [Category.comp_id,
    (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) p).rightDerivedFunctor.map_id,
    Category.comp_id]
  rfl

/-- The coefficient comparison commutes with the independent identity-factor unit maps.
There is no etale-origin condition or geometric composition comparison in this equation.

Source: def-sf-operation-stages, proper/open normalizations; the section and K-injective
normalizations of sfIntrinsicDerivedDirectImageComparison.
(blueprint: lem-sf-identity-factor-coefficient-comparison).

Proof: expand the three compact-support comparisons into their open and direct-image
comparisons. For the proper compactification, the open comparison followed by the
realization of the fixed-scalar identity open unit is the intrinsic identity open unit;
this follows by uniqueness of the transported left adjoint and exact-functor descent.
For the open compactification, the direct-image comparison followed by realization of
the fixed-scalar identity direct-image unit is the intrinsic identity direct-image unit.
Indeed both are right-adjoint comparisons for the same realized identity inverse image;
the section normalization and K-injective normalization identify their underived and
derived mates. Naturality of the proper direct-image comparison moves the open identity
map into proper image. Cancel the intermediate realization units. The surviving factors
are exactly the open and direct-image comparison for the actual pair (i,p). These
arguments apply to arbitrary inputs, including zero and empty schemes. -/
theorem identityFactorCoefficientComparison (A : Type u) [CommRing A] [Finite A]
    {X Z Y : Scheme.{u}} (i : X ⟶ Z) (p : Z ⟶ Y)
    [IsOpenImmersion i] [IsProper p]
    (M : DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} A)))) :
    (sfIntrinsicCompactSupport (Compactification.ofIsProper p) A).map
        ((sfIntrinsicCompactSupportComparison A
          (Compactification.ofIsOpenImmersion i)).hom.app M) ≫
      (sfIntrinsicCompactSupportComparison A (Compactification.ofIsProper p)).hom.app
        ((sfFixedCompactSupport A (Compactification.ofIsOpenImmersion i)).obj M) ≫
      (sfIntrinsicDerivedEquivalence Y A).functor.map
        ((identityFactorFixedIso (ULift.{u + 1} A) i p).hom.app M) =
    (sixFunctorProperCandidateIso A p).hom.app
        ((sfIntrinsicCompactSupport (Compactification.ofIsOpenImmersion i) A).obj
          ((sfIntrinsicDerivedEquivalence X A).functor.obj M)) ≫
      (proEtaleConstantDerivedDirectImage p A).map
        ((sixFunctorOpenCandidateIso A i).hom.app
          ((sfIntrinsicDerivedEquivalence X A).functor.obj M)) ≫
      (sfIntrinsicCompactSupportComparison A (identityFactorPair i p)).hom.app M := by
  rw [supportComparison_app, supportComparison_app, supportComparison_app,
    properCandidate_app, openCandidate_app, fixedIdentity_app]
  have h := paste_identity_units
    (sfIntrinsicDerivedEquivalence Z A).functor
    (sfIntrinsicDerivedEquivalence Y A).functor
    (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) p).rightDerivedFunctor
    (proEtaleConstantDerivedDirectImage p A)
    (openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} A)) (𝟙 Z)).mapDerivedCategory
    (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) (𝟙 Z)).rightDerivedFunctor
    (sfIntrinsicExtensionByZero (𝟙 Z) A).mapDerivedCategory
    (proEtaleConstantDerivedDirectImage (𝟙 Z) A)
    (Functor.mapDerivedCategoryNatIso
      (openImmersionLowerShriekIdIso (ModuleCat.{u + 1} (ULift.{u + 1} A)) Z) ≪≫
      Functor.mapDerivedCategoryIdIso _)
    (rightDerivedLowerStarId (ModuleCat.{u + 1} (ULift.{u + 1} A)) Z)
    (Functor.mapDerivedCategoryNatIso (sfIntrinsicOpenId A Z) ≪≫
      Functor.mapDerivedCategoryIdIso _)
    (WeilConjectures.sixFunctorDirectIdentity A Z)
    (openRealization A (𝟙 Z))
    (sfIntrinsicDerivedDirectImageComparison (𝟙 Z) A)
    (sfIntrinsicDerivedDirectImageComparison p A)
    (by simpa only [openRealization] using open_identity_square A Z)
    (direct_identity_square A Z)
    ((openRealization A i).hom.app M)
  simpa only [sfIntrinsicCompactSupport, sfFixedCompactSupport,
    identityFactorPair, Compactification.ofIsProper, Compactification.ofIsOpenImmersion,
    Functor.comp_map, Functor.comp_obj, Functor.map_comp, Category.assoc] using h

end WeilConjectures.FixProjectionCompactification
