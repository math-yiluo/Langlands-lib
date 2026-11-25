/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarOrdinaryPullbackComparison
import all WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedScalarRestrictionDirectImage
import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicDirectImageUnitNormalization
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Factorized representative equation for finite scalar pullback

Source: Stacks Tags 07A6 and 0D6E.
(blueprint: lem-sf-finite-scalar-pullback-representative-factors-factorized).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MonoidalCategory
open CategoryTheory.Functor
attribute [local instance 2000] isNoetherian_of_finite
attribute [local instance 10000] WeilConjectures.sfAbBijective WeilConjectures.sfAbSheafify
  finiteProjection_moduleSheafify finiteProjection_sheafGroth finiteProjection_functorLimits
  finiteProjection_functorColimits finiteProjection_inverseAdditive finiteProjection_inverseLimits
  finiteProjection_inverseColimits finiteProjection_moduleGroth finiteProjection_modulePreadditive
  finiteProjection_moduleFlat
attribute [local instance 10000] WeilConjectures.finiteScalarCountableColimits
  WeilConjectures.finiteScalarTensorTotal WeilConjectures.finiteScalarIntrinsicCountableColimits
  WeilConjectures.finiteScalarFunctorAdditive WeilConjectures.finiteScalarFunctorEquivalence
  WeilConjectures.finiteScalarFixedTensorPreadditive
attribute [local instance 2000] SymmetricCategory.toBraidedCategory Abelian.toPreadditive
attribute [local instance 4000] Preadditive.preadditiveHasZeroMorphisms
attribute [local instance 30000] SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive CategoryTheory.functorCategoryPreadditive
  Preadditive.preadditiveHasZeroMorphisms Functor.preservesZeroMorphisms_of_additive

open CategoryTheory.Limits

private theorem inverse_mate_localization
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions B] [Abelian.HasKInjectiveResolutions D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (a : L ⊣ R) (b : L' ⊣ R') (s : G ⋙ L' ≅ L ⋙ H)
    (t : R ⋙ G ≅ H ⋙ R')
    (d : R.rightDerivedFunctor ⋙ G.mapDerivedCategory ≅
      H.mapDerivedCategory ⋙ R'.rightDerivedFunctor)
    (hs : (mateEquiv a b s.hom) = t.hom)
    (hd : ∀ I : CochainComplex B ℤ,
      G.mapDerivedCategory.map (R.rightDerivedFunctorUnitQ I) ≫
        d.hom.app (DerivedCategory.Q.obj I) ≫
        R'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app I) =
      G.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex t.hom (.up ℤ)).app I) ≫
        R'.rightDerivedFunctorUnitQ ((H.mapHomologicalComplex (.up ℤ)).obj I)) :
    ((mateEquiv a.mapDerivedCategoryRightDerivedAdjunction
      b.mapDerivedCategoryRightDerivedAdjunction).symm d.hom) =
        (Functor.mapDerivedCategorySquareIso s).hom := by
  let m := (mateEquiv a.mapDerivedCategoryRightDerivedAdjunction
    b.mapDerivedCategoryRightDerivedAdjunction
      (Functor.mapDerivedCategorySquareIso s).hom)
  have hm : m = d.hom := by
    ext N
    obtain ⟨I, hI, ⟨eI⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective N
    have : I.IsKInjective := hI
    have hi := AlgebraicGeometry.ProEtale.simple_derived_mate_factors a b s I
    rw [hs] at hi
    have hi' := hd I
    dsimp only [AlgebraicGeometry.ProEtale.restrictionDerivedUnit] at hi
    dsimp only [Functor.rightDerivedFunctorUnitQ, DerivedCategory.quotientCompQhIso,
      HomologicalComplexUpToQuasiIso.quotientCompQhIso,
      Quotient.lift.isLift_hom, Quotient.lift.isLift_inv] at hi'
    erw [R.rightDerivedFunctor.map_id, Category.id_comp, Category.comp_id,
      R'.rightDerivedFunctor.map_id, Category.id_comp, Category.comp_id] at hi'
    have : IsIso (R.rightDerivedFunctorUnitQ I) := by
      rw [Functor.rightDerivedFunctorUnitQ_eq]
      infer_instance
    have heq : m.app (DerivedCategory.Q.obj I) = d.hom.app (DerivedCategory.Q.obj I) := by
      apply (cancel_epi (G.mapDerivedCategory.map (R.rightDerivedFunctorUnitQ I))).mp
      apply (cancel_mono
        (R'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app I))).mp
      have hu : R.rightDerivedFunctorUnitQ I =
          R.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj I) := by
        dsimp only [Functor.rightDerivedFunctorUnitQ, DerivedCategory.quotientCompQhIso,
          HomologicalComplexUpToQuasiIso.quotientCompQhIso,
          Quotient.lift.isLift_hom, Quotient.lift.isLift_inv]
        erw [R.rightDerivedFunctor.map_id, Category.id_comp, Category.comp_id]
      rw [hu]
      simpa only [Category.assoc] using hi.trans hi'.symm
    have hn := m.naturality eI.hom
    have hn' := d.hom.naturality eI.hom
    dsimp only [Functor.comp_map] at hn hn'
    apply (cancel_mono
      ((H.mapDerivedCategory ⋙ R'.rightDerivedFunctor).map eI.hom)).mp
    exact hn.symm.trans ((congrArg (fun z ↦ _ ≫ z) heq).trans hn')
  have he := (mateEquiv a.mapDerivedCategoryRightDerivedAdjunction
    b.mapDerivedCategoryRightDerivedAdjunction).symm_apply_apply
      ((Functor.mapDerivedCategorySquareIso s).hom : TwoSquare _ _ _ _)
  have hm' : (mateEquiv a.mapDerivedCategoryRightDerivedAdjunction
      b.mapDerivedCategoryRightDerivedAdjunction
      (Functor.mapDerivedCategorySquareIso s).hom) =
        (d.hom : TwoSquare _ _ _ _) := by
    refine NatTrans.ext (funext fun N ↦ ?_)
    exact congrArg (fun z ↦ z.app N) hm
  rw [hm'] at he
  exact he

private theorem normalization_transport
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions B] [Abelian.HasKInjectiveResolutions D]
    (R : B ⥤ A) (R' S' : D ⥤ C) (G : A ⥤ C) (H : B ⥤ D)
    [R.Additive] [R'.Additive] [S'.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (h : R' = S') (t : R ⋙ G ≅ H ⋙ S')
    (d : R.rightDerivedFunctor ⋙ G.mapDerivedCategory ≅
      H.mapDerivedCategory ⋙ S'.rightDerivedFunctor)
    (hd : ∀ I : CochainComplex B ℤ,
      G.mapDerivedCategory.map (R.rightDerivedFunctorUnitQ I) ≫
        d.hom.app (DerivedCategory.Q.obj I) ≫
        S'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app I) =
      G.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex t.hom (.up ℤ)).app I) ≫
        S'.rightDerivedFunctorUnitQ ((H.mapHomologicalComplex (.up ℤ)).obj I)) :
    ∀ I : CochainComplex B ℤ,
      G.mapDerivedCategory.map (R.rightDerivedFunctorUnitQ I) ≫
        (d ≪≫ isoWhiskerLeft H.mapDerivedCategory
          (Functor.rightDerivedFunctorNatIso (eqToIso h)).symm).hom.app
            (DerivedCategory.Q.obj I) ≫
        R'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app I) =
      G.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (t ≪≫ isoWhiskerLeft H (eqToIso h).symm).hom (.up ℤ)).app I) ≫
        R'.rightDerivedFunctorUnitQ ((H.mapHomologicalComplex (.up ℤ)).obj I) := by
  subst S'
  simpa [Functor.rightDerivedFunctorNatIso, Functor.rightDerivedFunctorNatTrans] using hd

private theorem inverse_mate_left_iso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L E : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    (a : L ⊣ R) (b : L' ⊣ R') (e : L ≅ E)
    (t : R ⋙ G ⟶ H ⋙ R') :
    ((mateEquiv (a.ofNatIsoLeft e) b).symm t) ≫
        Functor.whiskerRight e.inv H =
      ((mateEquiv a b).symm t) := by
  let s := ((mateEquiv (a.ofNatIsoLeft e) b).symm t)
  have hb : b.ofNatIsoLeft (Iso.refl L') = b := by
    apply Adjunction.ext
    ext N
    simp [Adjunction.ofNatIsoLeft_unit]
  have hm := mate_left_iso a b e (Iso.refl L') s
  rw [hb] at hm
  erw [Functor.whiskerLeft_id, Category.id_comp] at hm
  have hs : (mateEquiv a b
      (TwoSquare.mk _ _ _ _ (s ≫ Functor.whiskerRight e.inv H))) =
        (t : TwoSquare _ _ _ _) := by
    refine NatTrans.ext (funext fun N ↦ ?_)
    have hh := congrArg (fun z ↦ z.app N) hm.symm
    have hr := congrArg (fun z : TwoSquare _ _ _ _ ↦ z.app N)
      ((mateEquiv (a.ofNatIsoLeft e) b).apply_symm_apply t)
    exact hh.trans hr
  exact (
    ((mateEquiv a b).symm_apply_eq.mpr hs.symm)).symm

private theorem square_factors
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (L : A ⥤ B) (L' : C ⥤ D) (G : A ⥤ C) (H : B ⥤ D)
    [L.Additive] [L'.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (s : G ⋙ L' ≅ L ⋙ H) (P : CochainComplex A ℤ) :
    (Functor.mapDerivedCategorySquareIso s).hom.app (DerivedCategory.Q.obj P) ≫
        H.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app P) ≫
        H.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj P) =
      L'.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app P) ≫
        L'.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso s (.up ℤ)).hom.app P) := by
  dsimp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  rw [Category.assoc, Category.assoc,
    Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac]
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_factors G L' P]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rfl

namespace WeilConjectures

/--
The factorized form of the representative equation.  It isolates the ordinary
termwise comparison and the two exact localization factors; the parent theorem
obtains the displayed left-derived counit form by the standard counit
factorization.  This is the derived mate calculation before that final rewrite.

Source: Stacks Tags 07A6 and 0D6E; the localization step in the proof of the
finite scalar inverse-mate representative formula.
(blueprint: lem-sf-finite-scalar-pullback-representative-factors-factorized).
-/
theorem finiteScalarPullback_representative_factors_factorized
    (R : Type u) [CommRing R] [Finite R] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (P : CochainComplex
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} R))) ℤ) :
    (sfIntrinsicDerivedEquivalence X R).functor.map
        ((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R))
          p).leftDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Q.obj P)) ≫
      (sfIntrinsicDerivedEquivalence X R).functor.map
        ((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R))
          p).mapDerivedCategoryFactors.hom.app P) ≫
      (sfIntrinsicModuleEquivalence X R).functor.mapDerivedCategoryFactors.hom.app
        (((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).mapHomologicalComplex
          (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((mapHomologicalComplexCompIso (finiteScalarOrdinaryPullbackComparison R p)
          (.up ℤ)).inv.app P) =
    (finiteScalarPullbackComparison R p).inv.app (DerivedCategory.Q.obj P) ≫
      (proEtaleConstantRingDerivedPullback R p).map
        ((sfIntrinsicModuleEquivalence Y R).functor.mapDerivedCategoryFactors.hom.app P) ≫
      (proEtaleRingDerivedPullbackFactors p (proEtaleConstantRing Y R)
        (proEtaleConstantRing X R) (proEtaleConstantRingComparison p R)).hom.app
          (((sfIntrinsicModuleEquivalence Y R).functor.mapHomologicalComplex (.up ℤ)).obj P) := by
  let L := ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p
  let L' := proEtaleRingModulePullback p (proEtaleConstantRing Y R)
    (proEtaleConstantRing X R) (proEtaleConstantRingComparison p R)
  let G := (sfIntrinsicModuleEquivalence Y R).functor
  let H := (sfIntrinsicModuleEquivalence X R).functor
  let a := ProEtale.upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} R)) p
  let b := proEtaleRingModuleAdjunction p (proEtaleConstantRing Y R)
    (proEtaleConstantRing X R) (proEtaleConstantRingComparison p R)
  let s := finiteScalarOrdinaryPullbackComparison R p
  let hg := finiteScalarConstantPushforward_eq R p
  let t := (sfIntrinsicDirectImageComparison p R).symm ≪≫
    isoWhiskerLeft H (eqToIso hg).symm
  let d := (sfIntrinsicDerivedDirectImageComparison p R).symm ≪≫
    isoWhiskerLeft H.mapDerivedCategory
      (Functor.rightDerivedFunctorNatIso (eqToIso hg)).symm
  have hs : (mateEquiv a b s.hom) = t.hom := by
    unfold s finiteScalarOrdinaryPullbackComparison
    change (mateEquiv a b ((mateEquiv a b).symm
      (TwoSquare.mk _ _ _ _ t.hom))) = t.hom
    exact ((mateEquiv a b).apply_symm_apply
      (TwoSquare.mk _ _ _ _ t.hom))
  have hd := normalization_transport
    (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p)
    (proEtaleConstantRingPushforward R p) (proEtaleConstantModuleDirectImage p R) G H hg
    (sfIntrinsicDirectImageComparison p R).symm
    (sfIntrinsicDerivedDirectImageComparison p R).symm
    (sfIntrinsicDerivedDirectImageComparison_inv_unitQ_factors R p)
  have he := inverse_mate_localization a b s t d hs hd
  have hα : (finiteScalarPullbackComparison R p).hom ≫
      Functor.whiskerRight L.leftDerivedFunctorIsoMapDerivedCategory.hom H.mapDerivedCategory =
        (Functor.mapDerivedCategorySquareIso s).hom := by
    change ((mateEquiv
      (ProEtale.derivedUpperStarLowerStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1} R)) p)
      b.mapDerivedCategoryRightDerivedAdjunction).symm d.hom) ≫
      Functor.whiskerRight L.leftDerivedFunctorIsoMapDerivedCategory.hom H.mapDerivedCategory = _
    rw [AlgebraicGeometry.ProEtale.restriction_derived_adj_eq]
    exact (inverse_mate_left_iso a.mapDerivedCategoryRightDerivedAdjunction
      b.mapDerivedCategoryRightDerivedAdjunction
      L.leftDerivedFunctorIsoMapDerivedCategory.symm d.hom).trans he
  have hαP := congrArg (fun z ↦ z.app (DerivedCategory.Q.obj P)) hα
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app] at hαP
  have hf := square_factors L L' G H s P
  have key := congrArg (fun z ↦ z ≫ DerivedCategory.Q.map
      ((mapHomologicalComplexCompIso s (.up ℤ)).inv.app P))
    ((congrArg (fun z ↦ z ≫ H.mapDerivedCategory.map
      (L.mapDerivedCategoryFactors.hom.app P) ≫
      H.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj P))
        hαP).trans hf)
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app] at key
  erw [DerivedCategory.Q.map_id, Category.comp_id] at key
  have h1 : (sfIntrinsicDerivedEquivalence X R).functor.map
      (L.leftDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Q.obj P)) =
      H.mapDerivedCategory.map
        (L.leftDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Q.obj P)) := by
    rfl
  have h2 : (sfIntrinsicDerivedEquivalence X R).functor.map
      (L.mapDerivedCategoryFactors.hom.app P) =
      H.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app P) := by
    rfl
  apply (cancel_epi
    ((finiteScalarPullbackComparison R p).hom.app (DerivedCategory.Q.obj P))).mp
  erw [h1, h2]
  simpa only [Category.assoc, Iso.hom_inv_id_app_assoc, s, L, L', G, H,
    proEtaleConstantRingDerivedPullback, proEtaleConstantRingPullback,
    proEtaleRingDerivedPullbackFactors] using key

end WeilConjectures
