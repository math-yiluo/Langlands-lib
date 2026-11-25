/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FiniteProjectionFixedCoordinates
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicDirectImageUnitNormalization
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction

/-! # Transport for the direct counit in fixed coefficients -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.privateModule false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
section
universe a b c d va vb vc vd
variable {A : Type a} {B : Type b} {A' : Type c} {B' : Type d}
  [Category.{va} A] [Category.{vb} B] [Category.{vc} A'] [Category.{vd} B']

private def conjugateRight (E : A ≌ A') (J : B ≌ B')
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R) (R' : B' ⥤ A')
    (e : J.functor ⋙ R' ≅ R ⋙ E.functor) :
    E.inverse ⋙ L ⋙ J.functor ⊣ R' :=
  ((E.symm.toAdjunction.comp adj).comp J.toAdjunction).ofNatIsoRight
    (Functor.isoWhiskerLeft _ e.symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight J.counitIso _ ≪≫ Functor.leftUnitor _)

private theorem conjugateRight_counit (E : A ≌ A') (J : B ≌ B')
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R) (R' : B' ⥤ A')
    (e : J.functor ⋙ R' ≅ R ⋙ E.functor) (N : B) :
    J.functor.map (adj.counit.app N) =
      (E.funInvIdAssoc (L ⋙ J.functor)).inv.app (R.obj N) ≫
        (E.inverse ⋙ L ⋙ J.functor).map (e.inv.app N) ≫
        (conjugateRight E J adj R' e).counit.app (J.functor.obj N) := by
  simp only [conjugateRight, Adjunction.ofNatIsoRight_counit,
    Adjunction.comp_counit_app, Equivalence.toAdjunction_counit,
    Equivalence.symm_counit, Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.leftUnitor_inv_app,
    Equivalence.funInvIdAssoc_inv_app, Functor.comp_map, CategoryTheory.Functor.map_comp,
    Category.assoc]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp,
    Equivalence.counitInv_app_functor]
  simp only [← CategoryTheory.Functor.map_comp, ← Category.assoc]
  simp only [Category.assoc]
  have he := e.hom.naturality (J.unit.app N)
  dsimp only [Functor.comp_map] at he
  erw [he]
  simp only [← Category.assoc]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app_assoc]
  have hu := E.unit.naturality (R.map (J.unit.app N))
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  erw [← Category.assoc, ← hu]
  simp only [Category.assoc, Equivalence.unit, Equivalence.unitInv]
  erw [Iso.hom_inv_id_app, Category.comp_id]
  erw [adj.counit.naturality]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc, Functor.id_map,
    Functor.id_obj]
  erw [J.functor_unitIso_comp, Category.comp_id]

private theorem coordinate_counit
    (E : A ≌ A') (J : B ≌ B') {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R)
    {Li : A' ⥤ B'} {Ri : B' ⥤ A'} (adji : Li ⊣ Ri)
    (o : Li ≅ E.inverse ⋙ L ⋙ J.functor)
    (l : L ⋙ J.functor ≅ E.functor ⋙ Li)
    (c : J.functor ⋙ Ri ≅ R ⋙ E.functor)
    (hc : ∀ N : B, J.functor.map (adj.counit.app N) =
      l.hom.app (R.obj N) ≫ Li.map (c.inv.app N) ≫
        adji.counit.app (J.functor.obj N))
    (ho : ∀ H : A', o.hom.app H ≫ l.hom.app (E.inverse.obj H) =
      Li.map (E.counitInv.app H)) (M : B') :
    J.inverse.map (o.hom.app (Ri.obj M)) ≫
      J.unitInv.app (L.obj (E.inverse.obj (Ri.obj M))) ≫
      L.map (E.inverse.map (Ri.map (J.counitInv.app M) ≫
        c.hom.app (J.inverse.obj M)) ≫ E.unitInv.app (R.obj (J.inverse.obj M))) ≫
      adj.counit.app (J.inverse.obj M) = J.inverse.map (adji.counit.app M) := by
  let delta := E.inverse.map (Ri.map (J.counitInv.app M) ≫
    c.hom.app (J.inverse.obj M)) ≫ E.unitInv.app (R.obj (J.inverse.obj M))
  have hd : E.counitInv.app (Ri.obj M) ≫ E.functor.map delta ≫
      c.inv.app (J.inverse.obj M) = Ri.map (J.counitInv.app M) := by
    dsimp only [delta]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    erw [E.counitInv_naturality_assoc, E.counitInv_naturality_assoc]
    erw [Equivalence.counitInv_app_functor]
    simp only [← E.functor.map_comp_assoc, Equivalence.unit, Equivalence.unitInv,
      Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
    erw [Category.comp_id]
  apply J.functor.map_injective
  change J.functor.map (J.inverse.map (o.hom.app (Ri.obj M)) ≫
    J.unitInv.app _ ≫ L.map delta ≫ adj.counit.app _) =
    J.functor.map (J.inverse.map (adji.counit.app M))
  simp only [CategoryTheory.Functor.map_comp]
  rw [← J.counit_app_functor]
  erw [J.counit_naturality_assoc]
  rw [hc]
  erw [l.hom.naturality_assoc]
  rw [reassoc_of% ho (Ri.obj M)]
  simp only [Functor.comp_map, ← Li.map_comp_assoc]
  rw [hd]
  erw [adji.counit.naturality]
  exact (J.fun_inv_map _ _ _).symm

private theorem coordinate_counit_comp
    (E : A ≌ A') (J : B ≌ B')
    (L Lf : A ⥤ B) (R : B ⥤ A) (Li : A' ⥤ B') (Ri : B' ⥤ A')
    (adj : L ⊣ R) (adjf : Lf ⊣ R) (adji : Li ⊣ Ri)
    (e : Lf ≅ L) (o : Li ≅ E.inverse ⋙ L ⋙ J.functor)
    (b : J.functor ⋙ Ri ≅ R ⋙ E.functor)
    (ha : ∀ M, adj.counit.app M = e.inv.app (R.obj M) ≫ adjf.counit.app M)
    (M : B') (N : A') (P : B') (p : P ⟶ Li.obj N) (t : N ⟶ Ri.obj M)
    (ht : J.inverse.map (o.hom.app (Ri.obj M)) ≫
      J.unitInv.app (L.obj (E.inverse.obj (Ri.obj M))) ≫
      L.map (E.inverse.map (Ri.map (J.counitInv.app M) ≫
        b.hom.app (J.inverse.obj M)) ≫ E.unitInv.app (R.obj (J.inverse.obj M))) ≫
      adj.counit.app (J.inverse.obj M) = J.inverse.map (adji.counit.app M)) :
    J.inverse.map (p ≫ o.hom.app N) ≫ J.unitInv.app _ ≫
      e.inv.app (E.inverse.obj N) ≫
      Lf.map (E.inverse.map (t ≫ Ri.map (J.counitInv.app M) ≫
        b.hom.app (J.inverse.obj M)) ≫ E.unitInv.app (R.obj (J.inverse.obj M))) ≫
      adjf.counit.app (J.inverse.obj M) =
    J.inverse.map (p ≫ Li.map t ≫ adji.counit.app M) := by
  let delta := E.inverse.map (Ri.map (J.counitInv.app M) ≫
    b.hom.app (J.inverse.obj M)) ≫ E.unitInv.app (R.obj (J.inverse.obj M))
  let rho : Li ⋙ J.inverse ⟶ E.inverse ⋙ L :=
    Functor.whiskerRight o.hom J.inverse ≫ Functor.whiskerLeft (E.inverse ⋙ L) J.unitInv
  have ht' : rho.app (Ri.obj M) ≫ L.map delta ≫ adj.counit.app (J.inverse.obj M) =
      J.inverse.map (adji.counit.app M) := by
    simpa only [rho, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.comp_obj, Category.assoc] using ht
  have hm : rho.app N ≫ L.map (E.inverse.map t ≫ delta) ≫
      adj.counit.app (J.inverse.obj M) = J.inverse.map (Li.map t ≫ adji.counit.app M) := by
    have hn := rho.naturality t
    dsimp only [Functor.comp_map] at hn
    rw [L.map_comp, Category.assoc, ← reassoc_of% hn, ht']
    exact (J.inverse.map_comp _ _).symm
  have hd : E.inverse.map (t ≫ Ri.map (J.counitInv.app M) ≫
      b.hom.app (J.inverse.obj M)) ≫ E.unitInv.app (R.obj (J.inverse.obj M)) =
      E.inverse.map t ≫ delta := by
    simp only [delta, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [hd]
  have hn := e.inv.naturality (E.inverse.map t ≫ delta)
  rw [← reassoc_of% hn, ← ha]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  dsimp only [rho, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.comp_obj] at hm
  simpa only [CategoryTheory.Functor.map_comp, Category.assoc] using
    congrArg (fun z => J.inverse.map p ≫ z) hm

variable [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory A'] [HasDerivedCategory B']

private theorem derivedEquivalence_counit_factors (E : A ≌ A')
    [E.functor.Additive] [E.inverse.Additive] (H : HomotopyCategory A' (.up ℤ)) :
    E.functor.mapDerivedCategory.map (E.inverse.mapDerivedCategoryFactorsh.hom.app H) ≫
      E.functor.mapDerivedCategoryFactorsh.hom.app
        ((E.inverse.mapHomotopyCategory (.up ℤ)).obj H) ≫
      DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory E.counitIso.hom (.up ℤ)).app H) =
    E.mapDerivedCategory.counitIso.hom.app (DerivedCategory.Qh.obj H) := by
  change _ = (Functor.mapDerivedCategoryCompIso E.inverse E.functor).hom.app _ ≫
    (Functor.mapDerivedCategoryNatIso E.counitIso).hom.app _ ≫
    (Functor.mapDerivedCategoryIdIso A').hom.app _
  rw [Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj]
  rw [Functor.mapDerivedCategoryNatIso_fach]
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_factorsh]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

private theorem derivedEquivalence_counitInv_factors (E : A ≌ A')
    [E.functor.Additive] [E.inverse.Additive] (H : HomotopyCategory A' (.up ℤ)) :
    E.mapDerivedCategory.counitIso.inv.app (DerivedCategory.Qh.obj H) ≫
      E.functor.mapDerivedCategory.map (E.inverse.mapDerivedCategoryFactorsh.hom.app H) ≫
      E.functor.mapDerivedCategoryFactorsh.hom.app
        ((E.inverse.mapHomotopyCategory (.up ℤ)).obj H) =
    DerivedCategory.Qh.map
      ((NatTrans.mapHomotopyCategory E.counitIso.inv (.up ℤ)).app H) := by
  apply (cancel_epi (E.mapDerivedCategory.counitIso.hom.app
    (DerivedCategory.Qh.obj H))).mp
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← derivedEquivalence_counit_factors E H]
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, ← NatTrans.comp_app,
    ← NatTrans.mapHomotopyCategory_comp, Iso.hom_inv_id,
    NatTrans.mapHomotopyCategory_id, NatTrans.id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

-- The published exact-square proof is used with independent derived hom universes.
private theorem canonicalCounit (F : A ⥤ B) [F.Additive]
    [Abelian.HasKInjectiveResolutions A] (L : B ⥤ A) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (adj : L ⊣ F) (I : CochainComplex A ℤ) :
    L.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ I) ≫
        adj.mapDerivedCategoryRightDerivedAdjunction.counit.app (DerivedCategory.Q.obj I) =
      L.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).counit.app I) := by
  have h := (adj.mapHomotopyCategory (.up ℤ)).derivedε_fac_app
    (HomotopyCategory.quasiIso A (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
    F.rightDerivedFunctorUnit ((HomotopyCategory.quotient A (.up ℤ)).obj I)
  change L.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app _) ≫
    adj.mapDerivedCategoryRightDerivedAdjunction.counit.app _ =
    L.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient B (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj I)) ≫ _ at h
  simp only [Functor.mapDerivedCategoryFactorsh_hom_app,
    Adjunction.mapHomotopyCategory_counit_app_quotient, Functor.rightDerivedFunctorUnitQ,
    DerivedCategory.quotientCompQhIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    CategoryTheory.Functor.map_comp, Category.assoc] at h ⊢
  simp only [Quotient.lift.isLift_hom] at h ⊢
  repeat erw [CategoryTheory.Functor.map_id] at h
  repeat erw [CategoryTheory.Functor.map_id]
  repeat erw [Category.id_comp] at h
  repeat erw [Category.id_comp]
  exact h

private theorem squareFactors
    (Fp : B' ⥤ A') (F : B ⥤ A) (r : A' ⥤ A) (s : B' ⥤ B)
    [Fp.Additive] [F.Additive] [r.Additive] [s.Additive]
    [PreservesFiniteLimits Fp] [PreservesFiniteColimits Fp]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits r] [PreservesFiniteColimits r]
    [PreservesFiniteLimits s] [PreservesFiniteColimits s]
    (hF : Fp ⋙ r ≅ s ⋙ F) (K : CochainComplex B' ℤ) :
    (Functor.mapDerivedCategorySquareIso hF).hom.app (DerivedCategory.Q.obj K) ≫
        F.mapDerivedCategory.map (s.mapDerivedCategoryFactors.hom.app K) ≫
        F.mapDerivedCategoryFactors.hom.app ((s.mapHomologicalComplex (.up ℤ)).obj K) =
      r.mapDerivedCategory.map (Fp.mapDerivedCategoryFactors.hom.app K) ≫
        r.mapDerivedCategoryFactors.hom.app ((Fp.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex hF (.up ℤ)).hom.app K) := by
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso Fp r).inv.app
    (DerivedCategory.Q.obj K))).mp
  dsimp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  simp only [← Category.assoc]
  simp only [Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac,
    Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc]
  simp only [Iso.inv_hom_id_app_assoc]
  rfl

private theorem squareCounit
    (F : A ⥤ B) (G : A' ⥤ B') (x : A ⥤ A') (y : B ⥤ B')
    [F.Additive] [G.Additive] [x.Additive] [y.Additive]
    [PreservesFiniteLimits x] [PreservesFiniteColimits x]
    [PreservesFiniteLimits y] [PreservesFiniteColimits y]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions A']
    (L : B ⥤ A) (Lp : B' ⥤ A') [L.Additive] [Lp.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits Lp] [PreservesFiniteColimits Lp]
    (adj : L ⊣ F) (adjp : Lp ⊣ G)
    (l : L ⋙ x ≅ y ⋙ Lp) (c : F ⋙ y ≅ x ⋙ G)
    (hc : ∀ N : A, x.map (adj.counit.app N) =
      l.hom.app (F.obj N) ≫ Lp.map (c.hom.app N) ≫ adjp.counit.app (x.obj N))
    (b : F.rightDerivedFunctor ⋙ y.mapDerivedCategory ≅
      x.mapDerivedCategory ⋙ G.rightDerivedFunctor)
    (hb : ∀ M : CochainComplex A ℤ,
      y.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ M) ≫
        b.hom.app (DerivedCategory.Q.obj M) ≫
        G.rightDerivedFunctor.map (x.mapDerivedCategoryFactors.hom.app M) =
      y.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj M) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app M) ≫
        G.rightDerivedFunctorUnitQ ((x.mapHomologicalComplex (.up ℤ)).obj M))
    (N : DerivedCategory A) :
    x.mapDerivedCategory.map
        (adj.mapDerivedCategoryRightDerivedAdjunction.counit.app N) =
      (Functor.mapDerivedCategorySquareIso l).hom.app (F.rightDerivedFunctor.obj N) ≫
        Lp.mapDerivedCategory.map (b.hom.app N) ≫
        adjp.mapDerivedCategoryRightDerivedAdjunction.counit.app (x.mapDerivedCategory.obj N) := by
  let α := Functor.mapDerivedCategorySquareIso l
  let d := adj.mapDerivedCategoryRightDerivedAdjunction
  let dp := adjp.mapDerivedCategoryRightDerivedAdjunction
  let left : F.rightDerivedFunctor ⋙ L.mapDerivedCategory ⋙ x.mapDerivedCategory ⟶
      x.mapDerivedCategory := Functor.whiskerRight d.counit x.mapDerivedCategory
  let right : F.rightDerivedFunctor ⋙ L.mapDerivedCategory ⋙ x.mapDerivedCategory ⟶
      x.mapDerivedCategory := Functor.whiskerLeft F.rightDerivedFunctor α.hom ≫
        Functor.whiskerRight b.hom Lp.mapDerivedCategory ≫
        Functor.whiskerLeft x.mapDerivedCategory dp.counit
  have hI (I : CochainComplex A ℤ) (hI : I.IsKInjective) :
      left.app (DerivedCategory.Q.obj I) = right.app (DerivedCategory.Q.obj I) := by
    have := hI
    have : IsIso (F.rightDerivedFunctorUnitQ I) := by
      rw [F.rightDerivedFunctorUnitQ_eq]
      infer_instance
    apply (cancel_epi (x.mapDerivedCategory.map
      (L.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ I)))).mp
    apply (cancel_mono (x.mapDerivedCategoryFactors.hom.app I)).mp
    change (x.mapDerivedCategory.map (L.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ I)) ≫
      x.mapDerivedCategory.map (d.counit.app (DerivedCategory.Q.obj I))) ≫ _ =
      (x.mapDerivedCategory.map (L.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ I)) ≫
        α.hom.app (F.rightDerivedFunctor.obj (DerivedCategory.Q.obj I)) ≫
        Lp.mapDerivedCategory.map (b.hom.app (DerivedCategory.Q.obj I)) ≫
        dp.counit.app (x.mapDerivedCategory.obj (DerivedCategory.Q.obj I))) ≫ _
    rw [← CategoryTheory.Functor.map_comp, canonicalCounit F L adj I,
      CategoryTheory.Functor.map_comp, Category.assoc]
    erw [x.mapDerivedCategoryFactors.hom.naturality
      ((adj.mapHomologicalComplex (.up ℤ)).counit.app I)]
    have hn := α.hom.naturality (F.rightDerivedFunctorUnitQ I)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hn
    have hcn := dp.counit.naturality (x.mapDerivedCategoryFactors.hom.app I)
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map] at hcn
    simp only [Category.assoc]
    rw [reassoc_of% hn, ← hcn]
    simp only [← CategoryTheory.Functor.map_comp_assoc]
    rw [hb I]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    rw [canonicalCounit G Lp adjp _]
    erw [reassoc_of% (Lp.mapDerivedCategoryFactors.hom.naturality
      ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app I))]
    erw [reassoc_of% (squareFactors L Lp x y l
      ((F.mapHomologicalComplex (.up ℤ)).obj I))]
    simp only [← DerivedCategory.Q.map_comp]
    congr 2
    apply DerivedCategory.Q.congr_map
    ext n
    exact hc (I.X n)
  change left.app N = right.app N
  obtain ⟨I, hIi, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective N
  apply (cancel_mono (x.mapDerivedCategory.map e.hom)).mp
  rw [← left.naturality, ← right.naturality, hI I hIi]

variable (E : A ≌ A') [E.functor.Additive] [E.inverse.Additive]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

private def liftUnitIso :
    F.mapDerivedCategory ≅ E.functor.mapDerivedCategory ⋙
      (E.inverse ⋙ F).mapDerivedCategory :=
  Functor.mapDerivedCategoryNatIso (E.funInvIdAssoc F).symm ≪≫
    (Functor.mapDerivedCategoryCompIso E.functor (E.inverse ⋙ F)).symm

private theorem liftUnitIso_factors (H : HomotopyCategory A (.up ℤ)) :
    (liftUnitIso E F).hom.app (DerivedCategory.Qh.obj H) ≫
      (E.inverse ⋙ F).mapDerivedCategory.map (E.functor.mapDerivedCategoryFactorsh.hom.app H) ≫
      (E.inverse ⋙ F).mapDerivedCategoryFactorsh.hom.app
        ((E.functor.mapHomotopyCategory (.up ℤ)).obj H) =
    F.mapDerivedCategoryFactorsh.hom.app H ≫ DerivedCategory.Qh.map
      ((NatTrans.mapHomotopyCategory (E.funInvIdAssoc F).inv (.up ℤ)).app H) := by
  dsimp only [liftUnitIso, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom]
  rw [Category.assoc, Functor.mapDerivedCategoryCompIso_hom_app_factorsh,
    Functor.mapDerivedCategoryNatIso_fach]
  rfl

private theorem derived_unit_counit_coherence :
    (Functor.mapDerivedCategoryCompIso E.inverse F).inv ≫
      Functor.whiskerLeft E.inverse.mapDerivedCategory (liftUnitIso E F).hom =
    Functor.whiskerRight E.mapDerivedCategory.counitIso.inv
      (E.inverse ⋙ F).mapDerivedCategory := by
  refine Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso A' (.up ℤ)) (fun H => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  let I := (E.inverse.mapHomotopyCategory (.up ℤ)).obj H
  let T := (E.inverse ⋙ F).mapDerivedCategory
  apply (cancel_mono (T.map
    (E.functor.mapDerivedCategory.map (E.inverse.mapDerivedCategoryFactorsh.hom.app H)) ≫
    T.map (E.functor.mapDerivedCategoryFactorsh.hom.app I) ≫
    (E.inverse ⋙ F).mapDerivedCategoryFactorsh.hom.app
      ((E.functor.mapHomotopyCategory (.up ℤ)).obj I))).mp
  simp only [Category.assoc]
  have hn := (liftUnitIso E F).hom.naturality
    (E.inverse.mapDerivedCategoryFactorsh.hom.app H)
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn, liftUnitIso_factors]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factorsh_assoc]
  dsimp only [T, I]
  simp only [← (E.inverse ⋙ F).mapDerivedCategory.map_comp_assoc]
  rw [derivedEquivalence_counitInv_factors]
  erw [(E.inverse ⋙ F).mapDerivedCategoryFactorsh.hom.naturality]
  dsimp only [Functor.comp_map]
  change (E.inverse ⋙ F).mapDerivedCategoryFactorsh.hom.app H ≫
    DerivedCategory.Qh.map _ = (E.inverse ⋙ F).mapDerivedCategoryFactorsh.hom.app H ≫
      DerivedCategory.Qh.map _
  apply congrArg (fun z => (E.inverse ⋙ F).mapDerivedCategoryFactorsh.hom.app H ≫
    DerivedCategory.Qh.map z)
  obtain ⟨Hc, rfl⟩ := HomotopyCategory.quotient_obj_surjective H
  simp only [NatTrans.mapHomotopyCategory_app]
  rw [Functor.mapHomotopyCategory_map]
  apply (HomotopyCategory.quotient B (.up ℤ)).congr_map
  ext i
  simp only [NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplex_map_f,
    Equivalence.funInvIdAssoc_inv_app, Functor.comp_map]
  dsimp only [Functor.mapHomotopyCategory, Quotient.lift, Functor.comp_obj]
  simp only [HomotopyCategory.quotient_obj_as, Functor.mapHomologicalComplex_obj_X]
  exact congrArg F.map (E.unit_app_inverse (Hc.X i))

private theorem derived_square_coherence
    (G : B ⥤ B') [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (H : DerivedCategory A') :
    ((Functor.mapDerivedCategoryCompIso E.inverse (F ⋙ G)).symm ≪≫
      Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso F G).symm).hom.app H ≫
      (Functor.mapDerivedCategorySquareIso (E.funInvIdAssoc (F ⋙ G)).symm).hom.app
        (E.inverse.mapDerivedCategory.obj H) =
    (E.inverse ⋙ F ⋙ G).mapDerivedCategory.map
      (E.mapDerivedCategory.counitInv.app H) := by
  have h := congr_app (derived_unit_counit_coherence E (F ⋙ G)) H
  dsimp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    liftUnitIso, Functor.whiskerRight_app] at h ⊢
  simpa only [Category.assoc, Iso.inv_hom_id_app_assoc] using h

end

private theorem exactProEtaleAdjunction_eq (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
      ).mapDerivedCategoryRightDerivedAdjunction =
    (ProEtale.derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).ofNatIsoLeft
      (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) f) := by
  refine ((ProEtale.upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).mapHomotopyCategory (.up ℤ)
    ).derived_eq_ofNatIsoLeft (HomotopyCategory.quasiIso _ (.up ℤ))
    (HomotopyCategory.quasiIso _ (.up ℤ)) _ _ _
    (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).symm ?_
  ext H
  simp only [ProEtale.leftDerivedUpperStarIsoMapDerivedCategory, Iso.symm_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [← (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
    ).leftDerivedFunctorIsoMapDerivedCategory_hom_fac]
  rw [NatTrans.comp_app, Functor.whiskerLeft_app, Iso.inv_hom_id_app_assoc]

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  AlgebraicGeometry.Scheme.sfIntrinsicModuleEquivalence
attribute [local implicit_reducible] Equivalence.mapDerivedCategory
  AlgebraicGeometry.Scheme.sfIntrinsicDerivedEquivalence

/-- The normalized coefficient square preserves the intrinsic derived counit, before
any restriction to the specified finite constructible operations. -/
private theorem intrinsicDerivedCounit_coordinates (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : proEtaleDerivedCategory X A) :
  let EX := sfIntrinsicModuleEquivalence X A
  let EY := sfIntrinsicModuleEquivalence Y A
  let L := ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
  let R := ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
  let Ri := proEtaleConstantModuleDirectImage f A
  let adj := ProEtale.upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
  let adji := sfIntrinsicConstantModuleAdjunction f A
  let b := sfIntrinsicDerivedDirectImageComparison f A
  let o := (Functor.mapDerivedCategoryCompIso EY.inverse (L ⋙ EX.functor)).symm ≪≫
    Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso L EX.functor).symm
  let RX := EX.mapDerivedCategory
  let RY := EY.mapDerivedCategory
  RX.inverse.map (o.hom.app (Ri.rightDerivedFunctor.obj M)) ≫
    RX.unitInv.app (L.mapDerivedCategory.obj
      (RY.inverse.obj (Ri.rightDerivedFunctor.obj M))) ≫
    L.mapDerivedCategory.map (RY.inverse.map
      (Ri.rightDerivedFunctor.map (RX.counitInv.app M) ≫ b.hom.app (RX.inverse.obj M)) ≫
      RY.unitInv.app (R.rightDerivedFunctor.obj (RX.inverse.obj M))) ≫
    adj.mapDerivedCategoryRightDerivedAdjunction.counit.app (RX.inverse.obj M) =
    RX.inverse.map (adji.mapDerivedCategoryRightDerivedAdjunction.counit.app M) := by
  let EX := sfIntrinsicModuleEquivalence X A
  let EY := sfIntrinsicModuleEquivalence Y A
  let L := ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
  let R := ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
  let Li := sfIntrinsicPullback A f
  let Ri := proEtaleConstantModuleDirectImage f A
  let adj := ProEtale.upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
  let adji := sfIntrinsicConstantModuleAdjunction f A
  let l := (EY.funInvIdAssoc (L ⋙ EX.functor)).symm
  let c := sfIntrinsicDirectImageComparison f A
  let b := sfIntrinsicDerivedDirectImageComparison f A
  have hc : ∀ N, EX.functor.map (adj.counit.app N) =
      l.hom.app (R.obj N) ≫ Li.map (c.inv.app N) ≫
        adji.counit.app (EX.functor.obj N) :=
    fun N => conjugateRight_counit EY EX adj Ri c N
  have h := squareCounit R Ri EX.functor EY.functor
    L Li adj adji l c.symm hc b.symm
    (sfIntrinsicDerivedDirectImageComparison_inv_unitQ_factors A f)
  let o := (Functor.mapDerivedCategoryCompIso EY.inverse (L ⋙ EX.functor)).symm ≪≫
    Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso L EX.functor).symm
  have ho := derived_square_coherence EY L EX.functor
  have ht := coordinate_counit EY.mapDerivedCategory EX.mapDerivedCategory
    adj.mapDerivedCategoryRightDerivedAdjunction
    adji.mapDerivedCategoryRightDerivedAdjunction o
    (Functor.mapDerivedCategorySquareIso l) b h ho M
  exact ht

namespace WeilConjectures.CompactSupportFiniteProjection

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

end WeilConjectures.CompactSupportFiniteProjection
