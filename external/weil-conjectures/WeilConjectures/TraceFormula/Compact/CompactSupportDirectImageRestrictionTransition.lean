/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Compact.CompactSupportSystemEvaluationDiagram
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Restriction-form transition of derived direct image

Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks 03DI, 03DJ, 07A4, 0941.
This module specializes the ordinary system calculus to the actual pro-etale functors.
(blueprint: lem-trf-direct-image-restriction-transition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local irreducible] CategoryTheory.Functor.rightDerivedFunctor

universe t u c₁ c₂ d₁ d₂ v

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures

section Normalization

variable {C : Type c₁} {C' : Type c₂} {A : Type d₁} {A' : Type d₂}
  [Category.{v} C] [Category.{v} C'] [Category.{v} A] [Category.{v} A']
  [Abelian C] [Abelian C'] [Abelian A] [Abelian A']
  [HasDerivedCategory C] [HasDerivedCategory C']
  [HasDerivedCategory A] [HasDerivedCategory A']
  [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions C']
  (G : C ⥤ A) (G' : C' ⥤ A') (H : C ⥤ C') (K : A ⥤ A')
  [G.Additive] [G'.Additive] [H.Additive] [K.Additive]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits K] [PreservesFiniteColimits K]
  (a : H ⋙ G' ≅ G ⋙ K)
  (d : H.mapDerivedCategory ⋙ G'.rightDerivedFunctor ≅
    G.rightDerivedFunctor ⋙ K.mapDerivedCategory)

private theorem normalized_unit_kinjective
    (hd : CompactSupportDerivedSquareNormalization G G' H K a d)
    (J : CochainComplex C ℤ) [J.IsKInjective] :
    G'.rightDerivedFunctorUnitQ ((H.mapHomologicalComplex (.up ℤ)).obj J) ≫
        G'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.inv.app J) ≫
        d.hom.app (DerivedCategory.Q.obj J) =
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex a (.up ℤ)).hom.app J) ≫
        K.mapDerivedCategoryFactors.inv.app ((G.mapHomologicalComplex (.up ℤ)).obj J) ≫
        K.mapDerivedCategory.map (G.rightDerivedFunctorUnitQ J) := by
  obtain ⟨I, hI, r, _, hr⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective
    ((H.mapHomologicalComplex (.up ℤ)).obj J)
  let := hI
  let := hr
  let s := K.mapDerivedCategory.map (G.rightDerivedFunctorObjQIso J).hom ≫
    K.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj J) ≫
    DerivedCategory.Q.map ((NatIso.mapHomologicalComplex a (.up ℤ)).inv.app J) ≫
    DerivedCategory.Q.map ((G'.mapHomologicalComplex (.up ℤ)).map r)
  have hs : IsIso (d.hom.app (DerivedCategory.Q.obj J) ≫ s) := by
    change IsIso (_ ≫ _ ≫ _ ≫ _ ≫ _)
    rw [hd J I r]
    infer_instance
  have : IsIso s := IsIso.of_isIso_comp_left (d.hom.app _) s
  apply (cancel_mono s).mp
  dsimp only [s]
  simp only [Category.assoc]
  rw [hd J I r]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc]
  erw [← G'.rightDerivedFunctorUnitQ_naturality_assoc r,
    G'.rightDerivedFunctorUnitQ_eq I]
  simp only [Functor.rightDerivedFunctorUnitQ_eq, ← Functor.map_comp, Iso.inv_hom_id]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
  erw [← DerivedCategory.Q.map_comp, Iso.hom_inv_id_app_assoc]
  erw [Category.comp_id]

private def cochainDerivedUnit {B B' : Type*} [Category B] [Category B']
    [Abelian B] [Abelian B'] [HasDerivedCategory B] [HasDerivedCategory B']
    [Abelian.HasKInjectiveResolutions B] (F : B ⥤ B') [F.Additive] :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor where
  app := F.rightDerivedFunctorUnitQ
  naturality _ _ f := F.rightDerivedFunctorUnitQ_naturality f

private theorem normalized_unit
    (hd : CompactSupportDerivedSquareNormalization G G' H K a d)
    (J : CochainComplex C ℤ) :
    G'.rightDerivedFunctorUnitQ ((H.mapHomologicalComplex (.up ℤ)).obj J) ≫
        G'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.inv.app J) ≫
        d.hom.app (DerivedCategory.Q.obj J) =
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex a (.up ℤ)).hom.app J) ≫
        K.mapDerivedCategoryFactors.inv.app ((G.mapHomologicalComplex (.up ℤ)).obj J) ≫
        K.mapDerivedCategory.map (G.rightDerivedFunctorUnitQ J) := by
  let α := Functor.whiskerLeft (H.mapHomologicalComplex (.up ℤ)) (cochainDerivedUnit G') ≫
    Functor.whiskerRight H.mapDerivedCategoryFactors.inv G'.rightDerivedFunctor ≫
    Functor.whiskerLeft DerivedCategory.Q d.hom
  let β := Functor.whiskerRight (NatIso.mapHomologicalComplex a (.up ℤ)).hom
      DerivedCategory.Q ≫
    Functor.whiskerLeft (G.mapHomologicalComplex (.up ℤ)) K.mapDerivedCategoryFactors.inv ≫
    Functor.whiskerRight (cochainDerivedUnit G) K.mapDerivedCategory
  suffices hh : α.app J = β.app J by
    simpa only [α, β, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, cochainDerivedUnit, Category.assoc] using hh
  obtain ⟨I, hI, r, _, hr⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective J
  let := hI
  let := hr
  apply (cancel_mono ((G.rightDerivedFunctor ⋙ K.mapDerivedCategory).map
    (DerivedCategory.Q.map r))).mp
  erw [← α.naturality r, ← β.naturality r]
  congr 1
  simpa only [α, β, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, cochainDerivedUnit, Category.assoc] using
    normalized_unit_kinjective G G' H K a d hd I

private theorem normalized_unit_inv
    (hd : CompactSupportDerivedSquareNormalization G G' H K a d)
    (J : CochainComplex C ℤ) :
    K.mapDerivedCategory.map (G.rightDerivedFunctorUnitQ J) ≫
        d.inv.app (DerivedCategory.Q.obj J) ≫
        G'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app J) =
      K.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj J) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex a (.up ℤ)).inv.app J) ≫
        G'.rightDerivedFunctorUnitQ ((H.mapHomologicalComplex (.up ℤ)).obj J) := by
  apply (cancel_epi (K.mapDerivedCategoryFactors.inv.app
    ((G.mapHomologicalComplex (.up ℤ)).obj J))).mp
  apply (cancel_epi (DerivedCategory.Q.map
    ((NatIso.mapHomologicalComplex a (.up ℤ)).hom.app J))).mp
  rw [← reassoc_of% (normalized_unit G G' H K a d hd J)]
  simp only [Iso.hom_inv_id_app_assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    Iso.inv_hom_id_app_assoc, ← DerivedCategory.Q.map_comp_assoc]
  erw [Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]

end Normalization

section DerivedTransition

variable {C Cm Cn A Am An : Type*}
  [Category C] [Category Cm] [Category Cn] [Category A] [Category Am] [Category An]
  [Abelian C] [Abelian Cm] [Abelian Cn] [Abelian A] [Abelian Am] [Abelian An]
  [HasDerivedCategory C] [HasDerivedCategory Cm] [HasDerivedCategory Cn]
  [HasDerivedCategory A] [HasDerivedCategory Am] [HasDerivedCategory An]
  [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions Cm]
  [Abelian.HasKInjectiveResolutions Cn]
  (G : C ⥤ A) (Gm : Cm ⥤ Am) (Gn : Cn ⥤ An)
  (Hm : C ⥤ Cm) (Hn : C ⥤ Cn) (Km : A ⥤ Am) (Kn : A ⥤ An)
  (R : Cn ⥤ Cm) (S : An ⥤ Am)
  [G.Additive] [Gm.Additive] [Gn.Additive]
  [Hm.Additive] [Hn.Additive] [Km.Additive] [Kn.Additive] [R.Additive] [S.Additive]
  [PreservesFiniteLimits Hm] [PreservesFiniteColimits Hm]
  [PreservesFiniteLimits Hn] [PreservesFiniteColimits Hn]
  [PreservesFiniteLimits Km] [PreservesFiniteColimits Km]
  [PreservesFiniteLimits Kn] [PreservesFiniteColimits Kn]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]

private theorem derived_transition
    (a : R.mapDerivedCategory ⋙ Gm.rightDerivedFunctor ≅
      Gn.rightDerivedFunctor ⋙ S.mapDerivedCategory)
    (b : R ⋙ Gm ≅ Gn ⋙ S)
    (dm : G.rightDerivedFunctor ⋙ Km.mapDerivedCategory ≅
      Hm.mapDerivedCategory ⋙ Gm.rightDerivedFunctor)
    (dn : G.rightDerivedFunctor ⋙ Kn.mapDerivedCategory ≅
      Hn.mapDerivedCategory ⋙ Gn.rightDerivedFunctor)
    (bm : G ⋙ Km ≅ Hm ⋙ Gm) (bn : G ⋙ Kn ≅ Hn ⋙ Gn)
    (hc0 : CompactSupportDerivedSquareNormalization Gn Gm R S b a)
    (hm0 : CompactSupportDerivedSquareNormalization G Gm Hm Km bm.symm dm.symm)
    (hn0 : CompactSupportDerivedSquareNormalization G Gn Hn Kn bn.symm dn.symm)
    (τ₀ : Hm ⟶ Hn ⋙ R) (σ₀ : Km ⟶ Kn ⋙ S)
    (τ : Hm.mapDerivedCategory ⟶ Hn.mapDerivedCategory ⋙ R.mapDerivedCategory)
    (σ : Km.mapDerivedCategory ⟶ Kn.mapDerivedCategory ⋙ S.mapDerivedCategory)
    (hz0 : ∀ J : CochainComplex C ℤ,
      τ.app (DerivedCategory.Q.obj J) ≫
          R.mapDerivedCategory.map (Hn.mapDerivedCategoryFactors.hom.app J) ≫
          R.mapDerivedCategoryFactors.hom.app ((Hn.mapHomologicalComplex (.up ℤ)).obj J) =
        Hm.mapDerivedCategoryFactors.hom.app J ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ₀ (.up ℤ)).app J))
    (hy0 : ∀ J : CochainComplex A ℤ,
      σ.app (DerivedCategory.Q.obj J) ≫
          S.mapDerivedCategory.map (Kn.mapDerivedCategoryFactors.hom.app J) ≫
          S.mapDerivedCategoryFactors.hom.app ((Kn.mapHomologicalComplex (.up ℤ)).obj J) =
        Km.mapDerivedCategoryFactors.hom.app J ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex σ₀ (.up ℤ)).app J))
    (ho0 : ∀ M : C, σ₀.app (G.obj M) ≫ S.map (bn.hom.app M) =
      bm.hom.app M ≫ Gm.map (τ₀.app M) ≫ b.hom.app (Hn.obj M))
    (N : DerivedCategory C) :
    σ.app (G.rightDerivedFunctor.obj N) ≫ S.mapDerivedCategory.map (dn.hom.app N) =
      dm.hom.app N ≫ Gm.rightDerivedFunctor.map (τ.app N) ≫ a.hom.app
        (Hn.mapDerivedCategory.obj N) := by
  let α := Functor.whiskerLeft G.rightDerivedFunctor σ ≫
    Functor.whiskerRight dn.hom S.mapDerivedCategory
  let β := dm.hom ≫ Functor.whiskerRight τ Gm.rightDerivedFunctor ≫
    Functor.whiskerLeft Hn.mapDerivedCategory a.hom
  have hQ (J : CochainComplex (C) ℤ)
      (hJ : J.IsKInjective) : α.app (DerivedCategory.Q.obj J) =
        β.app (DerivedCategory.Q.obj J) := by
    let := hJ
    have : IsIso (G.rightDerivedFunctorUnitQ J) := by
      rw [Functor.rightDerivedFunctorUnitQ_eq]
      infer_instance
    have hm := normalized_unit_inv G Gm Hm Km bm.symm dm.symm hm0 J
    have hn := normalized_unit_inv G Gn Hn Kn bn.symm dn.symm hn0 J
    dsimp only [Iso.symm_inv, NatIso.mapHomologicalComplex] at hm hn
    have hc := normalized_unit_inv Gn Gm R S b a hc0
      ((Hn.mapHomologicalComplex (.up ℤ)).obj J)
    have hz := hz0 J
    have hy := hy0 ((G.mapHomologicalComplex (.up ℤ)).obj J)
    have ho :
        (NatTrans.mapHomologicalComplex (σ₀)
            (.up ℤ)).app ((G.mapHomologicalComplex (.up ℤ)).obj J) ≫
          (S.mapHomologicalComplex (.up ℤ)).map
            ((NatIso.mapHomologicalComplex bn (.up ℤ)).hom.app J) ≫
          (NatIso.mapHomologicalComplex b (.up ℤ)).inv.app
            ((Hn.mapHomologicalComplex (.up ℤ)).obj J) =
        (NatIso.mapHomologicalComplex bm (.up ℤ)).hom.app J ≫
          (Gm.mapHomologicalComplex (.up ℤ)).map
            ((NatTrans.mapHomologicalComplex (τ₀)
              (.up ℤ)).app J) := by
      apply (cancel_mono ((NatIso.mapHomologicalComplex b (.up ℤ)).hom.app
        ((Hn.mapHomologicalComplex (.up ℤ)).obj J))).mp
      simp only [Category.assoc, Iso.inv_hom_id_app]
      ext k
      change σ₀.app (G.obj (J.X k)) ≫ S.map (bn.hom.app (J.X k)) ≫ 𝟙 _ =
        bm.hom.app (J.X k) ≫ Gm.map (τ₀.app (J.X k)) ≫ b.hom.app (Hn.obj (J.X k))
      simpa only [Category.comp_id] using ho0 (J.X k)
    apply (cancel_epi (Km.mapDerivedCategory.map (G.rightDerivedFunctorUnitQ J))).mp
    apply (cancel_mono (a.inv.app (Hn.mapDerivedCategory.obj (DerivedCategory.Q.obj J)) ≫
      Gm.rightDerivedFunctor.map (R.mapDerivedCategory.map
        (Hn.mapDerivedCategoryFactors.hom.app J)) ≫
      Gm.rightDerivedFunctor.map (R.mapDerivedCategoryFactors.hom.app
        ((Hn.mapHomologicalComplex (.up ℤ)).obj J)))).mp
    dsimp only [α, β, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    have hσ := σ.naturality (G.rightDerivedFunctorUnitQ J)
    dsimp only [Functor.comp_map] at hσ
    rw [reassoc_of% hσ]
    have ha := a.inv.naturality (Hn.mapDerivedCategoryFactors.hom.app J)
    dsimp only [Functor.comp_map] at ha
    rw [← reassoc_of% ha]
    rw [← S.mapDerivedCategory.map_comp_assoc, ← S.mapDerivedCategory.map_comp_assoc]
    simp only [Category.assoc]
    rw [hn]
    simp only [Functor.map_comp, Category.assoc]
    rw [hc]
    have hf := S.mapDerivedCategoryFactors.hom.naturality
      ((NatIso.mapHomologicalComplex bn (.up ℤ)).hom.app J)
    dsimp only [Functor.comp_map] at hf
    erw [reassoc_of% hf, reassoc_of% hy]
    have hzm := congrArg Gm.rightDerivedFunctor.map hz
    simp only [Functor.map_comp] at hzm
    rw [hzm, reassoc_of% hm]
    rw [← Gm.rightDerivedFunctorUnitQ_naturality]
    have hqo := congrArg DerivedCategory.Q.map ho
    simp only [Functor.map_comp] at hqo
    rw [reassoc_of% hqo]
    rfl
  have heq : α = β := by
    apply NatTrans.ext
    funext M
    obtain ⟨J, hJ, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective M
    apply (cancel_mono ((Hn.mapDerivedCategory ⋙ Gn.rightDerivedFunctor ⋙
      S.mapDerivedCategory).map e.hom)).mp
    erw [← α.naturality e.hom, ← β.naturality e.hom, hQ J hJ]
  exact congr_app heq N

end DerivedTransition

attribute [local irreducible] HasDerivedCategory.standard
  CategoryTheory.constantSheaf normalizedDVRQuotient coefficientSequenceCommRingSheaf
  integralComparisonSequenceRingMap Scheme.coefficientProEtaleDirectRingMap

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem ab_conjugate_apply_heq
    {A B A' B' : AddCommGrpCat.{v}} (hA : A = A') (hB : B = B')
    (f : A ⟶ B) (g : A' ⟶ B')
    (h : eqToHom hA.symm ≫ f ≫ eqToHom hB = g)
    (x : A) (y : A') (hxy : HEq x y) : HEq (f x) (g y) := by
  subst A' B'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h
  subst g
  have hx : x = y := eq_of_heq hxy
  subst y
  rfl

private theorem coefficientTransition_section (W : Scheme.{t})
    (N : coefficientSequenceModules l E W) {m n : ℕ} (h : n ≤ m) (U : W.ProEtᵒᵖ)
    (x : ((coefficientSequenceEvaluation l E W m).obj N).val.obj U) :
    ((coefficientSequenceTransition l E W h).app N).val.app U x =
      N.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x := by
  have ht := (coefficientSequenceTransition_exists l E W h).exists.choose_spec N U
  have hh := ab_conjugate_apply_heq
    (coefficientSequenceEvaluationAb_eq l E W N m U)
    (coefficientSequenceRestrictedEvaluationAb_eq l E W N h U)
    ((forget₂ (ModuleCat.{max u (t + 1)}
      ((integralCoefficientSheaf l E W m).obj.obj U)) AddCommGrpCat).map
        (((coefficientSequenceTransition l E W h).app N).val.app U))
    (N.val.presheaf.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op) ht x x (HEq.refl x)
  exact eq_of_heq hh

private theorem transition_rep (W : Scheme.{t}) {m n : ℕ} (h : n ≤ m)
    (J : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    (coefficientSequenceDerivedTransition l E W h).app (DerivedCategory.Q.obj J) ≫
        (normalizedDVRRes l E W h).map
          ((coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app J) ≫
        (normalizedDVRModuleRes l E W h).mapDerivedCategoryFactors.hom.app
          (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj J) =
      (coefficientSequenceEvaluation l E W m).mapDerivedCategoryFactors.hom.app J ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (coefficientSequenceTransition l E W h)
            (.up ℤ)).app J) := by
  dsimp only [coefficientSequenceDerivedTransition, NatTrans.comp_app]
  rw [Category.assoc, Functor.mapDerivedCategoryCompIso_hom_app_factors]
  rw [Localization.liftNatTrans_app]
  change ((coefficientSequenceEvaluation l E W m).mapDerivedCategoryFactors.hom.app J ≫
    DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex (coefficientSequenceTransition l E W h)
        (.up ℤ)).app J) ≫
    (coefficientSequenceEvaluation l E W n ⋙
      normalizedDVRModuleRes l E W h).mapDerivedCategoryFactors.inv.app J) ≫
    (coefficientSequenceEvaluation l E W n ⋙
      normalizedDVRModuleRes l E W h).mapDerivedCategoryFactors.hom.app J = _
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]

private theorem system_transition_section {Z Y : Scheme.{t}} (p : Z ⟶ Y)
    {m n : ℕ} (h : n ≤ m) (N : coefficientSequenceModules l E Z) (V : Y.ProEtᵒᵖ)
    (x : ((coefficientSequenceEvaluation l E Y m).obj
      ((integralComparisonSequenceDirectImage l E p).obj N)).val.obj V) :
    ((coefficientSequenceTransition l E Y h).app
        ((integralComparisonSequenceDirectImage l E p).obj N)).val.app V x =
      ((coefficientSequenceTransition l E Z h).app N).val.app
        ((Scheme.proEtaleBaseChange p).op.obj V) x := by
  refine (coefficientTransition_section l E Y
    ((integralComparisonSequenceDirectImage l E p).obj N) h V x).trans ?_
  refine Eq.trans ?_ (coefficientTransition_section l E Z N h
    ((Scheme.proEtaleBaseChange p).op.obj V) x).symm
  change N.val.map ((integralComparisonSequenceBaseChange p).map
      (Prod.mkHom (homOfLE h) (𝟙 V.unop))).op x =
    N.val.map (Prod.mkHom (homOfLE h)
      (𝟙 ((Scheme.proEtaleBaseChange p).op.obj V).unop)).op x
  have hh : (integralComparisonSequenceBaseChange p).map
      (Prod.mkHom (homOfLE h) (𝟙 V.unop)) =
      Prod.mkHom (homOfLE h) (𝟙 ((Scheme.proEtaleBaseChange p).obj V.unop)) := by
    simp only [integralComparisonSequenceBaseChange, Functor.prod_map, Functor.id_map,
      CategoryTheory.Functor.map_id]
  exact N.val.congr_map_apply (congrArg Quiver.Hom.op hh) x

private theorem system_transition_section_heq {Z Y : Scheme.{t}} (p : Z ⟶ Y)
    {m n : ℕ} (h : n ≤ m) (N : coefficientSequenceModules l E Z) (V : Y.ProEtᵒᵖ)
    (x : ((coefficientSequenceEvaluation l E Y m).obj
      ((integralComparisonSequenceDirectImage l E p).obj N)).val.obj V)
    (y : ((coefficientSequenceEvaluation l E Z m).obj N).val.obj
      ((Scheme.proEtaleBaseChange p).op.obj V)) (hxy : HEq x y) :
    HEq (((coefficientSequenceTransition l E Y h).app
      ((integralComparisonSequenceDirectImage l E p).obj N)).val.app V x)
      (((coefficientSequenceTransition l E Z h).app N).val.app
        ((Scheme.proEtaleBaseChange p).op.obj V) y) := by
  have hh : x = y := eq_of_heq hxy
  subst y
  exact heq_of_eq (system_transition_section l E p h N V x)

private theorem sheaf_square {B : Type*} [Category B]
    {T : GrothendieckTopology B} {R : Sheaf T RingCat.{v}}
    {M₀ M₁ M₂ M₃ M₄ : SheafOfModules.{u} R}
    (f₁ : M₀ ⟶ M₁) (f₂ : M₁ ⟶ M₂)
    (g₁ : M₀ ⟶ M₃) (g₂ : M₃ ⟶ M₄) (g₃ : M₄ ⟶ M₂)
    (hh : ∀ (U : Bᵒᵖ) (x : M₀.val.obj U),
      f₂.val.app U (f₁.val.app U x) =
        g₃.val.app U (g₂.val.app U (g₁.val.app U x))) :
    f₁ ≫ f₂ = g₁ ≫ g₂ ≫ g₃ := by
  ext U x
  exact hh U x

private theorem sheaf_square_identity {B : Type*} [Category B]
    {T : GrothendieckTopology B} {R : Sheaf T RingCat.{v}}
    {M₀ M₁ M₂ M₃ M₄ : SheafOfModules.{u} R}
    (f₁ : M₀ ⟶ M₁) (f₂ : M₁ ⟶ M₂)
    (g₁ : M₀ ⟶ M₃) (g₂ : M₃ ⟶ M₄) (g₃ : M₄ ⟶ M₂)
    (hf : ∀ (U : Bᵒᵖ) (x : M₁.val.obj U), HEq (f₂.val.app U x) x)
    (hg : ∀ (U : Bᵒᵖ) (x : M₀.val.obj U), HEq (g₁.val.app U x) x)
    (hk : ∀ (U : Bᵒᵖ) (x : M₄.val.obj U), HEq (g₃.val.app U x) x)
    (hs : ∀ (U : Bᵒᵖ) (x : M₀.val.obj U) (y : M₃.val.obj U),
      HEq x y → HEq (f₁.val.app U x) (g₂.val.app U y)) :
    f₁ ≫ f₂ = g₁ ≫ g₂ ≫ g₃ := by
  apply sheaf_square
  intro U x
  exact eq_of_heq ((hf U _).trans
    ((hs U x _ (hg U x).symm).trans (hk U _).symm))

private theorem restrict_map_section {B : Type*} [Category B]
    {T : GrothendieckTopology B} {R S : Sheaf T RingCat.{v}} (φ : R ⟶ S)
    {M N : SheafOfModules.{u} S} (f : M ⟶ N) (V : Bᵒᵖ)
    (x : ((SheafOfModules.restrictScalars φ).obj M).val.obj V) :
    (((SheafOfModules.restrictScalars φ).map f).val.app V) x = f.val.app V x := by
  rfl

private theorem pushforward_map_section {B B' : Type*} [Category B] [Category B']
    {T : GrothendieckTopology B} {T' : GrothendieckTopology B'} {F : B ⥤ B'}
    [F.IsContinuous T T'] {R : Sheaf T' RingCat.{v}} {S : Sheaf T RingCat.{v}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{v} T T').obj R)
    {M N : SheafOfModules.{u} R} (f : M ⟶ N) (V : Bᵒᵖ)
    (x : ((SheafOfModules.pushforward φ).obj M).val.obj V) :
    (((SheafOfModules.pushforward φ).map f).val.app V) x =
      f.val.app (op (F.obj V.unop)) x := by
  rfl

private theorem restrict_identity {B : Type*} [Category B]
    {T : GrothendieckTopology B} {R S : Sheaf T RingCat.{v}} (φ : R ⟶ S)
    {M N : SheafOfModules.{u} S} (f : M ⟶ N)
    (hf : ∀ (V : Bᵒᵖ) (x : M.val.obj V), HEq (f.val.app V x) x)
    (V : Bᵒᵖ) (x : ((SheafOfModules.restrictScalars φ).obj M).val.obj V) :
    HEq ((((SheafOfModules.restrictScalars φ).map f).val.app V) x) x := by
  exact (heq_of_eq (restrict_map_section φ f V x)).trans (hf V x)

private theorem pushforward_apply_heq {B B' : Type*} [Category B] [Category B']
    {T : GrothendieckTopology B} {T' : GrothendieckTopology B'} {F : B ⥤ B'}
    [F.IsContinuous T T'] {R : Sheaf T' RingCat.{v}} {S : Sheaf T RingCat.{v}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{v} T T').obj R)
    {M N : SheafOfModules.{u} R} (f : M ⟶ N) (V : Bᵒᵖ)
    (x : ((SheafOfModules.pushforward φ).obj M).val.obj V)
    (y : M.val.obj (op (F.obj V.unop))) (hxy : HEq x y) :
    HEq ((((SheafOfModules.pushforward φ).map f).val.app V) x)
      (f.val.app (op (F.obj V.unop)) y) := by
  have hh : x = y := eq_of_heq hxy
  subst y
  exact heq_of_eq (pushforward_map_section φ f V x)

private theorem pushforward_element {B B' : Type*} [Category B] [Category B']
    {T : GrothendieckTopology B} {T' : GrothendieckTopology B'} {F : B ⥤ B'}
    [F.IsContinuous T T'] {R : Sheaf T' RingCat.{v}} {S : Sheaf T RingCat.{v}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{v} T T').obj R)
    (M : SheafOfModules.{u} R) (V : Bᵒᵖ)
    (x : ((SheafOfModules.pushforward φ).obj M).val.obj V) :
    ∃ y : M.val.obj (op (F.obj V.unop)), HEq x y := by
  exact ⟨x, HEq.refl x⟩

private theorem restrict_carrier_eq {B : Type*} [Category B]
    {T : GrothendieckTopology B} {R S : Sheaf T RingCat.{v}} (φ : R ⟶ S)
    (M : SheafOfModules.{u} S) (V : Bᵒᵖ) :
    (↑(((SheafOfModules.restrictScalars φ).obj M).val.obj V) : Type u) =
      (↑(M.val.obj V) : Type u) := by
  rfl

private theorem pushforward_carrier_eq {B B' : Type*} [Category B] [Category B']
    {T : GrothendieckTopology B} {T' : GrothendieckTopology B'} {F : B ⥤ B'}
    [F.IsContinuous T T'] {R : Sheaf T' RingCat.{v}} {S : Sheaf T RingCat.{v}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{v} T T').obj R)
    (M : SheafOfModules.{u} R) (V : Bᵒᵖ) :
    (↑(((SheafOfModules.pushforward φ).obj M).val.obj V) : Type u) =
      (↑(M.val.obj (op (F.obj V.unop))) : Type u) := by
  rfl

private theorem normalized_res_carrier_eq (W : Scheme.{t}) {m n : ℕ} (h : n ≤ m)
    (M : normalizedDVRModules l E W n) (V : W.ProEtᵒᵖ) :
    (↑(((normalizedDVRModuleRes l E W h).obj M).val.obj V) : Type (max u (t + 1))) =
      (↑(M.val.obj V) : Type (max u (t + 1))) := by
  exact restrict_carrier_eq (normalizedDVRQuotient l E W h) M V

private theorem level_carrier_eq {Z Y : Scheme.{t}} (p : Z ⟶ Y) (k : ℕ)
    (M : normalizedDVRModules l E Z k) (V : Y.ProEtᵒᵖ) :
    (↑(((compactSupportLevelDirectImage l E p k).obj M).val.obj V) :
      Type (max u (t + 1))) =
      (↑(M.val.obj ((Scheme.proEtaleBaseChange p).op.obj V)) : Type (max u (t + 1))) := by
  exact pushforward_carrier_eq _ M V

private theorem function_identity_of_heq {A B C : Type u} (eA : A = C) (eB : B = C)
    (f : A → B) (hf : HEq f (@id C)) (x : A) : HEq (f x) x := by
  subst C B
  exact heq_of_eq (congrFun (eq_of_heq hf) x)

attribute [local irreducible] coefficientSequenceTransition coefficientSequenceEvaluation
  integralCoefficientSheaf sheafCompose CommRingCat.hasForgetToRingCat
  CommRingCat.instConcreteCategoryRingHomCarrier RingCat.instConcreteCategoryRingHomCarrier

private theorem ordinary_transition {Z Y : Scheme.{t}} (p : Z ⟶ Y)
    {m n : ℕ} (h : n ≤ m)
    (a : normalizedDVRModuleRes l E Z h ⋙ compactSupportLevelDirectImage l E p m ≅
      compactSupportLevelDirectImage l E p n ⋙ normalizedDVRModuleRes l E Y h)
    (bm : integralComparisonSequenceDirectImage l E p ⋙ coefficientSequenceEvaluation l E Y m ≅
      coefficientSequenceEvaluation l E Z m ⋙ compactSupportLevelDirectImage l E p m)
    (bn : integralComparisonSequenceDirectImage l E p ⋙ coefficientSequenceEvaluation l E Y n ≅
      coefficientSequenceEvaluation l E Z n ⋙ compactSupportLevelDirectImage l E p n)
    (ha : ∀ (M : normalizedDVRModules l E Z n) (V : Y.ProEtᵒᵖ),
      HEq (fun x ↦ (a.hom.app M).val.app V x)
        (fun x : M.val.obj ((Scheme.proEtaleBaseChange p).op.obj V) ↦ x))
    (hm : ∀ (M : coefficientSequenceModules l E Z) (V : Y.ProEtᵒᵖ)
      (x : ((integralComparisonSequenceDirectImage l E p ⋙
        coefficientSequenceEvaluation l E Y m).obj M).val.obj V),
      HEq ((bm.hom.app M).val.app V x) x)
    (hn : ∀ (M : coefficientSequenceModules l E Z) (V : Y.ProEtᵒᵖ)
      (x : ((integralComparisonSequenceDirectImage l E p ⋙
        coefficientSequenceEvaluation l E Y n).obj M).val.obj V),
      HEq ((bn.hom.app M).val.app V x) x)
    (N : coefficientSequenceModules l E Z) :
    (coefficientSequenceTransition l E Y h).app
        ((integralComparisonSequenceDirectImage l E p).obj N) ≫
      (normalizedDVRModuleRes l E Y h).map (bn.hom.app N) =
    bm.hom.app N ≫ (compactSupportLevelDirectImage l E p m).map
      ((coefficientSequenceTransition l E Z h).app N) ≫
      a.hom.app ((coefficientSequenceEvaluation l E Z n).obj N) := by
  apply sheaf_square_identity
  · as_aux_lemma =>
      intro V x
      exact restrict_identity (normalizedDVRQuotient l E Y h) (bn.hom.app N) (hn N) V x
  · as_aux_lemma =>
      intro V x
      exact hm N V x
  · as_aux_lemma =>
      intro V x
      let M := (coefficientSequenceEvaluation l E Z n).obj N
      have eA := (level_carrier_eq l E p m ((normalizedDVRModuleRes l E Z h).obj M) V).trans
        (normalized_res_carrier_eq l E Z h M ((Scheme.proEtaleBaseChange p).op.obj V))
      have eB := (normalized_res_carrier_eq l E Y h
        ((compactSupportLevelDirectImage l E p n).obj M) V).trans
          (level_carrier_eq l E p n M V)
      exact function_identity_of_heq eA eB _ (ha M V) x
  · as_aux_lemma =>
      intro V x y hxy
      obtain ⟨z, hz⟩ := pushforward_element _
        ((coefficientSequenceEvaluation l E Z m).obj N) V y
      exact (system_transition_section_heq l E p h N V x z (hxy.trans hz)).trans
        (pushforward_apply_heq _ ((coefficientSequenceTransition l E Z h).app N)
          V y z hz).symm

/-- Derived direct-image evaluation intertwines the restriction-form system transition.
This is a statement about arbitrary systems N on Z, before open extension or completed
restriction, and involves neither the coefficient mate nor any scalar adjunction.
Source: coherence proof steps 2 and 4; Zheng 4.10; Stacks 07A4, 0941
(blueprint: lem-trf-direct-image-restriction-transition).
Proof: on ordinary systems the evaluation maps and the coefficient square are identities
on sections by h0 and h2. Both composites are therefore the horizontal restriction
map of N evaluated on the base change of a pro-etale test object. Resolve N on the
whole sequence site, with K-injective representative J. Choose K-injective resolutions
r_m:e_m J -> I_m and r_n:e_n J -> I_n. Choose a K-injective resolution
r:Res I_n -> K. The chain map r followed after Res(r_n) and the transition of J
factors through r_m in the homotopy category, since K is K-injective and r_m is a
quasi-isomorphism. Choose a chain representative s:I_m -> K for this factorization.
Thus s r_m and r Res(r_n) tau_J are chain homotopic. Apply the additive direct image:
it preserves this homotopy. The normalization h3 at (J,I_m,r_m) and (J,I_n,r_n)
identifies the two evaluation comparisons, while h1 at (I_n,K,r) identifies the
coefficient comparison. Substitute these three normalization equations and use the
ordinary sectionwise transition square. The displayed equality now follows from the
homotopy just obtained. Cancel the resolution comparison isomorphisms to return to N.
The choice of evaluated resolutions cancels by uniqueness of right-derived comparisons.
In particular, the argument does not assume that evaluation or quotient restriction
preserves injectives,
K-injectives, flatness, or cartesian systems. -/
theorem compactSupportDirectImageRestrictionTransition
    {X Z Y : Scheme.{t}} {j : X ⟶ Z} {p : Z ⟶ Y} [IsOpenImmersion j]
    [D : CompactSupportSystemEvaluationData l E X Z Y j p]
    (h0 : ∀ {m n : ℕ} (h : n ≤ m)
            (N : normalizedDVRModules l E Z n) (V : Y.ProEtᵒᵖ),
            HEq (fun x ↦ ((D.operations.ordinaryCoefficientComparison h).hom.app N).val.app V x)
              (fun x : N.val.obj ((Scheme.proEtaleBaseChange p).op.obj V) ↦ x))
    (h1 : ∀ {m n : ℕ} (h : n ≤ m),
      letI := normalizedDVRModuleRes_limits l E Z h
      letI := normalizedDVRModuleRes_colimits l E Z h
      letI := normalizedDVRModuleRes_limits l E Y h
      letI := normalizedDVRModuleRes_colimits l E Y h
      CompactSupportDerivedSquareNormalization
          (compactSupportLevelDirectImage l E p n) (compactSupportLevelDirectImage l E p m)
          (normalizedDVRModuleRes l E Z h) (normalizedDVRModuleRes l E Y h)
          (D.operations.ordinaryCoefficientComparison h) (D.operations.derivedCoefficientComparison
            h))
    (h2 : ∀ (n : ℕ) (N : coefficientSequenceModules l E Z)
            (V : Y.ProEtᵒᵖ)
            (x : ((integralComparisonSequenceDirectImage l E p ⋙
              coefficientSequenceEvaluation l E Y n).obj N).val.obj V),
            HEq (((D.pOrdinaryEvaluation n).hom.app N).val.app V x) x)
    (h3 : ∀ n : ℕ,
      letI := coefficientSequenceEvaluation_additiveInstance l E Z n
      letI := coefficientSequenceEvaluation_additiveInstance l E Y n
      letI := coefficientSequenceEvaluation_limits l E Z n
      letI := coefficientSequenceEvaluation_colimits l E Z n
      letI := coefficientSequenceEvaluation_limits l E Y n
      letI := coefficientSequenceEvaluation_colimits l E Y n
      CompactSupportDerivedSquareNormalization
          (integralComparisonSequenceDirectImage l E p) (compactSupportLevelDirectImage l E p n)
          (coefficientSequenceEvaluation l E Z n) (coefficientSequenceEvaluation l E Y n)
          (D.pOrdinaryEvaluation n).symm (D.pRightEvaluation n).symm)
    {m n : ℕ} (h : n ≤ m) (N : coefficientSequenceDerived l E Z) :
    (coefficientSequenceDerivedTransition l E Y h).app
        ((integralComparisonSequenceDirectImage l E p).rightDerivedFunctor.obj N) ≫
      (normalizedDVRRes l E Y h).map ((D.pRightEvaluation n).hom.app N) =
    (D.pRightEvaluation m).hom.app N ≫
      (compactSupportLevelDirectImage l E p m).rightDerivedFunctor.map
        ((coefficientSequenceDerivedTransition l E Z h).app N) ≫
      (D.operations.derivedCoefficientComparison h).hom.app
        ((coefficientSequenceDerivedEvaluation l E Z n).obj N) := by
  exact derived_transition
    (integralComparisonSequenceDirectImage l E p)
    (compactSupportLevelDirectImage l E p m) (compactSupportLevelDirectImage l E p n)
    (coefficientSequenceEvaluation l E Z m) (coefficientSequenceEvaluation l E Z n)
    (coefficientSequenceEvaluation l E Y m) (coefficientSequenceEvaluation l E Y n)
    (normalizedDVRModuleRes l E Z h) (normalizedDVRModuleRes l E Y h)
    (D.operations.derivedCoefficientComparison h) (D.operations.ordinaryCoefficientComparison h)
    (D.pRightEvaluation m) (D.pRightEvaluation n)
    (D.pOrdinaryEvaluation m) (D.pOrdinaryEvaluation n) (h1 h) (h3 m) (h3 n)
    (coefficientSequenceTransition l E Z h) (coefficientSequenceTransition l E Y h)
    (coefficientSequenceDerivedTransition l E Z h) (coefficientSequenceDerivedTransition l E Y h)
    (transition_rep l E Z h) (transition_rep l E Y h)
    (ordinary_transition l E p h (D.operations.ordinaryCoefficientComparison h)
      (D.pOrdinaryEvaluation m) (D.pOrdinaryEvaluation n) (h0 h) (h2 m) (h2 n)) N

end WeilConjectures
