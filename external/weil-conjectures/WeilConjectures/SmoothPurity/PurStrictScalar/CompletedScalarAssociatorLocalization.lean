/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.CompletedScalarExactLocalization
public import WeilConjectures.SmoothPurity.PurStrictScalar.ConstantCompletedOrdinaryAssociativity
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcRationalAutomorphismScalarCoherence

/-! # Localization of the completed scalar associator

Source: Stacks Tag 07A6, the derived scalar adjunction and its unit normalization.
(blueprint: lem-pur-completed-scalar-associator-localization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PurStrictScalar

private theorem exact_associator_factors
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) (J : A ⥤ C)
    [F.Additive] [G.Additive] [J.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    (e : F ⋙ G ≅ J) (P : CochainComplex A ℤ) :
    (Functor.mapDerivedCategoryCompIso F G ≪≫
      Functor.mapDerivedCategoryNatIso e).hom.app (DerivedCategory.Q.obj P) ≫
      J.mapDerivedCategoryFactors.hom.app P =
    G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.app P) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryNatIso_fac]
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_factors F G P]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rfl

private theorem model_naturality
    {A B : Type*} [Category A] [Category B]
    (G G' : A ⥤ B) (e : G ≅ G') {X Y Z : A} {W : B}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : G'.obj Z ⟶ W) :
    G.map a ≫ e.hom.app Y ≫ G'.map b ≫ c =
      G.map (a ≫ b) ≫ e.hom.app Z ≫ c := by
  rw [← Category.assoc (e.hom.app Y), ← e.hom.naturality b]
  simp only [Functor.map_comp, Category.assoc]

private theorem model_composition
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) (J : A ⥤ C)
    [F.Additive] [G.Additive] [J.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    (Fd : DerivedCategory A ⥤ DerivedCategory B)
    (Gd : DerivedCategory B ⥤ DerivedCategory C)
    (Jd : DerivedCategory A ⥤ DerivedCategory C)
    (mF : Fd ≅ F.mapDerivedCategory) (mG : Gd ≅ G.mapDerivedCategory)
    (mJ : Jd ≅ J.mapDerivedCategory) (e : F ⋙ G ≅ J) (a : Fd ⋙ Gd ≅ Jd)
    (cF : ∀ P : CochainComplex A ℤ, Fd.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (cG : ∀ P : CochainComplex B ℤ, Gd.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj P))
    (cJ : ∀ P : CochainComplex A ℤ, Jd.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((J.mapHomologicalComplex (.up ℤ)).obj P))
    (hF : ∀ P, mF.hom.app (DerivedCategory.Q.obj P) ≫
      F.mapDerivedCategoryFactors.hom.app P = cF P)
    (hG : ∀ P, mG.hom.app (DerivedCategory.Q.obj P) ≫
      G.mapDerivedCategoryFactors.hom.app P = cG P)
    (hJ : ∀ P, mJ.hom.app (DerivedCategory.Q.obj P) ≫
      J.mapDerivedCategoryFactors.hom.app P = cJ P)
    (hn : ∀ P, a.hom.app (DerivedCategory.Q.obj P) ≫ cJ P =
      Gd.map (cF P) ≫ cG ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.app P))
    (K : DerivedCategory A) :
    a.hom.app K ≫ mJ.hom.app K =
      Gd.map (mF.hom.app K) ≫ mG.hom.app (F.mapDerivedCategory.obj K) ≫
        (Functor.mapDerivedCategoryCompIso F G ≪≫
          Functor.mapDerivedCategoryNatIso e).hom.app K := by
  let τ : Fd ⋙ Gd ⟶ J.mapDerivedCategory := a.hom ≫ mJ.hom
  let σ : Fd ⋙ Gd ⟶ J.mapDerivedCategory :=
    Functor.whiskerRight mF.hom Gd ≫
      Functor.whiskerLeft F.mapDerivedCategory mG.hom ≫
        (Functor.mapDerivedCategoryCompIso F G ≪≫
          Functor.mapDerivedCategoryNatIso e).hom
  have he : τ = σ := by
    apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
    intro P
    apply (cancel_mono (J.mapDerivedCategoryFactors.hom.app P)).mp
    change (a.hom.app _ ≫ mJ.hom.app _) ≫ _ =
      (Gd.map (mF.hom.app _) ≫ mG.hom.app _ ≫ _) ≫ _
    simp only [Category.assoc]
    rw [hJ, exact_associator_factors F G J e P, model_naturality]
    erw [reassoc_of% hG ((F.mapHomologicalComplex (.up ℤ)).obj P), hF]
    exact hn P
  exact NatTrans.congr_app he K

/-- The completed scalar associator agrees with exact localization under the
counit-normalized models. Source: Stacks Tag 07A6 (lemma-adjoint)
(blueprint: lem-pur-completed-scalar-associator-localization).
Proof: localize each ordinary scalar adjunction. Conjugate its left functor by
completedTensorModel. On a K-flat complex the resulting unit satisfies precisely
the defining equation of pbcDerivedScalarAdjunction: this follows from
completedTensorModel_counit and the ordinary adjunction unit. Uniqueness in
pbcDerivedScalarAdjunction_exists therefore identifies the two adjunctions.
The ordinary restriction compositor is the identity on sections; its localization
is by definition pbcDerivedRestrictComp. Localization preserves adjunction
composition and transport by this compositor, as follows by their unit formulas.
Finally leftAdjointUniq is characterized by preservation of the unit, so its
localized ordinary instance is the completed derived instance conjugated by the
three exact models. This gives the equation below. All comparisons are natural
and all counits used here are invertible because completedTensor_exact holds;
there are no boundedness, nonzero-object, or nonempty-site assumptions. -/
theorem completedTensorModel_composition
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (i : E →ₐ[ℚ_[l]] F)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (j : F →ₐ[ℚ_[l]] L) (W : Scheme.{u})
    (K : DerivedCategory (scalarReductionSource l E W)) :
    (haveI := (completedTensor_exact l E F i W).1
     haveI := (completedTensor_exact l E F i W).2
     haveI := (completedTensor_exact l F L j W).1
     haveI := (completedTensor_exact l F L j W).2
     haveI := (completedTensor_exact l E L (j.comp i) W).1
     haveI := (completedTensor_exact l E L (j.comp i) W).2
     haveI := pbcExtend_additive (completedCoefficientMap l E F i W)
     haveI := pbcExtend_additive (completedCoefficientMap l F L j W)
     haveI := pbcExtend_additive (completedCoefficientMap l E L (j.comp i) W)
     (PurCompactSupport.tensorComposition _ _ _
       (PurCompactSupport.completedMap_composition l E F i L j W)).hom.app K ≫
       (completedTensorModel l E L (j.comp i) W).hom.app K =
     (pbcDerivedExtend (completedCoefficientMap l F L j W)).map
       ((completedTensorModel l E F i W).hom.app K) ≫
       (completedTensorModel l F L j W).hom.app
         ((pbcExtend (completedCoefficientMap l E F i W)).mapDerivedCategory.obj K) ≫
       (Functor.mapDerivedCategoryCompIso _ _ ≪≫
         Functor.mapDerivedCategoryNatIso
           (ordinaryScalarAssociator _ _ _
             (PurCompactSupport.completedMap_composition l E F i L j W))).hom.app K) := by
  have := (completedTensor_exact l E F i W).1
  have := (completedTensor_exact l E F i W).2
  have := (completedTensor_exact l F L j W).1
  have := (completedTensor_exact l F L j W).2
  have := (completedTensor_exact l E L (j.comp i) W).1
  have := (completedTensor_exact l E L (j.comp i) W).2
  have := pbcExtend_additive (completedCoefficientMap l E F i W)
  have := pbcExtend_additive (completedCoefficientMap l F L j W)
  have := pbcExtend_additive (completedCoefficientMap l E L (j.comp i) W)
  apply model_composition
    (pbcExtend (completedCoefficientMap l E F i W))
    (pbcExtend (completedCoefficientMap l F L j W))
    (pbcExtend (completedCoefficientMap l E L (j.comp i) W))
    (pbcDerivedExtend (completedCoefficientMap l E F i W))
    (pbcDerivedExtend (completedCoefficientMap l F L j W))
    (pbcDerivedExtend (completedCoefficientMap l E L (j.comp i) W))
    (completedTensorModel l E F i W) (completedTensorModel l F L j W)
    (completedTensorModel l E L (j.comp i) W)
    (ordinaryScalarAssociator _ _ _
      (PurCompactSupport.completedMap_composition l E F i L j W))
    (PurCompactSupport.tensorComposition _ _ _
      (PurCompactSupport.completedMap_composition l E F i L j W))
    (pbcComplexCounit (completedCoefficientMap l E F i W))
    (pbcComplexCounit (completedCoefficientMap l F L j W))
    (pbcComplexCounit (completedCoefficientMap l E L (j.comp i) W))
    (completedTensorModel_counit l E F i W)
    (completedTensorModel_counit l F L j W)
    (completedTensorModel_counit l E L (j.comp i) W)
  intro P
  have hh := extensionAssociator_normalization
    (completedCoefficientMap l E F i W) (completedCoefficientMap l F L j W)
    (completedCoefficientMap l E L (j.comp i) W)
    (PurCompactSupport.completedMap_composition l E F i L j W) P
  simpa only [leftAdjointCompIso_eq, PurCompactSupport.tensorComposition,
    ordinaryScalarAssociator] using hh

end WeilConjectures.PurStrictScalar
