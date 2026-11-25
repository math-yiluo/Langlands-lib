/-
Copyright (c) 2026 Anthropic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SmoothPurity.Rational.RationalPullbackTransitionShiftLevel
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
public import WeilConjectures.TraceFormula.Integral.IntegralDerivedOperations
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift

/-! # Shift compatibility of the ordinary scalar/pullback comparison

The defining comparison of the integral derived pullback with the pullback of good
representatives commutes with the cochain and derived pullback shifts related by
representative descent (`integralDerivedPullbackComparison_commShift`). Combined with the
chain-level result `scalarPullbackRoosChain_commShift`, this shows that the ordinary
scalar/pullback comparison `scalarPullbackOrdinary` commutes with the descended integral
pullback shifts (`scalarPullbackOrdinary_commShift`).

This is the derived-level step of the proof of `rationalPullbackTransitionShift`.
Source: current blueprint sec-smooth-purity/sk-prop-sf-localization,
prop-sf-open-closed-triangle-all-stages.proof.md, Weil-structures paragraph.
(blueprint: lem-sf-rational-pullback-transition-shift).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

/-- The shift on the localization from good representatives. -/
@[instance_reducible]
noncomputable def integralOperationsGoodLocalizationCommShift (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    [(integralOperationsGoodComplex l E X).IsStableUnderShift ℤ] :
    (integralOperationsGoodLocalization l E X).CommShift ℤ :=
  inferInstanceAs (((integralOperationsGoodComplex l E X).ι ⋙ DerivedCategory.Q).CommShift ℤ)

/-- The shift on the localized pullback construction on good representatives. -/
@[instance_reducible]
noncomputable def integralOperationsPullbackOnGoodCommShift (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [(integralOperationsGoodComplex l E X).IsStableUnderShift ℤ]
    (c : (integralOperationsPullbackComplexFunctor l E f).CommShift ℤ) :
    (integralOperationsPullbackOnGood l E f).CommShift ℤ :=
  @Functor.CommShift.comp _ _ _ _ _ _ (integralOperationsGoodComplex l E X).ι
    (integralOperationsPullbackComplexFunctor l E f ⋙ DerivedCategory.Q) ℤ _ _ _ _
    inferInstance (@Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _ c inferInstance)

/-- The shift comparison of the pullback on good representatives, in terms of the cochain
pullback shift. -/
theorem integralOperationsPullbackOnGoodCommShift_hom_app (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [(integralOperationsGoodComplex l E X).IsStableUnderShift ℤ]
    (c : (integralOperationsPullbackComplexFunctor l E f).CommShift ℤ) (r : ℤ)
    (P : (integralOperationsGoodComplex l E X).FullSubcategory) :
    (@Functor.commShiftIso _ _ _ _ (integralOperationsPullbackOnGood l E f) ℤ _ _ _
      (integralOperationsPullbackOnGoodCommShift l E f c) r).hom.app P =
      DerivedCategory.Q.map ((integralOperationsPullbackComplexFunctor l E f).map
        (((integralOperationsGoodComplex l E X).ι.commShiftIso r).hom.app P)) ≫
      DerivedCategory.Q.map (((integralOperationsPullbackComplexFunctor l E f).commShiftIso
        (self := c) r).hom.app P.obj) ≫
      (DerivedCategory.Q.commShiftIso r).hom.app
        ((integralOperationsPullbackComplexFunctor l E f).obj P.obj) := by
  unfold integralOperationsPullbackOnGoodCommShift
  erw [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_hom_app]
  simp only [Functor.comp_map]
  rfl

-- Matching the good-subcategory and ambient derived category instances is slow.
/-- The defining integral pullback comparison commutes with the cochain and derived
pullback shifts related by representative descent. -/
theorem integralDerivedPullbackComparison_commShift (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (c : (integralOperationsPullbackComplexFunctor l E f).CommShift ℤ)
    (d : (integralDerivedPullback l E f).CommShift ℤ)
    (hd : IntegralCompletedComparison.ShiftDescent l E f c d)
    [(integralOperationsGoodComplex l E X).IsStableUnderShift ℤ] :
    @NatTrans.CommShift _ _ _ _ _ _ (integralDerivedPullbackComparison l E f).hom ℤ _ _ _
      (@Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _
        (integralOperationsGoodLocalizationCommShift l E X) d)
      (integralOperationsPullbackOnGoodCommShift l E f c) := by
  let := integralOperationsGoodLocalizationCommShift l E X
  let := integralOperationsPullbackOnGoodCommShift l E f c
  constructor
  intro r
  ext P
  obtain ⟨hP, H⟩ := hd P r
  let g : P⟦r⟧ ⟶ (⟨P.obj⟦r⟧, hP⟩ : (integralOperationsGoodComplex l E X).FullSubcategory) :=
    ObjectProperty.homMk (((integralOperationsGoodComplex l E X).ι.commShiftIso r).hom.app P)
  have hn := (integralDerivedPullbackComparison l E f).hom.naturality g
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  have hG : ((integralOperationsGoodLocalization l E X).commShiftIso r).hom.app P =
      DerivedCategory.Q.map (((integralOperationsGoodComplex l E X).ι.commShiftIso r).hom.app P) ≫
        (DerivedCategory.Q.commShiftIso r).hom.app P.obj :=
    Functor.commShiftIso_comp_hom_app (integralOperationsGoodComplex l E X).ι DerivedCategory.Q r P
  rw [Functor.commShiftIso_comp_hom_app, hG, integralOperationsPullbackOnGoodCommShift_hom_app,
    Category.assoc]
  erw [H]
  erw [CategoryTheory.Functor.map_comp, Category.assoc,
    ← Functor.map_comp_assoc (integralDerivedPullback l E f)
      ((DerivedCategory.Q.commShiftIso r).hom.app P.obj), Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  erw [reassoc_of% hn]
  rfl

/-- The ordinary scalar/pullback comparison commutes with the descended integral pullback
shifts and the ordinary derived scalar shifts.
Source: current blueprint sec-smooth-purity/sk-prop-sf-localization,
prop-sf-open-closed-triangle-all-stages.proof.md, Weil-structures paragraph
(blueprint: lem-sf-framework-theta-shift-compatibility). -/
theorem scalarPullbackOrdinary_commShift (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) {X Y : Scheme.{u}} (f : Y ⟶ X)
    (cE : (integralOperationsPullbackComplexFunctor l E f).CommShift ℤ)
    (dE : (integralDerivedPullback l E f).CommShift ℤ)
    (hcE : IntegralCompletedComparison.ShiftCoordinates l E f cE)
    (hdE : IntegralCompletedComparison.ShiftDescent l E f cE dE)
    (cL : (integralOperationsPullbackComplexFunctor l L f).CommShift ℤ)
    (dL : (integralDerivedPullback l L f).CommShift ℤ)
    (hcL : IntegralCompletedComparison.ShiftCoordinates l L f cL)
    (hdL : IntegralCompletedComparison.ShiftDescent l L f cL dL) :
    @NatTrans.CommShift _ _ _ _ _ _ (scalarPullbackOrdinary l E L ι f).hom ℤ _ _ _
      (@Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _ dE _)
      (@Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _ _ dL) := by
  let := dE
  let := dL
  let := cE
  let := cL
  have : (integralOperationsGoodComplex l E X).IsStableUnderShift ℤ :=
    ⟨fun r ↦ ⟨fun P hP ↦ (hdE ⟨P, hP⟩ r).1⟩⟩
  have : (integralOperationsGoodComplex l L X).IsStableUnderShift ℤ :=
    ⟨fun r ↦ ⟨fun P hP ↦ (hdL ⟨P, hP⟩ r).1⟩⟩
  let ιE := (integralOperationsGoodComplex l E X).ι
  let ιL := (integralOperationsGoodComplex l L X).ι
  let Q := (DerivedCategory.Q : CochainComplex (integralTowerModules l E X) ℤ ⥤ _)
  let FE := integralDerivedPullback l E f
  let FL := integralDerivedPullback l L f
  let TE := integralOperationsPullbackComplexFunctor l E f
  let TL := integralOperationsPullbackComplexFunctor l L f
  let OcX := (integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)
  let OcY := (integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)
  let ODX := integralOrdinaryDerivedScalar l E L ι X
  let ODY := integralOrdinaryDerivedScalar l E L ι Y
  let Og : (integralOperationsGoodComplex l E X).FullSubcategory ⥤
      (integralOperationsGoodComplex l L X).FullSubcategory :=
    (integralOperationsGoodComplex l L X).lift (ιE ⋙ OcX) (fun P ↦ scalarGood l E L ι X P)
  let eE : (ιE ⋙ DerivedCategory.Q) ⋙ FE ≅ ιE ⋙ TE ⋙ DerivedCategory.Q :=
    integralDerivedPullbackComparison l E f
  let eL : (ιL ⋙ DerivedCategory.Q) ⋙ FL ≅ ιL ⋙ TL ⋙ DerivedCategory.Q :=
    integralDerivedPullbackComparison l L f
  have : NatTrans.CommShift eE.hom ℤ :=
    integralDerivedPullbackComparison_commShift l E f cE dE hdE
  have : NatTrans.CommShift eL.hom ℤ :=
    integralDerivedPullbackComparison_commShift l L f cL dL hdL
  let ch : TE ⋙ OcY ⟶ OcX ⋙ TL :=
    scalarRoosChain (integralOperationsPullbackTowerFunctor l E f)
      (integralOperationsPullbackTowerFunctor l L f) OcX (integralOrdinaryScalar l E L ι Y)
      (scalarPullbackTower l E L ι f)
  have : NatTrans.CommShift ch ℤ := scalarPullbackRoosChain_commShift l E L ι f cE hcE cL hcL
  let φY : DerivedCategory.Q ⋙ ODY ≅ OcY ⋙ DerivedCategory.Q :=
    (integralOrdinaryScalar l E L ι Y).mapDerivedCategoryFactors
  let φX : DerivedCategory.Q ⋙ ODX ≅ OcX ⋙ DerivedCategory.Q :=
    (integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors
  let lamE : Og ⋙ ιL ≅ ιE ⋙ OcX := ObjectProperty.liftCompιIso _ _ _
  let θ : Og ⋙ (ιL ⋙ DerivedCategory.Q) ⟶ (ιE ⋙ DerivedCategory.Q) ⋙ ODX :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight lamE.hom DerivedCategory.Q ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft ιE φX.inv ≫
      (Functor.associator _ _ _).inv
  let ψ : (ιE ⋙ DerivedCategory.Q) ⋙ (FE ⋙ ODY) ⟶ (ιE ⋙ DerivedCategory.Q) ⋙ (ODX ⋙ FL) :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight eE.hom ODY ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft ιE (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft ιE (Functor.whiskerLeft TE φY.hom) ≫
      Functor.whiskerLeft ιE (Functor.associator _ _ _).inv ≫
      Functor.whiskerLeft ιE (Functor.whiskerRight ch DerivedCategory.Q) ≫
      Functor.whiskerLeft ιE (Functor.associator _ _ _).hom ≫ (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight lamE.inv (TL ⋙ DerivedCategory.Q) ≫ (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft Og eL.inv ≫ (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight θ FL ≫ (Functor.associator _ _ _).hom
  have hθ : NatTrans.CommShift θ ℤ := by
    dsimp only [θ]
    infer_instance
  have hψ : NatTrans.CommShift ψ ℤ := by
    dsimp only [ψ]
    infer_instance
  have hN := (scalarPullbackOrdinary_existsUnique l E L ι f).exists.choose_spec
  have key : Functor.whiskerLeft (ιE ⋙ DerivedCategory.Q) (scalarPullbackOrdinary l E L ι f).hom =
      ψ := by
    ext P
    have hP := hN P
    have hl1 : lamE.hom.app P = 𝟙 _ := rfl
    have hl2 : lamE.inv.app P = 𝟙 _ := rfl
    simp only [ψ, θ, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
      Category.comp_id, hl1, hl2]
    have hP' : ODY.map (eE.hom.app P) ≫ φY.hom.app (TE.obj (ιE.obj P)) ≫
        DerivedCategory.Q.map (ch.app (ιE.obj P)) ≫ eL.inv.app (Og.obj P) ≫
        FL.map (φX.inv.app (ιE.obj P)) =
        (scalarPullbackOrdinary l E L ι f).hom.app ((ιE ⋙ DerivedCategory.Q).obj P) := by
      have hP2 := (reassoc_of% hP) (eL.inv.app (Og.obj P) ≫ FL.map (φX.inv.app (ιE.obj P)))
      erw [Category.assoc] at hP2
      erw [hP2, Category.assoc, Category.assoc, eL.hom_inv_id_app_assoc (Og.obj P),
        ← FL.map_comp, φX.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.comp_id]
      rfl
    rw [← hP']
    simp only [CategoryTheory.Functor.map_id]
    erw [Category.id_comp, Category.id_comp, Category.id_comp, Category.id_comp,
      Category.id_comp, Category.id_comp]
  have hes (K : DerivedCategory (integralTowerModules l E X)) :
      ∃ P, Nonempty ((ιE ⋙ DerivedCategory.Q).obj P ≅ K) := by
    have := integralOperationsGoodLocalization_isLocalization l E X
    exact (Localization.essSurj (integralOperationsGoodLocalization l E X)
      ((HomologicalComplex.quasiIso (integralTowerModules l E X) (.up ℤ)).inverseImage
        (integralOperationsGoodComplex l E X).ι)).mem_essImage K
  rw [← key] at hψ
  refine NatTrans.CommShift.of_whiskerLeft _ (ιE ⋙ DerivedCategory.Q) (fun K ↦ ?_)
  obtain ⟨P, ⟨e⟩⟩ := hes K
  exact ⟨P, e.inv, inferInstance⟩

end WeilConjectures
