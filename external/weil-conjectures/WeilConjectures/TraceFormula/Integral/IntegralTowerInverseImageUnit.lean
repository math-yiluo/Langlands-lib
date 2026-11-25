/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
public import WeilConjectures.AlgebraicGeometry.SixFunctors.InverseImagePullbackComparisonDerived
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# The tensor-unit comparison on whole quotient towers

Source: Stacks Project, Tags 03D6 and 0941; blueprint Global powers in
`sec-trace-formula/sk-thm-trace-transport/thm-trf-l-function-euler-product.proof.md`
(blueprint: def-trf-integral-tower-inverse-image-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u v w
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]

private def towerSiteAdjunction : proEtaleIsoPostcompose g ⊣ proEtaleBaseChange g :=
  MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
    (inferInstance : WeaklyEtale g) trivial

private def towerSiteEquivalence : X.ProEt ≌ Y.ProEt := by
  letI := (proEtaleIsoPostcompose_equivalence g).1
  letI := (towerSiteAdjunction g).isEquivalence_right_of_isEquivalence_left
  exact (towerSiteAdjunction g).toEquivalence

private theorem towerBaseChangeCocontinuous :
    (proEtaleBaseChange g).IsCocontinuous (ProEt.topology Y) (ProEt.topology X) := by
  exact ((towerSiteEquivalence g).symm.toAdjunction.isCocontinuous_iff_coverPreserving
    (ProEt.topology Y) (ProEt.topology X)).2
      (proEtaleIsoPostcompose_equivalence g).2.2.2.1.some

private theorem towerDirectRingMap_isIso (A : CommRingCat.{max u (t + 1)}) :
    IsIso (coefficientProEtaleDirectRingMap g A) := by
  have := towerBaseChangeCocontinuous g
  let e := (proEtaleBaseChange g).pushforwardContinuousSheafificationCompatibility
    CommRingCat.{max u (t + 1)} (ProEt.topology Y) (ProEt.topology X)
  have h : coefficientProEtaleDirectRingMap g A =
      e.hom.app ((Functor.const X.ProEtᵒᵖ).obj A) := by
    apply ((sheafificationAdjunction (ProEt.topology Y)
      CommRingCat.{max u (t + 1)}).homEquiv _ _).injective
    rw [coefficientProEtaleDirectRingMap, Equiv.apply_symm_apply]
    exact ((proEtaleBaseChange g).toSheafify_pullbackSheafificationCompatibility
      CommRingCat.{max u (t + 1)} (ProEt.topology Y) (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj A)).symm
  rw [h]
  infer_instance

private def towerSequenceSiteEquivalence : (ℕ × X.ProEt) ≌ (ℕ × Y.ProEt) :=
  (CategoryTheory.Equivalence.refl (C := ℕ)).prod (towerSiteEquivalence g)

private theorem towerSequencePostcomposeContinuous :
    ((𝟭 ℕ).prod (proEtaleIsoPostcompose g)).IsContinuous
      (coefficientSequenceTopology (ProEt.topology X))
      (coefficientSequenceTopology (ProEt.topology Y)) := by
  let F := (𝟭 ℕ).prod (proEtaleIsoPostcompose g)
  have : F.IsEquivalence := (towerSequenceSiteEquivalence g).isEquivalence_functor
  have : RepresentablyFlat F := inferInstance
  apply Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfFlat _ _)
  constructor
  intro A S hS
  change (S.functorPushforward F).functorPullback (Prod.sectR A.1 Y.ProEt) ∈
    ProEt.topology Y _
  apply (ProEt.topology Y).superset_covering _
    ((proEtaleIsoPostcompose_equivalence g).2.2.2.1.some.cover_preserve hS)
  rintro V a ⟨W, b, c, hb, rfl⟩
  exact ⟨(A.1, W), Prod.mkHom (𝟙 A.1) b, Prod.mkHom (𝟙 A.1) c, hb, rfl⟩

private theorem towerSequenceRingMap_isIso :
    IsIso (integralComparisonSequenceRingMap l E g) := by
  have : ∀ A, IsIso ((integralComparisonSequenceRingMap l E g).hom.app A) := by
    intro A
    change IsIso ((coefficientProEtaleDirectRingMap g
      (CommRingCat.of (ULift.{t + 1}
        (Padic.coefficientExtensionRing l E (A.unop.1 + 1))))).hom.app (op A.unop.2))
    have := towerDirectRingMap_isIso g (CommRingCat.of (ULift.{t + 1}
      (Padic.coefficientExtensionRing l E (A.unop.1 + 1))))
    infer_instance
  have : IsIso (integralComparisonSequenceRingMap l E g).hom :=
    NatIso.isIso_of_isIso_app _
  exact (ObjectProperty.isIso_hom_iff _).mp inferInstance

private theorem towerSequenceDirectImage_equivalence :
    (integralComparisonSequenceDirectImage l E g).IsEquivalence := by
  let B := integralComparisonSequenceBaseChange g
  let P := (𝟭 ℕ).prod (proEtaleIsoPostcompose g)
  let J := coefficientSequenceTopology (ProEt.topology Y)
  let K := coefficientSequenceTopology (ProEt.topology X)
  let eqv := (towerSequenceSiteEquivalence g).symm
  have : B.IsContinuous J K := integralComparisonSequenceBaseChangeContinuous g
  have : P.IsContinuous K J := towerSequencePostcomposeContinuous g
  have : eqv.functor.IsContinuous J K :=
    (show B.IsContinuous J K from inferInstance)
  have : eqv.inverse.IsContinuous K J :=
    (show P.IsContinuous K J from inferInstance)
  let R := (sheafCompose K (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
    (coefficientSequenceCommRingSheaf l E X)
  let S := (sheafCompose J (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
    (coefficientSequenceCommRingSheaf l E Y)
  let φ : S ⟶ (B.sheafPushforwardContinuous RingCat.{max u (t + 1)} J K).obj R :=
    ⟨Functor.whiskerRight (integralComparisonSequenceRingMap l E g).hom
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})⟩
  have := towerSequenceRingMap_isIso l E g
  have : IsIso φ.hom := by
    change IsIso (Functor.whiskerRight
      (integralComparisonSequenceRingMap l E g).hom
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}))
    infer_instance
  have : IsIso φ := (ObjectProperty.isIso_hom_iff _).mp inferInstance
  let adj := eqv.toAdjunction
  let shAdj := adj.sheafPushforwardContinuous (E := RingCat.{max u (t + 1)}) J K
  let ψ : R ⟶ (P.sheafPushforwardContinuous RingCat.{max u (t + 1)} K J).obj S :=
    shAdj.unit.app R ≫ (P.sheafPushforwardContinuous RingCat.{max u (t + 1)} K J).map (inv φ)
  have H₁ : Functor.whiskerRight (NatTrans.op eqv.counit) R.obj =
      ψ.hom ≫ eqv.inverse.op.whiskerLeft φ.hom := by
    have h : shAdj.unit.app R =
        ψ ≫ (P.sheafPushforwardContinuous RingCat.{max u (t + 1)} K J).map φ := by
      simp [ψ]
    exact congrArg (fun f ↦ f.hom) h
  have H₂ : φ.hom ≫ eqv.functor.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op eqv.unit) S.obj = 𝟙 S.obj := by
    have hh : φ ≫ (B.sheafPushforwardContinuous RingCat.{max u (t + 1)} J K).map ψ ≫
        shAdj.counit.app S = 𝟙 S := by
      dsimp only [ψ]
      simp only [Functor.map_comp, Category.assoc]
      erw [shAdj.counit.naturality (inv φ)]
      have ht := shAdj.left_triangle_components R
      calc
        _ = φ ≫ ((B.sheafPushforwardContinuous RingCat.{max u (t + 1)} J K).map
            (shAdj.unit.app R) ≫ shAdj.counit.app
              ((B.sheafPushforwardContinuous RingCat.{max u (t + 1)} J K).obj R)) ≫ inv φ := by
          simp only [Category.assoc, Functor.id_map]
        _ = φ ≫ 𝟙 _ ≫ inv φ := congrArg (fun h ↦ φ ≫ h ≫ inv φ) ht
        _ = _ := by simp
    exact congrArg (fun f ↦ f.hom) hh
  exact (SheafOfModules.pushforwardPushforwardEquivalence eqv φ ψ H₁ H₂).isEquivalence_functor

private abbrev towerQuotientRing (W : Scheme.{t}) (n : ℕ) :=
  integralCoefficientSheaf l E W n

private theorem towerPostcomposeBaseChangeContinuous :
    (proEtaleIsoPostcompose g ⋙ proEtaleBaseChange g).IsContinuous
      (ProEt.topology X) (ProEt.topology X) :=
  Functor.isContinuous_comp _ _ _ (ProEt.topology Y) _

attribute [local instance] towerPostcomposeBaseChangeContinuous

private def towerFiniteCoefficientMap (n : ℕ) :
    (isoSectionwiseInverseImage g RingCat.{max u (t + 1)}).obj
      (towerQuotientRing l E Y n) ⟶ towerQuotientRing l E X n :=
  (isoSectionwiseInverseImage g RingCat.{max u (t + 1)}).map
    (show towerQuotientRing l E Y n ⟶
      ((proEtaleBaseChange g).sheafPushforwardContinuous RingCat.{max u (t + 1)}
        (ProEt.topology Y) (ProEt.topology X)).obj (towerQuotientRing l E X n) from
    ⟨Functor.whiskerRight (coefficientProEtaleDirectRingMap g
      (CommRingCat.of (ULift.{t + 1}
        (Padic.coefficientExtensionRing l E (n + 1))))).hom
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})⟩) ≫
    (Functor.sheafPushforwardContinuousNatTrans (towerSiteAdjunction g).unit
      RingCat.{max u (t + 1)} (ProEt.topology X) (ProEt.topology X)).app (towerQuotientRing l E X n)

omit [IsIso g] in
private theorem towerConstantUnit (A : CommRingCat.{max u (t + 1)})
    (U : Y.ProEtᵒᵖ) :
    (toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app U ≫
      (coefficientProEtaleDirectRingMap.{t, u} g A).hom.app U =
    (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app
      ((proEtaleBaseChange g).op.obj U) := by
  have h := (sheafificationAdjunction (ProEt.topology Y)
      CommRingCat.{max u (t + 1)}).homEquiv ((Functor.const Y.ProEtᵒᵖ).obj A)
        (((proEtaleBaseChange g).sheafPushforwardContinuous CommRingCat.{max u (t + 1)}
          (ProEt.topology Y) (ProEt.topology X)).obj
            ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).obj A))
      |>.apply_symm_apply (Functor.whiskerLeft (proEtaleBaseChange g).op
        (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)))
  exact congrArg (fun α ↦ α.app U) h

private theorem towerFiniteCoefficientMap_eq (n : ℕ) :
    towerFiniteCoefficientMap l E g n = inverseImageFiniteCoefficientMap l E g n := by
  apply (isoSectionwiseConstantMap_existsUnique g
    (CommRingCat.of (ULift.{t + 1}
      (Padic.coefficientExtensionRing l E (n + 1))))).unique
  · intro U a
    let A : CommRingCat.{max u (t + 1)} := CommRingCat.of (ULift.{t + 1}
      (Padic.coefficientExtensionRing l E (n + 1)))
    have h' := congrArg (fun f ↦ f a)
      (towerConstantUnit g A (op ((proEtaleIsoPostcompose g).obj U)))
    change (towerQuotientRing l E X n).obj.map (proEtaleIsoCommaArrow g U).op
      ((coefficientProEtaleDirectRingMap g A).hom.app
        (op ((proEtaleIsoPostcompose g).obj U))
        ((toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app
          (op ((proEtaleIsoPostcompose g).obj U)) a)) = _
    simp only [CommRingCat.comp_apply] at h'
    trans (towerQuotientRing l E X n).obj.map (proEtaleIsoCommaArrow g U).op
      ((toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app
        ((proEtaleBaseChange g).op.obj (op ((proEtaleIsoPostcompose g).obj U))) a)
    · exact congrArg (fun z ↦
        (towerQuotientRing l E X n).obj.map (proEtaleIsoCommaArrow g U).op z) h'
    exact congrArg (fun f ↦ f a)
      ((toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).naturality
        (proEtaleIsoCommaArrow g U).op).symm
  · exact (isoSectionwiseConstantMap_existsUnique g _).exists.choose_spec

private theorem towerCompletedProjection (n : ℕ) :
    inverseImageCompletedCoefficientMap l E g ≫
      (limit.π (integralCoefficientSheafSystem l E X) (op n)) =
    (isoSectionwiseInverseImage g RingCat.{max u (t + 1)}).map
        (limit.π (integralCoefficientSheafSystem l E Y) (op n)) ≫
      towerFiniteCoefficientMap l E g n := by
  rw [towerFiniteCoefficientMap_eq]
  exact limit.lift_π _ (op n)

private def towerRestrictionRing (W : Scheme.{t}) (n : ℕ) :=
  ((sheafCompose (ProEt.topology W)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
    (completedIntegralCommRingProjectionUnrestricted l E W n)) ≫
      eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm

private def towerComma (n : ℕ) :
    Prod.sectR n X.ProEt ⟶
      (proEtaleIsoPostcompose g ⋙ Prod.sectR n Y.ProEt) ⋙
        integralComparisonSequenceBaseChange g where
  app U := Prod.mkHom (𝟙 n) (proEtaleIsoCommaArrow g U)
  naturality := by
    intro U V f
    apply Prod.hom_ext
    · apply Subsingleton.elim
    · exact (towerSiteAdjunction g).unit.naturality f

private theorem towerPostcomposeSliceContinuous (n : ℕ) :
    (proEtaleIsoPostcompose g ⋙ Prod.sectR n Y.ProEt).IsContinuous
      (ProEt.topology X) (coefficientSequenceTopology (ProEt.topology Y)) := by
  have := coefficientSequenceEvaluationContinuous Y n
  exact Functor.isContinuous_comp _ _ _ (ProEt.topology Y) _

attribute [local instance] towerPostcomposeSliceContinuous

private theorem towerPostcomposeSliceBaseChangeContinuous (n : ℕ) :
    ((proEtaleIsoPostcompose g ⋙ Prod.sectR n Y.ProEt) ⋙
      integralComparisonSequenceBaseChange g).IsContinuous
      (ProEt.topology X) (coefficientSequenceTopology (ProEt.topology X)) :=
  Functor.isContinuous_comp _ _ _ (coefficientSequenceTopology (ProEt.topology Y)) _

attribute [local instance] towerPostcomposeSliceBaseChangeContinuous

private theorem towerComma_isIso (n : ℕ) : IsIso (towerComma g n) := by
  have := (proEtaleIsoPostcompose_equivalence g).1
  have := (towerSiteAdjunction g).isEquivalence_right_of_isEquivalence_left
  have : ∀ U, IsIso ((towerComma g n).app U) := by
    intro U
    change IsIso (Prod.mkHom (𝟙 n) ((towerSiteAdjunction g).unit.app U))
    apply (isIso_prod_iff _ _).mpr
    exact ⟨inferInstance, inferInstance⟩
  exact NatIso.isIso_of_isIso_app _

private def towerRestrictionTransportRing (n : ℕ) :
    completedIntegralCoefficientSheafUnrestricted l E X ⟶
      (((proEtaleIsoPostcompose g ⋙ Prod.sectR n Y.ProEt) ⋙
        integralComparisonSequenceBaseChange g).sheafPushforwardContinuous
          RingCat.{max u (t + 1)} (ProEt.topology X)
            (coefficientSequenceTopology (ProEt.topology X))).obj
      ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
        (coefficientSequenceCommRingSheaf l E X)) :=
  inv (inverseImageCompletedCoefficientMap l E g) ≫
    (isoSectionwiseInverseImage g RingCat.{max u (t + 1)}).map
      (towerRestrictionRing l E Y n) ≫
    ((proEtaleIsoPostcompose g ⋙ Prod.sectR n Y.ProEt).sheafPushforwardContinuous
      RingCat.{max u (t + 1)} (ProEt.topology X)
        (coefficientSequenceTopology (ProEt.topology Y))).map
        (show (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
          (coefficientSequenceCommRingSheaf l E Y) ⟶
          ((integralComparisonSequenceBaseChange g).sheafPushforwardContinuous
            RingCat.{max u (t + 1)} _ _).obj ((sheafCompose _
              (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
                (coefficientSequenceCommRingSheaf l E X)) from
          ⟨Functor.whiskerRight (integralComparisonSequenceRingMap l E g).hom
            (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})⟩)

private theorem towerRestrictionRing_app (W : Scheme.{t}) (n : ℕ) (U : W.ProEtᵒᵖ) :
    (towerRestrictionRing l E W n).hom.app U =
      (limit.π (integralCoefficientSheafSystem l E W) (op n)).hom.app U := by
  have he :
      (eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm).hom.app U = 𝟙 _ := by
    rw [ObjectProperty.eqToHom_hom, eqToHom_app]
    rfl
  change _ ≫ (eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm).hom.app U = _
  rw [he, Category.comp_id]
  rfl

private theorem towerPushforwardMapApp {C : Type*} [Category* C]
    {D : Type*} [Category* D] (F : C ⥤ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) [F.IsContinuous J K]
    {R S : Sheaf K RingCat.{v}} (f : R ⟶ S) (U : Cᵒᵖ) :
    ((F.sheafPushforwardContinuous RingCat.{v} J K).map f).hom.app U =
      f.hom.app (F.op.obj U) := rfl

private theorem towerVerticalMap {C : Type*} [Category* C]
    {A : Type*} [Category* A] (F : ℕᵒᵖ ⥤ Cᵒᵖ ⥤ A) (n : ℕ)
    {U V : C} (f : U ⟶ V) :
    ((prodOpEquiv (C := ℕ) (D := C)).functor ⋙ Functor.uncurry.obj F).map
      (Prod.mkHom (𝟙 n) f).op = (F.obj (op n)).map f.op := by
  dsimp
  rw [CategoryTheory.Functor.map_id]
  simp

private theorem towerSequenceVerticalRingMap (n : ℕ) {U V : X.ProEt} (f : U ⟶ V) :
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}).map
      (((coefficientSequenceCommRingSystem l E X ⋙
        sheafToPresheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).obj (op n)).map
          f.op) = (integralCoefficientSheaf l E X n).obj.map f.op := rfl

private theorem towerRestrictionTransportRing_eq (n : ℕ) :
    towerRestrictionTransportRing l E g n ≫
      (Functor.sheafPushforwardContinuousNatTrans (towerComma g n) RingCat.{max u (t + 1)}
        (ProEt.topology X) (coefficientSequenceTopology (ProEt.topology X))).app
          ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
            (coefficientSequenceCommRingSheaf l E X)) =
      towerRestrictionRing l E X n := by
  apply (cancel_epi (inverseImageCompletedCoefficientMap l E g)).1
  simp only [towerRestrictionTransportRing, ← Category.assoc,
    IsIso.hom_inv_id, Category.id_comp]
  have h := towerCompletedProjection l E g n
  ext1
  apply NatTrans.ext
  funext U
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    towerPushforwardMapApp, towerRestrictionRing_app]
  have hh := congrArg (fun f ↦ f.hom.app U) h.symm
  simp only [towerFiniteCoefficientMap, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app, towerPushforwardMapApp] at hh
  dsimp only [Functor.sheafPushforwardContinuousNatTrans,
    Functor.whiskerRight_app, NatTrans.op_app] at hh ⊢
  change (_ ≫ _) ≫
    (coefficientSequenceCommRingPresheaf l E X ⋙
      forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}).map
        (Prod.mkHom (𝟙 n) (proEtaleIsoCommaArrow g U.unop)).op = _
  change (_ ≫ _) ≫
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}).map
      (((prodOpEquiv (C := ℕ) (D := X.ProEt)).functor ⋙ Functor.uncurry.obj
        (coefficientSequenceCommRingSystem l E X ⋙
          sheafToPresheaf (ProEt.topology X) CommRingCat.{max u (t + 1)})).map
            (Prod.mkHom (𝟙 n) (proEtaleIsoCommaArrow g U.unop)).op) = _
  rw [towerVerticalMap, towerSequenceVerticalRingMap]
  change ((limit.π (integralCoefficientSheafSystem l E Y) (op n)).hom.app
      ((proEtaleIsoPostcompose g).op.obj U) ≫
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}).map
      ((coefficientProEtaleDirectRingMap g
        (CommRingCat.of (ULift.{t + 1}
          (Padic.coefficientExtensionRing l E (n + 1))))).hom.app
            ((proEtaleIsoPostcompose g).op.obj U))) ≫
      (integralCoefficientSheaf l E X n).obj.map
        (proEtaleIsoCommaArrow g U.unop).op = _
  exact (Category.assoc _ _ _).trans hh

set_option backward.defeqAttrib.useBackward true

private def towerHomApply {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{v}}
    {M N : SheafOfModules.{w} R} (f : M ⟶ N) (U : Cᵒᵖ) :
    ↥(M.val.obj U) → ↥(N.val.obj U) := fun x ↦ f.val.app U x

private def towerMapApply {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{v}}
    (M : SheafOfModules.{w} R) {U V : Cᵒᵖ} (f : U ⟶ V) :
    ↥(M.val.obj U) → ↥(M.val.obj V) := fun x ↦ M.val.map f x

private theorem towerHomApplyHEq {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{v}}
    {M N : SheafOfModules.{w} R} (f : M ⟶ N) (U : Cᵒᵖ) :
    HEq (fun x ↦ f.val.app U x) (towerHomApply f U) := HEq.rfl

private theorem towerMapApplyHEq {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{v}}
    (M : SheafOfModules.{w} R) {U V : Cᵒᵖ} (f : U ⟶ V) :
    HEq (fun x ↦ M.val.map f x) (towerMapApply M f) := HEq.rfl

private def towerPushSection
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    {S : Sheaf J RingCat.{v}} {R : Sheaf K RingCat.{v}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R)
    (M : SheafOfModules.{w} R) (U : Cᵒᵖ) (x : M.val.obj (F.op.obj U)) :
    ((SheafOfModules.pushforward φ).obj M).val.obj U := x

private theorem towerPushSection_surjective
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    {S : Sheaf J RingCat.{v}} {R : Sheaf K RingCat.{v}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R)
    (M : SheafOfModules.{w} R) (U : Cᵒᵖ) :
    Function.Surjective (towerPushSection F φ M U) := fun x ↦ ⟨x, rfl⟩

private theorem towerPushSection_map
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    {S : Sheaf J RingCat.{v}} {R : Sheaf K RingCat.{v}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R)
    {M N : SheafOfModules.{w} R} (f : M ⟶ N) (U : Cᵒᵖ)
    (x : M.val.obj (F.op.obj U)) :
    towerHomApply ((SheafOfModules.pushforward φ).map f) U
        (towerPushSection F φ M U x) =
      towerPushSection F φ N U (towerHomApply f (F.op.obj U) x) := rfl

private def towerGenericUnitSection
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    {S : Sheaf J RingCat.{v}} {R : Sheaf K RingCat.{v}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R)
    (L : SheafOfModules.{w} S ⥤ SheafOfModules.{w} R)
    (η : 𝟭 _ ⟶ L ⋙ SheafOfModules.pushforward φ)
    (M : SheafOfModules.{w} S) (U : Cᵒᵖ) (x : M.val.obj U) :
    (L.obj M).val.obj (F.op.obj U) := (η.app M).val.app U x

private theorem towerGenericUnitSection_naturality
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    {S : Sheaf J RingCat.{v}} {R : Sheaf K RingCat.{v}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R)
    (L : SheafOfModules.{w} S ⥤ SheafOfModules.{w} R)
    (η : 𝟭 _ ⟶ L ⋙ SheafOfModules.pushforward φ)
    (M : SheafOfModules.{w} S) {U V : Cᵒᵖ} (f : U ⟶ V) (x : M.val.obj U) :
    towerGenericUnitSection F φ L η M V (towerMapApply M f x) =
      towerMapApply (L.obj M) (F.op.map f)
        (towerGenericUnitSection F φ L η M U x) := by
  exact PresheafOfModules.naturality_apply (η.app M).val f x

private def towerEvaluationIso
    {A : Type*} [Category* A] {B : Type*} [Category* B]
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    {Q : Type*} [Category* Q]
    (RY : A ⥤ B ⥤ C) (I : C ⥤ D) (L : A ⥤ Q) (RX : Q ⥤ B ⥤ D) (n : B)
    (e : (RY ⋙ (evaluation B C).obj n) ⋙ I ≅
      L ⋙ RX ⋙ (evaluation B D).obj n) :
    (RY ⋙ (Functor.whiskeringRight B C D).obj I) ⋙ (evaluation B D).obj n ≅
      (L ⋙ RX) ⋙ (evaluation B D).obj n := e

private def towerAssembleIso
    {A : Type*} [Category* A] {B : Type*} [Category* B]
    {D : Type*} [Category* D] (F G : A ⥤ B ⥤ D)
    (e : ∀ n : B, F ⋙ (evaluation B D).obj n ≅ G ⋙ (evaluation B D).obj n)
    (h : ∀ (M : A) {m n : B} (f : m ⟶ n),
      (F.obj M).map f ≫ (e n).hom.app M = (e m).hom.app M ≫ (G.obj M).map f) :
    F ≅ G :=
  NatIso.ofComponents (fun M ↦ NatIso.ofComponents (fun n ↦ (e n).app M)
    (by intro m n f; exact h M f)) (by
      intro M N f
      apply NatTrans.ext
      funext n
      exact (e n).hom.naturality f)

private theorem towerAssembleIso_hom_app
    {A : Type*} [Category* A] {B : Type*} [Category* B]
    {D : Type*} [Category* D] (F G : A ⥤ B ⥤ D)
    (e : ∀ n : B, F ⋙ (evaluation B D).obj n ≅ G ⋙ (evaluation B D).obj n)
    (h : ∀ (M : A) {m n : B} (f : m ⟶ n),
      (F.obj M).map f ≫ (e n).hom.app M = (e m).hom.app M ≫ (G.obj M).map f)
    (M : A) (n : B) :
    ((towerAssembleIso F G e h).hom.app M).app n = (e n).hom.app M := rfl

private theorem towerHomApply_comp
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{v}} {M N P : SheafOfModules.{w} R}
    (f : M ⟶ N) (g : N ⟶ P) (U : Cᵒᵖ) (x : M.val.obj U) :
    towerHomApply (f ≫ g) U x = towerHomApply g U (towerHomApply f U x) := rfl

private theorem towerHom_ext_basis
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{v}} {M N : SheafOfModules.{w} R} {f g : M ⟶ N}
    (A : Cᵒᵖ → Type w) (s : ∀ U, A U → M.val.obj U)
    (hs : ∀ U, Function.Surjective (s U))
    (h : ∀ U x, towerHomApply f U (s U x) = towerHomApply g U (s U x)) :
    f = g := by
  ext U z
  obtain ⟨x, rfl⟩ := hs U z
  exact h U x

private theorem towerWhiskered_map
    {A : Type*} [Category* A] {B : Type*} [Category* B]
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    (RY : A ⥤ B ⥤ C) (I : C ⥤ D) (M : A) {m n : B} (f : m ⟶ n) :
    (((RY ⋙ (Functor.whiskeringRight B C D).obj I).obj M).map f) =
      I.map ((RY.obj M).map f) := rfl

private theorem towerComp_obj_map
    {A : Type*} [Category* A] {B : Type*} [Category* B]
    {D : Type*} [Category* D] {Q : Type*} [Category* Q]
    (L : A ⥤ Q) (RX : Q ⥤ B ⥤ D) (M : A) {m n : B} (f : m ⟶ n) :
    (((L ⋙ RX).obj M).map f) = (RX.obj (L.obj M)).map f := rfl

private theorem towerProductVertical_map
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    {J : GrothendieckTopology (ℕ × D)} {R : Sheaf J RingCat.{v}}
    (B : C ⥤ D) (M : SheafOfModules.{w} R) {m n : ℕ} (h : n ≤ m)
    (U : D) (V : C) (a : U ⟶ B.obj V) (x : M.val.obj (op (m, B.obj V))) :
    towerMapApply M (Prod.mkHom (𝟙 n) a).op
        (towerMapApply M (((𝟭 ℕ).prod B).map
          (Prod.mkHom (homOfLE h) (𝟙 V))).op x) =
      towerMapApply M (Prod.mkHom (homOfLE h) (𝟙 U)).op
        (towerMapApply M (Prod.mkHom (𝟙 m) a).op x) := by
  unfold towerMapApply
  rw [← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply]
  apply PresheafOfModules.congr_map_apply
  apply Quiver.Hom.unop_inj
  ext <;> simp [Functor.prod]

private theorem towerCastApply {A C : Type v} {B D : Type w} (hA : A = C) (hB : B = D)
    (f : A → B) (k : C → D) (h : HEq f k) (x : C) :
    f (cast hA.symm x) = cast hB.symm (k x) := by
  subst C D
  cases h
  rfl

private theorem towerRestrictedSection_surjective (W : Scheme.{t})
    (M : coefficientSequenceModules l E W) (n : ℕ) (U : W.ProEtᵒᵖ) :
    Function.Surjective (integralComparisonRestrictedSection l E W M n U) := by
  intro x
  exact ⟨cast (integralComparisonRestrictedSectionType l E W M n U) x, by
    simp [integralComparisonRestrictedSection]⟩

private theorem towerRestrictionTransitionSpec (W : Scheme.{t})
    (M : coefficientSequenceModules l E W) (m n : ℕ) (h : n ≤ m) (U : W.ProEtᵒᵖ) :
    HEq (fun x ↦ (((coefficientSequenceRestriction l E W).obj M).map
      (homOfLE h).op).val.app U x)
      (fun x : M.val.obj (op (m, U.unop)) ↦
        M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x) := by
  unfold coefficientSequenceRestriction
  exact (coefficientSequenceRestriction_exists l E W).exists.choose_spec.2.1 M m n h U

set_option backward.defeqAttrib.useBackward true in
private theorem towerRestrictedSection_transition (W : Scheme.{t})
    (M : coefficientSequenceModules l E W) {m n : ℕ} (h : n ≤ m)
    (U : W.ProEtᵒᵖ) (x : M.val.obj (op (m, U.unop))) :
    towerHomApply (((coefficientSequenceRestriction l E W).obj M).map
      (homOfLE h).op) U
        (integralComparisonRestrictedSection l E W M m U x) =
      integralComparisonRestrictedSection l E W M n U
        (towerMapApply M (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x) := by
  exact towerCastApply (integralComparisonRestrictedSectionType l E W M m U)
    (integralComparisonRestrictedSectionType l E W M n U)
    (towerHomApply (((coefficientSequenceRestriction l E W).obj M).map
      (homOfLE h).op) U)
    (towerMapApply M (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op)
    ((towerHomApplyHEq _ U).symm.trans
      ((towerRestrictionTransitionSpec l E W M m n h U).trans
        (towerMapApplyHEq M _))) x

section GenericComma

variable {C₀ : Type*} [Category* C₀] {C₁ : Type*} [Category* C₁]
  {C₂ : Type*} [Category* C₂] {C₃ : Type*} [Category* C₃]
  {J₀ : GrothendieckTopology C₀} {J₁ : GrothendieckTopology C₁}
  {J₂ : GrothendieckTopology C₂} {J₃ : GrothendieckTopology C₃}
  {F₀ : C₀ ⥤ C₁} {F₁ : C₁ ⥤ C₂} {F₂ : C₂ ⥤ C₃} {H : C₀ ⥤ C₃}
  [F₀.IsContinuous J₀ J₁] [F₁.IsContinuous J₁ J₂] [F₂.IsContinuous J₂ J₃]
  [H.IsContinuous J₀ J₃] [(F₀ ⋙ F₁).IsContinuous J₀ J₂]
  [((F₀ ⋙ F₁) ⋙ F₂).IsContinuous J₀ J₃]
  {R₀ : Sheaf J₀ RingCat.{v}} {R₁ : Sheaf J₁ RingCat.{v}}
  {R₂ : Sheaf J₂ RingCat.{v}} {R₃ : Sheaf J₃ RingCat.{v}}
  (φ : R₀ ⟶ (F₀.sheafPushforwardContinuous RingCat J₀ J₁).obj R₁)
  (ψ : R₁ ⟶ (F₁.sheafPushforwardContinuous RingCat J₁ J₂).obj R₂)
  (χ : R₂ ⟶ (F₂.sheafPushforwardContinuous RingCat J₂ J₃).obj R₃)
  (ρ : R₀ ⟶ (H.sheafPushforwardContinuous RingCat J₀ J₃).obj R₃)
  (α : H ≅ (F₀ ⋙ F₁) ⋙ F₂)
  (hρ : (φ ≫ (F₀.sheafPushforwardContinuous RingCat J₀ J₁).map ψ ≫
    ((F₀ ⋙ F₁).sheafPushforwardContinuous RingCat J₀ J₂).map χ) ≫
      (Functor.sheafPushforwardContinuousNatTrans α.hom RingCat J₀ J₃).app R₃ = ρ)

private def towerGenericCommaIso :
    SheafOfModules.pushforward.{w} χ ⋙ SheafOfModules.pushforward ψ ⋙
        SheafOfModules.pushforward φ ≅ SheafOfModules.pushforward ρ :=
  isoWhiskerLeft (SheafOfModules.pushforward χ) (SheafOfModules.pushforwardComp φ ψ) ≪≫
    SheafOfModules.pushforwardComp _ χ ≪≫
    SheafOfModules.pushforwardCongr (Category.assoc _ _ _) ≪≫
    SheafOfModules.pushforwardNatIso _ α ≪≫ SheafOfModules.pushforwardCongr hρ

private theorem towerGenericCommaIso_apply (M : SheafOfModules.{w} R₃) (U : C₀ᵒᵖ)
    (x : M.val.obj (((F₀ ⋙ F₁) ⋙ F₂).op.obj U)) :
    ((towerGenericCommaIso φ ψ χ ρ α hρ).hom.app M).val.app U x =
      M.val.map (α.hom.app U.unop).op x := by
  simp [towerGenericCommaIso]
  rfl

private def towerGenericCoreUnitMap
    (L : SheafOfModules.{w} R₂ ⥤ SheafOfModules.{w} R₃)
    (η : 𝟭 _ ⟶ L ⋙ SheafOfModules.pushforward χ) :
    SheafOfModules.pushforward.{w} (F := F₀ ⋙ F₁) (J := J₀) (K := J₂)
        (S := R₀) (R := R₂)
        (φ ≫ (F₀.sheafPushforwardContinuous RingCat J₀ J₁).map ψ) ⟶
      L ⋙ SheafOfModules.pushforward ρ :=
  (SheafOfModules.pushforwardComp φ ψ).inv ≫
    whiskerRight η (SheafOfModules.pushforward ψ ⋙ SheafOfModules.pushforward φ) ≫
    (Functor.associator L (SheafOfModules.pushforward χ)
      (SheafOfModules.pushforward ψ ⋙ SheafOfModules.pushforward φ)).hom ≫
    whiskerLeft L (towerGenericCommaIso φ ψ χ ρ α hρ).hom

private theorem towerGenericCoreUnitMap_apply
    (L : SheafOfModules.{w} R₂ ⥤ SheafOfModules.{w} R₃)
    (η : 𝟭 _ ⟶ L ⋙ SheafOfModules.pushforward χ)
    (M : SheafOfModules.{w} R₂) (U : C₀ᵒᵖ)
    (x : M.val.obj ((F₀ ⋙ F₁).op.obj U)) :
    towerHomApply ((towerGenericCoreUnitMap φ ψ χ ρ α hρ L η).app M) U x =
      towerMapApply (L.obj M) (α.hom.app U.unop).op
        ((η.app M).val.app ((F₀ ⋙ F₁).op.obj U) x) := by
  change ((towerGenericCommaIso φ ψ χ ρ α hρ).hom.app
    (L.obj M)).val.app U ((η.app M).val.app ((F₀ ⋙ F₁).op.obj U) x) =
      (L.obj M).val.map (α.hom.app U.unop).op
        ((η.app M).val.app ((F₀ ⋙ F₁).op.obj U) x)
  exact towerGenericCommaIso_apply φ ψ χ ρ α hρ (L.obj M) U _

private def towerGenericComparisonIso
    (L : SheafOfModules.{w} R₂ ⥤ SheafOfModules.{w} R₃)
    (V : SheafOfModules.{w} R₂ ⥤ SheafOfModules.{w} R₁)
    (W : SheafOfModules.{w} R₃ ⥤ SheafOfModules.{w} R₀)
    (eY : V ≅ SheafOfModules.pushforward ψ)
    (eX : W ≅ SheafOfModules.pushforward ρ)
    (s : SheafOfModules.pushforward.{w} (F := F₀ ⋙ F₁)
      (J := J₀) (K := J₂) (S := R₀) (R := R₂)
      (φ ≫ (F₀.sheafPushforwardContinuous RingCat J₀ J₁).map ψ) ⟶
        L ⋙ SheafOfModules.pushforward ρ) [IsIso s]
    : V ⋙ SheafOfModules.pushforward φ ≅ L ⋙ W :=
  isoWhiskerRight eY (SheafOfModules.pushforward φ) ≪≫
    SheafOfModules.pushforwardComp φ ψ ≪≫ asIso s ≪≫ isoWhiskerLeft L eX.symm

private theorem towerGenericComparison_cancel
    (L : SheafOfModules.{w} R₂ ⥤ SheafOfModules.{w} R₃)
    (V : SheafOfModules.{w} R₂ ⥤ SheafOfModules.{w} R₁)
    (W : SheafOfModules.{w} R₃ ⥤ SheafOfModules.{w} R₀)
    (eY : V ≅ SheafOfModules.pushforward ψ)
    (eX : W ≅ SheafOfModules.pushforward ρ)
    (s : SheafOfModules.pushforward.{w} (F := F₀ ⋙ F₁)
      (J := J₀) (K := J₂) (S := R₀) (R := R₂)
      (φ ≫ (F₀.sheafPushforwardContinuous RingCat J₀ J₁).map ψ) ⟶
        L ⋙ SheafOfModules.pushforward ρ) [IsIso s]
    (M : SheafOfModules.{w} R₂) (U : C₀ᵒᵖ)
    (x : (V.obj M).val.obj (F₀.op.obj U)) :
    towerHomApply (eX.hom.app (L.obj M)) U
      (towerHomApply
        ((towerGenericComparisonIso φ ψ ρ L V W eY eX s).hom.app M) U x) =
      towerHomApply (s.app M) U
        ((eY.hom.app M).val.app (F₀.op.obj U) x) := by
  change (eX.hom.app (L.obj M)).val.app U
    ((eX.inv.app (L.obj M)).val.app U
      ((s.app M).val.app U ((eY.hom.app M).val.app (F₀.op.obj U) x))) = _
  exact congrArg (fun f ↦ f.val.app U
    ((s.app M).val.app U ((eY.hom.app M).val.app (F₀.op.obj U) x)))
    (eX.inv_hom_id_app (L.obj M))

end GenericComma

private theorem towerEvaluationPushforward_eq
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    {S T : Sheaf J RingCat.{v}} {R : Sheaf K RingCat.{v}}
    (p : S ⟶ T) (φ : T ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R) :
    SheafOfModules.pushforward.{w} φ ⋙ SheafOfModules.restrictScalars p =
      SheafOfModules.pushforward (p ≫ φ) := rfl

private theorem towerPushforwardEqToHom_cast
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    {S : Sheaf J RingCat.{v}} {R : Sheaf K RingCat.{v}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R)
    {V : SheafOfModules.{w} R ⥤ SheafOfModules.{w} S}
    (h : V = SheafOfModules.pushforward φ) (M : SheafOfModules.{w} R) (U : Cᵒᵖ)
    (e : ↥((V.obj M).val.obj U) = ↥(M.val.obj (F.op.obj U)))
    (x : M.val.obj (F.op.obj U)) :
    ((eqToHom h).app M).val.app U (cast e.symm x) = x := by
  subst V
  cases e
  rfl

private abbrev towerCompletedModuleRing (W : Scheme.{t}) :
    Sheaf (ProEt.topology W) RingCat.{max u (t + 1)} :=
  (sheafCompose (ProEt.topology W)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
      (completedIntegralCommRingSheafUnrestricted l E W)

private abbrev towerSequenceModuleRing (W : Scheme.{t}) :
    Sheaf (coefficientSequenceTopology (ProEt.topology W)) RingCat.{max u (t + 1)} :=
  (sheafCompose (coefficientSequenceTopology (ProEt.topology W))
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
      (coefficientSequenceCommRingSheaf l E W)

private def towerInverseModuleRingMap :
    towerCompletedModuleRing l E X ⟶
      ((proEtaleIsoPostcompose g).sheafPushforwardContinuous RingCat.{max u (t + 1)}
        (ProEt.topology X) (ProEt.topology Y)).obj (towerCompletedModuleRing l E Y) :=
  inv (inverseImageCompletedCoefficientMap l E g)

private def towerDirectSequenceModuleRingMap :
    towerSequenceModuleRing l E Y ⟶
      ((integralComparisonSequenceBaseChange g).sheafPushforwardContinuous
        RingCat.{max u (t + 1)} (coefficientSequenceTopology (ProEt.topology Y))
          (coefficientSequenceTopology (ProEt.topology X))).obj
            (towerSequenceModuleRing l E X) :=
  ⟨Functor.whiskerRight (integralComparisonSequenceRingMap l E g).hom
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})⟩

private def towerModuleInverseImage :
    scalarReductionSource l E Y ⥤ scalarReductionSource l E X :=
  SheafOfModules.pushforward.{max u (t + 1)} (F := proEtaleIsoPostcompose g)
    (J := ProEt.topology X) (K := ProEt.topology Y)
    (S := towerCompletedModuleRing l E X) (R := towerCompletedModuleRing l E Y)
    (towerInverseModuleRingMap l E g)

private def towerInverseSection (M : scalarReductionSource l E Y)
    (U : X.ProEtᵒᵖ) (x : M.val.obj (op ((proEtaleIsoPostcompose g).obj U.unop))) :
    ((towerModuleInverseImage l E g).obj M).val.obj U :=
  towerPushSection (J := ProEt.topology X) (K := ProEt.topology Y)
    (proEtaleIsoPostcompose g)
    (S := towerCompletedModuleRing l E X) (R := towerCompletedModuleRing l E Y)
    (towerInverseModuleRingMap l E g) M U x

private theorem towerInverseSection_surjective (M : scalarReductionSource l E Y)
    (U : X.ProEtᵒᵖ) : Function.Surjective (towerInverseSection l E g M U) :=
  towerPushSection_surjective (J := ProEt.topology X) (K := ProEt.topology Y)
    (proEtaleIsoPostcompose g)
    (S := towerCompletedModuleRing l E X) (R := towerCompletedModuleRing l E Y)
    (towerInverseModuleRingMap l E g) M U

private theorem towerInverseSection_map {M N : scalarReductionSource l E Y}
    (f : M ⟶ N) (U : X.ProEtᵒᵖ)
    (x : M.val.obj (op ((proEtaleIsoPostcompose g).obj U.unop))) :
    towerHomApply ((towerModuleInverseImage l E g).map f) U
        (towerInverseSection l E g M U x) =
      towerInverseSection l E g N U
        (towerHomApply f (op ((proEtaleIsoPostcompose g).obj U.unop)) x) :=
  towerPushSection_map (J := ProEt.topology X) (K := ProEt.topology Y)
    (proEtaleIsoPostcompose g)
    (S := towerCompletedModuleRing l E X) (R := towerCompletedModuleRing l E Y)
    (towerInverseModuleRingMap l E g) f U x

private def towerCoreMiddle (W : Scheme.{t}) (n : ℕ) :
    coefficientSequenceModules l E W ⥤ scalarReductionSource l E W :=
  SheafOfModules.pushforward.{max u (t + 1)} (F := Prod.sectR n W.ProEt)
    (J := ProEt.topology W) (K := coefficientSequenceTopology (ProEt.topology W))
    (S := towerCompletedModuleRing l E W) (R := towerSequenceModuleRing l E W)
    (towerRestrictionRing l E W n)

private def towerCoreSourceRing (n : ℕ) :
    towerCompletedModuleRing l E X ⟶
      ((proEtaleIsoPostcompose g ⋙ Prod.sectR n Y.ProEt).sheafPushforwardContinuous
        RingCat.{max u (t + 1)} (ProEt.topology X)
          (coefficientSequenceTopology (ProEt.topology Y))).obj
            (towerSequenceModuleRing l E Y) :=
  towerInverseModuleRingMap l E g ≫
    ((proEtaleIsoPostcompose g).sheafPushforwardContinuous RingCat.{max u (t + 1)}
      (ProEt.topology X) (ProEt.topology Y)).map (towerRestrictionRing l E Y n)

private def towerCoreSource (n : ℕ) :
    coefficientSequenceModules l E Y ⥤ scalarReductionSource l E X :=
  SheafOfModules.pushforward.{max u (t + 1)}
    (F := proEtaleIsoPostcompose g ⋙ Prod.sectR n Y.ProEt)
    (J := ProEt.topology X) (K := coefficientSequenceTopology (ProEt.topology Y))
    (S := towerCompletedModuleRing l E X) (R := towerSequenceModuleRing l E Y)
    (towerCoreSourceRing l E g n)

private theorem towerRestrictionCore_eq (W : Scheme.{t}) (n : ℕ) :
    coefficientSequenceRestriction l E W ⋙
        (evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n) =
      towerCoreMiddle l E W n := by
  exact (coefficientSequenceRestriction_evaluation l E W n).trans
    (towerEvaluationPushforward_eq (J := ProEt.topology W)
      (K := coefficientSequenceTopology (ProEt.topology W)) (Prod.sectR n W.ProEt)
      (S := towerCompletedModuleRing l E W) (T := integralCoefficientSheaf l E W n)
      (R := towerSequenceModuleRing l E W)
      ((sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
          (completedIntegralCommRingProjectionUnrestricted l E W n))
      (eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm))

private def towerLevelMap (n : ℕ) :
    towerCoreSource l E g n ⟶
      integralComparisonSequencePullback l E g ⋙ towerCoreMiddle l E X n := by
  have := towerComma_isIso g n
  exact towerGenericCoreUnitMap
    (C₀ := X.ProEt) (C₁ := Y.ProEt) (C₂ := ℕ × Y.ProEt) (C₃ := ℕ × X.ProEt)
    (J₀ := ProEt.topology X) (J₁ := ProEt.topology Y)
    (J₂ := coefficientSequenceTopology (ProEt.topology Y))
    (J₃ := coefficientSequenceTopology (ProEt.topology X))
    (F₀ := proEtaleIsoPostcompose g) (F₁ := Prod.sectR n Y.ProEt)
    (F₂ := integralComparisonSequenceBaseChange g) (H := Prod.sectR n X.ProEt)
    (R₀ := towerCompletedModuleRing l E X) (R₁ := towerCompletedModuleRing l E Y)
    (R₂ := towerSequenceModuleRing l E Y) (R₃ := towerSequenceModuleRing l E X)
    (towerInverseModuleRingMap l E g) (towerRestrictionRing l E Y n)
    (towerDirectSequenceModuleRingMap l E g) (towerRestrictionRing l E X n)
    (asIso (towerComma g n)) (towerRestrictionTransportRing_eq l E g n)
    (integralComparisonSequencePullback l E g)
    (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E g)).unit

private theorem towerLevelMap_apply (n : ℕ) (M : coefficientSequenceModules l E Y)
    (U : X.ProEt) (x : M.val.obj (op (n, (proEtaleIsoPostcompose g).obj U))) :
    towerHomApply (C := X.ProEt) (J := ProEt.topology X)
      (R := towerCompletedModuleRing l E X) ((towerLevelMap l E g n).app M) (op U) x =
      towerMapApply ((integralComparisonSequencePullback l E g).obj M)
        (Prod.mkHom (𝟙 n) (proEtaleIsoCommaArrow g U)).op
        (integralComparisonSequenceGenerator l E g M n
          ((proEtaleIsoPostcompose g).obj U) x) := by
  have := towerComma_isIso g n
  exact towerGenericCoreUnitMap_apply
    (C₀ := X.ProEt) (C₁ := Y.ProEt) (C₂ := ℕ × Y.ProEt) (C₃ := ℕ × X.ProEt)
    (J₀ := ProEt.topology X) (J₁ := ProEt.topology Y)
    (J₂ := coefficientSequenceTopology (ProEt.topology Y))
    (J₃ := coefficientSequenceTopology (ProEt.topology X))
    (F₀ := proEtaleIsoPostcompose g) (F₁ := Prod.sectR n Y.ProEt)
    (F₂ := integralComparisonSequenceBaseChange g) (H := Prod.sectR n X.ProEt)
    (R₀ := towerCompletedModuleRing l E X) (R₁ := towerCompletedModuleRing l E Y)
    (R₂ := towerSequenceModuleRing l E Y) (R₃ := towerSequenceModuleRing l E X)
    (towerInverseModuleRingMap l E g) (towerRestrictionRing l E Y n)
    (towerDirectSequenceModuleRingMap l E g) (towerRestrictionRing l E X n)
    (asIso (towerComma g n)) (towerRestrictionTransportRing_eq l E g n)
    (integralComparisonSequencePullback l E g)
    (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E g)).unit
    M (op U) x

private theorem towerLevelMap_isIso (n : ℕ) : IsIso (towerLevelMap l E g n) := by
  have := towerSequenceDirectImage_equivalence l E g
  have := towerComma_isIso g n
  unfold towerLevelMap towerGenericCoreUnitMap
  infer_instance

private def towerRestrictedLevelIso (W : Scheme.{t}) (n : ℕ) :
    coefficientSequenceRestriction l E W ⋙
        (evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n) ≅
      towerCoreMiddle l E W n :=
  eqToIso (towerRestrictionCore_eq l E W n)

private theorem towerRestrictedLevelIso_apply (W : Scheme.{t}) (n : ℕ)
    (M : coefficientSequenceModules l E W) (U : W.ProEtᵒᵖ)
    (x : M.val.obj (op (n, U.unop))) :
    ((towerRestrictedLevelIso l E W n).hom.app M).val.app U
        (integralComparisonRestrictedSection l E W M n U x) = x := by
  exact towerPushforwardEqToHom_cast (J := ProEt.topology W)
    (K := coefficientSequenceTopology (ProEt.topology W)) (Prod.sectR n W.ProEt)
    (S := towerCompletedModuleRing l E W) (R := towerSequenceModuleRing l E W)
    (towerRestrictionRing l E W n)
    (V := coefficientSequenceRestriction l E W ⋙
      (evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n))
    (towerRestrictionCore_eq l E W n) M U
    (integralComparisonRestrictedSectionType l E W M n U) x

private theorem towerRestrictedLevelIsoHomApply (W : Scheme.{t}) (n : ℕ)
    (M : coefficientSequenceModules l E W) (U : W.ProEtᵒᵖ)
    (x : M.val.obj (op (n, U.unop))) :
    towerHomApply (C := W.ProEt) (J := ProEt.topology W)
      (R := towerCompletedModuleRing l E W)
      ((towerRestrictedLevelIso l E W n).hom.app M) U
        (integralComparisonRestrictedSection l E W M n U x) = x := by
  exact towerRestrictedLevelIso_apply l E W n M U x

private def towerComparisonLevel (n : ℕ) :
    (coefficientSequenceRestriction l E Y ⋙
      (evaluation ℕᵒᵖ (scalarReductionSource l E Y)).obj (op n)) ⋙
        towerModuleInverseImage l E g ≅
      integralComparisonSequencePullback l E g ⋙ coefficientSequenceRestriction l E X ⋙
        (evaluation ℕᵒᵖ (scalarReductionSource l E X)).obj (op n) := by
  have := towerLevelMap_isIso l E g n
  exact towerGenericComparisonIso
    (C₀ := X.ProEt) (C₁ := Y.ProEt) (C₂ := ℕ × Y.ProEt) (C₃ := ℕ × X.ProEt)
    (J₀ := ProEt.topology X) (J₁ := ProEt.topology Y)
    (J₂ := coefficientSequenceTopology (ProEt.topology Y))
    (J₃ := coefficientSequenceTopology (ProEt.topology X))
    (F₀ := proEtaleIsoPostcompose g) (F₁ := Prod.sectR n Y.ProEt)
    (H := Prod.sectR n X.ProEt)
    (R₀ := towerCompletedModuleRing l E X) (R₁ := towerCompletedModuleRing l E Y)
    (R₂ := towerSequenceModuleRing l E Y) (R₃ := towerSequenceModuleRing l E X)
    (towerInverseModuleRingMap l E g) (towerRestrictionRing l E Y n)
    (towerRestrictionRing l E X n) (integralComparisonSequencePullback l E g)
    (coefficientSequenceRestriction l E Y ⋙
      (evaluation ℕᵒᵖ (scalarReductionSource l E Y)).obj (op n))
    (coefficientSequenceRestriction l E X ⋙
      (evaluation ℕᵒᵖ (scalarReductionSource l E X)).obj (op n))
    (towerRestrictedLevelIso l E Y n) (towerRestrictedLevelIso l E X n)
    (towerLevelMap l E g n)

private theorem towerModuleIso_injective {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{v}}
    {M N : SheafOfModules.{w} R} (e : M ≅ N) (U : Cᵒᵖ) :
    Function.Injective (towerHomApply e.hom U) := by
  exact (ConcreteCategory.bijective_of_isIso
    ((SheafOfModules.evaluation R U).mapIso e).hom).injective

private theorem towerComparisonLevel_apply (n : ℕ) (M : coefficientSequenceModules l E Y)
    (U : X.ProEt) (x : M.val.obj (op (n, (proEtaleIsoPostcompose g).obj U))) :
    towerHomApply (C := X.ProEt) (J := ProEt.topology X)
      (R := towerCompletedModuleRing l E X) ((towerComparisonLevel l E g n).hom.app M)
        (op U)
        (integralComparisonRestrictedSection l E Y M n
          (op ((proEtaleIsoPostcompose g).obj U)) x) =
      integralComparisonRestrictedSection l E X
        ((integralComparisonSequencePullback l E g).obj M) n (op U)
        (towerMapApply ((integralComparisonSequencePullback l E g).obj M)
          (Prod.mkHom (𝟙 n) (proEtaleIsoCommaArrow g U)).op
          (integralComparisonSequenceGenerator l E g M n
            ((proEtaleIsoPostcompose g).obj U) x)) := by
  apply towerModuleIso_injective (C := X.ProEt) (J := ProEt.topology X)
    (R := towerCompletedModuleRing l E X)
    ((towerRestrictedLevelIso l E X n).app
      ((integralComparisonSequencePullback l E g).obj M)) (op U)
  dsimp only [Iso.app_hom]
  conv_rhs => rw [towerRestrictedLevelIsoHomApply l E X n]
  have := towerLevelMap_isIso l E g n
  have h := towerGenericComparison_cancel
    (C₀ := X.ProEt) (C₁ := Y.ProEt) (C₂ := ℕ × Y.ProEt) (C₃ := ℕ × X.ProEt)
    (J₀ := ProEt.topology X) (J₁ := ProEt.topology Y)
    (J₂ := coefficientSequenceTopology (ProEt.topology Y))
    (J₃ := coefficientSequenceTopology (ProEt.topology X))
    (F₀ := proEtaleIsoPostcompose g) (F₁ := Prod.sectR n Y.ProEt)
    (H := Prod.sectR n X.ProEt)
    (R₀ := towerCompletedModuleRing l E X) (R₁ := towerCompletedModuleRing l E Y)
    (R₂ := towerSequenceModuleRing l E Y) (R₃ := towerSequenceModuleRing l E X)
    (towerInverseModuleRingMap l E g) (towerRestrictionRing l E Y n)
    (towerRestrictionRing l E X n) (integralComparisonSequencePullback l E g)
    (coefficientSequenceRestriction l E Y ⋙
      (evaluation ℕᵒᵖ (scalarReductionSource l E Y)).obj (op n))
    (coefficientSequenceRestriction l E X ⋙
      (evaluation ℕᵒᵖ (scalarReductionSource l E X)).obj (op n))
    (towerRestrictedLevelIso l E Y n) (towerRestrictedLevelIso l E X n)
    (towerLevelMap l E g n) M (op U)
    (integralComparisonRestrictedSection l E Y M n
      (op ((proEtaleIsoPostcompose g).obj U)) x)
  erw [towerRestrictedLevelIso_apply l E Y n M
    (op ((proEtaleIsoPostcompose g).obj U)) x] at h
  exact h.trans (towerLevelMap_apply l E g n M U x)

private theorem towerComparisonPush_apply (n : ℕ) (M : coefficientSequenceModules l E Y)
    (U : X.ProEt) (x : M.val.obj (op (n, (proEtaleIsoPostcompose g).obj U))) :
    towerHomApply (C := X.ProEt) (J := ProEt.topology X)
      (R := towerCompletedModuleRing l E X) ((towerComparisonLevel l E g n).hom.app M)
        (op U)
        (towerInverseSection l E g
          (((coefficientSequenceRestriction l E Y).obj M).obj (op n)) (op U)
          (integralComparisonRestrictedSection l E Y M n
            (op ((proEtaleIsoPostcompose g).obj U)) x)) =
      integralComparisonRestrictedSection l E X
        ((integralComparisonSequencePullback l E g).obj M) n (op U)
        (towerMapApply ((integralComparisonSequencePullback l E g).obj M)
          (Prod.mkHom (𝟙 n) (proEtaleIsoCommaArrow g U)).op
          (integralComparisonSequenceGenerator l E g M n
            ((proEtaleIsoPostcompose g).obj U) x)) := by
  exact towerComparisonLevel_apply l E g n M U x

/-- Apply the specified exact completed inverse image to every level and transition.
Source: Stacks 03D6, 0941 (blueprint: def-trf-integral-tower-inverse-image-unit). -/
abbrev integralTowerInverseImage :
    (ℕᵒᵖ ⥤ scalarReductionSource l E Y) ⥤ (ℕᵒᵖ ⥤ scalarReductionSource l E X) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (inverseImageIntegralModules l E g)

/-- Levelwise finite-limit preservation by the exact inverse image.
Source: Stacks 0941 (blueprint: def-trf-integral-tower-inverse-image-unit). -/
instance integralTowerInverseImageLimits : PreservesFiniteLimits
    (integralTowerInverseImage l E g) := ⟨fun _ _ _ ↦ inferInstance⟩

/-- Levelwise finite-colimit preservation by the exact inverse image.
Source: Stacks 0941 (blueprint: def-trf-integral-tower-inverse-image-unit). -/
instance integralTowerInverseImageColimits : PreservesFiniteColimits
    (integralTowerInverseImage l E g) := ⟨fun _ _ _ ↦ inferInstance⟩

private abbrev towerSourceDiagram :
    coefficientSequenceModules l E Y ⥤ ℕᵒᵖ ⥤ scalarReductionSource l E X :=
  coefficientSequenceRestriction l E Y ⋙
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj (towerModuleInverseImage l E g)

private abbrev towerTargetDiagram :
    coefficientSequenceModules l E Y ⥤ ℕᵒᵖ ⥤ scalarReductionSource l E X :=
  integralComparisonSequencePullback l E g ⋙ coefficientSequenceRestriction l E X

private def towerEvaluationComparison (n : ℕ) :
    towerSourceDiagram l E g ⋙
        (evaluation ℕᵒᵖ (scalarReductionSource l E X)).obj (op n) ≅
      towerTargetDiagram l E g ⋙
        (evaluation ℕᵒᵖ (scalarReductionSource l E X)).obj (op n) :=
  towerEvaluationIso (coefficientSequenceRestriction l E Y) (towerModuleInverseImage l E g)
    (integralComparisonSequencePullback l E g) (coefficientSequenceRestriction l E X)
    (op n) (towerComparisonLevel l E g n)

private theorem towerEvaluationComparisonPush_apply (n : ℕ) (M : coefficientSequenceModules l E Y)
    (U : X.ProEt) (x : M.val.obj (op (n, (proEtaleIsoPostcompose g).obj U))) :
    towerHomApply (C := X.ProEt) (J := ProEt.topology X)
      (R := towerCompletedModuleRing l E X) ((towerEvaluationComparison l E g n).hom.app M)
        (op U)
        (towerInverseSection l E g
          (((coefficientSequenceRestriction l E Y).obj M).obj (op n)) (op U)
          (integralComparisonRestrictedSection l E Y M n
            (op ((proEtaleIsoPostcompose g).obj U)) x)) =
      integralComparisonRestrictedSection l E X
        ((integralComparisonSequencePullback l E g).obj M) n (op U)
        (towerMapApply ((integralComparisonSequencePullback l E g).obj M)
          (Prod.mkHom (𝟙 n) (proEtaleIsoCommaArrow g U)).op
          (integralComparisonSequenceGenerator l E g M n
            ((proEtaleIsoPostcompose g).obj U) x)) := by
  exact towerComparisonPush_apply l E g n M U x

omit [IsIso g] in
private theorem towerSequenceGenerator_transition
    (M : coefficientSequenceModules l E Y) {m n : ℕ} (h : n ≤ m) (V : Y.ProEt)
    (x : M.val.obj (op (m, V))) :
    integralComparisonSequenceGenerator l E g M n V
        (towerMapApply M (Prod.mkHom (homOfLE h) (𝟙 V)).op x) =
      towerMapApply ((integralComparisonSequencePullback l E g).obj M)
        ((integralComparisonSequenceBaseChange g).map
          (Prod.mkHom (homOfLE h) (𝟙 V))).op
        (integralComparisonSequenceGenerator l E g M m V x) := by
  exact towerGenericUnitSection_naturality
    (J := coefficientSequenceTopology (ProEt.topology Y))
    (K := coefficientSequenceTopology (ProEt.topology X))
    (integralComparisonSequenceBaseChange g)
    (S := towerSequenceModuleRing l E Y) (R := towerSequenceModuleRing l E X)
    (towerDirectSequenceModuleRingMap l E g)
    (integralComparisonSequencePullback l E g)
    (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E g)).unit
    M (Prod.mkHom (homOfLE h) (𝟙 V)).op x

private theorem towerEvaluationComparison_naturality
    (M : coefficientSequenceModules l E Y) {m n : ℕᵒᵖ} (f : m ⟶ n) :
    ((towerSourceDiagram l E g).obj M).map f ≫
        (towerEvaluationComparison l E g n.unop).hom.app M =
      (towerEvaluationComparison l E g m.unop).hom.app M ≫
        ((towerTargetDiagram l E g).obj M).map f := by
  apply towerHom_ext_basis (C := X.ProEt) (J := ProEt.topology X)
    (R := towerCompletedModuleRing l E X)
    (M := ((towerSourceDiagram l E g).obj M).obj m)
    (N := ((towerTargetDiagram l E g).obj M).obj n)
    (fun U ↦ ↥(M.val.obj (op (m.unop, (proEtaleIsoPostcompose g).obj U.unop))))
    (fun U x ↦ towerInverseSection l E g
      (((coefficientSequenceRestriction l E Y).obj M).obj m) U
      (integralComparisonRestrictedSection l E Y M m.unop
        (op ((proEtaleIsoPostcompose g).obj U.unop)) x))
    (fun U ↦ (towerInverseSection_surjective l E g
      (((coefficientSequenceRestriction l E Y).obj M).obj m) U).comp
        (towerRestrictedSection_surjective l E Y M m.unop
          (op ((proEtaleIsoPostcompose g).obj U.unop))))
  intro U x
  rw [towerHomApply_comp, towerHomApply_comp,
    towerWhiskered_map (coefficientSequenceRestriction l E Y)
      (towerModuleInverseImage l E g) M f,
    towerComp_obj_map (integralComparisonSequencePullback l E g)
      (coefficientSequenceRestriction l E X) M f]
  have hf : f = (homOfLE (leOfHom f.unop)).op := Subsingleton.elim _ _
  rw [hf, towerInverseSection_map, towerRestrictedSection_transition,
    towerEvaluationComparisonPush_apply]
  rw [towerEvaluationComparisonPush_apply, towerRestrictedSection_transition]
  apply congrArg (integralComparisonRestrictedSection l E X
    ((integralComparisonSequencePullback l E g).obj M) n.unop U)
  rw [towerSequenceGenerator_transition l E g M (leOfHom f.unop)
    ((proEtaleIsoPostcompose g).obj U.unop) x]
  exact towerProductVertical_map
    (J := coefficientSequenceTopology (ProEt.topology X))
    (R := towerSequenceModuleRing l E X) (proEtaleBaseChange g)
    ((integralComparisonSequencePullback l E g).obj M) (leOfHom f.unop)
    U.unop ((proEtaleIsoPostcompose g).obj U.unop)
    (proEtaleIsoCommaArrow g U.unop)
    (integralComparisonSequenceGenerator l E g M m.unop
      ((proEtaleIsoPostcompose g).obj U.unop) x)

private theorem towerUnit_existsUnique :
    ∃! a : coefficientSequenceRestriction l E Y ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj (towerModuleInverseImage l E g) ≅
        integralComparisonSequencePullback l E g ⋙ coefficientSequenceRestriction l E X,
      ∀ (M : coefficientSequenceModules l E Y) (n : ℕ) (U : X.ProEt)
        (x : M.val.obj (op (n, (proEtaleIsoPostcompose g).obj U))),
        ((a.hom.app M).app (op n)).val.app (op U)
            (towerInverseSection l E g
              (((coefficientSequenceRestriction l E Y).obj M).obj (op n)) (op U)
              (integralComparisonRestrictedSection l E Y M n
                (op ((proEtaleIsoPostcompose g).obj U)) x)) =
          integralComparisonRestrictedSection l E X
            ((integralComparisonSequencePullback l E g).obj M) n (op U)
            (((integralComparisonSequencePullback l E g).obj M).val.map
              (CategoryTheory.Prod.mkHom (𝟙 n) (proEtaleIsoCommaArrow g U)).op
              (integralComparisonSequenceGenerator l E g M n
                ((proEtaleIsoPostcompose g).obj U) x)) := by
  let a : coefficientSequenceRestriction l E Y ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj (towerModuleInverseImage l E g) ≅
      integralComparisonSequencePullback l E g ⋙ coefficientSequenceRestriction l E X :=
    towerAssembleIso (towerSourceDiagram l E g) (towerTargetDiagram l E g)
      (fun n ↦ towerEvaluationComparison l E g n.unop)
      (fun M _ _ f ↦ towerEvaluationComparison_naturality l E g M f)
  refine ⟨a, ?_, ?_⟩
  · intro M n U x
    dsimp only [a]
    rw [towerAssembleIso_hom_app]
    exact towerEvaluationComparisonPush_apply l E g n M U x
  · intro b hb
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply NatTrans.ext
    funext n
    ext U z
    dsimp only [a]
    rw [towerAssembleIso_hom_app]
    obtain ⟨z, rfl⟩ := towerInverseSection_surjective l E g
      (((coefficientSequenceRestriction l E Y).obj M).obj n) U z
    obtain ⟨x, rfl⟩ := towerRestrictedSection_surjective l E Y M n.unop
      (op ((proEtaleIsoPostcompose g).obj U.unop)) z
    exact (hb M n.unop U.unop x).trans (towerEvaluationComparisonPush_apply l E g n.unop
      M U.unop x).symm

/-- The whole-tower unit is uniquely determined by the sheafified tensor unit at
all indices and all sections. Source: Stacks 03D6, 0941
(blueprint: def-trf-integral-tower-inverse-image-unit).

Proof: evaluate the actual sequence-pullback adjunction unit at the postcomposition
of U with g, then restrict along the distinguished comma arrow U to g-star(gU).
This sends x to x tensor 1. The completed coefficient projection equation proves
linearity after restriction of scalars. Naturality in restrictions and quotient
transitions gives a map of entire towers, natural in the quotient system.
The coefficient map is invertible and the underlying site map is an equivalence,
so multiplication gives its inverse at each level. Sectionwise equality proves
uniqueness of the transformation and its inverse. -/
theorem integralTowerInverseImageUnit_existsUnique :
    ∃! a : coefficientSequenceRestriction l E Y ⋙ integralTowerInverseImage l E g ≅
        integralComparisonSequencePullback l E g ⋙ coefficientSequenceRestriction l E X,
      ∀ (M : coefficientSequenceModules l E Y) (n : ℕ) (U : X.ProEt)
        (x : M.val.obj (op (n, (proEtaleIsoPostcompose g).obj U))),
        ((a.hom.app M).app (op n)).val.app (op U)
            (integralComparisonRestrictedSection l E Y M n
              (op ((proEtaleIsoPostcompose g).obj U)) x) =
          integralComparisonRestrictedSection l E X
            ((integralComparisonSequencePullback l E g).obj M) n (op U)
            (((integralComparisonSequencePullback l E g).obj M).val.map
              (CategoryTheory.Prod.mkHom (𝟙 n) (proEtaleIsoCommaArrow g U)).op
              (integralComparisonSequenceGenerator l E g M n
                ((proEtaleIsoPostcompose g).obj U) x)) := by
  exact towerUnit_existsUnique l E g

/-- The canonical sheafified x tensor 1 map, retaining all quotient transitions.
Source: Stacks 03D6, 0941 (blueprint: def-trf-integral-tower-inverse-image-unit). -/
def integralTowerInverseImageUnit :=
  (integralTowerInverseImageUnit_existsUnique l E g).exists.choose

/-- Exact inverse image of the entire completed-coefficient tower.
Source: Stacks 03D6, 0941 (blueprint: def-trf-integral-tower-inverse-image-unit). -/
def integralDerivedTowerInverseImage :
    coefficientSequenceRestrictedDerived l E Y ⥤ coefficientSequenceRestrictedDerived l E X :=
  (integralTowerInverseImage l E g).mapDerivedCategory

/-- Localize the same whole-tower tensor-unit map, including the canonical
composition comparisons of exact derived functors.
Source: Stacks 03D6, 0941 (blueprint: def-trf-integral-tower-inverse-image-unit). -/
def integralDerivedTowerInverseImageUnit :
    coefficientSequenceDerivedRestriction l E Y ⋙ integralDerivedTowerInverseImage l E g ≅
      integralComparisonDerivedSequencePullback l E g ⋙
        coefficientSequenceDerivedRestriction l E X :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (integralTowerInverseImageUnit l E g) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm

/-- Exact inverse image commutes with the diagonal by the identity at each level.
Source: Stacks 0941 (blueprint: def-trf-integral-tower-inverse-image-unit). -/
def integralTowerInverseImageDiagonal :
    inverseImageIntegralDerived l E g ⋙ integralComparisonConstantTower l E X ≅
      integralComparisonConstantTower l E Y ⋙ integralDerivedTowerInverseImage l E g :=
  Functor.mapDerivedCategoryCompIso
    (inverseImageIntegralModules l E g)
    (Functor.const ℕᵒᵖ : scalarReductionSource l E X ⥤ _) ≪≫
    Functor.mapDerivedCategoryNatIso
      (@id
        (inverseImageIntegralModules l E g ⋙
            (Functor.const ℕᵒᵖ : scalarReductionSource l E X ⥤ _) ≅
          (Functor.const ℕᵒᵖ : scalarReductionSource l E Y ⥤ _) ⋙
            integralTowerInverseImage l E g)
        (Functor.compConstIso ℕᵒᵖ (inverseImageIntegralModules l E g))) ≪≫
      (Functor.mapDerivedCategoryCompIso
        (Functor.const ℕᵒᵖ : scalarReductionSource l E Y ⥤ _)
        (integralTowerInverseImage l E g)).symm

end WeilConjectures
