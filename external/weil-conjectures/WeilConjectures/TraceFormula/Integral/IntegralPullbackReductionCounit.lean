/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralTowerInverseImageUnit
public import WeilConjectures.PoincareDuality.Integral.IntegralPullbackComparisonRealization
public import WeilConjectures.TraceFormula.Integral.IntegralPullbackRoosAugmentation
public import WeilConjectures.TraceFormula.Integral.IntegralTowerInverseImageFactors
public import WeilConjectures.TraceFormula.Coherent.CoherentPrimitiveReductionPresentation
public import WeilConjectures.TraceFormula.Supporting.RoosAdjunctionTranspose

/-!
# The reduction-unit computation of the integral inverse-image comparison

Source: Bhatt--Scholze, Lemma 6.5.9(4); Stacks Project, Tags 06YY and 0941.
(blueprint: lem-trf-integral-pullback-reduction-counit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures

/-- The left side of `integralPullbackKFlatReductionCounit`, after composing with the
presentation isomorphism: the normalized realization, the Roos transpose and the strict
Roos lift turn it into the localization of the strict family `β`. -/
private theorem integralPullbackKFlatReductionCounit_left
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {W Z : Scheme.{u}} (h : Z ⟶ W) [IsIso h]
    (S : CoefficientDerivedSystemCalculus l E W)
    (ρ : IntegralComparisonRoosModel l E Z)
    (F : IntegralComparisonPullbackModel l E h S ρ)
    (P : (integralOperationsGoodComplex l E W).FullSubcategory)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (e : S.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (q : (((coefficientSequenceRestriction l E Z).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequencePullback l E h).mapHomologicalComplex
          (.up ℤ)).obj C)).asFunctor ≅
      (integralOperationsPullbackTowerFunctor l E h).obj P.obj)
    (hn : F.realization.hom.app (DerivedCategory.Q.obj P.obj) ≫
        (coefficientSequenceLimit l E Z).map
          ((integralComparisonDerivedSequencePullback l E h).map e.hom) ≫
        (coefficientSequenceLimit l E Z).map
          ((integralComparisonSequencePullback l E h).mapDerivedCategoryFactors.hom.app C) ≫
        (integralComparisonRoosBridge l E Z ρ _).hom ≫
        DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom) =
          (integralDerivedPullbackComparison l E h).hom.app P)
    (β : ((Functor.const ℕᵒᵖ : scalarReductionSource l E Z ⥤
        ℕᵒᵖ ⥤ scalarReductionSource l E Z).mapHomologicalComplex (.up ℤ)).obj
          (((inverseImageIntegralModules l E h).mapHomologicalComplex (.up ℤ)).obj P.obj) ⟶
      ((coefficientSequenceRestriction l E Z).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequencePullback l E h).mapHomologicalComplex (.up ℤ)).obj C))
    (hθ : inverseImageRoosComparisonComplex l E h P.obj =
      ((constLimAdj (J := ℕᵒᵖ) (C := scalarReductionSource l E Z)).mapHomologicalComplex
          (.up ℤ)).homEquiv _ _ β ≫
        integralComparisonLimitToRoos l E Z _ ≫ integralOperationsRoosFunctor.map q.hom) :
    ((integralComparisonConstantTower l E Z).map
        ((inverseImageIntegralModules l E h).mapDerivedCategoryFactors.hom.app P.obj ≫
          DerivedCategory.Q.map (inverseImageRoosComparisonComplex l E h P.obj) ≫
          (integralDerivedPullbackComparison l E h).inv.app P ≫
          F.realization.hom.app (DerivedCategory.Q.obj P.obj)) ≫
        (integralComparisonTowerCounit l E Z).app
          ((coefficientSequenceDerivedRestriction l E Z).obj
            ((integralComparisonDerivedSequencePullback l E h).obj
              (S.reduction.obj (DerivedCategory.Q.obj P.obj))))) ≫
      ((coefficientSequenceDerivedRestriction l E Z).map
          ((integralComparisonDerivedSequencePullback l E h).map e.hom ≫
            (integralComparisonSequencePullback l E h).mapDerivedCategoryFactors.hom.app C) ≫
        (coefficientSequenceRestriction l E Z).mapDerivedCategoryFactors.hom.app
          (((integralComparisonSequencePullback l E h).mapHomologicalComplex (.up ℤ)).obj C)) =
    (integralComparisonConstantTower l E Z).map
        ((inverseImageIntegralModules l E h).mapDerivedCategoryFactors.hom.app P.obj) ≫
      (Functor.const ℕᵒᵖ : scalarReductionSource l E Z ⥤
        ℕᵒᵖ ⥤ scalarReductionSource l E Z).mapDerivedCategoryFactors.hom.app
          (((inverseImageIntegralModules l E h).mapHomologicalComplex (.up ℤ)).obj P.obj) ≫
      DerivedCategory.Q.map β := by
  let Hm := inverseImageIntegralModules l E h
  let cZ := (Functor.const ℕᵒᵖ : scalarReductionSource l E Z ⥤
    ℕᵒᵖ ⥤ scalarReductionSource l E Z)
  let AZ := integralComparisonConstantAdjunction l E Z
  let ΔZ := integralComparisonConstantTower l E Z
  let limZ := coefficientConstantTowerLimit l E Z
  let Hc := (Hm.mapHomologicalComplex (.up ℤ)).obj P.obj
  let D := ((coefficientSequenceRestriction l E Z).mapHomologicalComplex (.up ℤ)).obj
    (((integralComparisonSequencePullback l E h).mapHomologicalComplex (.up ℤ)).obj C)
  let Y := (coefficientSequenceDerivedRestriction l E Z).map
      ((integralComparisonDerivedSequencePullback l E h).map e.hom ≫
        (integralComparisonSequencePullback l E h).mapDerivedCategoryFactors.hom.app C) ≫
    (coefficientSequenceRestriction l E Z).mapDerivedCategoryFactors.hom.app
      (((integralComparisonSequencePullback l E h).mapHomologicalComplex (.up ℤ)).obj C)
  change _ ≫ Y = _
  have hk : F.realization.hom.app (DerivedCategory.Q.obj P.obj) ≫ limZ.map Y ≫
      ρ.comparison.hom.app D ≫ DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom) =
      (integralDerivedPullbackComparison l E h).hom.app P := by
    rw [← hn]
    dsimp only [Y, integralComparisonRoosBridge, coefficientSequenceLimit, limZ]
    simp only [Functor.map_comp, Category.assoc, Iso.trans_hom, Functor.mapIso_hom,
      Iso.app_hom, Functor.comp_map]
    rfl
  have hL : (inverseImageIntegralModules l E h).mapDerivedCategoryFactors.hom.app P.obj ≫
        DerivedCategory.Q.map (inverseImageRoosComparisonComplex l E h P.obj) ≫
        (integralDerivedPullbackComparison l E h).inv.app P ≫
        F.realization.hom.app (DerivedCategory.Q.obj P.obj) ≫ limZ.map Y =
      Hm.mapDerivedCategoryFactors.hom.app P.obj ≫
        AZ.homEquiv _ _ (cZ.mapDerivedCategoryFactors.hom.app Hc ≫ DerivedCategory.Q.map β) := by
    have ht := integralComparisonRoosTranspose l E Z ρ Hc D β
    rw [← cancel_mono (ρ.comparison.hom.app D ≫
      DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom))]
    simp only [Category.assoc]
    rw [hk, Iso.inv_hom_id_app]
    erw [Category.comp_id, reassoc_of% ht, hθ]
    simp only [Functor.map_comp, Category.assoc]
    rfl
  have hn' : (integralComparisonTowerCounit l E Z).app _ ≫ Y =
      ΔZ.map (limZ.map Y) ≫ (integralComparisonTowerCounit l E Z).app _ :=
    ((integralComparisonTowerCounit l E Z).naturality Y).symm
  rw [Category.assoc, hn', ← Functor.map_comp_assoc]
  simp only [Category.assoc]
  rw [hL, Functor.map_comp, Category.assoc]
  dsimp only [integralComparisonTowerCounit]
  rw [← Adjunction.homEquiv_counit]
  exact congrArg (ΔZ.map (Hm.mapDerivedCategoryFactors.hom.app P.obj) ≫ ·)
    (Equiv.symm_apply_apply _ _)

/-- The counit image of the defining Roos lift is the inverse image of the
whole-system reduction unit, followed by the finite tensor unit. This is the
reduction-unit computation, before composing with a map from the reduction to
any other quotient system. It is stated only on a flat-term K-flat complex,
before any resolution is inverted.

Source: Bhatt--Scholze, Lemma 6.5.9(4); Stacks Project, Tags 06YY and 0941;
Steps 1, 3 and 5 of the resolution-matching argument
(blueprint: lem-trf-integral-pullback-reduction-counit).

Proof: choose a coherent strict reduction presentation (C, e, kappa, b) of P, and
normalize the realization of F on it; this gives the tower identification q.
Postcompose both sides with the isomorphism from U_Z(B(S.reduction(P))) to the
localization of the strict tower Res_Z(B(C)). On the right, the coherence of b
turns the derived unit followed by the derived-limit counit into the localization
of b; the factor isomorphisms of the diagonal and of the tower unit then identify
the right side with the localization of the strict family
const(h^* P) to T(Res_W C) to Res_Z(B C). On the left, the normalization of F
replaces the realization by the inverse of the Roos bridge followed by q. The
defining Roos lift theta is the limit lift of that strict family followed by q
(inverseImageRoosComparisonComplex_eq_limitToRoos), and
integralComparisonRoosTranspose identifies its image under the normalized Roos
comparison with the adjunct of the same family. The counit then gives the same
localized family. No equality is detected merely by evaluation at finite levels. -/
theorem integralPullbackKFlatReductionCounit
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {W Z : Scheme.{u}} (h : Z ⟶ W) [IsIso h]
    (S : CoefficientDerivedSystemCalculus l E W)
    (ρ : IntegralComparisonRoosModel l E Z)
    (F : IntegralComparisonPullbackModel l E h S ρ)
    (P : (integralOperationsGoodComplex l E W).FullSubcategory) :
    (integralComparisonConstantTower l E Z).map
        ((inverseImageIntegralModules l E h).mapDerivedCategoryFactors.hom.app P.obj ≫
          DerivedCategory.Q.map (inverseImageRoosComparisonComplex l E h P.obj) ≫
          (integralDerivedPullbackComparison l E h).inv.app P ≫
          F.realization.hom.app (DerivedCategory.Q.obj P.obj)) ≫
        (integralComparisonTowerCounit l E Z).app
          ((coefficientSequenceDerivedRestriction l E Z).obj
            ((integralComparisonDerivedSequencePullback l E h).obj
              (S.reduction.obj (DerivedCategory.Q.obj P.obj)))) =
      (integralTowerInverseImageDiagonal l E h).hom.app (DerivedCategory.Q.obj P.obj) ≫
        (integralDerivedTowerInverseImage l E h).map
          ((integralComparisonConstantTower l E W).map
              (S.adjunction.unit.app (DerivedCategory.Q.obj P.obj)) ≫
            (integralComparisonTowerCounit l E W).app
              ((coefficientSequenceDerivedRestriction l E W).obj
                (S.reduction.obj (DerivedCategory.Q.obj P.obj)))) ≫
        (integralDerivedTowerInverseImageUnit l E h).hom.app
          (S.reduction.obj (DerivedCategory.Q.obj P.obj)) := by
  classical
  let RW := coefficientSequenceRestriction l E W
  let RZ := coefficientSequenceRestriction l E Z
  let B := integralComparisonSequencePullback l E h
  let T := integralTowerInverseImage l E h
  let Hm := inverseImageIntegralModules l E h
  let cW := (Functor.const ℕᵒᵖ : scalarReductionSource l E W ⥤
    ℕᵒᵖ ⥤ scalarReductionSource l E W)
  let cZ := (Functor.const ℕᵒᵖ : scalarReductionSource l E Z ⥤
    ℕᵒᵖ ⥤ scalarReductionSource l E Z)
  let AZ := integralComparisonConstantAdjunction l E Z
  let τ := integralTowerInverseImageUnit l E h
  obtain ⟨C, e, κ, hp, hc⟩ := coherentPrimitiveReductionPresentation l E S P
  obtain ⟨q, hq, hn⟩ := F.normalization P C e κ hp hc
  rw [IsIntegralComparisonPresentationCoherent] at hc
  obtain ⟨b, hb, hc⟩ := hc
  let D := (RZ.mapHomologicalComplex (.up ℤ)).obj ((B.mapHomologicalComplex (.up ℤ)).obj C)
  let β : (cZ.mapHomologicalComplex (.up ℤ)).obj
      ((Hm.mapHomologicalComplex (.up ℤ)).obj P.obj) ⟶ D :=
    (NatTrans.mapHomologicalComplex (Functor.compConstIso ℕᵒᵖ Hm).hom (.up ℤ)).app P.obj ≫
      (T.mapHomologicalComplex (.up ℤ)).map b ≫
      (NatTrans.mapHomologicalComplex τ.hom (.up ℤ)).app C
  have hθ := inverseImageRoosComparisonComplex_eq_limitToRoos l E h P.obj C κ b hb q hq
  let Y := (coefficientSequenceDerivedRestriction l E Z).map
      ((integralComparisonDerivedSequencePullback l E h).map e.hom ≫
        B.mapDerivedCategoryFactors.hom.app C) ≫
    RZ.mapDerivedCategoryFactors.hom.app ((B.mapHomologicalComplex (.up ℤ)).obj C)
  have hY : IsIso Y := by dsimp only [Y]; infer_instance
  apply (cancel_mono Y).1
  let ΔZ := integralComparisonConstantTower l E Z
  let ΔW := integralComparisonConstantTower l E W
  let limZ := coefficientConstantTowerLimit l E Z
  let UW := coefficientSequenceDerivedRestriction l E W
  let UZ := coefficientSequenceDerivedRestriction l E Z
  let Td := integralDerivedTowerInverseImage l E h
  let τd := integralDerivedTowerInverseImageUnit l E h
  let Hc := (Hm.mapHomologicalComplex (.up ℤ)).obj P.obj
  let fac := ΔZ.map (Hm.mapDerivedCategoryFactors.hom.app P.obj) ≫
    cZ.mapDerivedCategoryFactors.hom.app Hc ≫ DerivedCategory.Q.map β
  trans fac
  · exact integralPullbackKFlatReductionCounit_left l E h S ρ F P C e q hn β hθ
  · -- the right side, through the coherence of `b` and the factor isomorphisms
    have hR1 : τd.hom.app (S.reduction.obj (DerivedCategory.Q.obj P.obj)) ≫
        UZ.map ((integralComparisonDerivedSequencePullback l E h).map e.hom) =
        Td.map (UW.map e.hom) ≫ τd.hom.app (DerivedCategory.Q.obj C) :=
      (τd.hom.naturality e.hom).symm
    have hR2 : ΔW.map (S.adjunction.unit.app (DerivedCategory.Q.obj P.obj)) ≫
        (integralComparisonTowerCounit l E W).app
          (UW.obj (S.reduction.obj (DerivedCategory.Q.obj P.obj))) ≫ UW.map e.hom =
        cW.mapDerivedCategoryFactors.hom.app P.obj ≫ DerivedCategory.Q.map b ≫
          RW.mapDerivedCategoryFactors.inv.app C := by
      have hn2 : (integralComparisonTowerCounit l E W).app
          (UW.obj (S.reduction.obj (DerivedCategory.Q.obj P.obj))) ≫ UW.map e.hom =
          ΔW.map ((coefficientConstantTowerLimit l E W).map (UW.map e.hom)) ≫
            (integralComparisonTowerCounit l E W).app _ :=
        ((integralComparisonTowerCounit l E W).naturality _).symm
      rw [hn2, ← Functor.map_comp_assoc]
      exact hc
    calc fac = _ := integralTowerInverseImage_strictFamily_factors l E h P.obj C b
      _ = _ := by
          rw [← hR2]
          dsimp only [Y]
          simp only [Functor.map_comp, Category.assoc]
          rw [reassoc_of% hR1]

end WeilConjectures
