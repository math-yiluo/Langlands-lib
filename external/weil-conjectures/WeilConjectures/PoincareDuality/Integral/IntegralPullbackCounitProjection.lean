/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
public import WeilConjectures.SmoothPurity.Integral.IntegralSystemReductionFullyFaithful
public import WeilConjectures.ProperBaseChange.IntegralFinitePullbackComposition
public import WeilConjectures.SixFunctors.Integral.IntegralOperationsPreserveConstructible
import WeilConjectures.PoincareDuality.Integral.IntegralPullbackStrictFiniteComponent
import WeilConjectures.TraceFormula.Coherent.CoherentPrimitiveReductionPresentation
import all WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels

/-! # Finite projection of the normalized coherent pullback counit

The counit projection is computed from a coherent strict quotient presentation,
the normalized Roos projection, and the finite inverse-image unit comparison.
Source: Stacks Tags 0941 and 099N(5).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  WeilConjectures.scalarReductionExistence WeilConjectures.scalarReductionDerivedExistence
  WeilConjectures.integralDerivedPullback
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory
attribute [local implicit_reducible] WeilConjectures.integralCoefficientSheaf
  WeilConjectures.integralCoefficientCommRingSheaf
  WeilConjectures.coefficientFiniteDerivedExtension
  WeilConjectures.coefficientFiniteDerivedRestriction
  WeilConjectures.integralComparisonDerivedSequencePullback
  WeilConjectures.coefficientConstantTowerLimit
  WeilConjectures.coefficientConstantTowerEvaluation
  WeilConjectures.coefficientSequenceLimit
  WeilConjectures.integralOperationsRoos WeilConjectures.integralOperationsRoosFunctor
  WeilConjectures.integralOperationsGoodComplex
  WeilConjectures.integralOperationsGoodLocalization
  WeilConjectures.integralOperationsPullbackOnGood
  WeilConjectures.integralOperationsPullbackComplexFunctor
  WeilConjectures.integralPullbackFiniteComplex
  WeilConjectures.integralOperationsPullbackTowerFunctor
  WeilConjectures.integralOperationsPullbackLevel WeilConjectures.integralOperationsRestrict
  WeilConjectures.scalarReductionDerivedRestriction
  HomologicalComplex.complexOfFunctorsToFunctorToComplex HomologicalComplex.asFunctor
  CategoryTheory.Functor.ofOpSequence CategoryTheory.Functor.ofSequence
  WeilConjectures.unrestrictedIntegralReductionFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem roos_projection_natural {W : Scheme.{u}}
    {A B : ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E W) ℤ}
    (a : A ⟶ B) (n : ℕ) :
    DerivedCategory.Q.map (integralOperationsRoosFunctor.map a) ≫
        integralOperationRoosProjection l E W B n =
      integralOperationRoosProjection l E W A n ≫ DerivedCategory.Q.map (a.app (op n)) := by
  unfold integralOperationRoosProjection
  rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
  congr 1
  erw [← Category.assoc, (IntegralAmbient.roosMap_coordinates a).1, Category.assoc,
    Pi.map_π]
  exact (Category.assoc _ _ _).symm

private theorem normalized_roos_projection (W : Scheme.{u})
    (ρ : IntegralComparisonRoosModel l E W)
    (C : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) (n : ℕ) :
    ρ.comparison.hom.app C ≫ integralOperationRoosProjection l E W C.asFunctor n =
      (coefficientConstantTowerProjection l E W n).app (DerivedCategory.Q.obj C) ≫
        (coefficientConstantTowerEvaluationFactors l E W n).hom.app C := by
  have hi (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
      [I.IsKInjective] :
      ρ.comparison.hom.app I ≫ integralOperationRoosProjection l E W I.asFunctor n =
        (coefficientConstantTowerProjection l E W n).app (DerivedCategory.Q.obj I) ≫
          (coefficientConstantTowerEvaluationFactors l E W n).hom.app I := by
    rw [ρ.computes I]
    unfold integralOperationRoosProjection
    rw [Category.assoc, ← DerivedCategory.Q.map_comp]
    have h := (integralComparisonLimitToRoos_existsUnique l E W I).exists.choose_spec.1 n
    change integralComparisonLimitToRoos l E W I ≫ _ ≫ _ = _ at h
    rw [h]
    exact ((coefficientConstantTowerProjection_exists l E W n).choose_spec.1 I).symm
  obtain ⟨I, hI, f, _, hf⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective C
  have : QuasiIso f := hf
  let V := (evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n)
  apply (cancel_mono (DerivedCategory.Q.map
    ((V.mapHomologicalComplex (.up ℤ)).map f))).1
  have hv := V.mapDerivedCategoryFactors.hom.naturality f
  have hp := (coefficientConstantTowerProjection l E W n).naturality
    (DerivedCategory.Q.map f)
  have hθ := ρ.comparison.hom.naturality f
  dsimp only [Functor.comp_map] at hv hθ
  erw [Category.assoc, ← roos_projection_natural l E
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f) n]
  rw [← Category.assoc, ← hθ, Category.assoc]
  erw [hi I]
  rw [Category.assoc, ← hv]
  exact (reassoc_of% hp) _

private theorem bridge_projection (W : Scheme.{u})
    (ρ : IntegralComparisonRoosModel l E W)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) (n : ℕ) :
    (integralComparisonRoosBridge l E W ρ C).hom ≫
        integralOperationRoosProjection l E W
          (((coefficientSequenceRestriction l E W).mapHomologicalComplex
            (.up ℤ)).obj C).asFunctor n =
      (coefficientSequenceProjection l E W n).app (DerivedCategory.Q.obj C) ≫
        (integralComparisonRestrictedEvaluationFactors l E W C n).hom := by
  dsimp only [integralComparisonRoosBridge, Iso.trans_hom, Functor.mapIso_hom]
  erw [Category.assoc, normalized_roos_projection l E W ρ
    (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C) n]
  unfold coefficientSequenceProjection integralComparisonRestrictedEvaluationFactors
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_inv, Iso.app_hom, Category.assoc,
    Iso.hom_inv_id_app_assoc]
  erw [reassoc_of% ((coefficientConstantTowerProjection l E W n).naturality
    ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.hom.app C))]

private theorem evaluated_counit_adjunct (W : Scheme.{u})
    (T : CoefficientDerivedSystemCalculus l E W)
    {A : DerivedCategory (scalarReductionSource l E W)}
    (N : coefficientSequenceDerived l E W)
    (a : A ⟶ (coefficientSequenceLimit l E W).obj N) (n : ℕ) :
    (coefficientFiniteAdjunction l E W n).homEquiv _ _
      ((T.reductionEvaluation n).inv.app A ≫
        (coefficientSequenceDerivedEvaluation l E W n).map
          (T.reduction.map a ≫ T.adjunction.counit.app N)) =
      a ≫ (coefficientSequenceProjection l E W n).app N := by
  rw [Functor.map_comp, ← Category.assoc]
  have hn := (T.reductionEvaluation n).inv.naturality a
  dsimp only [Functor.comp_map] at hn
  rw [← hn, Category.assoc, Adjunction.homEquiv_naturality_left,
    T.counit_projection]

private theorem counit_projection_map_component
    {A B : Type*} [Category A] [Category B] (R : A ⥤ B)
    {X Y Z W V U : A} {D E : B}
    (a : X ⟶ Y) (p : R.obj Y ⟶ D) (q : D ⟶ E) (r : E ⟶ R.obj Z)
    (c : Z ⟶ W) (d : W ⟶ V) (e : V ⟶ U) (t : Y ⟶ V) (b : X ⟶ U)
    (ht : p ≫ q ≫ r ≫ R.map (c ≫ d) = R.map t) (hf : a ≫ t ≫ e = b) :
    R.map a ≫ p ≫ q ≫ r ≫ R.map (c ≫ d ≫ e) = R.map b := by
  calc
    _ = R.map a ≫ (p ≫ q ≫ r ≫ R.map (c ≫ d)) ≫ R.map e := by
      simp only [Functor.map_comp, Category.assoc]
    _ = R.map (a ≫ t ≫ e) := by
      rw [ht]
      simp only [Functor.map_comp]
    _ = _ := congrArg R.map hf

private theorem counit_projection_transport
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (α : F ⟶ G) {X Y : C} (e : X ≅ Y) :
    α.app Y = F.map e.inv ≫ α.app X ≫ G.map e.hom := by
  rw [← α.naturality, ← F.map_comp_assoc, e.inv_hom_id, F.map_id, Category.id_comp]

private theorem counit_projection_on_representative {X Y : Scheme.{u}} (f : X ⟶ Y)
    (S : CoefficientDerivedSystemCalculus l E Y)
    (ρ : IntegralComparisonRoosModel l E X)
    (M : IntegralComparisonPullbackModel l E f S ρ)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) (n : ℕ) :
    M.realization.hom.app (DerivedCategory.Q.obj P.obj) ≫
      (coefficientSequenceProjection l E X n).app
        ((integralComparisonDerivedSequencePullback l E f).obj
          (S.reduction.obj (DerivedCategory.Q.obj P.obj))) ≫
      (coefficientFiniteDerivedRestriction l E X n).map
        ((finiteSystemDerivedPullbackEvaluation (integralSystemRings l E)
          (integralSystemTransition l E) f n).hom.app
            (S.reduction.obj (DerivedCategory.Q.obj P.obj)) ≫
          (proEtaleConstantRingDerivedPullback
            (Padic.coefficientExtensionRing l E (n + 1)) f).map
            ((S.reductionEvaluation n).hom.app (DerivedCategory.Q.obj P.obj))) =
    (integralDerivedPullbackComparison l E f).hom.app P ≫
      integralOperationRoosProjection l E X
        ((integralOperationsPullbackTowerFunctor l E f).obj P.obj) n ≫
      (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.inv.app
        (integralPullbackFiniteComplex l E f P.obj n) ≫
      (coefficientFiniteDerivedRestriction l E X n).map
        (DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (integralFinitePullbackModel l E f n)
            (.up ℤ)).hom.app ((unrestrictedIntegralFiniteComplex l E Y n).obj P.obj)) ≫
          (proEtaleConstantRingPullback
            (Padic.coefficientExtensionRing l E (n + 1)) f).mapDerivedCategoryFactors.inv.app
            ((unrestrictedIntegralFiniteComplex l E Y n).obj P.obj) ≫
          (proEtaleConstantRingDerivedPullback
            (Padic.coefficientExtensionRing l E (n + 1)) f).map
            (coefficientFiniteReductionModel l E Y P.obj P.property.1 n).inv) := by
  classical
  have hP : P.obj.IsKFlatIndependentCoefficients := P.property.1
  obtain ⟨C, d, κ, hpres, hcoh⟩ := coherentPrimitiveReductionPresentation l E S P
  obtain ⟨q, hq, hm⟩ := M.normalization P C d κ hpres hcoh
  let D := ((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)).obj C
  let F := integralComparisonDerivedSequencePullback l E f
  let V := coefficientSequenceDerivedEvaluation l E X n
  let R := coefficientFiniteDerivedRestriction l E X n
  let B := proEtaleConstantRingDerivedPullback
    (Padic.coefficientExtensionRing l E (n + 1)) f
  let β : F ⋙ V ≅ coefficientSequenceDerivedEvaluation l E Y n ⋙ B :=
    finiteSystemDerivedPullbackEvaluation (integralSystemRings l E)
      (integralSystemTransition l E) f n
  let a := F.map d.hom ≫
    (integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.hom.app C
  let b : V.obj (F.obj (S.reduction.obj (DerivedCategory.Q.obj P.obj))) ⟶
      B.obj ((scalarReductionDerivedExtension l E Y n).obj (DerivedCategory.Q.obj P.obj)) :=
    β.hom.app (S.reduction.obj (DerivedCategory.Q.obj P.obj)) ≫
    B.map ((S.reductionEvaluation n).hom.app (DerivedCategory.Q.obj P.obj))
  let c := DerivedCategory.Q.map
      ((NatIso.mapHomologicalComplex (integralFinitePullbackModel l E f n)
        (.up ℤ)).hom.app ((unrestrictedIntegralFiniteComplex l E Y n).obj P.obj)) ≫
    (proEtaleConstantRingPullback
      (Padic.coefficientExtensionRing l E (n + 1)) f).mapDerivedCategoryFactors.inv.app
        ((unrestrictedIntegralFiniteComplex l E Y n).obj P.obj) ≫
    B.map (coefficientFiniteReductionModel l E Y P.obj hP n).inv
  let r := (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.inv.app
    (integralPullbackFiniteComplex l E f P.obj n)
  have hf : V.map a ≫
      V.map ((integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.inv.app C) ≫
      β.hom.app (DerivedCategory.Q.obj C) ≫
      B.map ((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.app C ≫
        DerivedCategory.Q.map (κ n).hom) ≫
      B.map (coefficientFiniteReductionModel l E Y P.obj hP n).inv = b := by
    dsimp only [a, b]
    have hcancel :
        V.map ((integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.hom.app C) ≫
          V.map ((integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.inv.app C) =
            𝟙 _ := by
      rw [← V.map_comp, Iso.hom_inv_id_app, V.map_id]
    simp only [V.map_comp, Category.assoc]
    erw [reassoc_of% hcancel]
    have hn := β.hom.naturality d.hom
    erw [reassoc_of% hn]
    dsimp only [B]
    simp only [Category.assoc, ← Functor.map_comp]
    erw [reassoc_of% (hpres.1 n)]
    simp only [Iso.hom_inv_id, Category.comp_id]
  have hcomponent : R.map (V.map a) ≫
      (integralComparisonRestrictedEvaluationFactors l E X D n).hom ≫
      DerivedCategory.Q.map (q.hom.app (op n)) ≫ r ≫ R.map c = R.map b := by
    apply counit_projection_map_component R (V.map a) _ _ r _ _
      (B.map (coefficientFiniteReductionModel l E Y P.obj hP n).inv)
      (V.map ((integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.inv.app C) ≫
        β.hom.app (DerivedCategory.Q.obj C) ≫
        B.map ((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.app C ≫
          DerivedCategory.Q.map (κ n).hom)) b
    · exact integralPullbackStrictFiniteComponent l E f P.obj C κ q hq n
    · simpa only [Category.assoc] using hf
  have hm' : M.realization.hom.app (DerivedCategory.Q.obj P.obj) ≫
      (coefficientSequenceLimit l E X).map a ≫
      (integralComparisonRoosBridge l E X ρ D).hom ≫
      DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom) =
        (integralDerivedPullbackComparison l E f).hom.app P := by
    simpa only [a, F, D, Functor.map_comp, Category.assoc] using hm
  have hproj : M.realization.hom.app (DerivedCategory.Q.obj P.obj) ≫
      (coefficientSequenceProjection l E X n).app
        (F.obj (S.reduction.obj (DerivedCategory.Q.obj P.obj))) ≫ R.map b =
      (integralDerivedPullbackComparison l E f).hom.app P ≫
        integralOperationRoosProjection l E X
          ((integralOperationsPullbackTowerFunctor l E f).obj P.obj) n ≫ r ≫ R.map c := by
    have h := congrArg (fun t ↦ t ≫ integralOperationRoosProjection l E X
      ((integralOperationsPullbackTowerFunctor l E f).obj P.obj) n ≫ r ≫ R.map c) hm'
    simp only [Category.assoc] at h
    erw [reassoc_of% (roos_projection_natural l E q.hom n)] at h
    erw [reassoc_of% (bridge_projection l E X ρ D n)] at h
    erw [reassoc_of% ((coefficientSequenceProjection l E X n).naturality a)] at h
    rw [hcomponent] at h
    exact h
  exact hproj

/-- Evaluating normalized realization followed by the coherent counit gives
exactly the scalar adjunct of the defining pullback-tower projection. This is
a map equality; it asserts neither invertibility nor a system isomorphism.
Source: Stacks Tags 0941 and 099N(5)
(blueprint: lem-pod-integral-pullback-counit-projection).

Proof: choose the simultaneous strict quotient presentation of P supplied by
coherentPrimitiveReductionPresentation, including its whole-tower coherence and
its comparison at every finite level. Apply M.normalization
to obtain the strict pulled-back tower comparison q. At degree i, its specified
formula on inverse-image unit generators, followed by scalar balancing, fixes its
finite component: both sides are sheaf maps, and the completed coefficient
projection is locally surjective, so those generators determine the maps.
The comparison is therefore the unit-normalized integralFinitePullbackModel
transported by the finite presentation isomorphisms. The strict Roos map commutes
with its first-product projections. On a K-injective resolution the normalization
of rho identifies the derived limit-to-Roos map with the limit-tuple map having
zero shifted coordinate. Its projection is the ordinary limit projection.
Naturality along the resolution quasi-isomorphism gives this equality for every
input, and composition with q gives the defining integral pullback projection.
Apply T.counit_projection, and use naturality of T.reductionEvaluation to move
M.realization across the finite reduction. Under the finite scalar adjunction
this is the just-computed tower projection. The S.reductionModel equation
identifies the source reduction comparison with the universal reduction counit.
Transport along e from Q(P) to K. The inverse e appearing in the definition of
integralPullbackFiniteComparison cancels its forward map, as do the finite exact
pullback factorization and finite reduction isomorphisms. The adjunction Hom
bijection is injective, so the two finite maps are equal. All steps are natural
also for zero objects, empty schemes, and n=0 (quotient exponent one). -/
theorem integralPullbackCounitProjection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (S : CoefficientDerivedSystemCalculus l E Y)
    (T : CoefficientDerivedSystemCalculus l E X)
    (ρ : IntegralComparisonRoosModel l E X)
    (M : IntegralComparisonPullbackModel l E f S ρ)
    (K : DerivedCategory (scalarReductionSource l E Y))
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ K) (n : ℕ) :
    (T.reductionEvaluation n).inv.app ((integralDerivedPullback l E f).obj K) ≫
      (finiteSystemDerivedEvaluation (integralSystemRings l E)
        (integralSystemTransition l E) X n).map
        (T.reduction.map (M.realization.hom.app K) ≫
          T.adjunction.counit.app
            ((integralComparisonDerivedSequencePullback l E f).obj (S.reduction.obj K))) ≫
      (finiteSystemDerivedPullbackEvaluation (integralSystemRings l E)
        (integralSystemTransition l E) f n).hom.app (S.reduction.obj K) ≫
      (proEtaleConstantRingDerivedPullback
        (Padic.coefficientExtensionRing l E (n + 1)) f).map
        ((S.reductionEvaluation n).hom.app K) =
    integralPullbackFiniteComparison l E f K P e n ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (integralFinitePullbackModel l E f n)
          (ComplexShape.up ℤ)).hom.app
            ((unrestrictedIntegralFiniteComplex l E Y n).obj P.obj)) ≫
      (proEtaleConstantRingPullback
        (Padic.coefficientExtensionRing l E (n + 1)) f).mapDerivedCategoryFactors.inv.app
          ((unrestrictedIntegralFiniteComplex l E Y n).obj P.obj) ≫
      (proEtaleConstantRingDerivedPullback
        (Padic.coefficientExtensionRing l E (n + 1)) f).map
        ((coefficientFiniteReductionModel l E Y P.obj P.property.1 n).inv ≫
          (scalarReductionDerivedExtension l E Y n).map e.hom)  := by
  have hP : P.obj.IsKFlatIndependentCoefficients := P.property.1
  let F := integralComparisonDerivedSequencePullback l E f
  let V := coefficientSequenceDerivedEvaluation l E X n
  let R := coefficientFiniteDerivedRestriction l E X n
  let B := proEtaleConstantRingDerivedPullback
    (Padic.coefficientExtensionRing l E (n + 1)) f
  let β : F ⋙ V ≅ coefficientSequenceDerivedEvaluation l E Y n ⋙ B :=
    finiteSystemDerivedPullbackEvaluation (integralSystemRings l E)
      (integralSystemTransition l E) f n
  let b : V.obj (F.obj (S.reduction.obj (DerivedCategory.Q.obj P.obj))) ⟶
      B.obj ((scalarReductionDerivedExtension l E Y n).obj (DerivedCategory.Q.obj P.obj)) :=
    β.hom.app (S.reduction.obj (DerivedCategory.Q.obj P.obj)) ≫
    B.map ((S.reductionEvaluation n).hom.app (DerivedCategory.Q.obj P.obj))
  let c := DerivedCategory.Q.map
      ((NatIso.mapHomologicalComplex (integralFinitePullbackModel l E f n)
        (.up ℤ)).hom.app ((unrestrictedIntegralFiniteComplex l E Y n).obj P.obj)) ≫
    (proEtaleConstantRingPullback
      (Padic.coefficientExtensionRing l E (n + 1)) f).mapDerivedCategoryFactors.inv.app
        ((unrestrictedIntegralFiniteComplex l E Y n).obj P.obj) ≫
    B.map (coefficientFiniteReductionModel l E Y P.obj hP n).inv
  let r := (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.inv.app
    (integralPullbackFiniteComplex l E f P.obj n)
  have hproj : M.realization.hom.app (DerivedCategory.Q.obj P.obj) ≫
      (coefficientSequenceProjection l E X n).app
        (F.obj (S.reduction.obj (DerivedCategory.Q.obj P.obj))) ≫ R.map b =
      (integralDerivedPullbackComparison l E f).hom.app P ≫
        integralOperationRoosProjection l E X
          ((integralOperationsPullbackTowerFunctor l E f).obj P.obj) n ≫ r ≫ R.map c :=
    counit_projection_on_representative l E f S ρ M P n
  let bK : V.obj (F.obj (S.reduction.obj K)) ⟶
      B.obj ((scalarReductionDerivedExtension l E Y n).obj K) :=
    β.hom.app (S.reduction.obj K) ≫
    B.map ((S.reductionEvaluation n).hom.app K)
  change (T.reductionEvaluation n).inv.app ((integralDerivedPullback l E f).obj K) ≫
    V.map (T.reduction.map (M.realization.hom.app K) ≫
      T.adjunction.counit.app (F.obj (S.reduction.obj K))) ≫ bK = _
  apply ((coefficientFiniteAdjunction l E X n).homEquiv _ _).injective
  have hleft : (coefficientFiniteAdjunction l E X n).homEquiv _ _
      ((T.reductionEvaluation n).inv.app ((integralDerivedPullback l E f).obj K) ≫
        V.map (T.reduction.map (M.realization.hom.app K) ≫
          T.adjunction.counit.app (F.obj (S.reduction.obj K))) ≫ bK) =
      M.realization.hom.app K ≫
        (coefficientSequenceProjection l E X n).app (F.obj (S.reduction.obj K)) ≫
        R.map bK := by
    rw [← Category.assoc, Adjunction.homEquiv_naturality_right,
      evaluated_counit_adjunct l E X T]
    exact Category.assoc _ _ _
  erw [hleft]
  unfold integralPullbackFiniteComparison
  rw [Adjunction.homEquiv_naturality_right]
  dsimp only [coefficientFiniteAdjunction]
  erw [Equiv.apply_symm_apply]
  have htransport := counit_projection_transport
    (M.realization.hom ≫
      Functor.whiskerLeft (S.reduction ⋙ F) (coefficientSequenceProjection l E X n) ≫
      Functor.whiskerRight (Functor.whiskerLeft S.reduction β.hom ≫
        Functor.whiskerRight (S.reductionEvaluation n).hom B) R) e
  change M.realization.hom.app K ≫
      (coefficientSequenceProjection l E X n).app (F.obj (S.reduction.obj K)) ≫
      R.map bK = (integralDerivedPullback l E f).map e.inv ≫
        (M.realization.hom.app (DerivedCategory.Q.obj P.obj) ≫
          (coefficientSequenceProjection l E X n).app
            (F.obj (S.reduction.obj (DerivedCategory.Q.obj P.obj))) ≫ R.map b) ≫
        R.map (B.map ((scalarReductionDerivedExtension l E Y n).map e.hom)) at htransport
  rw [hproj] at htransport
  simpa only [c, r, R, B, Functor.map_comp, Category.assoc] using htransport

end WeilConjectures
