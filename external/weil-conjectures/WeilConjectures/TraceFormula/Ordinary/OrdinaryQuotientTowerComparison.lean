/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Isomorphism.IsomorphismStrictQuotientModels
public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationRoosEffectivity
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientSequenceRoosModel
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitOrdinaryAdjunction

/-! # Ordinary strict quotient tower comparison

Source: Stacks 03CZ, 03EK, 06YY, 08TC and 0941; the strict quotient-cone argument
of `lem-trf-isomorphism-multiplication-cone-descent`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  SheafOfModules.monoidalCategory CategoryTheory.Limits.limit

universe t u a b r
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures

attribute [local instance 3000] integralTowerHasDerivedCategory
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local implicit_reducible] completedIntegralCommRingSheafUnrestricted
  CategoryTheory.sheafCompose

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  integralOperationsGoodComplex coefficientSequenceLimit TrfCompletionRoosNormalized
  integralDerivedPullback integralDerivedPullbackComparison integralPullbackDescent
  Functor.mapDerivedCategoryFactors Functor.mapDerivedCategory DerivedCategory.Q
  integralOperationsRoosMap

attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence
  unrestrictedIntegralComplexFunctor scalarReductionExtension coefficientQuotientNatTrans
  unrestrictedIntegralTransition coefficientOrdinaryQuotientComponent coefficientOrdinaryQuotient
  coefficientSequenceEvaluation coefficientSequenceTransition unrestrictedIntegralReductionExistence

namespace OrdinaryTowerComparisonProof

private def operationOrdinaryAdjunction (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ) :
    scalarReductionExtension l E W n ⊣ scalarReductionRestriction l E W n :=
  (scalarReductionExtension_adjunction l E W n).choose

attribute [local irreducible] operationOrdinaryAdjunction

private theorem restrictionFull (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ) :
    (scalarReductionRestriction l E W n).Full := by
  let q := (sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology W)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      (completedIntegralCommRingProjectionUnrestricted l E W n)
  have : Presheaf.IsLocallySurjective (AlgebraicGeometry.Scheme.ProEt.topology W) q.hom :=
    completedProjection_locallySurjective l E W n
  exact SheafOfModules.restriction_full q

private noncomputable def operationEvaluationIso
    (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ) :
    coefficientSequenceRestriction l E W ⋙
        (evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n) ≅
      coefficientSequenceEvaluation l E W n ⋙ scalarReductionRestriction l E W n :=
  eqToIso (coefficientSequenceRestriction_evaluation l E W n)

attribute [local irreducible] operationEvaluationIso

private theorem evaluationObjectEq (W : Scheme.{t}) (n : ℕ)
    (M : coefficientSequenceModules l E W) :
    ((coefficientSequenceRestriction l E W).obj M).obj (op n) =
      (scalarReductionRestriction l E W n).obj ((coefficientSequenceEvaluation l E W n).obj M) :=
  (coefficientSequenceRestriction_exists l E W).exists.choose_spec.1 M n

private abbrev operationEvaluationAt (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ)
    (M : coefficientSequenceModules l E W) :
    ((coefficientSequenceRestriction l E W).obj M).obj (op n) ≅
      (scalarReductionRestriction l E W n).obj ((coefficientSequenceEvaluation l E W n).obj M) :=
  eqToIso (evaluationObjectEq l E W n M)

private abbrev towerProjection (W : Scheme.{t}) (n : ℕ) :=
  (sheafCompose (ProEt.topology W)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      (completedIntegralCommRingProjectionUnrestricted l E W n)

private theorem towerProjectionComp (W : Scheme.{t}) (m n : ℕ) (h : n ≤ m) :
    towerProjection l E W m ≫ normalizedDVRQuotient l E W h = towerProjection l E W n := by
  ext U x
  change ↥((completedIntegralCoefficientSheafUnrestricted l E W).obj.obj U) at x
  unfold completedIntegralCoefficientSheafUnrestricted at x
  exact congrArg (fun k ↦ k.hom.app U x)
    (limit.w (integralCoefficientSheafSystem l E W) (homOfLE h).op)

/-- Use the restriction composition isomorphism with literal module endpoints. -/
private noncomputable def operationRestrictionIso
    (W : AlgebraicGeometry.Scheme.{t}) (m n : ℕ) (h : n ≤ m) :
    normalizedDVRModuleRes l E W h ⋙ scalarReductionRestriction l E W m ≅
      scalarReductionRestriction l E W n :=
  restrictCompIso (towerProjection l E W m) (normalizedDVRQuotient l E W h)
    (towerProjection l E W n) (towerProjectionComp l E W m n h)

private theorem operationRestrictionIso_eq
    (W : AlgebraicGeometry.Scheme.{t}) (m n : ℕ) (h : n ≤ m) :
    operationRestrictionIso l E W m n h =
      eqToIso (coefficientRestrictionComp l E W h) := by
  exact restrictComp_eq (towerProjection l E W m) (normalizedDVRQuotient l E W h)
    (towerProjection l E W n) (towerProjectionComp l E W m n h)
    (coefficientRestrictionComp l E W h)

attribute [local irreducible] operationRestrictionIso

private abbrev operationRestrictionAt (W : AlgebraicGeometry.Scheme.{t})
    (m n : ℕ) (h : n ≤ m) (N : scalarReductionTarget l E W n) :
    (scalarReductionRestriction l E W m).obj ((normalizedDVRModuleRes l E W h).obj N) ≅
      (scalarReductionRestriction l E W n).obj N :=
  restrictionComparison (scalarReductionRestriction l E W m)
    (scalarReductionRestriction l E W n) (normalizedDVRModuleRes l E W h)
    (operationRestrictionIso l E W m n h) N

private theorem evaluationComparisonHom
    {A B C : Type*} [Category A] [Category B] [Category C]
    (U : C ⥤ (ℕᵒᵖ ⥤ A)) (V : C ⥤ B) (R : B ⥤ A) (n : ℕᵒᵖ)
    (e : U ⋙ (evaluation ℕᵒᵖ A).obj n ≅ V ⋙ R) (M : C) :
    (evaluationComparison U V R n e M).hom = e.hom.app M := rfl

private theorem comparisonWithObjectEq_f
    {A B C : Type*} [Category A] [Category B] [Category C]
    [HasZeroMorphisms A] [HasZeroMorphisms B] [HasZeroMorphisms C]
    (U : C ⥤ (ℕᵒᵖ ⥤ A)) (V : C ⥤ B) (R : B ⥤ A)
    [U.PreservesZeroMorphisms] [V.PreservesZeroMorphisms] [R.PreservesZeroMorphisms]
    (n : ℕᵒᵖ) (e : U ⋙ (evaluation ℕᵒᵖ A).obj n = V ⋙ R)
    (w : ∀ M, (U.obj M).obj n = R.obj (V.obj M))
    (K : CochainComplex C ℤ) (P : CochainComplex B ℤ)
    (κ : (V.mapHomologicalComplex (.up ℤ)).obj K ≅ P) (i : ℤ) :
    ((complexComparison U V R n (eqToIso e) K ≪≫
      (R.mapHomologicalComplex (.up ℤ)).mapIso κ).hom).f i =
      eqToHom (w (K.X i)) ≫ R.map (κ.hom.f i) := by
  rw [comparisonWithIso_f, evaluationComparisonHom, eqToIso.hom, eqToHom_app]

private theorem componentGeneral (W : AlgebraicGeometry.Scheme.{t})
    (m n : ℕ) (h : n ≤ m) (M : scalarReductionSource l E W) :
    coefficientOrdinaryQuotientComponent l E W h M =
      (coefficientQuotientNatTrans
        (operationOrdinaryAdjunction l E W m)
        (operationOrdinaryAdjunction l E W n)
        (normalizedDVRModuleRes l E W h)
        (eqToIso (coefficientRestrictionComp l E W h))).app M := by
  unfold operationOrdinaryAdjunction
  unfold coefficientOrdinaryQuotientComponent
  rfl
private theorem ordinaryQuotientFormula (W : AlgebraicGeometry.Scheme.{t})
    (m n : ℕ) (h : n ≤ m) (M : scalarReductionSource l E W) :
    (coefficientOrdinaryQuotient l E W h).app M =
      (coefficientQuotientNatTrans
        (operationOrdinaryAdjunction l E W m)
        (operationOrdinaryAdjunction l E W n)
        (normalizedDVRModuleRes l E W h)
        (eqToIso (coefficientRestrictionComp l E W h))).app M := by
  have hq : coefficientOrdinaryQuotient l E W h =
      (coefficientOrdinaryQuotient_exists l E W h).choose := by
    unfold coefficientOrdinaryQuotient
    rfl
  exact (congrArg (fun τ ↦ τ.app M) hq).trans
    (((coefficientOrdinaryQuotient_exists l E W h).choose_spec.1 M).trans
      (componentGeneral l E W m n h M))

private theorem ordinaryQuotientComparisonFormula (W : AlgebraicGeometry.Scheme.{t})
    (m n : ℕ) (h : n ≤ m) (M : scalarReductionSource l E W) :
    (coefficientOrdinaryQuotient l E W h).app M =
      (coefficientQuotientNatTrans
        (operationOrdinaryAdjunction l E W m)
        (operationOrdinaryAdjunction l E W n)
        (normalizedDVRModuleRes l E W h)
        (operationRestrictionIso l E W m n h)).app M := by
  exact (ordinaryQuotientFormula l E W m n h M).trans
    (congrArg (fun c ↦ (coefficientQuotientNatTrans
      (operationOrdinaryAdjunction l E W m)
      (operationOrdinaryAdjunction l E W n)
      (normalizedDVRModuleRes l E W h) c).app M)
      (operationRestrictionIso_eq l E W m n h).symm)

private theorem ordinaryRestrictedQuotient (W : AlgebraicGeometry.Scheme.{t})
    (m n : ℕ) (h : n ≤ m) (M : scalarReductionSource l E W)
    (v : (scalarReductionRestriction l E W m).obj
        ((scalarReductionExtension l E W m).obj M) ⟶
      (scalarReductionRestriction l E W n).obj ((scalarReductionExtension l E W n).obj M))
    (hu : (operationOrdinaryAdjunction l E W m).unit.app M ≫ v =
      (operationOrdinaryAdjunction l E W n).unit.app M) :
    (scalarReductionRestriction l E W m).map
        ((coefficientOrdinaryQuotient l E W h).app M) ≫
      (operationRestrictionIso l E W m n h).hom.app
        ((scalarReductionExtension l E W n).obj M) = v := by
  let : (scalarReductionRestriction l E W m).Full := restrictionFull l E W m
  exact rightMapChosen
    (operationOrdinaryAdjunction l E W m)
    (operationOrdinaryAdjunction l E W n)
    (normalizedDVRModuleRes l E W h) (operationRestrictionIso l E W m n h)
    (coefficientOrdinaryQuotient l E W h) M (ordinaryQuotientComparisonFormula l E W m n h M) v hu

private def ordinaryFiniteComparison (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (κ : ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
      ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P) :
    (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C).asFunctor.obj
      (op n) ≅ unrestrictedTowerComplex l E W n P :=
  complexComparison (coefficientSequenceRestriction l E W)
    (coefficientSequenceEvaluation l E W n) (scalarReductionRestriction l E W n) (op n)
    (operationEvaluationIso l E W n) C ≪≫
    ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).mapIso κ

private theorem ordinaryFiniteComparison_f (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (κ : ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
      ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P) (i : ℤ) :
    (ordinaryFiniteComparison l E W n C P κ).hom.f i =
      (operationEvaluationAt l E W n (C.X i)).hom ≫
        (scalarReductionRestriction l E W n).map (κ.hom.f i) := by
  unfold ordinaryFiniteComparison operationEvaluationIso
  exact comparisonWithObjectEq_f (coefficientSequenceRestriction l E W)
    (coefficientSequenceEvaluation l E W n) (scalarReductionRestriction l E W n)
    (op n) (coefficientSequenceRestriction_evaluation l E W n)
    (fun N ↦ evaluationObjectEq l E W n N) C
    (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P) κ i

private def operationTransitionComponent (W : AlgebraicGeometry.Scheme.{t})
    (m n : ℕ) (h : n ≤ m) (M : coefficientSequenceModules l E W) :
    (coefficientSequenceEvaluation l E W m).obj M ⟶
      (normalizedDVRModuleRes l E W h).obj ((coefficientSequenceEvaluation l E W n).obj M) :=
  compositeComponent (coefficientSequenceEvaluation l E W m)
    (coefficientSequenceEvaluation l E W n) (normalizedDVRModuleRes l E W h)
    (coefficientSequenceTransition l E W h) M

private def operationQuotientComponent (W : AlgebraicGeometry.Scheme.{t})
    (m n : ℕ) (h : n ≤ m) (N : scalarReductionSource l E W) :
    (scalarReductionExtension l E W m).obj N ⟶
      (normalizedDVRModuleRes l E W h).obj ((scalarReductionExtension l E W n).obj N) :=
  compositeComponent (scalarReductionExtension l E W m)
    (scalarReductionExtension l E W n) (normalizedDVRModuleRes l E W h)
    (coefficientOrdinaryQuotient l E W h) N

-- Compare the actual scalar restrictions, without switching to the older
-- finite-field-indexed completion presentation.
private theorem ordinaryTypedRestrictionSquare (W : AlgebraicGeometry.Scheme.{t})
    (m n : ℕ) (h : n ≤ m) (M : coefficientSequenceModules l E W) :
    ((coefficientSequenceRestriction l E W).obj M).map (homOfLE h).op ≫
        (operationEvaluationAt l E W n M).hom =
      (operationEvaluationAt l E W m M).hom ≫
        (scalarReductionRestriction l E W m).map
          (operationTransitionComponent l E W m n h M) ≫
        (operationRestrictionAt l E W m n h
          ((coefficientSequenceEvaluation l E W n).obj M)).hom := by
  dsimp only [operationEvaluationAt, eqToIso.hom]
  rw [restrictionComparison_hom]
  unfold operationRestrictionIso
  have hU := (coefficientSequenceRestriction_exists l E W).exists.choose_spec
  apply moduleHom_eq_of_heq (evaluationObjectEq l E W m M) (evaluationObjectEq l E W n M)
  intro U
  have hτ := restrictionComposite_heq (towerProjection l E W m)
    (normalizedDVRQuotient l E W h) (towerProjection l E W n)
    (towerProjectionComp l E W m n h) (operationTransitionComponent l E W m n h M) U
  have hσ : HEq
      (fun x : ((coefficientSequenceEvaluation l E W m).obj M).val.obj U ↦
        (((operationTransitionComponent l E W m n h M).val.app U) x))
      (fun x : M.val.obj (op (m, U.unop)) ↦
        M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x) :=
    transition_heq l E W M h U
  exact (hU.2.1 M m n h U).trans (hτ.trans hσ).symm

attribute [local irreducible] coefficientSequenceRestriction

private theorem ordinaryRestrictionNaturality (W : AlgebraicGeometry.Scheme.{t})
    (m n : ℕ) (h : n ≤ m)
    (M : coefficientSequenceModules l E W) (N : scalarReductionSource l E W)
    (κn : (coefficientSequenceEvaluation l E W n).obj M ⟶
      (scalarReductionExtension l E W n).obj N) :
    (scalarReductionRestriction l E W m).map ((normalizedDVRModuleRes l E W h).map κn) ≫
        (operationRestrictionAt l E W m n h
          ((scalarReductionExtension l E W n).obj N)).hom =
      (operationRestrictionAt l E W m n h
          ((coefficientSequenceEvaluation l E W n).obj M)).hom ≫
        (scalarReductionRestriction l E W n).map κn := by
  exact restrictionComparison_naturality
    (scalarReductionRestriction l E W m) (scalarReductionRestriction l E W n)
    (normalizedDVRModuleRes l E W h) (operationRestrictionIso l E W m n h)
    (X := (coefficientSequenceEvaluation l E W n).obj M)
    (Y := (scalarReductionExtension l E W n).obj N) κn

private theorem ordinaryMappedQuotientSquare (W : AlgebraicGeometry.Scheme.{t})
    (m n : ℕ) (h : n ≤ m)
    (M : coefficientSequenceModules l E W) (N : scalarReductionSource l E W)
    (κm : (coefficientSequenceEvaluation l E W m).obj M ⟶
      (scalarReductionExtension l E W m).obj N)
    (κn : (coefficientSequenceEvaluation l E W n).obj M ⟶
      (scalarReductionExtension l E W n).obj N)
    (hκ : (coefficientSequenceTransition l E W h).app M ≫
        (normalizedDVRModuleRes l E W h).map κn =
      κm ≫ (coefficientOrdinaryQuotient l E W h).app N) :
    (scalarReductionRestriction l E W m).map (operationTransitionComponent l E W m n h M) ≫
      (scalarReductionRestriction l E W m).map ((normalizedDVRModuleRes l E W h).map κn) =
    (scalarReductionRestriction l E W m).map κm ≫
      (scalarReductionRestriction l E W m).map (operationQuotientComponent l E W m n h N) := by
  exact mappedQuotientSquareAllComponents
    (coefficientSequenceEvaluation l E W m) (coefficientSequenceEvaluation l E W n)
    (scalarReductionExtension l E W m) (scalarReductionExtension l E W n)
    (scalarReductionRestriction l E W m) (normalizedDVRModuleRes l E W h)
    (coefficientSequenceTransition l E W h) (coefficientOrdinaryQuotient l E W h)
    M N κm κn hκ

private theorem ordinaryTypedRestrictedQuotient (W : AlgebraicGeometry.Scheme.{t})
    (m n : ℕ) (h : n ≤ m) (M : scalarReductionSource l E W)
    (v : (scalarReductionRestriction l E W m).obj
        ((scalarReductionExtension l E W m).obj M) ⟶
      (scalarReductionRestriction l E W n).obj ((scalarReductionExtension l E W n).obj M))
    (hu : (operationOrdinaryAdjunction l E W m).unit.app M ≫ v =
      (operationOrdinaryAdjunction l E W n).unit.app M) :
    (scalarReductionRestriction l E W m).map
        (operationQuotientComponent l E W m n h M) ≫
      (operationRestrictionAt l E W m n h
        ((scalarReductionExtension l E W n).obj M)).hom = v := by
  exact restrictionSquareAllComponents
    (scalarReductionExtension l E W m) (scalarReductionExtension l E W n)
    (scalarReductionRestriction l E W m) (scalarReductionRestriction l E W n)
    (normalizedDVRModuleRes l E W h) (operationRestrictionIso l E W m n h)
    (coefficientOrdinaryQuotient l E W h) M v
    (ordinaryRestrictedQuotient l E W m n h M v hu)

private theorem ordinaryModuleSquare (W : AlgebraicGeometry.Scheme.{t})
    (m n : ℕ) (h : n ≤ m)
    (M : coefficientSequenceModules l E W) (N : scalarReductionSource l E W)
    (κm : (coefficientSequenceEvaluation l E W m).obj M ⟶
      (scalarReductionExtension l E W m).obj N)
    (κn : (coefficientSequenceEvaluation l E W n).obj M ⟶
      (scalarReductionExtension l E W n).obj N)
    (hκ : (coefficientSequenceTransition l E W h).app M ≫
        (normalizedDVRModuleRes l E W h).map κn =
      κm ≫ (coefficientOrdinaryQuotient l E W h).app N)
    (v : (scalarReductionRestriction l E W m).obj
        ((scalarReductionExtension l E W m).obj N) ⟶
      (scalarReductionRestriction l E W n).obj ((scalarReductionExtension l E W n).obj N))
    (hu : (operationOrdinaryAdjunction l E W m).unit.app N ≫ v =
      (operationOrdinaryAdjunction l E W n).unit.app N) :
    ((coefficientSequenceRestriction l E W).obj M).map (homOfLE h).op ≫
        ((operationEvaluationAt l E W n M).hom ≫
          (scalarReductionRestriction l E W n).map κn) =
      ((operationEvaluationAt l E W m M).hom ≫
        (scalarReductionRestriction l E W m).map κm) ≫ v := by
  have ht := ordinaryTypedRestrictionSquare l E W m n h M
  have hf := ordinaryTypedRestrictedQuotient l E W m n h N v hu
  have hc := ordinaryRestrictionNaturality l E W m n h M N κn
  have hk := ordinaryMappedQuotientSquare l E W m n h M N κm κn hκ
  exact arrowSquare
    (((coefficientSequenceRestriction l E W).obj M).map (homOfLE h).op)
    (operationEvaluationAt l E W m M).hom (operationEvaluationAt l E W n M).hom
    ((scalarReductionRestriction l E W m).map (operationTransitionComponent l E W m n h M))
    ((operationRestrictionAt l E W m n h
      ((coefficientSequenceEvaluation l E W n).obj M)).hom)
    ((scalarReductionRestriction l E W m).map κm)
    ((scalarReductionRestriction l E W n).map κn)
    ((scalarReductionRestriction l E W m).map ((normalizedDVRModuleRes l E W h).map κn))
    ((operationRestrictionAt l E W m n h
      ((scalarReductionExtension l E W n).obj N)).hom)
    ((scalarReductionRestriction l E W m).map (operationQuotientComponent l E W m n h N))
    v ht hk hc hf

private theorem ordinaryChainSquare (W : AlgebraicGeometry.Scheme.{t})
    (m n : ℕ) (h : n ≤ m)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (κm : ((coefficientSequenceEvaluation l E W m).mapHomologicalComplex (.up ℤ)).obj C ≅
      ((scalarReductionExtension l E W m).mapHomologicalComplex (.up ℤ)).obj P)
    (κn : ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
      ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P)
    (hκ : (NatTrans.mapHomologicalComplex (coefficientSequenceTransition l E W h)
        (.up ℤ)).app C ≫
      ((normalizedDVRModuleRes l E W h).mapHomologicalComplex (.up ℤ)).map κn.hom =
      κm.hom ≫ (NatTrans.mapHomologicalComplex
        (coefficientOrdinaryQuotient l E W h) (.up ℤ)).app P)
    (v : unrestrictedTowerComplex l E W m P ⟶ unrestrictedTowerComplex l E W n P)
    (hu : ∀ i, (operationOrdinaryAdjunction l E W m).unit.app (P.X i) ≫
      v.f i = (operationOrdinaryAdjunction l E W n).unit.app (P.X i)) :
    (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C).asFunctor.map
        (homOfLE h).op ≫ (ordinaryFiniteComparison l E W n C P κn).hom =
      (ordinaryFiniteComparison l E W m C P κm).hom ≫ v := by
  apply HomologicalComplex.hom_ext
  intro i
  have hκi : (coefficientSequenceTransition l E W h).app (C.X i) ≫
      (normalizedDVRModuleRes l E W h).map (κn.hom.f i) =
    κm.hom.f i ≫ (coefficientOrdinaryQuotient l E W h).app (P.X i) :=
    congrArg (fun f ↦ f.f i) hκ
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    ordinaryFiniteComparison_f, ordinaryFiniteComparison_f]
  exact ordinaryModuleSquare l E W m n h (C.X i) (P.X i)
    (κm.hom.f i) (κn.hom.f i) hκi (v.f i) (hu i)

private theorem finite_unit_tensor (W : Scheme.{t}) (n : ℕ)
    (N : scalarReductionSource l E W) (U : W.ProEtᵒᵖ) (x : N.val.obj U) :
    ((operationOrdinaryAdjunction l E W n).unit.app N).val.app U x =
      unrestrictedIntegralTensorSection l E W n N U 1 x := by
  unfold operationOrdinaryAdjunction
  have hu := CompletionUnit.finite_unit_tensor l E W N n U x
  unfold purSequenceFiniteAdjunction at hu
  exact hu

attribute [local semireducible] unrestrictedIntegralComplexFunctor

private theorem unitStepDegree (W : Scheme.{t}) (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E W) ℤ) (i : ℤ) :
    (operationOrdinaryAdjunction l E W (n + 1)).unit.app (P.X i) ≫
      (unrestrictedTowerTransition l E W P n).f i =
      (operationOrdinaryAdjunction l E W n).unit.app (P.X i) := by
  ext U x
  have hm := finite_unit_tensor l E W (n + 1) (P.X i) U x
  have hn := finite_unit_tensor l E W n (P.X i) U x
  have ht : (((unrestrictedTowerTransition l E W P n).f i).val.app U)
      (unrestrictedIntegralTensorSection l E W (n + 1) (P.X i) U 1 x) =
      unrestrictedIntegralTensorSection l E W n (P.X i) U 1 x := by
    unfold unrestrictedTowerTransition unrestrictedIntegralTransition
    have hs :=
      (unrestrictedIntegralTransition_existsUnique l E W n).exists.choose_spec P i U 1 x
    have h1 : ((integralCoefficientSheafTransition l E W n).hom.app U) 1 = 1 :=
      map_one ((integralCoefficientSheafTransition l E W n).hom.app U).hom
    exact hs.trans (congrArg (fun s ↦ unrestrictedIntegralTensorSection l E W n (P.X i) U s x) h1)
  exact (congrArg (fun z ↦ (((unrestrictedTowerTransition l E W P n).f i).val.app U) z) hm).trans
    (ht.trans hn.symm)

private theorem moduleEqToHom_heq
    {D : Type*} [Category D] {J : GrothendieckTopology D}
    {R : Sheaf J RingCat.{r}} {A B : SheafOfModules.{r} R}
    (h : A = B) (U : Dᵒᵖ) (x : A.val.obj U) :
    HEq (((eqToHom h).val.app U) x) x := by
  subst B
  rfl

private theorem abEqToHom_heq {A B : AddCommGrpCat.{r}} (h : A = B) (x : A) :
    HEq ((eqToHom h : A ⟶ B) x) x := by
  subst B
  rfl

private theorem restricted_section (W : Scheme.{t})
    (N : coefficientSequenceModules l E W) (n : ℕ) (U : W.ProEtᵒᵖ)
    (x : N.val.obj (op (n, U.unop))) :
    ((operationEvaluationAt l E W n N).hom).val.app U
      (integralComparisonRestrictedSection l E W N n U x) =
        coefficientEvaluationSection l E W N n U x := by
  dsimp only [operationEvaluationAt, eqToIso.hom]
  have hleft := moduleEqToHom_heq
    (evaluationObjectEq l E W n N) U
    (integralComparisonRestrictedSection l E W N n U x)
  have hcast : HEq (integralComparisonRestrictedSection l E W N n U x) x :=
    cast_heq _ _
  have hright : HEq (coefficientEvaluationSection l E W N n U x) x :=
    abEqToHom_heq (coefficientSequenceEvaluationAb_eq l E W N n U).symm x
  exact eq_of_heq (hleft.trans (hcast.trans hright.symm))

private theorem cancelIsoPresentation
    {A : Type*} [Category A] {X Y Z : A}
    (a : X ≅ Y) (k : Y ≅ Z) (e : X ≅ Z) (h : a ≪≫ k = e) :
    a.inv ≫ e.hom = k.hom := by
  rw [← h, Iso.trans_hom, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

private theorem evaluationPresentation
    {A B C : Type*} [Category A] [Category B] [Category C]
    (U : C ⥤ (ℕᵒᵖ ⥤ A)) (V : C ⥤ B) (R : B ⥤ A) (n : ℕᵒᵖ)
    (e : U ⋙ (evaluation ℕᵒᵖ A).obj n = V ⋙ R)
    (w : ∀ M, (U.obj M).obj n = R.obj (V.obj M))
    {X Y : C} {Z : B} (f : X ⟶ Y) (k : V.obj Y ⟶ Z) (j : V.obj X ⟶ Z)
    (h : V.map f ≫ k = j) :
    (U.map f).app n ≫ (eqToHom (w Y) ≫ R.map k) =
      eqToHom (w X) ≫ R.map j := by
  have hn := (eqToHom e).naturality f
  simp only [eqToHom_app, Functor.comp_map] at hn
  have hn' : (U.map f).app n ≫ eqToHom (w Y) =
      eqToHom (w X) ≫ R.map (V.map f) := hn
  rw [← Category.assoc, hn', Category.assoc, ← R.map_comp, h]

end OrdinaryTowerComparisonProof

attribute [local semireducible] unrestrictedIntegralComplexFunctor

/-- Restriction of the ordinary quotient system is the actual strict quotient tower.
Source: Stacks 03D7, 03EK and 0941, strict quotient presentation construction.
(blueprint: lem-trf-ordinary-quotient-tower-comparison).

Proof: at level n compose the restriction/evaluation identification with the
restriction of M.evaluation n. Naturality in complexes follows from naturality
of both factors. The transition square is M.transition restricted to completed
coefficients, together with the coefficient projection composition identity.
It identifies the transition with the actual quotient map since both send
s tensor x to its reduced coefficient tensor x. Thus the components assemble
to a natural isomorphism of entire strict towers. For a second presentation a,
compose restriction of a inverse with this isomorphism. The finite comparison
identity cancels a inverse and gives exactly the displayed section formula.
This is an ordinary complex assertion; no derived category, resolving-class
assumption, completeness, or boundedness is used. -/
theorem ordinaryQuotientTowerComparison
    (W : Scheme.{t}) (M : CompletionUnit.OrdinaryModel l E W) :
    let T := (coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.complexOfFunctorsToFunctorToComplex
    ∃ θ : M.quotient l E W ⋙ T ≅ trfQuotientTowerFunctor l E W,
    ∀ (P : CochainComplex (scalarReductionSource l E W) ℤ)
      (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
      (a : (M.quotient l E W).obj P ≅ C)
      (κ : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
          (unrestrictedIntegralFiniteComplex l E W n).obj P),
      (∀ n : ℕ,
        ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).mapIso a ≪≫
          κ n = (NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).app P) →
      ∀ (n : ℕ) (i : ℤ) (U : W.ProEtᵒᵖ) (x : (C.X i).val.obj (op (n, U.unop))),
        (((T.mapIso a.symm ≪≫ θ.app P).hom.app (op n)).f i).val.app U
            (integralComparisonRestrictedSection l E W (C.X i) n U x) =
          ((κ n).hom.f i).val.app U
            (coefficientEvaluationSection l E W (C.X i) n U x)  := by
  classical
  let T := (coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ) ⋙
    HomologicalComplex.complexOfFunctorsToFunctorToComplex
  let b (P : CochainComplex (scalarReductionSource l E W) ℤ) (n : ℕ) :=
    OrdinaryTowerComparisonProof.ordinaryFiniteComparison l E W n
      ((M.quotient l E W).obj P) P
      ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).app P)
  have hb (P : CochainComplex (scalarReductionSource l E W) ℤ) (n : ℕ) :
      (T.obj ((M.quotient l E W).obj P)).map (homOfLE n.le_succ).op ≫ (b P n).hom =
        (b P (n + 1)).hom ≫
          ((trfQuotientTowerFunctor l E W).obj P).map (homOfLE n.le_succ).op := by
    change _ = (b P (n + 1)).hom ≫
      ((Functor.ofOpSequence (unrestrictedIntegralTransition l E W)).map
        (homOfLE n.le_succ).op).app P
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    apply OrdinaryTowerComparisonProof.ordinaryChainSquare l E W
      (n + 1) n n.le_succ ((M.quotient l E W).obj P) P
    · apply HomologicalComplex.hom_ext
      intro i
      exact M.transition (P.X i) n.le_succ
    · exact OrdinaryTowerComparisonProof.unitStepDegree l E W n P
  let e (P : CochainComplex (scalarReductionSource l E W) ℤ) :
      T.obj ((M.quotient l E W).obj P) ≅ (trfQuotientTowerFunctor l E W).obj P :=
    let τ : T.obj ((M.quotient l E W).obj P) ⟶
        (trfQuotientTowerFunctor l E W).obj P :=
      NatTrans.ofOpSequence (fun n ↦ (b P n).hom) (hb P)
    NatIso.ofComponents (fun n ↦ b P n.unop) (fun f ↦ τ.naturality f)
  let θ : M.quotient l E W ⋙ T ≅ trfQuotientTowerFunctor l E W :=
    NatIso.ofComponents e (by
      intro P Q f
      apply NatTrans.ext
      funext n
      apply HomologicalComplex.hom_ext
      intro i
      let en := Functor.isoWhiskerLeft M.tensor
          (OrdinaryTowerComparisonProof.operationEvaluationIso l E W n.unop) ≪≫
        Functor.isoWhiskerRight (M.evaluation n.unop)
          (scalarReductionRestriction l E W n.unop)
      exact en.hom.naturality (f.f i))
  refine ⟨θ, ?_⟩
  intro P C a κ hκ n i U x
  have hfinite :
      (coefficientSequenceEvaluation l E W n).map (a.inv.f i) ≫
          ((M.evaluation n).hom.app (P.X i)) = (κ n).hom.f i := by
    exact congrArg (fun z ↦ z.f i)
      (OrdinaryTowerComparisonProof.cancelIsoPresentation
        (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).mapIso a)
        (κ n) ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).app P) (hκ n))
  have hc : (((T.mapIso a.symm ≪≫ θ.app P).hom.app (op n)).f i) =
      (OrdinaryTowerComparisonProof.operationEvaluationAt l E W n (C.X i)).hom ≫
        (scalarReductionRestriction l E W n).map ((κ n).hom.f i) := by
    change ((coefficientSequenceRestriction l E W).map (a.inv.f i)).app (op n) ≫
      (b P n).hom.f i = _
    exact (congrArg
      (fun z ↦ ((coefficientSequenceRestriction l E W).map (a.inv.f i)).app (op n) ≫ z)
      (OrdinaryTowerComparisonProof.ordinaryFiniteComparison_f l E W n
        ((M.quotient l E W).obj P) P
        ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).app P) i)).trans
      (OrdinaryTowerComparisonProof.evaluationPresentation
        (coefficientSequenceRestriction l E W) (coefficientSequenceEvaluation l E W n)
        (scalarReductionRestriction l E W n) (op n)
        (coefficientSequenceRestriction_evaluation l E W n)
        (fun N ↦ OrdinaryTowerComparisonProof.evaluationObjectEq l E W n N)
        (a.inv.f i) ((M.evaluation n).hom.app (P.X i)) ((κ n).hom.f i) hfinite)
  erw [hc, SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply, OrdinaryTowerComparisonProof.restricted_section]
  rfl

end WeilConjectures
