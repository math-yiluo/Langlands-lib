/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.IsomorphismReductionTower
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorComparison
public import WeilConjectures.SmoothPurity.CompletedOperations.CompletedOperationTowerSubstitution
public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Projection-normalized reindexing of completion and completed tensor

Source: blueprint, theorem-poincare-duality-frobenius--2, proof Steps 1 and 5;
Stacks Tags 03EL, 07A4 and 0941
(blueprint: def-pod-completion-reindex-models).

The index n means the positive quotient exponent n+1. The ordinary inverse image
is the existing sectionwise relabelling, with its completed scalar action fixed
by every quotient projection. The sequence category retains all quotient arrows.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]

/-- Ordinary reindexing on the ambient derived category, with projection-fixed scalars.
Source: blueprint Steps 1 and 5 (blueprint: def-pod-completion-reindex-models). -/
def podOrdinaryReindex : DerivedCategory (scalarReductionSource l E Y) ⥤
    DerivedCategory (scalarReductionSource l E X) :=
  (isoReductionIntegralInverse l E g).mapDerivedCategory

/-- Reindex the entire strict tower of complexes before taking its Roos realization.
Source: Stacks 0941 (blueprint: def-pod-completion-reindex-models). -/
abbrev podReindexTower : (ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E Y) ℤ) ⥤
    (ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E X) ℤ) :=
  (whiskeringRight ℕᵒᵖ _ _).obj (isoReductionIntegralComplex l E g)

/-- The product map is defined by the actual product projections.
Source: Stacks 0941 (blueprint: def-pod-completion-reindex-models). -/
def podReindexProduct (C : ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E Y) ℤ) :
    (isoReductionIntegralComplex l E g).obj (∏ᶜ fun n : ℕ ↦ C.obj (op n)) ⟶
      ∏ᶜ fun n : ℕ ↦ ((podReindexTower l E g).obj C).obj (op n) :=
  Pi.lift (fun n ↦ (isoReductionIntegralComplex l E g).map
    (Pi.π (fun k : ℕ ↦ C.obj (op k)) n))

section SignedRoos
variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]

/-- The actual 1-s boundary of a strict tower.
Source: Stacks 0941 (blueprint: def-pod-completion-reindex-models). -/
abbrev podRoosBoundary (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) :=
  towerTransitionEndomorphism (K := fun n : ℕ ↦ C.obj (op n))
    (integralOperationsTowerStep C)

/-- Shift the entire strict tower, including its transitions.
Source: Stacks 011G, 0941 (blueprint: def-pod-completion-reindex-models). -/
def podShiftTower (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) (r : ℤ) :=
  C ⋙ shiftFunctor (CochainComplex A ℤ) r

/-- The inverse of the projection-defined product comparison for shift.
Source: Stacks 011G, 0941 (blueprint: def-pod-completion-reindex-models). -/
def podShiftProduct (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) (r : ℤ) :
    (∏ᶜ fun n : ℕ ↦ (C.obj (op n))⟦r⟧) ⟶ (∏ᶜ fun n : ℕ ↦ C.obj (op n))⟦r⟧ :=
  inv (piComparison (shiftFunctor (CochainComplex A ℤ) r) (fun n : ℕ ↦ C.obj (op n)))

/-- Signed cone-shift data, to be fixed by both coordinates below.
Source: Stacks 011G, 0941 (blueprint: def-pod-completion-reindex-models). -/
structure PodSignedRoosShift (A : Type a) [Category.{b} A] [Abelian A]
    [HasCountableProducts A] where
  /-- Comparison with the same signed cochain shift. -/
  comparison : ∀ (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) (r : ℤ),
    integralOperationsRoos (podShiftTower C r) ≅ (integralOperationsRoos C)⟦r⟧

/-- Both coordinates specify the actual signed cone-shift map.
Source: Stacks 011G, 0941 (blueprint: def-pod-completion-reindex-models). -/
def PodSignedRoosShift.Laws (S : PodSignedRoosShift A) : Prop :=
  (∀ (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) (r : ℤ),
    (S.comparison C r).hom ≫ (CochainComplex.mappingCocone.fst (podRoosBoundary C))⟦r⟧' =
      CochainComplex.mappingCocone.fst (podRoosBoundary (podShiftTower C r)) ≫
        podShiftProduct C r) ∧
  (∀ (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) (r i : ℤ),
    (S.comparison C r).hom.f i ≫ (CochainComplex.mappingCocone.snd (podRoosBoundary C)).v
        (i + r) (i - 1 + r) (by omega) =
      r.negOnePow • ((CochainComplex.mappingCocone.snd
        (podRoosBoundary (podShiftTower C r))).v i (i - 1) (by omega) ≫
          (podShiftProduct C r).f (i - 1)))

end SignedRoos

/-- The termwise shift comparison, with the identity component in each degree.
Source: Stacks 011G (blueprint: def-pod-completion-reindex-models). -/
def podTowerShift
    (C : ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E Y) ℤ) (r : ℤ) :
    (podReindexTower l E g).obj (podShiftTower C r) ≅
      podShiftTower ((podReindexTower l E g).obj C) r :=
  Functor.associator C _ _ ≪≫
    isoWhiskerLeft C ((isoReductionIntegralComplex l E g).commShiftIso r) ≪≫
      (Functor.associator C _ _).symm

/-- The specified coefficient reduction calculus, retaining its actual adjunction.
Source: Stacks 0941 (blueprint: def-pod-completion-reindex-models). -/
def podReindexCalculus (W : Scheme.{t}) :=
  (coefficientDerivedSystemEvaluationCalculus l E W).choose

/-- The restricted tower of a coherent system complex, before total derived limit.
Source: Stacks 0941 (blueprint: def-pod-completion-reindex-models). -/
def podRestrictedTower {W : Scheme.{t}}
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) :=
  (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C).asFunctor

/-- The existing K-injective-normalized comparison to the actual Roos complex.
Source: Stacks 0941 (blueprint: def-pod-completion-reindex-models). -/
def podLimitRoos {W : Scheme.{t}} (ρ : IntegralComparisonRoosModel l E W)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj C) ≅
      DerivedCategory.Q.obj (integralOperationsRoos (podRestrictedTower l E C)) :=
  (coefficientConstantTowerLimit l E W).mapIso
    ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.app C) ≪≫
  ρ.comparison.app
    (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C)

/-- All ambient comparisons, pinned on quotient generators, actual adjunction maps,
and both coordinates of the fixed Roos complex. These are data and their defining
normalizations; their existence, not an arbitrary choice of maps, is asserted below.
Source: blueprint Steps 1 and 5; Stacks 03EL, 07A4, 0941
(blueprint: def-pod-completion-reindex-models). -/
structure PodCompletionReindex where
  /-- The actual completion triangle in the original scalar identity normalization. -/
  completionSource : IntegralOnSlice.completion l E Y none ≅
    (podReindexCalculus l E Y).reduction ⋙ coefficientSequenceLimit l E Y
  /-- The same actual completion at the target. -/
  completionTarget : IntegralOnSlice.completion l E X none ≅
    (podReindexCalculus l E X).reduction ⋙ coefficientSequenceLimit l E X
  /-- Reindex the strict coherent reduction system. -/
  reduction : (podReindexCalculus l E Y).reduction ⋙
      integralComparisonDerivedSequencePullback l E g ≅
    podOrdinaryReindex l E g ⋙ (podReindexCalculus l E X).reduction
  /-- Reindex the specified total derived limit, for every ambient system. -/
  limit : coefficientSequenceLimit l E Y ⋙ podOrdinaryReindex l E g ≅
    integralComparisonDerivedSequencePullback l E g ⋙ coefficientSequenceLimit l E X
  /-- Finite evaluation uses ordinary finite coefficient reindexing. -/
  evaluation : ∀ n : ℕ, integralComparisonDerivedSequencePullback l E g ⋙
      coefficientSequenceDerivedEvaluation l E X n ≅
    coefficientSequenceDerivedEvaluation l E Y n ⋙ isoReductionFiniteDerived l E g n
  /-- Reindexing commutes with restriction through the actual quotient projection. -/
  restriction : ∀ n : ℕ, coefficientFiniteDerivedRestriction l E Y n ⋙
      podOrdinaryReindex l E g ≅
    isoReductionFiniteDerived l E g n ⋙ coefficientFiniteDerivedRestriction l E X n
  /-- The scalar reduction comparison, simultaneously for all quotient levels. -/
  finite : ∀ n : ℕ, coefficientFiniteDerivedExtension l E Y n ⋙
      isoReductionFiniteDerived l E g n ≅
    podOrdinaryReindex l E g ⋙ coefficientFiniteDerivedExtension l E X n
  /-- Flat-term K-flat representatives stay flat-term K-flat after relabelling. -/
  good : ∀ P : CochainComplex (scalarReductionSource l E Y) ℤ,
    integralOperationsGoodComplex l E Y P →
      integralOperationsGoodComplex l E X ((isoReductionIntegralComplex l E g).obj P)
  /-- The simultaneous quotient tensor comparison on complexes. -/
  quotient : ∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ),
    integralOperationsGoodComplex l E Y P → ∀ n : ℕ,
    (isoReductionFiniteComplex l E g n).obj (unrestrictedTowerFiniteComplex l E Y n P) ≅
      unrestrictedTowerFiniteComplex l E X n ((isoReductionIntegralComplex l E g).obj P)
  /-- The same natural Roos map on all strict towers, including incomplete inputs. -/
  roos : ∀ C : ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E Y) ℤ,
    (isoReductionIntegralComplex l E g).obj (integralOperationsRoos C) ≅
      integralOperationsRoos ((podReindexTower l E g).obj C)
  /-- The canonical signed shift comparison at the source. -/
  shiftSource : PodSignedRoosShift (scalarReductionSource l E Y)
  /-- The canonical signed shift comparison at the target. -/
  shiftTarget : PodSignedRoosShift (scalarReductionSource l E X)
  /-- The total-limit models are the actual K-injective-normalized models. -/
  sourceRoos : IntegralComparisonRoosModel l E Y
  /-- The actual K-injective model at the target. -/
  targetRoos : IntegralComparisonRoosModel l E X
  /-- Restriction and reindexing commute on the whole strict tower of complexes. -/
  restricted : ∀ C : CochainComplex (coefficientSequenceModules l E Y) ℤ,
    (podReindexTower l E g).obj (podRestrictedTower l E C) ≅
      podRestrictedTower l E
        (((integralComparisonSequencePullback l E g).mapHomologicalComplex (.up ℤ)).obj C)
  /-- The existing completed pullback, with its whole quotient/Roos realization. -/
  pullback : integralDerivedPullback l E g ≅ (podReindexCalculus l E Y).reduction ⋙
    integralComparisonDerivedSequencePullback l E g ⋙ coefficientSequenceLimit l E X

namespace PodCompletionReindex

/-- The two original completion units agree with the actual reduction units.
The original units are those used by finiteFreeCompletedScalarComparison for E=E.
Source: blueprint Steps 1 and 5 (blueprint: def-pod-completion-reindex-models). -/
def CompletionUnits (D : PodCompletionReindex l E g) : Prop :=
  (∀ K : DerivedCategory (scalarReductionSource l E Y),
    (IntegralOnSlice.completionUnit l E Y none).app K ≫
      D.completionSource.hom.app K = (podReindexCalculus l E Y).adjunction.unit.app K) ∧
  (∀ K : DerivedCategory (scalarReductionSource l E X),
    (IntegralOnSlice.completionUnit l E X none).app K ≫
      D.completionTarget.hom.app K = (podReindexCalculus l E X).adjunction.unit.app K)

/-- The coherent reduction comparison has exactly these finite evaluations.
Source: blueprint Steps 1 and 5; Stacks 03EL, 07A4, 0941
(blueprint: def-pod-completion-reindex-models). -/
def ReductionEvaluation (D : PodCompletionReindex l E g) : Prop :=
  ∀ (K : DerivedCategory (scalarReductionSource l E Y)) (n : ℕ),
    (coefficientSequenceDerivedEvaluation l E X n).map (D.reduction.hom.app K) ≫
        ((podReindexCalculus l E X).reductionEvaluation n).hom.app
          ((podOrdinaryReindex l E g).obj K) =
      (D.evaluation n).hom.app ((podReindexCalculus l E Y).reduction.obj K) ≫
        (isoReductionFiniteDerived l E g n).map
          (((podReindexCalculus l E Y).reductionEvaluation n).hom.app K) ≫
        (D.finite n).hom.app K

/-- Every limit projection, with its genuine restricted coefficient action.
Source: blueprint Steps 1 and 5; Stacks 03EL, 07A4, 0941
(blueprint: def-pod-completion-reindex-models). -/
def LimitProjection (D : PodCompletionReindex l E g) : Prop :=
  ∀ (A : coefficientSequenceDerived l E Y) (n : ℕ),
    (podOrdinaryReindex l E g).map ((coefficientSequenceProjection l E Y n).app A) ≫
        (D.restriction n).hom.app ((coefficientSequenceDerivedEvaluation l E Y n).obj A) =
      D.limit.hom.app A ≫ (coefficientSequenceProjection l E X n).app
        ((integralComparisonDerivedSequencePullback l E g).obj A) ≫
        (coefficientFiniteDerivedRestriction l E X n).map ((D.evaluation n).hom.app A)

/-- Transport of the actual unit, as a whole-system adjunction identity.
Source: blueprint Steps 1 and 5; Stacks 03EL, 07A4, 0941
(blueprint: def-pod-completion-reindex-models). -/
def Unit (D : PodCompletionReindex l E g) : Prop :=
  ∀ K : DerivedCategory (scalarReductionSource l E Y),
    (podOrdinaryReindex l E g).map ((podReindexCalculus l E Y).adjunction.unit.app K) ≫
        D.limit.hom.app ((podReindexCalculus l E Y).reduction.obj K) ≫
        (coefficientSequenceLimit l E X).map (D.reduction.hom.app K) =
      (podReindexCalculus l E X).adjunction.unit.app ((podOrdinaryReindex l E g).obj K)

/-- Transport of the actual counit, before taking any finite evaluation.
Source: blueprint Steps 1 and 5; Stacks 03EL, 07A4, 0941
(blueprint: def-pod-completion-reindex-models). -/
def Counit (D : PodCompletionReindex l E g) : Prop :=
  ∀ A : coefficientSequenceDerived l E Y,
    D.reduction.inv.app ((coefficientSequenceLimit l E Y).obj A) ≫
        (integralComparisonDerivedSequencePullback l E g).map
          ((podReindexCalculus l E Y).adjunction.counit.app A) =
      (podReindexCalculus l E X).reduction.map (D.limit.hom.app A) ≫
        (podReindexCalculus l E X).adjunction.counit.app
          ((integralComparisonDerivedSequencePullback l E g).obj A)

/-- Completeness concerns this unit, not an unspecified limit-triangle map.
Source: blueprint Steps 1 and 5; Stacks 03EL, 07A4, 0941
(blueprint: def-pod-completion-reindex-models). -/
def CompleteUnit (_D : PodCompletionReindex l E g) : Prop :=
  ∀ K : DerivedCategory (scalarReductionSource l E Y),
    IntegralOnSlice.IsComplete l E Y none K →
      IsIso ((podReindexCalculus l E Y).adjunction.unit.app K)

/-- Normalization on every local scalar-tensor generator.
Source: blueprint Steps 1 and 5; Stacks 03EL, 07A4, 0941
(blueprint: def-pod-completion-reindex-models). -/
def QuotientGenerators (D : PodCompletionReindex l E g) : Prop :=
  ∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (hP : integralOperationsGoodComplex l E Y P) (n : ℕ) (i : ℤ) (U : X.ProEt)
    (a : (integralCoefficientCommRingSheaf l E Y n).obj.obj
      (op ((proEtaleIsoPostcompose g).obj U)))
    (x : (P.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
    (((D.quotient P hP n).hom.f i).val.app (op U))
        (unrestrictedTowerTensorSection l E Y n (P.X i)
          (op ((proEtaleIsoPostcompose g).obj U)) a x) =
      unrestrictedTowerTensorSection l E X n
        (((isoReductionIntegralComplex l E g).obj P).X i) (op U)
        ((isoSectionwiseConstantMap g (CommRingCat.of
          (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).hom.app
            (op U) a) x

/-- Consecutive quotient squares hold as actual chain-map equations on sections.
Source: blueprint Steps 1 and 5; Stacks 03EL, 07A4, 0941
(blueprint: def-pod-completion-reindex-models). -/
def QuotientTransition (D : PodCompletionReindex l E g) : Prop :=
  ∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (hP : integralOperationsGoodComplex l E Y P) (n : ℕ) (i : ℤ) (U : X.ProEt)
    (z : ((unrestrictedTowerFiniteComplex l E Y (n + 1) P).X i).val.obj
      (op ((proEtaleIsoPostcompose g).obj U))),
    (((D.quotient P hP n).hom.f i).val.app (op U))
        (((unrestrictedTowerTransition l E Y P n).f i).val.app
          (op ((proEtaleIsoPostcompose g).obj U)) z) =
      (((unrestrictedTowerTransition l E X
        ((isoReductionIntegralComplex l E g).obj P) n).f i).val.app (op U))
          ((((D.quotient P hP (n + 1)).hom.f i).val.app (op U)) z)

/-- The finite derived maps are these chain maps on good representatives.
Source: blueprint Steps 1 and 5; Stacks 03EL, 07A4, 0941
(blueprint: def-pod-completion-reindex-models). -/
def FiniteModel (D : PodCompletionReindex l E g) : Prop :=
  ∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (hP : integralOperationsGoodComplex l E Y P) (n : ℕ),
    (isoReductionFiniteDerived l E g n).map
        (coefficientFiniteReductionModel l E Y P hP.1 n).hom ≫
        (isoReductionFiniteInverse l E g n).mapDerivedCategoryFactors.hom.app
          (unrestrictedTowerFiniteComplex l E Y n P) ≫
        DerivedCategory.Q.map (D.quotient P hP n).hom =
      (D.finite n).hom.app (DerivedCategory.Q.obj P) ≫
        (coefficientFiniteDerivedExtension l E X n).map
          ((isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app P) ≫
        (coefficientFiniteReductionModel l E X _ (D.good P hP).1 n).hom

/-- The product-defined square for the complete 1-s differential.
Source: blueprint Steps 1 and 5; Stacks 03EL, 07A4, 0941
(blueprint: def-pod-completion-reindex-models). -/
def RoosBoundary (_D : PodCompletionReindex l E g) : Prop :=
  ∀ C : ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E Y) ℤ,
    (isoReductionIntegralComplex l E g).map (podRoosBoundary C) ≫
        podReindexProduct l E g C =
      podReindexProduct l E g C ≫ podRoosBoundary ((podReindexTower l E g).obj C)

/-- The unshifted coordinate is the actual product comparison.
Source: blueprint Steps 1 and 5; Stacks 03EL, 07A4, 0941
(blueprint: def-pod-completion-reindex-models). -/
def RoosFst (D : PodCompletionReindex l E g) : Prop :=
  ∀ C : ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E Y) ℤ,
    (D.roos C).hom ≫ CochainComplex.mappingCocone.fst
        (podRoosBoundary ((podReindexTower l E g).obj C)) =
      (isoReductionIntegralComplex l E g).map
        (CochainComplex.mappingCocone.fst (podRoosBoundary C)) ≫ podReindexProduct l E g C

/-- The shifted coordinate has the same product comparison, with the cone shift retained.
Source: blueprint Steps 1 and 5; Stacks 03EL, 07A4, 0941
(blueprint: def-pod-completion-reindex-models). -/
def RoosSnd (D : PodCompletionReindex l E g) : Prop :=
  ∀ (C : ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E Y) ℤ) (i : ℤ),
    (D.roos C).hom.f i ≫ (CochainComplex.mappingCocone.snd
        (podRoosBoundary ((podReindexTower l E g).obj C))).v i (i - 1) (by omega) =
      (isoReductionIntegralInverse l E g).map
        ((CochainComplex.mappingCocone.snd (podRoosBoundary C)).v
          i (i - 1) (by omega)) ≫ (podReindexProduct l E g C).f (i - 1)

/-- Naturality before localization, as an equation of entire cone maps.
Source: blueprint Steps 1 and 5; Stacks 03EL, 07A4, 0941
(blueprint: def-pod-completion-reindex-models). -/
def RoosNaturality (D : PodCompletionReindex l E g) : Prop :=
  ∀ (C C' : ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E Y) ℤ)
    (a : C ⟶ C'),
    (isoReductionIntegralComplex l E g).map (integralOperationsRoosMap a) ≫
        (D.roos C').hom =
      (D.roos C).hom ≫ integralOperationsRoosMap ((podReindexTower l E g).map a)

/-- Reindexing and the signed shift give the same actual cone map.
  The projection-defined termwise shift map supplies the intervening tower comparison.
Source: blueprint Steps 1 and 5; Stacks 03EL, 07A4, 0941
(blueprint: def-pod-completion-reindex-models). -/
def RoosShift (D : PodCompletionReindex l E g) : Prop :=
  ∀ (C : ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E Y) ℤ) (r : ℤ),
    ((D.roos (podShiftTower C r)).hom ≫
      integralOperationsRoosMap (podTowerShift l E g C r).hom ≫
      (D.shiftTarget.comparison ((podReindexTower l E g).obj C) r).hom) =
      ((isoReductionIntegralComplex l E g).map (D.shiftSource.comparison C r).hom ≫
        ((isoReductionIntegralComplex l E g).commShiftIso r).hom.app
          (integralOperationsRoos C) ≫ (D.roos C).hom⟦r⟧')

/-- The restricted comparison is the actual sectionwise adjunction-unit map.
This formula fixes every component before localization and rules out a sign twist.
Source: Stacks 03D6, 0941, blueprint Steps 1 and 5
(blueprint: def-pod-completion-reindex-models). -/
def RestrictedGenerators (D : PodCompletionReindex l E g) : Prop :=
  ∀ (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (n : ℕ) (i : ℤ) (U : X.ProEt)
    (x : (C.X i).val.obj (op (n, (proEtaleIsoPostcompose g).obj U))),
    (((D.restricted C).hom.app (op n)).f i).val.app (op U)
        (integralComparisonRestrictedSection l E Y (C.X i) n
          (op ((proEtaleIsoPostcompose g).obj U)) x) =
      integralComparisonRestrictedSection l E X
        ((integralComparisonSequencePullback l E g).obj (C.X i)) n (op U)
        (((integralComparisonSequencePullback l E g).obj (C.X i)).val.map
          (Prod.mkHom (𝟙 n) (proEtaleIsoCommaArrow g U)).op
          (integralComparisonSequenceGenerator l E g (C.X i) n
            ((proEtaleIsoPostcompose g).obj U) x))

/-- The limit comparison is induced by this same full Roos chain map.
Source: blueprint Steps 1 and 5; Stacks 03EL, 07A4, 0941
(blueprint: def-pod-completion-reindex-models). -/
def LimitModel (D : PodCompletionReindex l E g) : Prop :=
  ∀ C : CochainComplex (coefficientSequenceModules l E Y) ℤ,
    (podOrdinaryReindex l E g).map (podLimitRoos l E D.sourceRoos C).hom ≫
        (isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app _ ≫
        DerivedCategory.Q.map (D.roos (podRestrictedTower l E C)).hom ≫
        DerivedCategory.Q.map (integralOperationsRoosFunctor.map (D.restricted C).hom) =
      D.limit.hom.app (DerivedCategory.Q.obj C) ≫
        (coefficientSequenceLimit l E X).map
          ((integralComparisonSequencePullback l E g).mapDerivedCategoryFactors.hom.app C) ≫
        (podLimitRoos l E D.targetRoos _).hom

/-- This is the specified representative comparison, not an arbitrary isomorphism.
Source: blueprint Steps 1 and 5; Stacks 03EL, 07A4, 0941
(blueprint: def-pod-completion-reindex-models). -/
def PullbackNormalization (D : PodCompletionReindex l E g) : Prop :=
  IsIntegralComparisonPullbackNormalized l E g
    (podReindexCalculus l E Y) D.targetRoos D.pullback

/-- All normalizations on the same ambient reindexing maps.
Source: blueprint Steps 1 and 5; Stacks 03EL, 07A4, 0941
(blueprint: def-pod-completion-reindex-models). -/
def Laws (D : PodCompletionReindex l E g) : Prop :=
  CompletionUnits l E g D ∧
  ReductionEvaluation l E g D ∧
  LimitProjection l E g D ∧
  Unit l E g D ∧
  Counit l E g D ∧
  CompleteUnit l E g D ∧
  QuotientGenerators l E g D ∧
  QuotientTransition l E g D ∧
  FiniteModel l E g D ∧
  RoosBoundary l E g D ∧
  RoosFst l E g D ∧
  RoosSnd l E g D ∧
  RoosNaturality l E g D ∧
  D.shiftSource.Laws ∧
  D.shiftTarget.Laws ∧
  RoosShift l E g D ∧
  RestrictedGenerators l E g D ∧
  LimitModel l E g D ∧
  PullbackNormalization l E g D

end PodCompletionReindex

/-- The specified ordinary-to-completed pullback arrow is F(unit), then the normalized
limit comparison, then the specified identification with completed pullback.
Source: blueprint Steps 1 and 5 (blueprint: def-pod-completion-reindex-models). -/
def podOrdinaryToCompleted (D : PodCompletionReindex l E g) :
    podOrdinaryReindex l E g ⟶ integralDerivedPullback l E g :=
  whiskerRight (podReindexCalculus l E Y).adjunction.unit (podOrdinaryReindex l E g) ≫
    whiskerLeft (podReindexCalculus l E Y).reduction D.limit.hom ≫ D.pullback.inv

end WeilConjectures
