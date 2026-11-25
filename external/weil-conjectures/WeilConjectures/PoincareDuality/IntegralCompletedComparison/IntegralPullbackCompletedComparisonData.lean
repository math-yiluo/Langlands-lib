/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcQbarCompletedPullback
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletionCompletedSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantExact
public import WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackTriangles
public import WeilConjectures.AlgebraicGeometry.ImmersionCompletedPullback.SfImmersionCompletedPullbackComparison
public import WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackReduction
public import WeilConjectures.FourierTransform.IntegralCompletedComparison.IntegralPullbackShiftCoordinates

/-! # Integral and strict-tower completed pullback

Source: Stacks Project, proetale.tex, Tag 099N(5), with sites-cohomology.tex,
Tag 0941 (blueprint: lem-a1-integral-pullback-completed-comparison).

The coefficient transport is the existing projection-normalized ring isomorphism.
Finite comparisons below are fixed on inverse-image generators; the integral
projections are the actual mapping-cocone projections on K-flat representatives.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] HasDerivedCategory.standard CategoryTheory.constantSheaf
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsCommHasDerivedCategory
  WeilConjectures.IntegralOnSlice.hasDerived
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsSiteSmall
attribute [local implicit_reducible] SheafOfModules.instAbelian
  CategoryTheory.abelianOfAdjunction CategoryTheory.Abelian.ofCoimageImageComparisonIsIso
  WeilConjectures.scalarReductionSourceDerived WeilConjectures.scalarReductionTargetDerived
  WeilConjectures.integralOperationsCommHasDerivedCategory
  WeilConjectures.integralTowerHasDerivedCategory
  WeilConjectures.integralCompletedRingHasDerivedCategory
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

private instance (priority := 6000) fixedAbSheafify (W : Scheme.{u}) :
    HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} W

private instance (priority := 6000) fixedAbBijective (W : Scheme.{u}) :
    (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} W

namespace WeilConjectures.IntegralCompletedComparison

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The existing completed-ring transport, on modules before localization.
Source: Stacks 099N, coefficient identification
(blueprint: lem-a1-integral-pullback-completed-comparison). -/
abbrev modules (T : Scheme.{u}) :=
  pbcRestrict (ImmersionCompletedPullback.completedRingIso l E T).inv

/-- The same transport on complexes.
Source: Stacks 099N (blueprint: lem-a1-integral-pullback-completed-comparison). -/
abbrev complexes (T : Scheme.{u}) := (modules l E T).mapHomologicalComplex (.up ℤ)

/-- The existing exact transport on derived categories.
Source: Stacks 099N (blueprint: lem-a1-integral-pullback-completed-comparison). -/
abbrev derived (T : Scheme.{u}) := ImmersionCompletedPullback.transport l E T

/-- Exact coefficient restriction inherits the standard termwise derived shift.
Source: Stacks 014E (blueprint: lem-a1-integral-pullback-completed-comparison). -/
instance derived_commShift (T : Scheme.{u}) : (derived l E T).CommShift ℤ :=
  inferInstanceAs ((modules l E T).mapDerivedCategory.CommShift ℤ)

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- Finite pullback followed by restriction, in the integral presentation.
Source: Stacks 099N(5) (blueprint: lem-a1-integral-pullback-completed-comparison). -/
def finiteIntegral (n : ℕ) :=
  modules l E Y ⋙ unrestrictedIntegralReductionFunctor.{u, u} l E Y n ⋙
    integralOperationsLevelPullback.{u, u} l E g n ⋙
      SheafOfModules.restrictScalars.{u + 1}
        ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (completedIntegralCommRingProjectionUnrestricted.{u, u} l E X n))

/-- Additivity of the composite finite pullback and exact coefficient restriction.
Source: Stacks 03D2 (blueprint: lem-a1-integral-pullback-completed-comparison). -/
instance finiteIntegral_additive (n : ℕ) : (finiteIntegral l E g n).Additive := by
  have := unrestrictedIntegralReductionFunctor_additive.{u, u} l E Y n
  have := integralOperationsLevelPullback_additive.{u, u} l E g n
  unfold finiteIntegral
  infer_instance

/-- The same finite pullback in the adic presentation, transported to the same ring.
Source: Stacks 099N(5) (blueprint: lem-a1-integral-pullback-completed-comparison). -/
def finiteCompleted (n : ℕ) :=
  reductionChange Y (completedReductionProjection Y (pbcIntegralDatum l E) n) ⋙
    completedReductionFiniteModules g (pbcIntegralDatum l E) n ⋙
      pbcRestrict (completedReductionProjection X (pbcIntegralDatum l E) n) ⋙ modules l E X

/-- Additivity of the finite target and its coefficient transports.
Source: Stacks 03D2 (blueprint: lem-a1-integral-pullback-completed-comparison). -/
instance finiteCompleted_additive (n : ℕ) : (finiteCompleted l E g n).Additive := by
  unfold finiteCompleted
  infer_instance

/-- Apply the actual finite natural comparison to complexes, with inherited zero preservation.
Source: Stacks 099N(5) (blueprint: lem-a1-integral-pullback-completed-comparison). -/
def finiteComplexComparison (n : ℕ)
    (e : finiteIntegral l E g n ≅ finiteCompleted l E g n) :
    (finiteIntegral l E g n).mapHomologicalComplex (.up ℤ) ⟶
      (finiteCompleted l E g n).mapHomologicalComplex (.up ℤ) :=
  letI := finiteIntegral_additive l E g n
  letI := finiteCompleted_additive l E g n
  NatTrans.mapHomologicalComplex e.hom (.up ℤ)

/-- The finite comparison sends each pulled-back tensor-unit generator to itself.
This fixes the comparison on the actual finite quotient modules, rather than allowing
an arbitrary automorphism of a derived tower evaluation.
Source: Stacks 099N(5), tensor balancing
(blueprint: lem-a1-integral-pullback-completed-comparison). -/
def FiniteNormalization (n : ℕ)
    (e : finiteIntegral l E g n ≅ finiteCompleted l E g n) : Prop :=
  ∀ (M : pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l E)))
    (V : Y.ProEt) (x : M.val.obj (op V)),
    ((e.hom.app M).val.app (op ((proEtaleBaseChange g).obj V)))
      (integralOperationsPullbackGenerator.{u, u} l E g n
        ((unrestrictedIntegralReductionFunctor.{u, u} l E Y n).obj ((modules l E Y).obj M)) V
        (unrestrictedIntegralTensorSection.{u, u} l E Y n ((modules l E Y).obj M) (op V) 1 x)) =
      completedReductionFiniteGenerator g (pbcIntegralDatum l E) n M V
        ((proEtaleBaseChange g).obj V) (𝟙 _) 1 1 x

/-- The representative computation map of the specified integral pullback.
Source: Stacks 099N(5), resolving-class descent
(blueprint: lem-a1-integral-pullback-completed-comparison). -/
def integralComputation
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l E))) ℤ)
    (hP : integralOperationsGoodComplex.{u, u} l E Y ((complexes l E Y).obj P)) :=
  (integralDerivedPullback.{u, u} l E g).map ((modules l E Y).mapDerivedCategoryFactors.hom.app P) ≫
    (integralDerivedPullbackComparison.{u, u} l E g).hom.app ⟨(complexes l E Y).obj P, hP⟩

/-- The actual integral projection is the first mapping-cocone map and the nth product leg.
Source: Stacks 0941 and 099N(5)
(blueprint: lem-a1-integral-pullback-completed-comparison). -/
def integralProjection
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l E))) ℤ)
    (hP : integralOperationsGoodComplex.{u, u} l E Y ((complexes l E Y).obj P)) (n : ℕ) :=
  integralComputation l E g P hP ≫ DerivedCategory.Q.map
    (CochainComplex.mappingCocone.fst
      (towerTransitionEndomorphism
        (K := fun k : ℕ ↦ ((integralOperationsPullbackTowerFunctor.{u, u} l E g).obj
          ((complexes l E Y).obj P)).obj (op k))
        (integralOperationsTowerStep ((integralOperationsPullbackTowerFunctor.{u, u} l E g).obj
          ((complexes l E Y).obj P)))) ≫
      Pi.π (fun k : ℕ ↦ ((integralOperationsPullbackTowerFunctor.{u, u} l E g).obj
        ((complexes l E Y).obj P)).obj (op k)) n)

/-- The existing unique unit-compatible strict-tower/reflector comparison.
Source: Stacks 099N(2),(5)
(blueprint: lem-a1-integral-pullback-completed-comparison). -/
def towerIso := (pbcActualCompletedPullback_tower (pbcIntegralDatum l E) g).exists.choose

/-- The defining strict derived-limit projection, followed by its normalized finite evaluation.
Source: Stacks 0941 and 099N(5)
(blueprint: lem-a1-integral-pullback-completed-comparison). -/
def completedProjection (K : PbcCompletedDerived Y (pbcIntegralDatum l E))
    (hK : PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E) K) (n : ℕ) :=
  (derived l E X).map
    ((towerIso l E g).inv.app ⟨K, hK⟩ ≫
      (completedReductionLimitProjection (pbcIntegralDatum l E) (X := X) n).app
        ((completedTowerPullback g (pbcIntegralDatum l E)).obj
          ((completedReductionTower Y (pbcIntegralDatum l E)).obj K)) ≫
      (completedReductionFiniteEvaluation g (pbcIntegralDatum l E) n).hom.app K)

/-- The canonical finite computation map, retaining both exact restriction comparisons.
Source: Stacks 099N(5), universal derived counits
(blueprint: lem-a1-integral-pullback-completed-comparison). -/
def finiteComputation
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l E))) ℤ)
    (n : ℕ) :=
  (derived l E X).map
    ((pbcDerivedRestrict (completedReductionProjection X (pbcIntegralDatum l E) n)).map
      (completedReductionFiniteModelMap g (pbcIntegralDatum l E) n P) ≫
      (completedReductionRestrictionFactors X
        (completedReductionProjection X (pbcIntegralDatum l E) n)).hom.app
        (((completedReductionFiniteModules g (pbcIntegralDatum l E) n).mapHomologicalComplex
          (.up ℤ)).obj
          (((reductionChange Y (completedReductionProjection Y
            (pbcIntegralDatum l E) n)).mapHomologicalComplex (.up ℤ)).obj P))) ≫
    (modules l E X).mapDerivedCategoryFactors.hom.app
      (((pbcRestrict (completedReductionProjection X
        (pbcIntegralDatum l E) n)).mapHomologicalComplex (.up ℤ)).obj
          (((completedReductionFiniteModules g (pbcIntegralDatum l E) n).mapHomologicalComplex
            (.up ℤ)).obj
              (((reductionChange Y (completedReductionProjection Y
                (pbcIntegralDatum l E) n)).mapHomologicalComplex (.up ℤ)).obj P)))

/-- The integral pullback after the existing coefficient identification.
Source: Stacks 099N(5) (blueprint: lem-a1-integral-pullback-completed-comparison). -/
abbrev integral := derived l E Y ⋙ integralDerivedPullback.{u, u} l E g

/-- The completed pullback after the same coefficient identification.
The shift is the normalized shift of completedPullback-preserves-triangles.
Source: Stacks 099N(2),(5)
(blueprint: lem-a1-integral-pullback-completed-comparison). -/
abbrev completed := pbcActualCompletedPull g (pbcIntegralDatum l E) ⋙ derived l E X

/-- Derived completeness is the recorded Roos predicate after canonical coefficient transport.
Source: Bhatt--Scholze 3.5.2
(blueprint: lem-a1-integral-pullback-completed-comparison). -/
abbrev Complete (K : PbcCompletedDerived Y (pbcIntegralDatum l E)) : Prop :=
  IntegralOnSlice.IsComplete l E Y none ((derived l E Y).obj K)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] pbcIntegralDatum finiteComputation integralProjection
  completedProjection finiteComplexComparison towerIso
  integralDerivedPullback integralOperationsPullbackComplexFunctor
  completedIntegralCommRingSheafUnrestricted
  completedIntegralCoefficientSheafUnrestricted
  integralOperationsGoodComplex pbcActualCompletedPull

-- Avoid unused generated size and constructor-injectivity lemmas for this large record.
set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- The clauses of the comparison, with all projections and shifts specified.
The finite isomorphisms identify the two exact finite module pullbacks on their
canonical generators. Every gamma is a morphism over the completed coefficient ring.
Source: Stacks 099N(5), 0941
(blueprint: lem-a1-integral-pullback-completed-comparison). -/
structure Comparison where
  intrinsic : ∀ (K : PbcCompletedDerived Y (pbcIntegralDatum l E)), Complete l E K →
    PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E) K
  finite : ∀ n : ℕ, finiteIntegral l E g n ≅ finiteCompleted l E g n
  finite_normalization : ∀ n : ℕ, FiniteNormalization l E g n (finite n)
  chainShift : (integralOperationsPullbackComplexFunctor.{u, u} l E g).CommShift ℤ
  chainShift_coordinates : ShiftCoordinates l E g chainShift
  derivedShift : (integralDerivedPullback.{u, u} l E g).CommShift ℤ
  derivedShift_descent : ShiftDescent l E g chainShift derivedShift
  gamma : ∀ (K : PbcCompletedDerived Y (pbcIntegralDatum l E)), Complete l E K →
    ((integral l E g).obj K ≅ (completed l E g).obj K)
  naturality : ∀ (K L : PbcCompletedDerived Y (pbcIntegralDatum l E))
    (hK : Complete l E K) (hL : Complete l E L) (a : K ⟶ L),
    (integral l E g).map a ≫ (gamma L hL).hom =
      (gamma K hK).hom ≫ (completed l E g).map a
  projections : ∀
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l E))) ℤ)
    (hP : integralOperationsGoodComplex.{u, u} l E Y ((complexes l E Y).obj P))
    (hK : Complete l E (DerivedCategory.Q.obj P)) (n : ℕ),
    (gamma (DerivedCategory.Q.obj P) hK).inv ≫ integralProjection l E g P hP n ≫
        DerivedCategory.Q.map
          ((finiteComplexComparison l E g n (finite n)).app P) =
      completedProjection l E g (DerivedCategory.Q.obj P)
          (intrinsic (DerivedCategory.Q.obj P) hK) n ≫ finiteComputation l E g P n
  shifts : (fun [_d : (integralDerivedPullback.{u, u} l E g).CommShift ℤ] ↦
    ∀ (K : PbcCompletedDerived Y (pbcIntegralDatum l E)) (hK : Complete l E K) (r : ℤ),
      ∃ hKr : Complete l E (K⟦r⟧),
        (gamma (K⟦r⟧) hKr).hom ≫ ((completed l E g).commShiftIso r).hom.app K =
          ((integral l E g).commShiftIso r).hom.app K ≫ ((gamma K hK).hom)⟦r⟧')
    (_d := derivedShift)

end WeilConjectures.IntegralCompletedComparison
