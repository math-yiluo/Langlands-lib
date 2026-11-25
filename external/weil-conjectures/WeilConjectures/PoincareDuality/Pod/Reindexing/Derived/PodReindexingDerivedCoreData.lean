/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexingStrictData.PodReindexingStrictComparisons
public import Mathlib.Basic.Logic.Lemmas

/-! Raw comparison data for the derived reindexing core.

The record contains the comparison maps while leaving their five normalization laws
as separate obligations.  It is used to decompose the core existence theorem.
(blueprint: def-pod-reindexing-derived-core-data) -/

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
  (SY : PodSignedRoosShift (scalarReductionSource l E Y))
  (SX : PodSignedRoosShift (scalarReductionSource l E X))

def podReindexingCoreQuotientGenerators
    (β : ∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ),
      integralOperationsGoodComplex l E Y P → ∀ n : ℕ,
      (isoReductionFiniteComplex l E g n).obj (unrestrictedTowerFiniteComplex l E Y n P) ≅
        unrestrictedTowerFiniteComplex l E X n
          ((isoReductionIntegralComplex l E g).obj P)) : Prop :=
  ∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (hP : integralOperationsGoodComplex l E Y P) (n : ℕ) (i : ℤ) (U : X.ProEt)
    (a : (integralCoefficientCommRingSheaf l E Y n).obj.obj
      (op ((proEtaleIsoPostcompose g).obj U)))
    (x : (P.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
    (((β P hP n).hom.f i).val.app (op U))
        (unrestrictedTowerTensorSection l E Y n (P.X i)
          (op ((proEtaleIsoPostcompose g).obj U)) a x) =
      unrestrictedTowerTensorSection l E X n
        (((isoReductionIntegralComplex l E g).obj P).X i) (op U)
        ((isoSectionwiseConstantMap g (CommRingCat.of
          (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).hom.app
            (op U) a) x

def podReindexingCoreQuotientTransition
    (β : ∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ),
      integralOperationsGoodComplex l E Y P → ∀ n : ℕ,
      (isoReductionFiniteComplex l E g n).obj (unrestrictedTowerFiniteComplex l E Y n P) ≅
        unrestrictedTowerFiniteComplex l E X n
          ((isoReductionIntegralComplex l E g).obj P)) : Prop :=
  ∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (hP : integralOperationsGoodComplex l E Y P) (n : ℕ) (i : ℤ) (U : X.ProEt)
    (z : ((unrestrictedTowerFiniteComplex l E Y (n + 1) P).X i).val.obj
      (op ((proEtaleIsoPostcompose g).obj U))),
    (((β P hP n).hom.f i).val.app (op U))
        (((unrestrictedTowerTransition l E Y P n).f i).val.app
          (op ((proEtaleIsoPostcompose g).obj U)) z) =
      (((unrestrictedTowerTransition l E X
        ((isoReductionIntegralComplex l E g).obj P) n).f i).val.app (op U))
          ((((β P hP (n + 1)).hom.f i).val.app (op U)) z)

structure PodReindexingDerivedCoreData where
  reduction : (podReindexCalculus l E Y).reduction ⋙
      integralComparisonDerivedSequencePullback l E g ≅
    podOrdinaryReindex l E g ⋙ (podReindexCalculus l E X).reduction
  limit : coefficientSequenceLimit l E Y ⋙ podOrdinaryReindex l E g ≅
    integralComparisonDerivedSequencePullback l E g ⋙ coefficientSequenceLimit l E X
  evaluation : ∀ n : ℕ, integralComparisonDerivedSequencePullback l E g ⋙
      coefficientSequenceDerivedEvaluation l E X n ≅
    coefficientSequenceDerivedEvaluation l E Y n ⋙ isoReductionFiniteDerived l E g n
  restriction : ∀ n : ℕ, coefficientFiniteDerivedRestriction l E Y n ⋙
      podOrdinaryReindex l E g ≅
    isoReductionFiniteDerived l E g n ⋙ coefficientFiniteDerivedRestriction l E X n
  finite : ∀ n : ℕ, coefficientFiniteDerivedExtension l E Y n ⋙
      isoReductionFiniteDerived l E g n ≅
    podOrdinaryReindex l E g ⋙ coefficientFiniteDerivedExtension l E X n
  sourceRoos : IntegralComparisonRoosModel l E Y
  targetRoos : IntegralComparisonRoosModel l E X
  pullback : integralDerivedPullback l E g ≅ (podReindexCalculus l E Y).reduction ⋙
    integralComparisonDerivedSequencePullback l E g ⋙ coefficientSequenceLimit l E X

namespace PodReindexingDerivedCoreData

variable (Q : PodReindexingDerivedCoreData l E g)

/-- Assemble raw comparison maps into the existing completion-reindex interface.
(blueprint: def-pod-reindexing-derived-core-data) -/
def assemble
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (S : PodReindexingStrictData l E g)
    (β : ∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ),
      integralOperationsGoodComplex l E Y P → ∀ n : ℕ,
      (isoReductionFiniteComplex l E g n).obj (unrestrictedTowerFiniteComplex l E Y n P) ≅
        unrestrictedTowerFiniteComplex l E X n
          ((isoReductionIntegralComplex l E g).obj P))
    (CY : IntegralOnSlice.completion l E Y none ≅
      (podReindexCalculus l E Y).reduction ⋙ coefficientSequenceLimit l E Y)
    (CX : IntegralOnSlice.completion l E X none ≅
      (podReindexCalculus l E X).reduction ⋙ coefficientSequenceLimit l E X) :
    PodCompletionReindex l E g where
  completionSource := CY
  completionTarget := CX
  reduction := Q.reduction
  limit := Q.limit
  evaluation := Q.evaluation
  restriction := Q.restriction
  finite := Q.finite
  good := S.good l E g
  quotient := β
  roos := S.roos
  shiftSource := SY
  shiftTarget := SX
  sourceRoos := Q.sourceRoos
  targetRoos := Q.targetRoos
  restricted := S.restricted
  pullback := Q.pullback

end PodReindexingDerivedCoreData

end WeilConjectures
