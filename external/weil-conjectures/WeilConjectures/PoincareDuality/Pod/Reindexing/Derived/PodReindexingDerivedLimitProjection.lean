/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Reindexing.Derived.PodReindexingDerivedCoreData

/-! Limit projection law for raw derived comparison data.

The proof constructs the corresponding normalized comparison law from the strict
quotient, evaluation, and Roos-limit calculations.  This is a strictly smaller
obligation than the assembled five-law package.
(blueprint: lem-pod-reindexing-derived-core-limit-projection) -/

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

/-- Limit projection law for raw derived comparison data.

Source: the strict quotient, evaluation, and Roos-limit descent calculation
from the proof of lem-pod-reindexing-derived-comparisons-core.  The statement
records one conjunct of the assembled core package; its proof is intentionally
split off so it can be proved independently.
(blueprint: lem-pod-reindexing-derived-core-limit-projection) -/
theorem podReindexingDerivedCoreData_limitProjection
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (S : PodReindexingStrictData l E g) (hS : S.Laws l E g SY SX)
    (β : ∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ),
      integralOperationsGoodComplex l E Y P → ∀ n : ℕ,
      (isoReductionFiniteComplex l E g n).obj (unrestrictedTowerFiniteComplex l E Y n P) ≅
        unrestrictedTowerFiniteComplex l E X n
          ((isoReductionIntegralComplex l E g).obj P))
    (hβ : podReindexingCoreQuotientGenerators l E g β)
    (htransition : podReindexingCoreQuotientTransition l E g β)
    (CY : IntegralOnSlice.completion l E Y none ≅
      (podReindexCalculus l E Y).reduction ⋙ coefficientSequenceLimit l E Y)
    (CX : IntegralOnSlice.completion l E X none ≅
      (podReindexCalculus l E X).reduction ⋙ coefficientSequenceLimit l E X)
    (Q : PodReindexingDerivedCoreData l E g) :
    PodCompletionReindex.LimitProjection l E g
      (Q.assemble l E g SY SX S β CY CX) := by
  sorry

end WeilConjectures
