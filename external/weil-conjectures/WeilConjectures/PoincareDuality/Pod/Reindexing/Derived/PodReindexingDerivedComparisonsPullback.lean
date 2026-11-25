/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Reindexing.Derived.PodReindexingDerivedComparisonsCore
import WeilConjectures.TraceFormula.Primitive.PrimitiveQuotientPullbackModelExistence

/-! Pullback normalization for the derived reindexing package.

Source: blueprint Steps 1 and 5; Stacks 03EL, 07A4, 0941.
(blueprint: lem-pod-reindexing-derived-comparisons-pullback)
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
  (SY : PodSignedRoosShift (scalarReductionSource l E Y))
  (SX : PodSignedRoosShift (scalarReductionSource l E X))

/-- Every derived-data witness can be given the normalized completed-pullback realization.
The other fields are unchanged.
Source: blueprint Steps 1 and 5; Stacks 099N(2),(5), 0941.
Proof: `primitiveQuotientPullbackModelExistence` for `g`, the source calculus
`podReindexCalculus l E Y` and the target Roos model `R.targetRoos` gives a pullback
model: a realization of the completed pullback with the representative normalization
`IsIntegralComparisonPullbackNormalized`. Replace the `pullback` field of `R` by this
realization. Then `PullbackNormalization` of the assembled package is that
normalization. Here `l` is invertible on `X` and `Y` by the `Invertible` instances.
An arbitrary `R.pullback` need not be normalized: the normalized realization is unique
(`primitiveQuotientRealizations_unique`), so the field is replaced, not kept.
(blueprint: lem-pod-reindexing-derived-comparisons-pullback) -/
theorem podReindexingDerivedComparisonsPullback
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (S : PodReindexingStrictData l E g)
    (β : ∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ),
      integralOperationsGoodComplex l E Y P → ∀ n : ℕ,
      (isoReductionFiniteComplex l E g n).obj (unrestrictedTowerFiniteComplex l E Y n P) ≅
        unrestrictedTowerFiniteComplex l E X n ((isoReductionIntegralComplex l E g).obj P))
    (CY : IntegralOnSlice.completion l E Y none ≅
      (podReindexCalculus l E Y).reduction ⋙ coefficientSequenceLimit l E Y)
    (CX : IntegralOnSlice.completion l E X none ≅
      (podReindexCalculus l E X).reduction ⋙ coefficientSequenceLimit l E X)
    (R : PodReindexingDerivedData l E g) :
    ∃ p : integralDerivedPullback l E g ≅ (podReindexCalculus l E Y).reduction ⋙
        integralComparisonDerivedSequencePullback l E g ⋙ coefficientSequenceLimit l E X,
      PodCompletionReindex.PullbackNormalization l E g
        (({ R with pullback := p } : PodReindexingDerivedData l E g).assemble
          l E g SY SX S β CY CX) := by
  obtain ⟨M⟩ := primitiveQuotientPullbackModelExistence l E g
    (fun x ↦ isUnit_of_invertible _) (fun y ↦ isUnit_of_invertible _)
    (podReindexCalculus l E Y) R.targetRoos
  exact ⟨M.realization, M.normalization⟩

end WeilConjectures
