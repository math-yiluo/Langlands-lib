/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Reindexing.Derived.PodReindexingDerivedComparisonsCore
import WeilConjectures.PoincareDuality.Pod.Reindexing.Derived.PodReindexingDerivedComparisonsPullback

/-! # Localization of the normalized strict reindexing comparisons

Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 03EL, 07A4, 0941 (blueprint: lem-pod-reindexing-derived-comparisons).
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

/-- Descend the prescribed strict comparisons to the selected derived adjunctions.
Source: blueprint theorem-poincare-duality-frobenius--2, proof Steps 1 and 5;
Stacks 03EL, 07A4, 0941 (blueprint: lem-pod-reindexing-derived-comparisons).

Proof: derive the exact sectionwise equivalences on integral modules, finite
modules and whole coherent systems. The restriction projection squares give the
finite restriction and evaluation comparisons. Conjugating the scalar-extension
adjunction by these equivalences gives the finite extension comparison; its
counit on K-flat representatives identifies it with the strict quotient map.
The quotient transitions make these maps a coherent reduction-system comparison.
Compute total limit on K-injective systems by the normalized limit-to-Roos map.
The strict diagonal Roos comparison then descends to the limit comparison, with
the displayed equation on every system complex. Its product projections give
the limit-projection formula. Transport the ordinary system tensor/limit Hom
bijection before deriving. The quotient generator formula identifies its unit,
and the projection formula identifies its counit, as whole-system maps. Hence
the reduction and limit comparisons satisfy both stated adjunction equations.
Identify completion with the chosen reduction/limit composite using the unique
left-adjoint comparison and the primitive completion-unit normalization. The
same simultaneous quotient presentation and the target's normalized Roos model
identify the given completed pullback with reduction, system pullback and total
limit. This gives its representative normalization on every good complex and
coherent presentation. Universal localization gives naturality and independence
of all representatives. No completeness or boundedness is used in these steps. -/
theorem podReindexingDerivedComparisons
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (S : PodReindexingStrictData l E g) (hS : S.Laws l E g SY SX)
    (β : ∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ),
      integralOperationsGoodComplex l E Y P → ∀ n : ℕ,
      (isoReductionFiniteComplex l E g n).obj (unrestrictedTowerFiniteComplex l E Y n P) ≅
        unrestrictedTowerFiniteComplex l E X n ((isoReductionIntegralComplex l E g).obj P))
    (hβ : podReindexingQuotientGenerators l E g β)
    (htransition : podReindexingQuotientTransition l E g β)
    (CY : IntegralOnSlice.completion l E Y none ≅
      (podReindexCalculus l E Y).reduction ⋙ coefficientSequenceLimit l E Y)
    (CX : IntegralOnSlice.completion l E X none ≅
      (podReindexCalculus l E X).reduction ⋙ coefficientSequenceLimit l E X) :
    ∃ R : PodReindexingDerivedData l E g, R.Laws l E g SY SX S β CY CX := by
  obtain ⟨R, hR⟩ := podReindexingDerivedComparisonsCore l E g SY SX S hS β hβ
    htransition CY CX
  obtain ⟨hReduction, hProjection, hUnit, hFinite, hLimit⟩ := hR
  obtain ⟨p, hPullback⟩ := podReindexingDerivedComparisonsPullback l E g SY SX S β CY CX R
  -- The five core laws do not read the `pullback` field, so they survive its replacement.
  exact ⟨{ R with pullback := p }, hReduction, hProjection, hUnit, hFinite, hLimit, hPullback⟩

end WeilConjectures
