/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Reindexing.Derived.PodReindexingDerivedCoreData
import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingRestrictedTowerNaturality
import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingLimitComplexModel

/-! # Constructing the normalized full-limit comparison

Raw comparison data do not normalize the limit map. We construct its replacement
by descending the specified natural strict Roos comparison, while keeping the
other raw fields and the completion comparisons fixed.
(blueprint: lem-pod-reindexing-derived-core-limit-model) -/

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
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
  (SY : PodSignedRoosShift (scalarReductionSource l E Y))
  (SX : PodSignedRoosShift (scalarReductionSource l E X))

private theorem descendIso {A B C : Type*} [Category* A] [Category* B] [Category* C]
    (q : A ⥤ B) (W : MorphismProperty A) [q.IsLocalization W]
    (F G : B ⥤ C) (e : q ⋙ F ≅ q ⋙ G) :
    ∃ L : F ≅ G, ∀ a, L.hom.app (q.obj a) = e.hom.app a := by
  let h := Localization.fullyFaithfulWhiskeringLeft q W C
  exact ⟨h.preimageIso e, fun a ↦ congr_app (h.map_preimage e.hom) a⟩

/-- Construct the limit comparison by descending the full strict Roos map.

Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 0941. STATEMENT-DISPUTED (old statement, repaired): the assertion for an
arbitrary raw limit map was false: its sign
could be changed independently. Here that map is replaced by the descent of the
specified Roos comparison. The restricted generator law identifies the strict
restriction comparison with the natural inverse-image unit. Compose this natural
isomorphism with both normalized Roos models and the exact-functor localization
comparisons. Fully faithful precomposition with the localization functor descends
it uniquely; its component formula gives the full-limit-model equation.
(blueprint: lem-pod-reindexing-derived-core-limit-model) -/
theorem podReindexingDerivedCoreData_limitModel
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (S : PodReindexingStrictData l E g) (hS : S.Laws l E g SY SX)
    (β : ∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ),
      integralOperationsGoodComplex l E Y P → ∀ n : ℕ,
      (isoReductionFiniteComplex l E g n).obj (unrestrictedTowerFiniteComplex l E Y n P) ≅
        unrestrictedTowerFiniteComplex l E X n
          ((isoReductionIntegralComplex l E g).obj P))
    (CY : IntegralOnSlice.completion l E Y none ≅
      (podReindexCalculus l E Y).reduction ⋙ coefficientSequenceLimit l E Y)
    (CX : IntegralOnSlice.completion l E X none ≅
      (podReindexCalculus l E X).reduction ⋙ coefficientSequenceLimit l E X)
    (Q : PodReindexingDerivedCoreData l E g) :
    ∃ L : coefficientSequenceLimit l E Y ⋙ podOrdinaryReindex l E g ≅
        integralComparisonDerivedSequencePullback l E g ⋙ coefficientSequenceLimit l E X,
      PodCompletionReindex.LimitModel l E g
        (({ Q with limit := L } : PodReindexingDerivedCoreData l E g).assemble
          l E g SY SX S β CY CX) := by
  obtain ⟨r, hr⟩ := podReindexingRestrictedTower_naturalIso l E g S hS.2.2.2.2
  obtain ⟨L, hL⟩ := descendIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (coefficientSequenceModules l E Y) (.up ℤ))
    (coefficientSequenceLimit l E Y ⋙ podOrdinaryReindex l E g)
    (integralComparisonDerivedSequencePullback l E g ⋙ coefficientSequenceLimit l E X)
    (podReindexingLimitComparisonOnComplexes l E g S hS.2.2.1 Q.sourceRoos Q.targetRoos r)
  refine ⟨L, ?_⟩
  intro C
  dsimp only [PodReindexingDerivedCoreData.assemble]
  rw [hL C, hr C]
  exact (podReindexingLimitComparisonOnComplexes_model l E g S hS.2.2.1
    Q.sourceRoos Q.targetRoos r C).symm

end WeilConjectures
