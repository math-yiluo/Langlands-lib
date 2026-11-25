/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Reindexing.Derived.PodReindexingDerivedCoreData
import all WeilConjectures.SmoothPurity.Supporting.IsomorphismReductionTower

/-! Unit-compatible reduction for the specified full-limit comparison.

Keep the full-limit comparison fixed and transport its adjunction to construct
its compatible reduction comparison. In particular this preserves the strict
Roos normalization used by the assembled five-law package.
(blueprint: lem-pod-reindexing-derived-core-unit) -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
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

/-- Construct the reduction comparison compatible with the supplied full-limit map.

Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5.
STATEMENT-DISPUTED (old statement, repaired): independent raw reduction and limit
isomorphisms need not satisfy Unit; negating only the reduction changes its left side.
Keep the given limit, including its full Roos normalization, and take its left mate
under the two reduction/limit adjunctions. The ordinary and whole-system reindexing
functors are equivalences, so `adjointSquare` makes this mate invertible and supplies
its unit equation. Use its inverse as the reduction comparison and cancel the inverse
pair after applying the target limit functor. No finite-evaluation conservativity is
used, so empty sites, zero objects and unbounded complexes are included.
(blueprint: lem-pod-reindexing-derived-core-unit) -/
theorem podReindexingDerivedCoreData_unit
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (S : PodReindexingStrictData l E g) (_hS : S.Laws l E g SY SX)
    (β : ∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ),
      integralOperationsGoodComplex l E Y P → ∀ n : ℕ,
      (isoReductionFiniteComplex l E g n).obj (unrestrictedTowerFiniteComplex l E Y n P) ≅
        unrestrictedTowerFiniteComplex l E X n
          ((isoReductionIntegralComplex l E g).obj P))
    (_hβ : podReindexingCoreQuotientGenerators l E g β)
    (_htransition : podReindexingCoreQuotientTransition l E g β)
    (CY : IntegralOnSlice.completion l E Y none ≅
      (podReindexCalculus l E Y).reduction ⋙ coefficientSequenceLimit l E Y)
    (CX : IntegralOnSlice.completion l E X none ≅
      (podReindexCalculus l E X).reduction ⋙ coefficientSequenceLimit l E X)
    (Q : PodReindexingDerivedCoreData l E g) :
    ∃ α : (podReindexCalculus l E Y).reduction ⋙
        integralComparisonDerivedSequencePullback l E g ≅
      podOrdinaryReindex l E g ⋙ (podReindexCalculus l E X).reduction,
      PodCompletionReindex.Unit l E g
        (({ Q with reduction := α } : PodReindexingDerivedCoreData l E g).assemble
          l E g SY SX S β CY CX) := by
  have : (isoReductionIntegralInverse l E g).IsEquivalence :=
    isoReduction_equivalence.{t, u} g (isoReductionCompletedMap l E g).hom
  have : (podOrdinaryReindex l E g).IsEquivalence :=
    Functor.isEquivalence_mapDerivedCategory (isoReductionIntegralInverse l E g)
  let F := integralComparisonDerivedSequencePullback l E g
  let G := integralComparisonDerivedSequencePullback l E (inv g)
  let η : 𝟭 (coefficientSequenceDerived l E Y) ≅ F ⋙ G :=
    ((integralComparisonSystemComposition l E (inv g) g).symm ≪≫
      eqToIso (by rw [IsIso.inv_hom_id]) ≪≫ integralComparisonSystemUnit l E Y).symm
  let ε : G ⋙ F ≅ 𝟭 (coefficientSequenceDerived l E X) :=
    (integralComparisonSystemComposition l E g (inv g)).symm ≪≫
      eqToIso (by rw [IsIso.hom_inv_id]) ≪≫ integralComparisonSystemUnit l E X
  have : F.IsEquivalence := (CategoryTheory.Equivalence.mk F G η ε).isEquivalence_functor
  obtain ⟨e, he⟩ := adjointSquare (podOrdinaryReindex l E g) F
    (podReindexCalculus l E Y).adjunction (podReindexCalculus l E X).adjunction Q.limit
  refine ⟨e.symm, ?_⟩
  intro K
  change (podOrdinaryReindex l E g).map
      ((podReindexCalculus l E Y).adjunction.unit.app K) ≫
      Q.limit.hom.app ((podReindexCalculus l E Y).reduction.obj K) ≫
      (coefficientSequenceLimit l E X).map (e.inv.app K) = _
  rw [← Category.assoc, ← he K, Category.assoc, ← Functor.map_comp]
  rw [e.hom_inv_id_app]
  rw [(coefficientSequenceLimit l E X).map_id
    ((podOrdinaryReindex l E g ⋙ (podReindexCalculus l E X).reduction).obj K)]
  exact Category.comp_id _

end WeilConjectures
