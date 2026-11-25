/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Reindexing.Derived.PodReindexingDerivedCoreData
import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitFixedCalculusModels
import all WeilConjectures.TraceFormula.Isomorphism.IsomorphismDerivedPullbackComparisonNormalization
import all WeilConjectures.SmoothPurity.Supporting.IsomorphismReductionTower
import all WeilConjectures.TraceFormula.Integral.IntegralTowerInverseImageUnit
import all WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonIsomorphism
import WeilConjectures.SmoothPurity.PrimitiveCounit.PrimitiveCounitEvaluation
import WeilConjectures.TraceFormula.Primitive.PrimitiveQuotientPullbackModelExistence
import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingGoodComplex

/-! Existence of the raw comparison maps for the derived reindexing core.

The construction assembles the strict quotient, finite evaluation, and normalized
Roos-limit comparisons.  The five normalization laws are separate obligations.
(blueprint: lem-pod-reindexing-derived-core-data-existence) -/

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

-- Perform this bookkeeping for abstract additive functors, so elaboration does not
-- unfold the concrete sheaf inverse-image and restriction constructions.
private def coreComplexTowerSquare
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
    (U : A ⥤ ℕᵒᵖ ⥤ B) [U.Additive] (V : C ⥤ ℕᵒᵖ ⥤ D) [V.Additive]
    (F : B ⥤ D) [F.Additive] (G : A ⥤ C) [G.Additive]
    (a : U ⋙ (Functor.whiskeringRight ℕᵒᵖ B D).obj F ≅ G ⋙ V) :
    U.mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj (F.mapHomologicalComplex (.up ℤ)) ≅
    G.mapHomologicalComplex (.up ℤ) ⋙ V.mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.complexOfFunctorsToFunctorToComplex := by
  let ac := NatIso.mapHomologicalComplex a (.up ℤ)
  refine NatIso.ofComponents (fun K ↦
    HomologicalComplex.complexOfFunctorsToFunctorToComplex.mapIso (ac.app K)) ?_
  intro K L f
  ext n i
  exact congrArg (fun z ↦ (z.f i).app n) (ac.hom.naturality f)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
  (SY : PodSignedRoosShift (scalarReductionSource l E Y))
  (SX : PodSignedRoosShift (scalarReductionSource l E X))

/-- The strict quotient and normalized limit constructions provide all raw maps.

The proof follows the construction in the strict comparison and coefficient
calculus nodes: take the induced derived reduction, finite evaluation and
restriction maps, the normalized total-limit comparison, and the two normalized
Roos models, together with the induced pullback comparison.  No normalization
law is asserted here; those five laws are the separate split obligations used by
the core theorem.
(blueprint: lem-pod-reindexing-derived-core-data-existence) -/
theorem podReindexingDerivedCoreData_exists
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
      (podReindexCalculus l E X).reduction ⋙ coefficientSequenceLimit l E X) :
    Nonempty (PodReindexingDerivedCoreData l E g) := by
  have _quotientGenerators := hβ
  have _quotientTransitions := htransition
  let _sourceCompletion := CY
  let _targetCompletion := CX
  let F := isoReductionIntegralInverse l E g
  let G := integralComparisonSequencePullback l E g
  have : F.IsEquivalence := isoReduction_equivalence.{t, u} g
    (isoReductionCompletedMap l E g).hom
  have : (integralComparisonSequenceDirectImage l E g).IsEquivalence :=
    towerSequenceDirectImage_equivalence l E g
  have : G.IsEquivalence :=
    (Adjunction.ofIsRightAdjoint
      (integralComparisonSequenceDirectImage l E g)).isEquivalence_left_of_isEquivalence_right
  have : (podOrdinaryReindex l E g).IsEquivalence :=
    Functor.isEquivalence_mapDerivedCategory F
  have : (integralComparisonDerivedSequencePullback l E g).IsEquivalence :=
    Functor.isEquivalence_mapDerivedCategory G
  obtain ⟨MY, ⟨DY⟩⟩ := CompletionUnit.fixedCalculusModels l E Y (podReindexCalculus l E Y)
  obtain ⟨MX, ⟨DX⟩⟩ := CompletionUnit.fixedCalculusModels l E X (podReindexCalculus l E X)
  let ρY := roosModel l E Y (podReindexCalculus l E Y) MY DY
  let ρX := roosModel l E X (podReindexCalculus l E X) MX DX
  have restriction (n : ℕ) : coefficientFiniteDerivedRestriction l E Y n ⋙
      podOrdinaryReindex l E g ≅ isoReductionFiniteDerived l E g n ⋙
        coefficientFiniteDerivedRestriction l E X n := by
    let s := (isoReduction_restrictionSquare l E g n).choose
    exact mapDerivedCategoryCompIso _ _ ≪≫ mapDerivedCategoryNatIso s ≪≫
      (mapDerivedCategoryCompIso _ _).symm
  have finite (n : ℕ) : coefficientFiniteDerivedExtension l E Y n ⋙
      isoReductionFiniteDerived l E g n ≅ podOrdinaryReindex l E g ⋙
        coefficientFiniteDerivedExtension l E X n := by
    have : (isoReductionFiniteInverse l E g n).IsEquivalence :=
      isoReduction_equivalence.{t, u} g (isoSectionwiseConstantMap g
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))
    have : (isoReductionFiniteDerived l E g n).IsEquivalence :=
      Functor.isEquivalence_mapDerivedCategory (isoReductionFiniteInverse l E g n)
    let e := (adjointSquare (podOrdinaryReindex l E g)
      (isoReductionFiniteDerived l E g n) (coefficientFiniteAdjunction l E Y n)
      (coefficientFiniteAdjunction l E X n) (restriction n)).choose
    exact e.symm
  have evaluation (n : ℕ) : integralComparisonDerivedSequencePullback l E g ⋙
      coefficientSequenceDerivedEvaluation l E X n ≅
        coefficientSequenceDerivedEvaluation l E Y n ⋙ isoReductionFiniteDerived l E g n := by
    let A := CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))
    let e := (Scheme.coefficientProEtaleModuleAdjunction g A).leftAdjointUniq
      (AlgebraicGeometry.ProEtale.finiteSectionwiseAdjunction l E g n)
    let s : G ⋙ coefficientSequenceEvaluation l E X n ≅
        coefficientSequenceEvaluation l E Y n ⋙ isoReductionFiniteInverse l E g n :=
      PrimitiveCounit.inverseEvaluation l E g n ≪≫
        isoWhiskerLeft (coefficientSequenceEvaluation l E Y n) e
    exact mapDerivedCategoryCompIso _ _ ≪≫ mapDerivedCategoryNatIso s ≪≫
      (mapDerivedCategoryCompIso _ _).symm
  have limit : coefficientSequenceLimit l E Y ⋙ podOrdinaryReindex l E g ≅
      integralComparisonDerivedSequencePullback l E g ⋙ coefficientSequenceLimit l E X := by
    have hc : inv (isoReductionCompletedMap l E g).hom =
        inv (inverseImageCompletedCoefficientMap l E g) := by
      apply (cancel_mono (inverseImageCompletedCoefficientMap l E g)).mp
      exact (congrArg (inv (isoReductionCompletedMap l E g).hom ≫ ·)
        (podCompletedCoefficientMap_eq l E g).symm).trans
          ((IsIso.inv_hom_id _).trans (IsIso.inv_hom_id _).symm)
    let c : F ≅ inverseImageIntegralModules l E g := by
      apply SheafOfModules.pushforwardCongr
      exact hc
    let a : coefficientSequenceRestriction l E Y ⋙
        ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F) ≅
        G ⋙ coefficientSequenceRestriction l E X :=
      isoWhiskerLeft (coefficientSequenceRestriction l E Y)
        ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso c) ≪≫ integralTowerInverseImageUnit l E g
    let T_Y := (coefficientSequenceRestriction l E Y).mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.complexOfFunctorsToFunctorToComplex
    let T_X := (coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.complexOfFunctorsToFunctorToComplex
    let GC := G.mapHomologicalComplex (.up ℤ)
    let RY := integralOperationsRoosFunctor (A := scalarReductionSource l E Y)
    let RX := integralOperationsRoosFunctor (A := scalarReductionSource l E X)
    let r : RY ⋙ isoReductionIntegralComplex l E g ≅
        podReindexTower l E g ⋙ RX :=
      NatIso.ofComponents S.roos (by
        intro C C' f
        exact hS.2.2.1 C C' f)
    let ac' : T_Y ⋙ podReindexTower l E g ≅ GC ⋙ T_X :=
      coreComplexTowerSquare (coefficientSequenceRestriction l E Y)
        (coefficientSequenceRestriction l E X) F G a
    let ηY : DerivedCategory.Q ⋙ coefficientSequenceLimit l E Y ≅
        T_Y ⋙ RY ⋙ DerivedCategory.Q :=
      isoWhiskerRight (coefficientSequenceRestriction l E Y).mapDerivedCategoryFactors
          (coefficientConstantTowerLimit l E Y) ≪≫
        isoWhiskerLeft ((coefficientSequenceRestriction l E Y).mapHomologicalComplex (.up ℤ))
          ρY.comparison
    let ηX : DerivedCategory.Q ⋙ coefficientSequenceLimit l E X ≅
        T_X ⋙ RX ⋙ DerivedCategory.Q :=
      isoWhiskerRight (coefficientSequenceRestriction l E X).mapDerivedCategoryFactors
          (coefficientConstantTowerLimit l E X) ≪≫
        isoWhiskerLeft ((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ))
          ρX.comparison
    let η : DerivedCategory.Q ⋙ (coefficientSequenceLimit l E Y ⋙
        podOrdinaryReindex l E g) ≅ DerivedCategory.Q ⋙
        (integralComparisonDerivedSequencePullback l E g ⋙ coefficientSequenceLimit l E X) :=
      isoWhiskerRight ηY (podOrdinaryReindex l E g) ≪≫
        isoWhiskerLeft (T_Y ⋙ RY) F.mapDerivedCategoryFactors ≪≫
        isoWhiskerLeft T_Y (isoWhiskerRight r DerivedCategory.Q) ≪≫
        isoWhiskerRight ac' (RX ⋙ DerivedCategory.Q) ≪≫
        isoWhiskerLeft GC ηX.symm ≪≫
        isoWhiskerRight G.mapDerivedCategoryFactors.symm (coefficientSequenceLimit l E X)
    exact Localization.liftNatIso DerivedCategory.Q
      (HomologicalComplex.quasiIso (coefficientSequenceModules l E Y) (.up ℤ))
      _ _ _ _ η
  obtain ⟨reduction, _⟩ := adjointSquare (podOrdinaryReindex l E g)
    (integralComparisonDerivedSequencePullback l E g)
    (podReindexCalculus l E Y).adjunction (podReindexCalculus l E X).adjunction limit
  obtain ⟨pullback⟩ := primitiveQuotientPullbackModelExistence l E g
    (fun x ↦ isUnit_of_invertible _) (fun y ↦ isUnit_of_invertible _)
    (podReindexCalculus l E Y) ρX
  exact ⟨⟨reduction.symm, limit, evaluation, restriction, finite, ρY, ρX,
    pullback.realization⟩⟩

end WeilConjectures
