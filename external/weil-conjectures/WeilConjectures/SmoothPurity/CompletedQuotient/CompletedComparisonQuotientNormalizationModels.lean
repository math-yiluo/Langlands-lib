/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonQuotientRealizationDefs
import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedQuotientReductionPresentation
import all WeilConjectures.SmoothPurity.StrictQuotient.QuotientExpressionStrictKFlatTowers
import WeilConjectures.SmoothPurity.StrictQuotient.QuotientExpressionKFlatOperations
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison

/-! # Good quotient expression models and invertible substitutions

Source: Stacks 07A2, 0G7E and 0941. This is the already-proved model part of
completed quotient normalization, separated from its naturality calculation.
(blueprint: lem-pur-completed-comparison-quotient-models).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.SemilinearSections.abelianSheafify
attribute [-instance] WeilConjectures.SemilinearSections.locallyBijective
attribute [-instance] WeilConjectures.finiteSystemSequenceSmall
attribute [-instance] AlgebraicGeometry.ProEtale.VaryingRing.sequenceSiteSmall
attribute [instance 4000] SheafOfModules.monoidalCategory
attribute [instance 4000] HomologicalComplex.monoidalCategory

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open MonoidalCategory
namespace WeilConjectures.CompletedQuotient
universe u

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] pullbackTensorCalculus pullbackTensorIntegralTensorModel
  pullbackTensorIntegralPullbackModel pullbackTensorReductionModel
  tensorSubstitution comparison pullBridge pullSubstitution
  substitution transport scalarSubstitution scalarBeta scalarTransport
  scalarLeft scalarRight ScalarIdentity ScalarComposition ScalarAssociation NaturalSubstitution
  ScalarGood StrictCoherence ScalarLimitImage reduction scalarQuotients
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local implicit_reducible] pullbackTensorReferenceTensor
  pullbackTensorReferencePullback integralOperationsGoodLocalization
  value expression IntegralCoherence.value coefficientSequenceInternalHom Pi.eval
attribute [local implicit_reducible] substituteInputs strictMap

private theorem quotient_good {Y : Scheme.{u}}
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    StrictQuotient.SystemGood l E (quotient l E P.obj) := by
  apply (StrictQuotient.levelwiseFlatModels l E Y _).1
  intro n
  let e := ((pullbackTensorReductionEvaluationComplex l E Y n).app P.obj).symm
  constructor
  · exact SheafOfModules.kFlat_iso_independent
      (integralCoefficientCommRingSheaf l E Y n) e.symm
      ((coefficientTensorModelPreservation l E Y).1 P.obj P.property.1 n)
  · intro k
    exact SheafOfModules.flatOnSite_of_iso (integralCoefficientCommRingSheaf l E Y n)
      ((HomologicalComplex.eval _ _ k).mapIso e).symm
      (StrictQuotient.reduction_flat l E Y P.obj P.property.1 P.property.2 n k)

private theorem expressions_good {Z X Y : Scheme.{u}} (h : Z ⟶ X) (f : X ⟶ Y)
    (P : Fin 3 → (integralOperationsGoodComplex l E Y).FullSubcategory) :
    GoodExpressions l E h f P := by
  intro W A
  induction A with
  | input i => exact quotient_good l E (P i)
  | unitY => exact StrictQuotient.unit_system_good l E Y
  | unitX => exact StrictQuotient.unit_system_good l E X
  | unitZ => exact StrictQuotient.unit_system_good l E Z
  | tensor A B hA hB => exact StrictQuotient.tensor_system_good l E _ _ hA hB
  | pullF A hA => exact StrictQuotient.pull_system_good l E f _ hA
  | pullH A hA => exact StrictQuotient.pull_system_good l E h _ hA
  | pullHF A hA => exact StrictQuotient.pull_system_good l E (h ≫ f) _ hA

private theorem expressions_generated {Z X Y : Scheme.{u}} (h : Z ⟶ X) (f : X ⟶ Y)
    (N : Fin 3 → StrictQuotient.Complex l E Y) {W : Scheme.{u}}
    (A : StrictQuotient.Expression h f 3 W) :
    StrictQuotient.Generated l E h f N W (strictValue l E N A) := by
  induction A with
  | input i => exact .input i
  | unitY => exact .unitY
  | unitX => exact .unitX
  | unitZ => exact .unitZ
  | tensor A B hA hB => exact .tensor hA hB
  | pullF A hA => exact .pullF hA
  | pullH A hA => exact .pullH hA
  | pullHF A hA => exact .pullHF hA

private theorem generated_good {Z X Y : Scheme.{u}} (h : Z ⟶ X) (f : X ⟶ Y)
    (P : Fin 3 → (integralOperationsGoodComplex l E Y).FullSubcategory)
    (W : Scheme.{u}) (K : StrictQuotient.Complex l E W)
    (hK : StrictQuotient.Generated l E h f (fun i ↦ quotient l E (P i).obj) W K) :
    ∀ n, StrictQuotient.Good l E K n := by
  apply (StrictQuotient.levelwiseFlatModels l E W K).2
  induction hK with
  | input i => exact quotient_good l E (P i)
  | unitY => exact StrictQuotient.unit_system_good l E Y
  | unitX => exact StrictQuotient.unit_system_good l E X
  | unitZ => exact StrictQuotient.unit_system_good l E Z
  | tensor hA hB hA' hB' => exact StrictQuotient.tensor_system_good l E _ _ hA' hB'
  | pullF hA hA' => exact StrictQuotient.pull_system_good l E f _ hA'
  | pullH hA hA' => exact StrictQuotient.pull_system_good l E h _ hA'
  | pullHF hA hA' => exact StrictQuotient.pull_system_good l E (h ≫ f) _ hA'

private theorem expressions_normalized {Z X Y : Scheme.{u}} (h : Z ⟶ X) (f : X ⟶ Y)
    (P : Fin 3 → (integralOperationsGoodComplex l E Y).FullSubcategory)
    (hpres : ∀ i : Fin 3, CoefficientReductionPresentation l E Y
      (pullbackTensorCalculus l E Y).toCoefficientDerivedSystemReduction
      (P i).obj (P i).property.1 (quotient l E (P i).obj)
      ((pullbackTensorReductionModel l E Y).app (P i))
      (fun n ↦ ((pullbackTensorReductionEvaluationComplex l E Y n).app (P i).obj).symm))
    {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W) :
    IsNormalizedCoefficientSequence l E W
      (DerivedCategory.Q.obj (strictValue l E (fun i ↦ quotient l E (P i).obj) A)) := by
  let N := fun i ↦ quotient l E (P i).obj
  let κ := fun i n ↦ ((pullbackTensorReductionEvaluationComplex l E Y n).app (P i).obj).symm
  have hκ : ∀ (i : Fin 3) {m n : ℕ} (hmn : n ≤ m),
      StrictQuotient.transition l E (N i) hmn ≫
          ((normalizedDVRModuleRes l E Y hmn).mapHomologicalComplex (.up ℤ)).map
            (κ i n).hom =
        (κ i m).hom ≫ (NatTrans.mapHomologicalComplex
          (coefficientOrdinaryQuotient l E Y hmn) (.up ℤ)).app (P i).obj := by
    intro i m n hmn
    exact (hpres i).2 m n hmn
  intro m n
  exact ((StrictQuotient.quotientExpressionKFlatOperations l E h f 3 N
    (fun i ↦ (P i).obj) κ hκ (generated_good l E h f P)).1 W _
      (expressions_generated l E h f N A)).1

private theorem counit_iso {W : Scheme.{u}} (A : coefficientSequenceDerived l E W)
    (hA : IsNormalizedCoefficientSequence l E W A) :
    IsIso ((pullbackTensorCalculus l E W).adjunction.counit.app A) :=
  ((purNormalizedReconstructionOfScheme l E W (pullbackTensorCalculus l E W)).1 A hA).2

private theorem reduction_iso {W : Scheme.{u}}
    {K : DerivedCategory (scalarReductionSource l E W)}
    {A : coefficientSequenceDerived l E W}
    (β : K ⟶ (coefficientSequenceLimit l E W).obj A)
    [IsIso β] (hA : IsNormalizedCoefficientSequence l E W A) :
    IsIso (reduction l E β) := by
  have := counit_iso l E A hA
  unfold reduction
  infer_instance

private theorem tensor_substitution_iso {W : Scheme.{u}}
    {K H : DerivedCategory (scalarReductionSource l E W)}
    (A B : StrictQuotient.Complex l E W)
    (hA : StrictQuotient.SystemGood l E A) (hB : StrictQuotient.SystemGood l E B)
    (βA : K ⟶ (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj A))
    (βB : H ⟶ (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj B))
    [IsIso βA] [IsIso βB]
    (hnA : IsNormalizedCoefficientSequence l E W (DerivedCategory.Q.obj A))
    (hnB : IsNormalizedCoefficientSequence l E W (DerivedCategory.Q.obj B)) :
    IsIso (tensorSubstitution l E A B hA hB βA βB) := by
  have := reduction_iso l E βA hnA
  have := reduction_iso l E βB hnB
  have : IsIso (Prod.mkHom (reduction l E βA) (reduction l E βB)) :=
    (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  unfold tensorSubstitution
  infer_instance

private theorem pull_substitution_iso {V W : Scheme.{u}} (g : V ⟶ W)
    {K : DerivedCategory (scalarReductionSource l E W)}
    (A : StrictQuotient.Complex l E W)
    (β : K ⟶ (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj A))
    [IsIso β] (hnA : IsNormalizedCoefficientSequence l E W (DerivedCategory.Q.obj A)) :
    IsIso (pullSubstitution l E g A β) := by
  have := reduction_iso l E β hnA
  let e := ((pullbackTensorIntegralPullbackModel l E g).app K) ≪≫
    (coefficientSequenceLimit l E V).mapIso
      ((pullbackTensorSequenceDerived l E g).mapIso (asIso (reduction l E β))) ≪≫
    (coefficientSequenceLimit l E V).mapIso
      (((pullbackTensorSequenceInverse l E g).mapDerivedCategoryFactors.app A) ≪≫
        DerivedCategory.Q.mapIso ((pullBridge l E g).app A))
  unfold pullSubstitution
  change IsIso e.hom
  infer_instance

private theorem substitute_inputs_iso {Z X Y : Scheme.{u}} {h : Z ⟶ X} {f : X ⟶ Y}
    (N : Fin 3 → StrictQuotient.Complex l E Y)
    (M : Fin 3 → DerivedCategory (scalarReductionSource l E Y))
    (β : ∀ i : Fin 3, M i ⟶ (coefficientSequenceLimit l E Y).obj
      (DerivedCategory.Q.obj (N i)))
    (good : ∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W),
      StrictQuotient.SystemGood l E (strictValue l E N A))
    (hn : ∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W),
      IsNormalizedCoefficientSequence l E W (DerivedCategory.Q.obj (strictValue l E N A)))
    (hβ : ∀ i, IsIso (β i))
    {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W) :
    IsIso (substituteInputs l E N M β good A) := by
  induction A with
  | input i => simpa only [substituteInputs, value, strictValue, expression,
      IntegralCoherence.value, Pi.eval_obj] using hβ i
  | unitY =>
      dsimp only [value, strictValue, expression, IntegralCoherence.value, substituteInputs]
      infer_instance
  | unitX =>
      dsimp only [value, strictValue, expression, IntegralCoherence.value, substituteInputs]
      infer_instance
  | unitZ =>
      dsimp only [value, strictValue, expression, IntegralCoherence.value, substituteInputs]
      infer_instance
  | tensor A B hA hB =>
      dsimp only [value, strictValue, expression, IntegralCoherence.value, substituteInputs]
      have := hA
      have := hB
      exact tensor_substitution_iso l E _ _ (good A) (good B) _ _ (hn A) (hn B)
  | pullF A hA =>
      dsimp only [value, strictValue, expression, IntegralCoherence.value, substituteInputs]
      have := hA
      exact pull_substitution_iso l E f _ _ (hn A)
  | pullH A hA =>
      dsimp only [value, strictValue, expression, IntegralCoherence.value, substituteInputs]
      have := hA
      exact pull_substitution_iso l E h _ _ (hn A)
  | pullHF A hA =>
      dsimp only [value, strictValue, expression, IntegralCoherence.value, substituteInputs]
      have := hA
      exact pull_substitution_iso l E (h ≫ f) _ _ (hn A)

private theorem constructible_complete {Y : Scheme.{u}}
    (M : sfIntegralConstructibleCategory l E Y) :
    IntegralOnSlice.IsComplete l E Y none M.obj := by
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hprime⟩
  let D : FiniteFieldDatum.{0} := {
    p := p, a := 1, q := p, prime := hprime, exponent_pos := le_refl 1,
    cardinality_eq := by simp, k₀ := ZMod p,
    card_base := by simp [Nat.card_eq_fintype_card], k := AlgebraicClosure (ZMod p) }
  have hl : l ≠ D.p := by change l ≠ p; omega
  exact ⟨D, hl, (sfDerivedComplete_iff_legacy l E Y D hl M.obj).mp M.property.1⟩

private theorem substitution_iso {Z X Y : Scheme.{u}} {h : Z ⟶ X} {f : X ⟶ Y}
    (M : Fin 3 → sfIntegralConstructibleCategory l E Y)
    (P : Fin 3 → (integralOperationsGoodComplex l E Y).FullSubcategory)
    (φ : ∀ i : Fin 3, DerivedCategory.Q.obj (P i).obj ≅ (M i).obj)
    (good : GoodExpressions l E h f P)
    (hn : ∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W),
      IsNormalizedCoefficientSequence l E W
        (DerivedCategory.Q.obj (strictValue l E (fun i ↦ quotient l E (P i).obj) A)))
    {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W) :
    IsIso (substitution l E P (fun i ↦ (M i).obj) φ good A) := by
  unfold substitution
  apply substitute_inputs_iso l E _ _ _ good hn
  intro i
  have := (purNormalizedReconstructionOfScheme l E Y (pullbackTensorCalculus l E Y)).2
    (M i).obj (constructible_complete l E (M i))
  exact ((asIso ((pullbackTensorCalculus l E Y).adjunction.unit.app (M i).obj)) ≪≫
    (coefficientSequenceLimit l E Y).mapIso
      ((pullbackTensorCalculus l E Y).reduction.mapIso (φ i).symm ≪≫
        (pullbackTensorReductionModel l E Y).app (P i))).isIso_hom

/-- The normalized quotient models and all their recursive substitutions are good.
Source: Stacks 07A2, 0G7E and 0941
(blueprint: lem-pur-completed-comparison-quotient-models).
Proof: reduce the prescribed flat-term K-flat representatives levelwise. Induct
on the expression constructors using tensor and inverse-image preservation.
Derived completeness gives the leaf reconstruction isomorphisms, and normalized
effective counits give the tensor and pullback substitutions. The original
reduction presentation theorem identifies the resulting finite levels. -/
theorem completedComparisonQuotientModels
    {Z X Y : Scheme.{u}} (h : Z ⟶ X) (f : X ⟶ Y)
    [∀ z : Z, Invertible (l : Z.residueField z)]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (M : Fin 3 → sfIntegralConstructibleCategory l E Y)
    (P : Fin 3 → (integralOperationsGoodComplex l E Y).FullSubcategory)
    (φ : ∀ i : Fin 3, DerivedCategory.Q.obj (P i).obj ≅ (M i).obj)
    :
    ∃ (good : GoodExpressions l E h f P)
      (_invertible : ∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W),
        IsIso (substitution l E P (fun i ↦ (M i).obj) φ good A)),
    (∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W),
      (∀ n : ℕ, StrictQuotient.Good l E
        (strictValue l E (fun i ↦ quotient l E (P i).obj) A) n) ∧
      IsNormalizedCoefficientSequence l E W
        (DerivedCategory.Q.obj (strictValue l E (fun i ↦ quotient l E (P i).obj) A)) ∧
      IsIso (reduction l E (substitution l E P (fun i ↦ (M i).obj) φ good A))) ∧
    (∀ i : Fin 3, CoefficientReductionPresentation l E Y
      (pullbackTensorCalculus l E Y).toCoefficientDerivedSystemReduction
      (P i).obj (P i).property.1 (quotient l E (P i).obj)
      ((pullbackTensorReductionModel l E Y).app (P i))
      (fun n ↦ ((pullbackTensorReductionEvaluationComplex l E Y n).app (P i).obj).symm)) := by
  let good : GoodExpressions l E h f P := expressions_good l E h f P
  have hpres := fun i : Fin 3 ↦ completedQuotientReductionPresentation l E Y (P i)
  have hn : ∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W),
      IsNormalizedCoefficientSequence l E W
        (DerivedCategory.Q.obj (strictValue l E (fun i ↦ quotient l E (P i).obj) A)) :=
    fun A ↦ expressions_normalized l E h f P hpres A
  have hb : ∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W),
      IsIso (substitution l E P (fun i ↦ (M i).obj) φ good A) :=
    fun A ↦ substitution_iso l E M P φ good hn A
  refine ⟨good, hb, ?_, hpres⟩
  intro W A
  have := hb A
  exact ⟨(StrictQuotient.levelwiseFlatModels l E W _).2 (good A),
    hn A, reduction_iso l E _ (hn A)⟩

end WeilConjectures.CompletedQuotient
