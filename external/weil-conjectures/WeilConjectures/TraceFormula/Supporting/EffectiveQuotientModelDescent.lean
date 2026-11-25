/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.TraceFormula.Supporting.RoosAdjunctionQuotientNormalization
public import WeilConjectures.TraceFormula.Primitive.PrimitiveQuotientRealizationComparisons
public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import all WeilConjectures.TraceFormula.Isomorphism.IsomorphismDerivedPullbackComparisonNormalization
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
import WeilConjectures.Algebra.Homology.System.SystemScalarCoherence
import WeilConjectures.TraceFormula.Supporting.TransportedReductionSystemsNormalized
import WeilConjectures.TraceFormula.Primitive.PrimitiveQuotientRealizationsUnique
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import WeilConjectures.SixFunctors.Integral.IntegralOperationsPreserveConstructible
import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructibleIntrinsic
import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined

/-! # Effectivity and simultaneous descent of quotient realization models

Source: Stacks Project, sites-cohomology.tex, Tags 0941 and 06YS; current blueprint,
sec-trace-formula/sk-thm-tf-uniform-formula, integral transport paragraph.
(blueprint: lem-trf-effective-quotient-model-descent).

The ambient assertions keep independent site and coefficient universes. In the
constructibility assertion, u is a common bound for schemes and coefficient fields,
as in the recorded intrinsic constructibility predicate. The small site still has
objects in Type (u+1) and morphisms in Type u. Level n means exponent n+1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

attribute [local irreducible] WeilConjectures.integralComparisonSequenceScalarModel
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory
  HasDerivedCategory.standard CategoryTheory.constantSheaf
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  WeilConjectures.coefficientSequenceLimit
  WeilConjectures.integralOperationsRoosFunctor WeilConjectures.integralOperationsGoodLocalization
  WeilConjectures.sfIntegralConstructible

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Ambient normalization, actual reconstruction maps, and primitive normalized models.
Source: Stacks 0941, 06YS, 07A4 and 099N; integral transport in the current blueprint
(blueprint: lem-trf-effective-quotient-model-descent).
Proof:
1. The evaluation calculus makes every reduction normalized. Exact whole-system
   inverse image preserves its transition adjoints by
   lem-pur-system-normalized-tensor-closure and prop-weil-pbc-proetale-constant-exact.
2. lem-pur-coefficient-extension-reduction-model identifies scalar change of that
   same strict reduction diagram with its normalized scalar quotient model. Balanced
   association commutes with every quotient map, even for ramified extensions.
3. Apply lem-pur-normalized-actual-reconstruction-maps to both normalized systems.
   It gives completeness and invertibility of the actual whole-system counits, and
   invertibility of the actual unit for complete inputs, without any bounds.
4. lem-trf-primitive-quotient-realization-comparisons gives the two natural models
   for these very functors and the fixed Roos comparisons. Its normalization tests
   every K-flat presentation, including all strict transitions and tensor generators.
   lem-trf-roos-adjunction-quotient-normalization identifies the counit with the
   K-injective projections and the unit with the zero-shifted quotient augmentation.
   Thus the maps here are the specified adjunction maps, not unrelated isomorphisms. -/
-- STATEMENT-DISPUTED: inherits the universal-presentation normalization obstruction of
-- primitiveQuotientRealizationComparisons; finite derived evaluations do not fix the
-- whole-system presentation isomorphism. See the report and the existing T6 counterexample.
theorem effectiveQuotientModelDescent
    {X Y : Scheme.{t}} (f : X ⟶ Y)
    (_hlX : ∀ x : X, IsUnit (l : X.residueField x))
    (_hlY : ∀ y : Y, IsUnit (l : Y.residueField y))
    (SY : CoefficientDerivedSystemCalculus l E Y)
    (SX : CoefficientDerivedSystemCalculus l E X)
    (SL : CoefficientDerivedSystemCalculus l L Y)
    (ρX : IntegralComparisonRoosModel l E X)
    (ρL : IntegralComparisonRoosModel l L Y) :
    (∀ K : DerivedCategory (scalarReductionSource l E Y),
      IsNormalizedCoefficientSequence l E Y (SY.reduction.obj K) ∧
      IsNormalizedCoefficientSequence l E X
        ((integralComparisonDerivedSequencePullback l E f).obj (SY.reduction.obj K)) ∧
      IsNormalizedCoefficientSequence l L Y
        ((integralComparisonDerivedSequenceScalar l E L ι Y).obj (SY.reduction.obj K)) ∧
      IntegralOnSlice.IsComplete l E X none ((coefficientSequenceLimit l E X).obj
        ((integralComparisonDerivedSequencePullback l E f).obj (SY.reduction.obj K))) ∧
      IntegralOnSlice.IsComplete l L Y none ((coefficientSequenceLimit l L Y).obj
        ((integralComparisonDerivedSequenceScalar l E L ι Y).obj (SY.reduction.obj K))) ∧
      IsIso (SX.adjunction.counit.app
        ((integralComparisonDerivedSequencePullback l E f).obj (SY.reduction.obj K))) ∧
      IsIso (SL.adjunction.counit.app
        ((integralComparisonDerivedSequenceScalar l E L ι Y).obj (SY.reduction.obj K))) ∧
      (IntegralOnSlice.IsComplete l E Y none K → IsIso (SY.adjunction.unit.app K))) ∧
    Nonempty (IntegralComparisonPullbackModel l E f SY ρX) ∧
    Nonempty (IntegralComparisonScalarModel l E L ι Y SY ρL) := by
  obtain ⟨hnp, hns⟩ := transportedReductionSystems_normalized l E L ι f _hlX _hlY SY
  obtain ⟨hp, hs⟩ := primitiveQuotientRealizationComparisons l E L ι f Y
    _hlX _hlY _hlY SY SY ρX ρL
  refine ⟨fun K ↦ ?_, hp, hs⟩
  have hx := (purNormalizedReconstructionOfScheme l E X SX).1 _ (hnp K)
  have hl := (purNormalizedReconstructionOfScheme l L Y SL).1 _ (hns K)
  exact ⟨SY.reduction_normalized K, hnp K, hns K, hx.1, hl.1, hx.2, hl.2,
    (purNormalizedReconstructionOfScheme l E Y SY).2 K⟩

/-- Bounded constructibility, with one interval for all reductions, is retained by
both completed operations and their specified system realizations.
Source: Bhatt--Scholze, Lemmas 6.5.4 and 6.5.9(5); current blueprint integral transport
(blueprint: lem-trf-effective-quotient-model-descent).
Proof: apply lem-pur-integral-operations-preserve-constructible(1) to f and K, and
lem-weil-integral-scalar-extension-constructible to E into L and K. Transport through
alpha and beta from lem-trf-primitive-quotient-realization-comparisons. Completeness,
constructible reductions and their common finite interval are invariant under these
isomorphisms. This gives precisely def-weil-derived-complete-integral-detailed for
both realizations, without any bound on the quotient ring map. -/
theorem effectiveQuotientModelConstructible
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (SY : CoefficientDerivedSystemCalculus l E Y)
    (ρX : IntegralComparisonRoosModel l E X)
    (ρL : IntegralComparisonRoosModel l L Y)
    (α : IntegralComparisonPullbackModel l E f SY ρX)
    (β : IntegralComparisonScalarModel l E L ι Y SY ρL)
    (K : DerivedCategory (scalarReductionSource l E Y))
    (_hK : sfIntegralConstructible l E Y K) :
    sfIntegralConstructible l E X ((integralDerivedPullback l E f).obj K) ∧
    sfIntegralConstructible l L Y ((integralScalarExtensionOfUniverses l E L ι Y).obj K) ∧
    sfIntegralConstructible l E X ((coefficientSequenceLimit l E X).obj
      ((integralComparisonDerivedSequencePullback l E f).obj (SY.reduction.obj K))) ∧
    sfIntegralConstructible l L Y ((coefficientSequenceLimit l L Y).obj
      ((integralComparisonDerivedSequenceScalar l E L ι Y).obj (SY.reduction.obj K))) := by
  have hp := ((integralOperations_preserve_constructible l E f).1 K _hK).1
  have hs : sfIntegralConstructible l L Y
      ((integralScalarExtensionOfUniverses l E L ι Y).obj K) :=
    sfIntegralScalarExtension_constructible (l + 1) l (by omega) E L ι Y K _hK
  exact ⟨hp, hs,
    (sfIntegralConstructible l E X).prop_of_iso (α.realization.app K) hp,
    (sfIntegralConstructible l L Y).prop_of_iso (β.realization.app K) hs⟩

section RoosComparisonUniqueness

-- The computes field uses the defining Roos object, so keep this comparison transparent.
attribute [local semireducible] HasDerivedCategory.standard CategoryTheory.constantSheaf
  completedIntegralCoefficientSheafUnrestricted coefficientSequenceLimit
  integralOperationsRoosFunctor integralOperationsGoodLocalization sfIntegralConstructible

end RoosComparisonUniqueness

universe sa sb sw

section ScalarData
open SheafOfModules
variable {C₀ : Type sa} [Category.{sb} C₀] {J : GrothendieckTopology C₀}
  [J.HasSheafCompose (forget₂ CommRingCat.{sw} RingCat.{sw})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{sw}] [HasSheafify J AddCommGrpCat.{sw}]
  [EssentiallySmall.{sw} C₀]

end ScalarData

end WeilConjectures
