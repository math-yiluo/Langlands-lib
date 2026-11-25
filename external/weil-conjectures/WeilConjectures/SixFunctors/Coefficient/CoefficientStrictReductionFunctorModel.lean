/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
public import WeilConjectures.SixFunctors.Coefficient.Tensor.CoefficientTensorAssociativityModelData
import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryReductionTensor
import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryQuotientTensorAssociativity

/-! # A functorial strict complex model of normalized coefficient reduction

Source: Stacks 06YS, 06YY, 07A4 and 0941.
(blueprint: lem-coef-strict-reduction-functor-model).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

attribute [local irreducible] DerivedCategory _root_.instCategoryDerivedCategory
  DerivedCategory.Q DerivedCategory.Qh HasDerivedCategory.standard
  CoefficientClosedStructure.tensor
  coefficientIntegralTensorModelIso coefficientSystemTensorModelIso
  CochainComplex.IsKFlatIndependentCoefficients SheafOfModules.IsFlatOnSite

/-- A strict complex presentation, with a binary normalization and ordinary chain
coherence. No associator of either derived closed structure occurs in these data.
Source: Stacks 07A4 and 0941
(blueprint: lem-coef-strict-reduction-functor-model). -/
structure CoefficientStrictReductionFunctorModel
    (R : CoefficientDerivedSystemReduction l E W) where
  /-- The ordinary pullback applied to complexes, before localization. -/
  complexFunctor : CochainComplex (scalarReductionSource l E W) ℤ ⥤
    CochainComplex (coefficientSequenceModules l E W) ℤ
  /-- Its actual universal comparison to the prescribed derived reduction. -/
  comparison : DerivedCategory.Q ⋙ R.reduction ⟶ complexFunctor ⋙ DerivedCategory.Q
  /-- Flat-term K-flat inputs compute reduction. -/
  computes : ∀ (P : CochainComplex (scalarReductionSource l E W) ℤ),
    P.IsKFlatIndependentCoefficients →
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{t+1, t, max u (t+1), max u (t+1)}
      (R := completedIntegralCommRingSheafUnrestricted l E W) (P.X i)) →
    IsIso (comparison.app P)
  /-- Ordinary pullback preserves the chosen resolving class. -/
  preserves : ∀ (P : CochainComplex (scalarReductionSource l E W) ℤ),
    P.IsKFlatIndependentCoefficients →
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{t+1, t, max u (t+1), max u (t+1)}
      (R := completedIntegralCommRingSheafUnrestricted l E W) (P.X i)) →
    CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf l E W) (complexFunctor.obj P)
  /-- The ordinary total tensor comparison, natural before localization. -/
  tensor : coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W) ⋙ complexFunctor ≅
    complexFunctor.prod complexFunctor ⋙
      coefficientTotalTensor.{u, t+1, t}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)
  /-- Reassociation for ordinary complex maps, with the native total associators. -/
  associativity : CoefficientComplexTensorAssociativity
    (Scheme.ProEt.topology W) (completedIntegralCommRingSheafUnrestricted l E W)
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W) complexFunctor tensor
  /-- A single functor and its counit realize the given binary normalization. -/
  normalization : ∀ (P Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients)
    (fP : ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{t+1, t, max u (t+1), max u (t+1)}
      (R := completedIntegralCommRingSheafUnrestricted l E W) (P.X i))
    (fQ : ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{t+1, t, max u (t+1), max u (t+1)}
      (R := completedIntegralCommRingSheafUnrestricted l E W) (Q.X i)),
    CoefficientTensorComparisonSquare R.integralClosed.tensor R.systemClosed.tensor
      R.reduction DerivedCategory.Q
      (coefficientIntegralTensorModelIso l E W R.toCoefficientDerivedSystemTensors
        P Q hP hQ).hom R.reductionTensor.hom
      (comparison.app P) (comparison.app Q) (comparison.app _)
      (tensor.hom.app (P, Q))
      (coefficientSystemTensorModelIso l E W R.toCoefficientDerivedSystemTensors
        (complexFunctor.obj P) (complexFunctor.obj Q)
        (preserves P hP fP) (preserves Q hQ fQ)).hom

/-- The pairwise strict reduction normalization has a functorial complex realization.
This is a binary model assertion; it makes no claim about derived associators.

Source: Stacks, sites-cohomology.tex, Tag 07A4, proof of
`lemma-pullback-tensor-product`, together with the sequence projection of Tag 0941.
(blueprint: lem-coef-strict-reduction-functor-model).

Proof: apply the ordinary sequence projection pullback to each term and differential
and transport the strict scalar systems to modules on the sequence site. Its ordinary
scalar tensor maps assemble naturally over the total coproducts. On a triple summand
both composites insert the scalar unit in each factor and reassociate without a
permutation; sheaf tensor generation and coproduct extensionality give the displayed
ordinary chain equation. Pullback preserves flat-term K-flat complexes. Its universal
left-derived counit, transported to R.reduction by the normalized reduction/limit
adjunction, gives comparison and computes. On a pair of flat-term K-flat inputs,
compare these functorial presentations with those in hR using the normalized ordinary
pullback/limit adjunction. The finite projection equations identify their ordinary
scalar units and transition adjuncts. The strict maps then agree on every local tensor
generator before localization. The last square of hR, transported along these
presentation comparisons, is precisely normalization. This argument takes place in
the strict system category before localization; it does not infer equality of derived
system maps merely from equality of their finite evaluations. The construction also
applies to the zero complex and the empty scheme. -/
theorem coefficientStrictReductionFunctorModel
    (R : CoefficientDerivedSystemReduction l E W)
    (hR : CoefficientReductionTensorNormalization l E W R) :
    Nonempty (CoefficientStrictReductionFunctorModel l E W R) := by
  obtain ⟨M⟩ := OrdinaryQuotient.ordinaryModel_exists l E W
  obtain ⟨b, hb⟩ := OrdinaryQuotient.OrdinaryModel.quotientTensor_exists l E W M
  have hb' : M.TensorEvaluation l E W b := by
    intro n P Q
    have h := hb n P Q
    unfold CoefficientComparisonEquation at h
    exact h
  obtain ⟨ε, -, hcomp, hhom⟩ :=
    OrdinaryQuotient.reductionComparison_exists l E W M R.reduction R.adjunction
  exact ⟨{
    complexFunctor := M.quotient l E W
    comparison := ε
    computes := hcomp
    preserves := OrdinaryQuotient.OrdinaryModel.quotient_isKFlat l E W M
    tensor := b
    associativity := M.quotientTensor_associativity l E W b hb'
    normalization := fun P Q hP hQ fP fQ ↦
      M.reductionTensor_normalization l E W R hR ε hcomp hhom b hb'
        (OrdinaryQuotient.OrdinaryModel.quotient_isKFlat l E W M) P Q hP hQ fP fQ }⟩

end WeilConjectures
