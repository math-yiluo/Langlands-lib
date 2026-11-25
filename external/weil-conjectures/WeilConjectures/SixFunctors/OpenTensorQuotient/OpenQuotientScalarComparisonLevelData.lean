/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenTensorQuotient.OpenTensorQuotientData
import WeilConjectures.SixFunctors.OpenTensorQuotient.OpenQuotientScalarComparisonTransition

/-! # Finite-level data for the strict open scalar comparison

Source: Stacks Project, Tags 0E8I and 0941.
(blueprint: lem-sf-open-quotient-scalar-comparison-level-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenTensorQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- A family of finite-level scalar comparison isomorphisms, with their
component formula and compatibility with every quotient transition.
Source: Stacks Tags 0E8I and 0941; degreewise comparison and transition coherence.
(blueprint: lem-sf-open-quotient-scalar-comparison-level-data). -/
structure ScalarComparisonLevelData
    (o : IntegralOpenReduction.Operations l E j)
    (tc : IntegralOpenReduction.TensorComparison l E j o)
    (sc : ScalarCompatibility l E j o) where
  level : ∀ (n : ℕ) (Q : CochainComplex (scalarReductionSource l E U) ℤ),
    (unrestrictedIntegralComplexFunctor l E X n).obj
        ((OpenSemilinearTensor.extensionComplex l E j o).obj Q) ≅
      (OpenSemilinearTensor.extensionComplex l E j o).obj
        ((unrestrictedIntegralComplexFunctor l E U n).obj Q)
  components : ∀ (n : ℕ) (Q : CochainComplex (scalarReductionSource l E U) ℤ)
    (i : ℤ),
    ((level n Q).hom.f i) =
      (scalarReductionRestriction l E X n).map ((tc.ordinary n).hom.app (Q.X i)) ≫
        (sc.finite n).hom.app ((scalarReductionExtension l E U n).obj (Q.X i))
  transition : ∀ (n : ℕ)
    (Q : CochainComplex (scalarReductionSource l E U) ℤ) (i : ℤ),
    ((unrestrictedIntegralTransition l E X n).app
      ((OpenSemilinearTensor.extensionComplex l E j o).obj Q)).f i ≫
        (level n Q).hom.f i =
      (level (n + 1) Q).hom.f i ≫
        ((OpenSemilinearTensor.extensionComplex l E j o).map
          ((unrestrictedIntegralTransition l E U n).app Q)).f i

/-- The finite-level comparison data can be constructed from the normalized finite
comparison and scalar compatibility maps. The proof is the degreewise generator
calculation followed by transition naturality.
Source: Stacks Tags 0E8I and 0941.
(blueprint: lem-sf-open-quotient-scalar-comparison-level-data). -/
theorem openQuotientScalarComparisonLevelData
    (o : IntegralOpenReduction.Operations l E j)
    (tc : IntegralOpenReduction.TensorComparison l E j o)
    (sc : ScalarCompatibility l E j o) :
    Nonempty (ScalarComparisonLevelData l E j o tc sc) := by
  let level : ∀ (n : ℕ) (Q : CochainComplex (scalarReductionSource l E U) ℤ),
      (unrestrictedIntegralComplexFunctor l E X n).obj
          ((OpenSemilinearTensor.extensionComplex l E j o).obj Q) ≅
        (OpenSemilinearTensor.extensionComplex l E j o).obj
          ((unrestrictedIntegralComplexFunctor l E U n).obj Q) := by
    intro n Q
    let e := Functor.isoWhiskerRight (tc.ordinary n)
        (scalarReductionRestriction l E X n) ≪≫
      Functor.isoWhiskerLeft (scalarReductionExtension l E U n) (sc.finite n)
    exact (NatIso.mapHomologicalComplex e (.up ℤ)).app Q
  refine ⟨{ level := level, components := ?_, transition := ?_ }⟩
  · intro n Q i
    rfl
  · intro n Q i
    exact openQuotientScalarComparisonTransition l E j o tc sc level
      (fun n Q i ↦ by rfl) n Q i

end WeilConjectures.OpenTensorQuotient
