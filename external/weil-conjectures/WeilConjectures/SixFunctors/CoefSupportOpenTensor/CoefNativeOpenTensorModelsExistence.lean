/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefSupportOpenTensor.CoefOpenTensorEvaluationData
import WeilConjectures.SixFunctors.CoefSupportOpenTensor.CoefNativeOpenTensorGammaEvaluation
import WeilConjectures.SixFunctors.CoefSupportOpenTensor.CoefNativeOpenTensorModelsDataExistence

/-! # Native normalized open tensor models and evaluation

Source: Stacks 0E8I, 0GL1 and 07A4
(blueprint: lem-coef-native-open-tensor-models-existence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CoefSupportOpenTensor

attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian
  SemilinearSections.abelianSheafify SemilinearSections.locallyBijective
  SemilinearSections.sequenceSmall SemilinearSections.sliceSmall

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Native open tensor models exist at the sequence and finite levels, and the
prescribed finite evaluation comparisons identify their gamma transformations.
Source: Stacks, sites-modules.tex, lemma-j-shriek-and-tensor (Tag 0E8I);
sites-cohomology.tex, lemma-j-shriek-and-tensor (Tag 0GL1) and
lemma-pullback-tensor-product (Tag 07A4); support-open-tensor steps 5--6.
(blueprint: lem-coef-native-open-tensor-models-existence).

Proof: construct the restriction tensor comparison on ordinary module sheaves
by the pure-tensor map x tensor y to their restrictions. The inverse open
comparison is the adjoint transpose of the open unit followed by the inverse
restriction comparison. Stacks 0E8I makes this an isomorphism. Totalize its
summands using coproduct preservation by open extension. Naturality in the two
differentials proves the chain equation, including the sign (-1)^a. Use a
flat-term K-flat resolution of the second factor. A K-flat refinement of the
arbitrary first factor and the acyclic-cone criterion identify this total tensor
with the prescribed derived tensors; tensor descent gives the ambient and open
one-flat-factor comparisons, their naturality, and the derived_model equation.
The inverse transpose fixes gamma_inverse. Do the same construction over each
finite coefficient ring. The given calculus pins its evaluationTensor to the
same ordinary pure-tensor maps. Exact evaluation preserves the ordinary open
unit, restriction comparison and every total summand; it preserves the K-flat
representatives by the vertical pullback theorem. Consequently the two sides of
GammaEvaluation are the same chain map on homogeneous generators. Bilinearity,
sheafification, coproduct uniqueness and tensor descent prove their equality on
all derived objects. All horizontal quotient restrictions commute with these
module maps; no flatness of a quotient map or boundedness is required. -/
theorem nativeOpenTensorModels_exists {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (SX : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (SZ : CoefficientDerivedSystemCalculus.{u, u} l E Z) :
    ∃ (O : SystemOpenModel l E j SX.toCoefficientDerivedSystemTensors
        SZ.toCoefficientDerivedSystemTensors)
      (On : ∀ n : ℕ, FiniteOpenModel l E j SX.toCoefficientDerivedSystemTensors
        SZ.toCoefficientDerivedSystemTensors n),
      GammaEvaluation l E j SX SZ O On := by
  obtain ⟨O, On, _⟩ := nativeOpenTensorModels_data_exists l E j SX SZ
  exact ⟨O, On, nativeOpenTensorGammaEvaluation l E j SX SZ O On⟩

end WeilConjectures.CoefSupportOpenTensor
