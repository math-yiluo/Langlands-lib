/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CanonicalCoefficient.CanonicalCoefficientReduction

/-! # Representative laws after changing closed tensor presentations

Source: Stacks 07A4 and 0941; cancellation in the simultaneous representative squares.
(blueprint: lem-pur-canonical-coefficient-representative-laws).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.CanonicalCoefficient
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- Only the representative normalization equations for the explicit conjugated data.
No fiber-Hom, internal composition, global sections or enriched assertion occurs here. -/
structure RepresentativeLaws (S : CoefficientDerivedSystemFibers l E W) : Prop where
  reduction_tensor : CoefficientReductionTensorNormalization l E W
    (reduction l E W S.toCoefficientDerivedSystemReduction)
  finite_tensor : CoefficientFiniteTensorNormalization l E W
    (reduction l E W S.toCoefficientDerivedSystemReduction)
  evaluation_tensor : CoefficientEvaluationTensorNormalization l E W
    (reduction l E W S.toCoefficientDerivedSystemReduction)
  reduction_evaluation : CoefficientReductionTensorEvaluation l E W
    (reduction l E W S.toCoefficientDerivedSystemReduction)
  quotient_tensor : CoefficientFiniteQuotientTensorNormalization l E W
    (tensors l E W S.toCoefficientDerivedSystemTensors)
    (quotientData l E W S.toCoefficientDerivedSystemTensors
      S.quotientCalculus.toCoefficientFiniteQuotientData)

/-- Conjugating the comparisons keeps their ordinary strict representative normalizations.

Source: Stacks 07A4, 0941; canonical integral calculus, proof step 2.
(blueprint: lem-pur-canonical-coefficient-representative-laws).

Proof: every new tensor-model comparison is the old one followed by the adjoint
comparison. In a representative square substitute F(a inverse); mu; b for mu.
Functoriality cancels a with its inverse. Naturality of b moves it past the two
representative identifications; the remaining equation is precisely the old square,
postcomposed with b. This is tensorSquare, for finite scalar extension, evaluation,
quotient extension, and the simultaneous strict reduction map. Retain all the old
strict complexes, quotient identifications, chain maps and pure-tensor equations.
For reduction_evaluation, expand the three conjugations; naturality at the two
reduction evaluations and cancellation of the sequence comparison identify the
new equation with the old one, conjugated at its source and target. These are
identities in the actual derived sequence category, not deductions from equality
of evaluations. The argument needs neither boundedness nor nonempty sites. -/
theorem representativeLaws (S : CoefficientDerivedSystemFibers l E W) :
    RepresentativeLaws l E W S := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro P Q hP hQ hPf hQf
    obtain ⟨C, D, Z, hC, hD, eC, eD, eZ, κC, κD, κZ, ψ,
      hPC, hQD, hTZ, hψ, hSq⟩ :=
      S.reductionTensor_normalization P Q hP hQ hPf hQf
    refine ⟨C, D, Z, hC, hD, eC, eD, eZ, κC, κD, κZ, ψ, hPC, hQD, hTZ, hψ, ?_⟩
    dsimp only [reduction]
    exact tensorSquare _ _ _ _ _ _ _ _ _ _ _ _ _ hSq
  · intro n P Q hP hQ
    dsimp only [reduction]
    exact tensorSquare _ _ _ _ _ _ _ _ _ _ _ _ _
      (S.finiteTensor_normalization n P Q hP hQ)
  · intro n P Q hP hQ
    dsimp only [reduction]
    exact tensorSquare _ _ _ _ _ _ _ _ _ _ _ _ _
      (S.evaluationTensor_normalization n P Q hP hQ)
  · intro P Q n
    exact evaluation_transport _ _ _ _ _ _ _ _ _ _ _ _ _ P Q
      (S.reductionTensor_evaluation P Q n)
  · intro m n h P Q hP hQ
    obtain ⟨e, he, hSq⟩ := S.quotientCalculus.tensor_model h P Q hP hQ
    refine ⟨e, he, ?_⟩
    exact tensorSquare _ _ _ _ _ _ _ _ _ _ _ _ _ hSq

end WeilConjectures.CanonicalCoefficient
