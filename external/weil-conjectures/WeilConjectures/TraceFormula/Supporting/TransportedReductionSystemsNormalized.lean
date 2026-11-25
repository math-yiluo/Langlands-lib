/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems

import WeilConjectures.TraceFormula.Supporting.TransportedReductionPullbackNormalized
import WeilConjectures.TraceFormula.Supporting.TransportedReductionScalarNormalized

/-! # Normalization of the two transported reduction systems

Source: Stacks 07A4, 06YY and 0941; steps 1--2 of
lem-trf-effective-quotient-model-descent.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Exact inverse image and ramified coefficient change preserve normalization of
an ambient object's strict derived reduction system.
Source: Stacks, sites-cohomology.tex, Tags 07A4 and 06YY; the integral transport
paragraph of the current blueprint, and steps 1--2 of the parent node.
(blueprint: lem-trf-transported-reduction-systems-normalized).

Proof: SY.reduction_normalized gives the universal tensor/restriction property
for each transition of the input reduction system. Apply
SemilinearSections.normalized_inverseImage_closure to the pro-etale inverse
image. Identify its pulled coefficient rings with the target constant quotient
rings by coefficientProEtaleModulePullback_exact and the constant-coefficient
comparison. The adjunction defining integralComparisonSequencePullback identifies
this geometric inverse image with the specified whole-system pullback. Its
transition-adjoint square is precisely the square in normalized_inverseImage_closure,
so every pulled transition adjunct is invertible. For scalar change choose the
semilinear coefficient-extension package from semilinearDerivedSections and apply
coefficientExtensionReductionModel, whose normalized field supplies normalization
of its coherent scalar system. Both that scalar functor and the one specified by
integralComparisonSequenceScalarModel derive change of rings for the identical
map of sequence coefficient sheaves. Identify their universal pairs by the unique
counit-compatible comparison; the finite evaluations and transition adjunctions
commute with this comparison. Transport normalization through it. This construction
uses balanced association of actual quotient tensors; it does not assume the
quotient-ring inclusions flat or of finite Tor dimension. Identity transitions,
exponent one, equal coefficient fields, empty schemes and zero inputs obey these
same adjunction and tensor equations. -/
theorem transportedReductionSystems_normalized
    {X Y : Scheme.{t}} (f : X ⟶ Y)
    (_hlX : ∀ x : X, IsUnit (l : X.residueField x))
    (_hlY : ∀ y : Y, IsUnit (l : Y.residueField y))
    (SY : CoefficientDerivedSystemCalculus l E Y) :
    (∀ K : DerivedCategory (scalarReductionSource l E Y),
      IsNormalizedCoefficientSequence l E X
        ((integralComparisonDerivedSequencePullback l E f).obj (SY.reduction.obj K))) ∧
    (∀ K : DerivedCategory (scalarReductionSource l E Y),
      IsNormalizedCoefficientSequence l L Y
        ((integralComparisonDerivedSequenceScalar l E L ι Y).obj (SY.reduction.obj K))) := by
  exact ⟨transportedReductionSystems_pullback_normalized l E f _hlX _hlY SY,
    transportedReductionSystems_scalar_normalized l E L ι _hlY SY⟩

end WeilConjectures
