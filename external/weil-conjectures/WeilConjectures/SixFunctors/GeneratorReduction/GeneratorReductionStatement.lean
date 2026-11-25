/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.GeneratorReduction.GeneratorReductionData
public import WeilConjectures.SixFunctors.GeneratorReduction.ShortWordCompletionIsomorphism
import WeilConjectures.SixFunctors.GeneratorReduction.ShortWordIntegralDomain
import WeilConjectures.SixFunctors.GeneratorReduction.PrimitiveQuotientAugmentations
import WeilConjectures.SixFunctors.GeneratorReduction.OpenReconstructionEffectivity
import WeilConjectures.SixFunctors.GeneratorReduction.GeneratorKind.TensorAdjunctionReductionSquares
import WeilConjectures.SixFunctors.OpenInterchangeReduction.OpenInterchangeReductionData
import WeilConjectures.SixFunctors.OpenInterchangeReduction.OpenBaseChangeReductionSquare
import WeilConjectures.SixFunctors.OpenInterchangeReduction.OpenTensorReductionSquare
/-! # Canonical coefficient squares for the basic six-functor generators

Source: blueprint fix-prop-coherence, basic structural maps
(blueprint: lem-sf-generator-reduction-coherence).
-/

@[expose] public noncomputable section

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u s i v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace WeilConjectures.GeneratorReduction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {S : Type s} (W : S → Scheme.{u}) {I : Type i} (location : I → S)

private theorem inverseOrZero_eq_inv {A : Type v} [Category.{w} A] [HasZeroMorphisms A]
    {X Y : A} (f : X ⟶ Y) [IsIso f] : inverseOrZero f = inv f := by
  simp only [inverseOrZero, dite_eq_left (inferInstance : IsIso f)]

end WeilConjectures.GeneratorReduction
