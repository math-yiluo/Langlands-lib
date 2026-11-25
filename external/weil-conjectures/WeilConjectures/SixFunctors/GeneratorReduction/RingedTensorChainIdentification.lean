/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
public import WeilConjectures.PoincareDuality.StrictTensorAugmentation.StrictTensorAugmentationConstruction
import WeilConjectures.PoincareDuality.StrictTensorAugmentation.StrictTensorAugmentationNormalization
import WeilConjectures.PoincareDuality.StrictTensorAugmentation.StrictTensorAugmentation

/-! # The canonical ringed tensor chain is the strict quotient augmentation

Source: the full-coordinate uniqueness of the strict tensor augmentation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.GeneratorReduction
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  completedIntegralCommRingSheafUnrestricted completedIntegralCoefficientSheafUnrestricted
  StrictTensorAugmentation.map
attribute [local implicit_reducible] integralOperationsTensorComplexFunctor
  integralOperationsRoos integralOperationsRoosFunctor
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The supplied ringed tensor chain is determined by its two canonical coordinates.
Source: strict tensor augmentation full-coordinate uniqueness, Stacks 07A4 and 08TC.
Proof: its first canonical clause gives the pure-tensor coordinate in every product
projection, and its second gives the zero shifted coordinate. These are exactly
StrictTensorAugmentation.Normalized. The constructed strict augmentation satisfies
the same clauses. The proved uniqueness theorem identifies the transformations.
(blueprint: lem-sf-ringed-tensor-chain-identification). -/
theorem ringedTensorChain_eq_strictAugmentation
    (ringed : IntegralSystemRealization.RingedModels l E) (X : Scheme.{u}) :
    (ringed.tensor X).chain = StrictTensorAugmentation.map l E X := by
  apply (StrictTensorAugmentation.existsUnique_normalized l E X).unique
  · constructor
    · intro P Q p q n V x y
      exact (ringed.tensor X).canonical.1.1 P Q p q n V x y
    · intro P Q i
      exact (ringed.tensor X).canonical.1.2 P Q i (i - 1) (by omega)
  · exact StrictTensorAugmentation.coordinates l E X

end WeilConjectures.GeneratorReduction
