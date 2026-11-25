/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.OpenInterchangeReduction.OpenInterchangeReductionData
import all WeilConjectures.SixFunctors.GeneratorReduction.GeneratorKind.TensorAdjunctionReductionSquares
import WeilConjectures.SixFunctors.GeneratorReduction.GeneratorReductionData

/-! # The coefficient square for cartesian open base change
Source: the open-adjunction and clopen expansion of the coherence proof.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u s i
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.GeneratorReduction
namespace WeilConjectures.OpenInterchangeReduction
-- Keep the derived constructions behind their functorial APIs during this proof.
attribute [local irreducible] pullbackTensorCalculus
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
  HasDerivedCategory.standard SheafOfModules.monoidalCategory
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  IntegralSystemRealization.ringedPullComp

end WeilConjectures.OpenInterchangeReduction
