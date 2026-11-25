/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
import WeilConjectures.SixFunctors.PurCompactSupport.OpenProjectionIsoCoefficientChange
import WeilConjectures.SixFunctors.PurCompactSupport.OpenProjectionFactorCompositorTransport

set_option linter.privateModule false

/-! # Coefficient compatibility of the open projection factor

Source: Stacks Project, Tags 0E8I, 07A6 and 0D6D.
(blueprint: lem-sf-open-projection-factor-coefficient-change).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  proEtaleRingDerivedAdjunction pbcDerivedScalarAdjunction
namespace WeilConjectures.PurCompactSupport
attribute [local irreducible] scalarTensor scalarPull projectionOpenFactor openComparison
  proEtaleCanonicalTensorComparison

end WeilConjectures.PurCompactSupport
