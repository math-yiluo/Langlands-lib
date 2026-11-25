/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
import all WeilConjectures.Algebra.Homology.RingedTensorSquare.RingedExchangeTensorCoherence
import WeilConjectures.SixFunctors.PurCompactSupport.ScalarPullTensorCoefficientCoherence
import WeilConjectures.SixFunctors.PurCompactSupport.OpenProjectionFactorCoefficientChange

set_option linter.privateModule false

/-! # Coefficient compatibility of the ordinary compact-support projection

Source: Stacks Project, Tags 07A4, 0D6D, 0E48 and 0E8I; the actual-map reduction
step of the blueprint projection-formula proof.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  proEtaleRingDerivedAdjunction pbcDerivedScalarAdjunction
namespace WeilConjectures.PurCompactSupport
attribute [local irreducible] scalarTensor properComparison openComparison comparison
  proEtaleCanonicalTensorComparison

attribute [local irreducible] scalarPull projectionOpenFactor

end WeilConjectures.PurCompactSupport
