/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicFiniteRealization.AdicFiniteRealizationData
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedFlatCoefficientCalculus
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Scalar coherence after extension to the native closure ring

Source: BS Proposition 6.8.14(2); balanced tensor associativity.
(blueprint: lem-sf-adic-closure-scalar-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicFiniteRealization
variable (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) [IsNoetherian T]
  [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [iT : Fact (∀ x : T, IsUnit (l : T.presheaf.stalk x))]

end WeilConjectures.AdicFiniteRealization
