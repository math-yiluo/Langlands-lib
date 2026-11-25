/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
import WeilConjectures.SixFunctors.IntegralSystemRealization.Open.OpenExtensionGoodComplexExtension
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations

/-! # Goodness after completed open extension and pullback

Source: Stacks Tags 03DI, 03DJ, 0E8I and 0G7E.
(blueprint: lem-sf-open-extension-good-complex-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Completed coefficient inverse image preserves goodness after open extension.
Source: Stacks Tag 0G7E, applied to the completed-ring geometric inverse image.
(blueprint: lem-sf-open-extension-good-complex-pullback).

Proof: apply the ringed-topos K-flat pullback theorem to the completed coefficient
inverse image and the already extended complex. Its two conclusions are precisely
independent-coefficient K-flatness and flatness of every term. The resulting
inverse-image functor is definitionally the canonical `integralOrdinaryPull`.
-/
theorem openExtension_goodComplex_pullback {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j]
    (P : (integralOperationsGoodComplex l E X).FullSubcategory) :
    integralOperationsGoodComplex l E X
      (((integralOrdinaryPull l E j).mapHomologicalComplex (.up ℤ)).obj
        (((PurCompactSupport.openExtension
        (PurCompactSupport.completed l E) j).mapHomologicalComplex
           (.up ℤ)).obj P.obj)) := by
  have h := openExtension_goodComplex_extension l E j P
  exact AlgebraicGeometry.ProEtale.VaryingRing.ringPull_preserves_flat j
    ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).ring X)
    ((PurCompactSupport.completed l E).pull j) _ h.1 h.2

end WeilConjectures.IntegralSystemRealization
