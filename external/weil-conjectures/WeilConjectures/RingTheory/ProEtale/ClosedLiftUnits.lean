/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.ProEtale.ClosedLiftMap

/-! # Units of the ind-etale closed lift

Source: blueprint, smooth purity, `proposition-extension-zero-restriction-closed-subscheme`,
`proposition-extension-zero-restriction-closed-subscheme` (blueprint:
proposition-extension-zero-restriction-closed-subscheme).
-/

@[expose] public section

universe u

namespace Algebra.ClosedLift

/-- An element of the closed lift is a unit if its image in the input algebra is a unit.
Source: blueprint `proposition-extension-zero-restriction-closed-subscheme`, statement and proof
(blueprint: proposition-extension-zero-restriction-closed-subscheme).

Proof: `isUnit_of_isUnit_image`, which lifts the inverse along a localization of a representing
étale stage of the colimit. -/
theorem isUnit_of_isUnit_toAlgHom
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
    (I : Ideal A) [Algebra (A ⧸ I) C] [IsScalarTower A (A ⧸ I) C]
    [Algebra.IndEtale (A ⧸ I) C] (h : Algebra.ClosedLift A C)
    (hh : IsUnit (toAlgHom A C h)) : IsUnit h :=
  isUnit_of_isUnit_image A C h hh

end Algebra.ClosedLift
