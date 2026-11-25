/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.NumberTheory.Padics.Extension

/-!
# The ring of integers of an `ℓ`-adic field is Noetherian

If `E` is a finite extension of `ℚ_ℓ` inside `ℚ̄_ℓ`, its ring of integers `𝒪_E` is a principal
ideal ring, hence Noetherian, and so is its universe `u + 1` copy `Shrink 𝒪_E`, the coefficient
ring of the integral stage of the `ℓ`-adic formalism. This is what makes the pullbacks of
sheaves of `𝒪_E`-modules preserve flatness.

## Main results

- `PadicAlgCl.isNoetherianRing_shrink_integers`: `Shrink 𝒪_E` is Noetherian.
-/

@[expose] public section

universe w u

namespace PadicAlgCl

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]
  [Small.{u + 1} E]

/-- The universe `u + 1` copy `Shrink 𝒪_E` of the ring of integers of a finite extension `E` of
`ℚ_ℓ` is Noetherian, `𝒪_E` being a principal ideal ring. -/
instance isNoetherianRing_shrink_integers :
    IsNoetherianRing (Shrink.{u + 1} (integers l E)) :=
  isNoetherianRing_of_ringEquiv _ (shrinkRingEquiv l E)

end PadicAlgCl
