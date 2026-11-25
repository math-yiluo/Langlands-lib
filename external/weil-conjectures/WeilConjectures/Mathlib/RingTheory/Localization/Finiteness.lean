/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Localization.Finiteness

/-!
# Finite generation of an extended ideal along an arbitrary localization away from `f`

`Ideal.fg_of_localizationSpan` is stated for the chosen localizations
`Localization.Away f`. This file records the transfer of finite generation from an
arbitrary realization of the localization, which is what one has in geometric situations:
the sections `Γ(X, X.basicOpen f)` of a scheme over a basic open.
-/

@[expose] public section

namespace Ideal

variable {R : Type*} [CommRing R]

/-- If the extension of `N` to some localization of `R` away from `f` is finitely
generated, so is its extension to `Localization.Away f`. -/
lemma FG.map_localizationAway {S : Type*} [CommRing S] [Algebra R S] {f : R}
    [IsLocalization.Away f S] {N : Ideal R} (H : (N.map (algebraMap R S)).FG) :
    (N.map (algebraMap R (Localization.Away f))).FG := by
  let e : S ≃ₐ[R] Localization.Away f :=
    IsLocalization.algEquiv (Submonoid.powers f) S (Localization.Away f)
  have h1 : N.map (algebraMap R (Localization.Away f)) =
      (N.map (algebraMap R S)).map (e.toAlgHom : S →+* Localization.Away f) := by
    rw [Ideal.map_map, AlgHom.comp_algebraMap]
  rw [h1]
  exact Ideal.FG.map H _

end Ideal
