/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Localization.Submodule

/-!
# Localizations of regular rings

A localization of a regular ring is regular.
-/

@[expose] public section

/-- A localization `R'` of a regular ring `R` at a multiplicative subset `M` is regular: it is
Noetherian, and its localization at a prime `q` is the localization of `R` at the contraction
of `q`. (blueprint: `theorem-finite-etale-covers-proper-henselian--2`) -/
theorem IsRegularRing.of_isLocalization {R R' : Type*} [CommRing R] [CommRing R']
    [Algebra R R'] (M : Submonoid R) [IsLocalization M R'] [IsRegularRing R] :
    IsRegularRing R' := by
  have : IsNoetherianRing R' := IsLocalization.isNoetherianRing M R' inferInstance
  rw [isRegularRing_iff]
  intro q _
  have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
    (Localization.AtPrime q) q
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv (q.under R).primeCompl
    (Localization.AtPrime (q.under R)) (Localization.AtPrime q)).toRingEquiv
