/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.RingTheory.LocalizationFiniteGlobalDimension
import WeilConjectures.RingTheory.RegularLocalFiniteGlobalDimension
import WeilConjectures.RingTheory.RegularLocalOfFiniteGlobalDimension

/-! # Localization of a regular local ring

Source: literature/stacks-project/algebra.tex, Lemma Tag 0AFS and Definition Tag 00OD
(blueprint: lem-weil-pbc-regular-local-localization)
-/

@[expose] public section

universe u

namespace IsRegularLocalRing

/-- A prime localization of a regular local ring is regular local, and the ring is regular.
Source: Stacks Project, Algebra, Lemma Tag 0AFS and Definition Tag 00OD
(blueprint: lem-weil-pbc-regular-local-localization).

Proof:
1. `R` is Noetherian by regularity. Its localization at the complement of `p` is Noetherian
   by `lem-weil-pbc-localization-noetherian` and local by
   `def-weil-pbc-localization-at-prime`, with maximal ideal the extension of `p`.
2. By `lem-weil-pbc-regular-local-finite-gl-dim`, `R` has global dimension at most its
   Krull dimension, hence finite global dimension (`def-weil-pbc-finite-global-dimension`).
3. By `lem-weil-pbc-localization-finite-gl-dim`, this bound is preserved upon localization
   at the complement of `p`, so `Localization.AtPrime p` has finite global dimension.
4. Apply `lem-weil-pbc-finite-gl-dim-regular-local` to this Noetherian local ring to obtain
   the first assertion.
5. Repeat for every prime. Together with Noetherianity of `R`, this is `IsRegularRing R`
   by `def-weil-regular-scheme` (Stacks Definition Tag 00OD). At the maximal ideal,
   the localization is isomorphic to `R`, consistently with its original regularity. -/
theorem localization_at_prime_and_isRegularRing
    {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (p : Ideal R) [p.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime p) ∧ IsRegularRing R := by
  have hdim : ∃ d : ℕ, ringKrullDim R = (d : WithBot ℕ∞) := by
    obtain ⟨a, ha⟩ := (WithBot.ne_bot_iff_exists.mp (ringKrullDim_ne_bot (R := R)))
    have ha_top : a ≠ ⊤ := by
      intro htop
      apply ringKrullDim_ne_top (R := R)
      simp [← ha, htop]
    obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp ha_top
    exact ⟨d, ha.symm.trans (congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hd).symm⟩
  obtain ⟨d, hd⟩ := hdim
  have hgl : Ring.HasGlobalDimensionLE.{u, u} R d :=
    IsRegularLocalRing.hasGlobalDimensionLE_of_ringKrullDim_eq R d hd
  have hreg (q : Ideal R) [q.IsPrime] :
      IsRegularLocalRing (Localization.AtPrime q) := by
    have hglq : Ring.HasGlobalDimensionLE.{u, u} (Localization.AtPrime q) d := by
      exact (Ring.localization_preserves_projective_and_global_dimension R q.primeCompl d).2.1 hgl
    have hfdq : Ring.HasFiniteGlobalDimension.{u, u} (Localization.AtPrime q) := ⟨d, hglq⟩
    exact IsRegularLocalRing.of_hasFiniteGlobalDimension _ hfdq
  refine ⟨hreg p, ?_⟩
  apply isRegularRing_iff.mpr
  intro q hq
  exact hreg q

end IsRegularLocalRing
