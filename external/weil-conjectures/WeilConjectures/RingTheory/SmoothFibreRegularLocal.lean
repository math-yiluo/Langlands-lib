/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.RingTheory.RegularLocalRing.Smooth

/-!
# Smooth fibres have regular local rings

Source: literature/stacks-project/algebra.tex, Algebra, Lemmas Tags 00T4 and 00TT
(blueprint: lem-weil-pbc-smooth-fibre-regular-local).
-/

@[expose] public section

universe u v

namespace Algebra

/-- A smooth algebra has smooth residue-field fibres, whose prime localizations are regular local.
Source: literature/stacks-project/algebra.tex, Algebra, Lemmas Tags 00T4 and 00TT
(blueprint: lem-weil-pbc-smooth-fibre-regular-local).

Proof:
1. Fix a prime ideal `p` of `R`. Base change of the smooth map along `R → κ(p)`
   gives a smooth `κ(p)`-algebra `p.Fiber S`, by the base-change clause of
   `lem-weil-pbc-smooth-ring-map-base-change-composition`.
2. For each prime `Q` of this fibre, the final assertion of Stacks Lemma 00TT,
   characterizing smooth algebras over fields, gives that the localization at `Q`
   is a regular local ring.
-/
theorem smooth_fibre_regular_local
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Smooth R S] :
    ∀ p : PrimeSpectrum R,
      Smooth p.asIdeal.ResidueField (p.asIdeal.Fiber S) ∧
        ∀ Q : PrimeSpectrum (p.asIdeal.Fiber S),
          IsRegularLocalRing (Localization.AtPrime Q.asIdeal) := by
  intro p
  have hs : Smooth p.asIdeal.ResidueField (p.asIdeal.Fiber S) := inferInstance
  refine ⟨hs, ?_⟩
  intro Q
  exact Smooth.isRegularLocalRing_localization p.asIdeal.ResidueField (p.asIdeal.Fiber S) Q.asIdeal

end Algebra
