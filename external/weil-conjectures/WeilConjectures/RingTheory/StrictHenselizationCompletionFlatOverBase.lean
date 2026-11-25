/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.IsStrictHenselization
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import WeilConjectures.RingTheory.FlatModuleCompletion
import WeilConjectures.RingTheory.StrictHenselizationModPowerFree

/-!
# Flatness over the base of the completed strict henselization

Source: Stacks Project, More on Algebra, Lemma Tag 06LJ, proof of (c), paragraph
“To finish the proof of (c)”
(blueprint: lem-sc-strict-henselization-completion-flat-over-base).
-/

@[expose] public section

universe v

namespace Algebra

/-- For a Noetherian local ring `A`, the completion of its strict henselization `C` at
`nC`, where `n` is the maximal ideal of `A`, is flat over `A`.
Source: Stacks Project, Tag 06LJ, proof of (c)
(blueprint: lem-sc-strict-henselization-completion-flat-over-base).

Proof: `lem-sc-strict-henselization-mod-power-free` identifies this completion with the
`n`-adic completion of a free `A`-module `F`, using the compatible isomorphisms modulo
`n^r`. The identification respects the action of the completed base ring through its
canonical map to the completed strict henselization. Since `F` is free and hence flat,
`lem-weil-pbc-flat-module-completion-flat` makes its completion flat over the completed
base ring. The map from `A` to its completion is flat by
`lem-weil-pbc-noetherian-completion-flat`. Composition, by
`lem-weil-pbc-flat-ring-map-comp`, gives flatness of the canonical map from `A`. -/
theorem strictHenselization_completion_flat_over_base
    (A K C : Type v) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Field K]
    [Algebra (IsLocalRing.ResidueField A) K] [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing C] [Algebra A C] (hC : IsStrictHenselization A K C) :
    (algebraMap A
      (AdicCompletion ((IsLocalRing.maximalIdeal A).map (algebraMap A C)) C)).Flat := by
  obtain ⟨X, _, _, _, E, _⟩ := strictHenselization_mod_power_free A K C hC
  let I := IsLocalRing.maximalIdeal A
  have : Module.Flat (AdicCompletion I A) (AdicCompletion I (X →₀ A)) :=
    Module.flat_adicCompletion A I (X →₀ A)
  have : Module.Flat A (AdicCompletion I (X →₀ A)) :=
    Module.Flat.trans A (AdicCompletion I A) (AdicCompletion I (X →₀ A))
  exact RingHom.flat_algebraMap_iff.mpr (Module.Flat.of_linearEquiv E.symm)

end Algebra
