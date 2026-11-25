/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.MvPowerSeries.Equiv
import WeilConjectures.RingTheory.PowerSeriesOntoCompletion
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Noetherianity of adic completion

Source: Stacks Project, Commutative Algebra, Lemma 10.97.6 (Tag 0316), second proof
(blueprint: lem-weil-pbc-adic-completion-noetherian).
-/

@[expose] public section

universe u

namespace AdicCompletion

/-- The completion of a Noetherian commutative ring with respect to any ideal is Noetherian.
Source: Stacks Project, Commutative Algebra, Lemma 10.97.6 (Tag 0316), second proof
(blueprint: lem-weil-pbc-adic-completion-noetherian).

Proof: Since `A` is Noetherian, choose finitely many generators `f₁, …, fₙ` of `I`
(`def-weil-pbc-noetherian-ring`), allowing `n = 0`. Substituting these generators for the
variables gives a surjective ring homomorphism from the multivariate formal power series ring
`A[[x₁, …, xₙ]]` to `AdicCompletion I A`
(`lem-weil-pbc-power-series-onto-completion`, `def-weil-pbc-multivariate-power-series`, and
`def-weil-pbc-adic-completion`). The source ring is Noetherian by
`lem-weil-pbc-power-series-noetherian` (Stacks Tag 0306). Its surjective image is Noetherian by
`lem-weil-pbc-surjective-image-noetherian` (Stacks Tag 00FN), proving the conclusion. -/
theorem isNoetherianRing {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    IsNoetherianRing (AdicCompletion I A) := by
  obtain ⟨n, f, hf⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian I)
  obtain ⟨Φ, _, hΦ, _, _⟩ :=
    MvPowerSeries.exists_surjective_toAdicCompletion n f I hf.symm
  exact isNoetherianRing_of_surjective (MvPowerSeries (Fin n) A) _ Φ hΦ

end AdicCompletion
