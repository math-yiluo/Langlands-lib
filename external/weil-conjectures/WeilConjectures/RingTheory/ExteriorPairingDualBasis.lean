/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-! # The exterior pairing on a basis and its coordinates

For a basis `b` of `M` indexed by a linear order and order embeddings `a c : Fin n ↪o ι`, the
exterior pairing of `b.coord (a 0) ∧ ⋯ ∧ b.coord (a (n-1))` with `b (c 0) ∧ ⋯ ∧ b (c (n-1))` is `1`
if `a = c` and `0` otherwise. These are the order-embedding forms of Mathlib's
`exteriorPower.ιMultiDual_apply_diag` / `ιMultiDual_apply_nondiag` (indexed by `powersetCard ι n`),
transported along `Set.powersetCard.ofFinEmbEquiv`. (Mathlib's former lemmas
`exteriorPower.pairingDual_apply_apply_eq_one{,_zero}` are deprecated without replacement.)
-/

@[expose] public section

namespace WeilConjectures.ExteriorPower

open exteriorPower Set

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  {ι : Type*} [LinearOrder ι] (b : Module.Basis ι R M) {n : ℕ}

/-- The exterior pairing of the wedge of the coordinates `b.coord (a i)` with the wedge of the
basis vectors `b (a i)` is `1`. -/
lemma pairingDual_coord_eq_one (a : Fin n ↪o ι) :
    pairingDual R M n (ιMulti R n (b.coord ∘ a)) (ιMulti R n (b ∘ a)) = 1 := by
  simpa [ιMultiDual, ιMulti_family, Function.comp_def] using
    ιMultiDual_apply_diag R n b (powersetCard.ofFinEmbEquiv a)

/-- The exterior pairing of the wedge of the coordinates `b.coord (a i)` with the wedge of the
basis vectors `b (c i)` is `0` for distinct order embeddings `a ≠ c`. -/
lemma pairingDual_coord_eq_zero (a c : Fin n ↪o ι) (h : a ≠ c) :
    pairingDual R M n (ιMulti R n (b.coord ∘ a)) (ιMulti R n (b ∘ c)) = 0 := by
  simpa [ιMultiDual, ιMulti_family, Function.comp_def] using
    ιMultiDual_apply_nondiag R n b (powersetCard.ofFinEmbEquiv a) (powersetCard.ofFinEmbEquiv c)
      (powersetCard.ofFinEmbEquiv.injective.ne h)

end WeilConjectures.ExteriorPower
