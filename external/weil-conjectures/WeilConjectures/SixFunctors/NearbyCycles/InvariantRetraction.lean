/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Card

/-!

# Retractions onto invariants by averaging

In a category linear over a field of characteristic zero, let `α : Z ⟶ Y` be a split monomorphism,
with retraction `s`, and `act i : Y ⟶ Y` (`i ∈ t`, a finite nonempty family) endomorphisms fixing
`α` (`α ≫ act i = α`) whose sum lands in the image of `α`
(`(∑ act i) ≫ s ≫ α = ∑ act i`). Then `α` has a retraction `r` with `|t| • (r ≫ α) = ∑ act i`
(`CategoryTheory.exists_retraction_card_smul_eq_sum`): `r = |t|⁻¹ • (∑ act i) ≫ s`. For the action
of a finite group this exhibits `α` as the inclusion of the invariants, with the averaging
idempotent. It is the formal part of the identification of nearby cycles with invariants used in
the generic-slicing step (SGA 4½, [Th. finitude], Lemme 3.3).

-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

variable {C : Type*} [Category C] [Preadditive C]

/-- **Retractions onto invariants by averaging**: a split monomorphism `α` fixed by the `act i` and
containing the image of `∑ act i` has a retraction `r` with `|t| • (r ≫ α) = ∑ act i`. -/
theorem exists_retraction_card_smul_eq_sum (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] [Linear 𝕜 C]
    {Z Y : C} (α : Z ⟶ Y) (s : Y ⟶ Z)
    (hs : α ≫ s = 𝟙 Z) {ι : Type*} (t : Finset ι) (ht : t.Nonempty) (act : ι → (Y ⟶ Y))
    (hinv : ∀ i ∈ t, α ≫ act i = α)
    (himg : (∑ i ∈ t, act i) ≫ s ≫ α = ∑ i ∈ t, act i) :
    ∃ r : Y ⟶ Z, α ≫ r = 𝟙 Z ∧ t.card • (r ≫ α) = ∑ i ∈ t, act i := by
  have hc : (t.card : 𝕜) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_pos.2 ht).ne'
  refine ⟨(t.card : 𝕜)⁻¹ • ((∑ i ∈ t, act i) ≫ s), ?_, ?_⟩
  · have hsum : α ≫ (∑ i ∈ t, act i) = t.card • α := by
      rw [Preadditive.comp_sum, Finset.sum_congr rfl hinv, Finset.sum_const]
    rw [Linear.comp_smul, ← Category.assoc, hsum, Preadditive.nsmul_comp, hs,
      ← Nat.cast_smul_eq_nsmul 𝕜, smul_smul, inv_mul_cancel₀ hc, one_smul]
  · rw [Linear.smul_comp, Category.assoc, himg, ← Nat.cast_smul_eq_nsmul 𝕜, smul_smul,
      mul_inv_cancel₀ hc, one_smul]

end CategoryTheory
