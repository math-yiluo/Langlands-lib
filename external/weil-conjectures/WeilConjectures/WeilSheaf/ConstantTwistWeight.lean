/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import WeilConjectures.WeilSheaf.StalkConstantTwist

/-!
# Punctual weights of constant twists

The constant Weil twist `F ⊗ 𝓑_b` of a Weil sheaf `F` punctually `ι`-pure of weight `w` by a unit
`b` with `2 log_q |ι b| = c` is punctually `ι`-pure of weight `w + c`
(`AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight.constantTwist`). Every punctually pure
sheaf can be normalized to weight zero in this way
(`AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight.exists_units_norm_eq`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- If `F` is lisse and punctually `ι`-pure of weight `w` and `2 log_q |ι b| = c`, then the
constant twist `F ⊗ 𝓑_b` is punctually `ι`-pure of weight `w + c`: at a closed point of degree
`m` every eigenvalue `α` of the local Frobenius becomes `bᵐ α`, of absolute value
`q^{mc/2} q^{mw/2}`. (blueprint: `proposition-weights-under-usual-operations--12`) -/
theorem IsPunctuallyPureOfWeight.constantTwist {ι : PadicAlgCl l →+* ℂ} {F : WeilSheaf k₀ l X}
    {w : ℝ} (h : F.IsPunctuallyPureOfWeight ι w) {b : (PadicAlgCl l)ˣ} {c : ℝ}
    (hb : 2 * Real.logb (Nat.card k₀) ‖ι b‖ = c) :
    (F.constantTwist b).IsPunctuallyPureOfWeight ι (w + c) := by
  intro x
  obtain ⟨e⟩ := F.nonempty_equiv_stalk_constantTwist b x
  have hq : (1 : ℝ) < Nat.card k₀ := by exact_mod_cast Finite.one_lt_card
  have hb0 : (b : PadicAlgCl l) ≠ 0 := b.ne_zero
  have hnorm : ‖ι b‖ = (Nat.card k₀ : ℝ) ^ (c / 2) := by
    rw [← hb, mul_div_cancel_left₀ _ two_ne_zero, Real.rpow_logb (by positivity) hq.ne'
      (norm_pos_iff.2 ((map_ne_zero ι).2 hb0))]
  refine FrobeniusModule.IsPureOfWeight.of_equiv e ((h x).rescale (pow_pos Nat.card_pos _)
    (pow_ne_zero _ hb0) ?_)
  rw [map_pow, norm_pow, hnorm, Nat.cast_pow, ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity), ← Real.rpow_natCast (Nat.card k₀ : ℝ),
    ← Real.rpow_mul (by positivity)]
  ring_nf

/-- The constant twist `F ⊗ 𝓑_b` with `|ι b| = q^{-w/2}` of a sheaf punctually `ι`-pure of
weight `w` is punctually `ι`-pure of weight `0`. -/
theorem IsPunctuallyPureOfWeight.constantTwist_zero {ι : PadicAlgCl l →+* ℂ}
    {F : WeilSheaf k₀ l X} {w : ℝ} (h : F.IsPunctuallyPureOfWeight ι w) {b : (PadicAlgCl l)ˣ}
    (hb : ‖ι b‖ = (Nat.card k₀ : ℝ) ^ (-w / 2)) :
    (F.constantTwist b).IsPunctuallyPureOfWeight ι 0 := by
  have hq : (1 : ℝ) < Nat.card k₀ := by exact_mod_cast Finite.one_lt_card
  have h' := h.constantTwist (b := b) (c := -w) (by
    rw [hb, Real.logb_rpow (by positivity) hq.ne']
    ring)
  rwa [add_neg_cancel] at h'

variable (ι : PadicAlgCl l →+* ℂ) in
/-- A Weil sheaf punctually `ι`-pure of weight `w` is punctually `ι`-pure of some weight `w'`
for which there is a unit `b ∈ ℚ̄_ℓˣ` with `|ι b| = q ^ (-w' / 2)`: if `F` has a local
Frobenius eigenvalue `α` at a closed point of degree `d`, then `|ι α| = q ^ (d w / 2)` and a
`d`-th root of `α⁻¹` will do; otherwise `F` is pure of every weight, and `w' = 0`, `b = 1`. -/
theorem IsPunctuallyPureOfWeight.exists_units_norm_eq {F : WeilSheaf k₀ l X} {w : ℝ}
    (hw : F.IsPunctuallyPureOfWeight ι w) :
    ∃ (w' : ℝ) (b : (PadicAlgCl l)ˣ), F.IsPunctuallyPureOfWeight ι w' ∧
      ‖ι b‖ = (Nat.card k₀ : ℝ) ^ (-w' / 2) := by
  by_cases hex : ∃ (x : X.finitePoints) (α : PadicAlgCl l),
      (F.stalk x).frobeniusEnd.HasEigenvalue α
  · obtain ⟨x, α, hα⟩ := hex
    have hq : (0 : ℝ) < Nat.card k₀ := by exact_mod_cast Nat.card_pos
    set d := (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1
    have hd : d ≠ 0 := Scheme.Hom.degreeOver_ne_zero _ x.2
    have hαw : ‖ι α‖ = ((Nat.card k₀ : ℝ) ^ d) ^ (w / 2) := by
      rw [hw x α hα, Scheme.Hom.residueCard, Nat.cast_pow]
    have hα0 : α ≠ 0 := by
      rintro rfl
      rw [map_zero, norm_zero] at hαw
      exact (Real.rpow_pos_of_pos (pow_pos hq d) _).ne hαw
    obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq α⁻¹ (Nat.pos_of_ne_zero hd)
    have hβ0 : β ≠ 0 := by
      rintro rfl
      exact inv_ne_zero hα0 (by rw [← hβ, zero_pow hd])
    refine ⟨w, Units.mk0 β hβ0, hw, ?_⟩
    rw [Units.val_mk0]
    refine (pow_left_inj₀ (norm_nonneg _) (Real.rpow_nonneg hq.le _) hd).1 ?_
    rw [← norm_pow, ← map_pow, hβ, map_inv₀, norm_inv, hαw, ← Real.rpow_pow_comm hq.le,
      neg_div, Real.rpow_neg hq.le, inv_pow]
  · simp only [not_exists] at hex
    exact ⟨0, 1, fun x α hα ↦ (hex x α hα).elim, by simp⟩

end AlgebraicGeometry.WeilSheaf
