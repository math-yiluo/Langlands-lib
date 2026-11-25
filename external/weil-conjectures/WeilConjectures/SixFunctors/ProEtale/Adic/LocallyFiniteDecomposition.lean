/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Locally finite functions as combinations of `ℤ_ℓ`-valued functions

A continuous function `a : T → ℚ̄_ℓ` on a compact space with values in a finite extension
`E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` is a finite combination `a = ∑ cₖ gₖ` of continuous `ℤ_ℓ`-valued functions
`gₖ` with constant coefficients `cₖ ∈ ℚ̄_ℓ` (`PadicAlgCl.exists_eq_sum_mul_padicInt`): its
coordinates in a `ℚ_ℓ`-basis of `E` are continuous, `E` being finite-dimensional, and bounded on
the compact `T`, hence integral after multiplication by a power of `ℓ`.
-/

@[expose] public section

namespace PadicAlgCl

variable {l : ℕ} [Fact l.Prime]

/-- **Locally finite functions on a compact space are combinations of `ℤ_ℓ`-valued functions**
with constant coefficients in `ℚ̄_ℓ`. -/
theorem exists_eq_sum_mul_padicInt {T : Type*} [TopologicalSpace T] [CompactSpace T]
    (a : C(T, PadicAlgCl l)) (E : IntermediateField ℚ_[l] (PadicAlgCl l))
    [FiniteDimensional ℚ_[l] E] (ha : ∀ x, a x ∈ E) :
    ∃ (n : ℕ) (c : Fin n → PadicAlgCl l) (g : Fin n → C(T, ℤ_[l])),
      ∀ x, a x = ∑ k, c k * algebraMap ℚ_[l] (PadicAlgCl l) (PadicInt.Coe.ringHom (g k x)) := by
  let W : Submodule ℚ_[l] (PadicAlgCl l) := Subalgebra.toSubmodule E.toSubalgebra
  have : FiniteDimensional ℚ_[l] W := inferInstanceAs (FiniteDimensional ℚ_[l] E)
  let B := Module.finBasis ℚ_[l] W
  let a' : C(T, W) := ⟨fun x ↦ ⟨a x, ha x⟩, a.continuous.subtype_mk _⟩
  let f (k : Fin (Module.finrank ℚ_[l] W)) : C(T, ℚ_[l]) :=
    ⟨fun x ↦ B.coord k (a' x),
      (LinearMap.continuous_of_finiteDimensional (B.coord k)).comp a'.continuous⟩
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ k x, ‖f k x‖ ≤ C := by
    choose C hC using fun k ↦ (isCompact_range (f k).continuous).isBounded.exists_norm_le
    exact ⟨∑ k, C k, fun k x ↦ (hC k _ ⟨x, rfl⟩).trans
      (Finset.single_le_sum (fun k _ ↦ (norm_nonneg _).trans (hC k _ ⟨x, rfl⟩))
        (Finset.mem_univ k))⟩
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt C
    (show (1 : ℝ) < l by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hint (k) (x) : ‖(l : ℚ_[l]) ^ N * f k x‖ ≤ 1 := by
    rw [norm_mul, Padic.norm_p_pow, zpow_neg, zpow_natCast]
    have hl : (0 : ℝ) < (l : ℝ) ^ N := pow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) N
    rw [inv_mul_le_iff₀ hl, mul_one]
    exact (hC k x).trans hN.le
  let g (k : Fin (Module.finrank ℚ_[l] W)) : C(T, ℤ_[l]) :=
    ⟨fun x ↦ (⟨(l : ℚ_[l]) ^ N * f k x, hint k x⟩ : ℤ_[l]),
      (continuous_const.mul (f k).continuous).subtype_mk _⟩
  refine ⟨_, fun k ↦ algebraMap ℚ_[l] (PadicAlgCl l) ((l : ℚ_[l]) ^ N)⁻¹ * (B k : PadicAlgCl l),
    g, fun x ↦ ?_⟩
  have hx := congrArg (fun w : W ↦ (w : PadicAlgCl l)) (B.sum_repr (a' x))
  simp only [Submodule.coe_sum, Submodule.coe_smul, Algebra.smul_def] at hx
  have hax : a x = (a' x : PadicAlgCl l) := rfl
  rw [hax, ← hx]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hl : algebraMap ℚ_[l] (PadicAlgCl l) ((l : ℚ_[l]) ^ N) ≠ 0 :=
    (map_ne_zero _).2 (pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero))
  have hg : PadicInt.Coe.ringHom (g k x) = (l : ℚ_[l]) ^ N * B.repr (a' x) k := rfl
  rw [hg, map_mul, map_inv₀]
  field_simp

end PadicAlgCl
