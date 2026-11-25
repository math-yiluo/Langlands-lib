/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Primitive roots of unity in a separably closed field

## Main statements

- `IsSepClosed.exists_isPrimitiveRoot_pow_eq`: a compatible system of primitive `ℓⁿ`-th roots of
  unity in a separably closed field.
- `IsSepClosed.exists_isPrimitiveRoot`: for `n` invertible in a separably closed field `k`,
  `xⁿ - 1` has `n` distinct roots in `k`, and there is a primitive `n`-th root of unity in `k`
  whose image in every field extension is again primitive.
-/

@[expose] public section

open Polynomial

/-- **Primitive roots of unity.** Let `k` be a separably closed field (for instance an
algebraically closed one) and let `n` be invertible in `k`. Then `xⁿ - 1` has exactly `n`
distinct roots in `k`, and there is a primitive `n`-th root of unity `ζ ∈ k`. Its image in any
field extension `k → K` is again a primitive `n`-th root of unity, which is the compatibility of
the trivialization `θ_ζ` (`IsPrimitiveRoot.zmodAddEquivRootsOfUnity`) with extension of the base
field.
(blueprint: `lem-sc-primitive-root`) -/
theorem IsSepClosed.exists_isPrimitiveRoot (k : Type*) [Field k] [IsSepClosed k] (n : ℕ)
    [NeZero (n : k)] :
    (nthRoots n (1 : k)).Nodup ∧ (nthRootsFinset n (1 : k)).card = n ∧
      ∃ ζ : k, IsPrimitiveRoot ζ n ∧
        ∀ (K : Type*) [Field K] (φ : k →+* K), IsPrimitiveRoot (φ ζ) n := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot k n
  exact ⟨hζ.nthRoots_one_nodup, hζ.card_nthRootsFinset, ζ, hζ,
    fun K _ φ ↦ hζ.map_of_injective φ.injective⟩

/-- An `ℓ`-th root of a primitive `ℓⁿ⁺¹`-th root of unity is a primitive `ℓⁿ⁺²`-th root of
unity. -/
theorem IsPrimitiveRoot.of_pow_eq_of_pow_succ {M : Type*} [CommMonoid M] {ℓ n : ℕ} (hℓ : 0 < ℓ)
    {ζ x : M} (h : IsPrimitiveRoot ζ (ℓ ^ (n + 1))) (hx : x ^ ℓ = ζ) :
    IsPrimitiveRoot x (ℓ ^ (n + 2)) := by
  have hη : IsPrimitiveRoot (ζ ^ ℓ ^ n) ℓ := h.pow (pow_pos hℓ _) (pow_succ ℓ n)
  refine IsPrimitiveRoot.mk_of_lt _ (pow_pos hℓ _) ?_ fun l hl hl' hxl ↦ ?_
  · rw [pow_succ', pow_mul, hx, h.pow_eq_one]
  · have hζl : ζ ^ l = 1 := by rw [← hx, ← pow_mul, mul_comm, pow_mul, hxl, one_pow]
    obtain ⟨m, rfl⟩ := h.dvd_of_pow_eq_one l hζl
    have hηm : (ζ ^ ℓ ^ n) ^ m = 1 := by
      rw [← hxl, ← hx, ← pow_mul, ← pow_mul]
      ring_nf
    obtain ⟨m', rfl⟩ := hη.dvd_of_pow_eq_one m hηm
    have e : ℓ ^ (n + 1) * (ℓ * m') = ℓ ^ (n + 2) * m' := by ring
    rw [e] at hl hl'
    obtain rfl : m' = 0 := Nat.lt_one_iff.1 (Nat.lt_of_mul_lt_mul_left (a := ℓ ^ (n + 2))
      (by simpa using hl'))
    simp at hl

/-- **A compatible system of primitive roots of unity.** In a separably closed field `k` in which
`ℓ` is invertible there are primitive `ℓⁿ`-th roots of unity `ζₙ` with `ζₙ₊₁ ^ ℓ = ζₙ`. -/
theorem IsSepClosed.exists_isPrimitiveRoot_pow_eq (k : Type*) [Field k] [IsSepClosed k] (ℓ : ℕ)
    [NeZero (ℓ : k)] :
    ∃ ζ : ℕ → k, (∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ n)) ∧ ∀ n, ζ (n + 1) ^ ℓ = ζ n := by
  have hℓ : 0 < ℓ := Nat.pos_of_ne_zero (NeZero.of_neZero_natCast k).ne
  obtain ⟨ζ₁, hζ₁⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot k ℓ
  choose r hr using fun x : k ↦ IsSepClosed.exists_pow_nat_eq x ℓ
  let f : ℕ → k := fun n ↦ Nat.rec ζ₁ (fun _ z ↦ r z) n
  have hf : ∀ n, IsPrimitiveRoot (f n) (ℓ ^ (n + 1)) := by
    intro n
    induction n with
    | zero => simpa [f] using hζ₁
    | succ n ih => exact ih.of_pow_eq_of_pow_succ hℓ (hr (f n))
  refine ⟨fun n ↦ Nat.casesOn n 1 f, fun n ↦ ?_, fun n ↦ ?_⟩
  · cases n with
    | zero => simp
    | succ n => exact hf n
  · cases n with
    | zero => exact hζ₁.pow_eq_one
    | succ n => exact hr (f n)
