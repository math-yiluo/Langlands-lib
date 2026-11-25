/-
Copyright (c) 2026 Claude and The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import WeilConjectures.Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # The cyclotomic character of a finite field

These are the field-level proofs from `FrobeniusTwist`, isolated from Weil
cohomology for the ordinary root-trivialization calculations.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.WeilSheaf

variable (k₀ : Type u) [Field k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section Fintype

variable [Fintype k₀]

omit [Fintype k₀] in
variable [Finite k₀] in
/-- `ℓ ≠ p` is nonzero in the algebraic closure of `k₀`. -/
lemma purity_neZero_natCast_algebraicClosure : NeZero ((l : ℕ) : AlgebraicClosure k₀) := ⟨by
  rw [← map_natCast (algebraMap k₀ (AlgebraicClosure k₀)),
    map_ne_zero_iff _ (algebraMap k₀ (AlgebraicClosure k₀)).injective, Ne, ringChar.spec,
    Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime k₀ _) Fact.out]
  exact Fact.out⟩

/-- The arithmetic Frobenius `x ↦ x ^ q` of `k̄` acts on `ℤ_ℓ(1)` by `q`. -/
lemma purity_cyclotomicCharacter_frobenius :
    ((cyclotomicCharacter (AlgebraicClosure k₀) l
      (FiniteField.frobeniusAlgEquivOfAlgebraic k₀ (AlgebraicClosure k₀)).toRingEquiv :
        ℤ_[l]ˣ) : ℤ_[l]) = (Nat.card k₀ : ℤ_[l]) := by
  have := purity_neZero_natCast_algebraicClosure k₀ l
  rw [Nat.card_eq_fintype_card]
  refine PadicInt.ext_of_toZModPow.mp fun n ↦ ?_
  rw [cyclotomicCharacter.toZModPow, ← modularCyclotomicCharacter.unique]
  intro t ht
  rw [map_natCast, ZMod.val_natCast, ← Units.val_pow_eq_pow_val,
    ← pow_eq_pow_mod _ ((mem_rootsOfUnity _ _).mp ht)]
  simp

/-- Blueprint `prose-10-21`: Frobenius on coefficient twists

At the integral stage: the geometric Frobenius `σ` of `k̄` acts on `ℤ_ℓ(1) = lim μ_{ℓ^r}(k̄)` by
`q⁻¹`, that is, its `ℓ`-adic cyclotomic character `χ_ℓ(σ)` satisfies `χ_ℓ(σ) q = 1`. -/
theorem purity_cyclotomicCharacter_geometricFrobenius_mul :
    ((cyclotomicCharacter (AlgebraicClosure k₀) l
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic k₀ (AlgebraicClosure k₀)).toRingEquiv :
        ℤ_[l]ˣ) : ℤ_[l]) * (Nat.card k₀ : ℤ_[l]) = 1 := by
  have hinv : (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic k₀
      (AlgebraicClosure k₀)).toRingEquiv = (FiniteField.frobeniusAlgEquivOfAlgebraic k₀
        (AlgebraicClosure k₀)).toRingEquiv⁻¹ := rfl
  rw [hinv, map_inv, ← purity_cyclotomicCharacter_frobenius, Units.inv_mul]

/-- Blueprint `prose-10-21`: Frobenius on coefficient twists

At the finite stages: the geometric Frobenius `σ` of `k̄` acts on `μ_{ℓ^N}(k̄)` by `q⁻¹`, that is,
`σ(ζ) = ζ^c` for the value `c ∈ (ℤ/ℓ^N)ˣ` of the modular cyclotomic character, and `c q = 1`. This
is the reduction modulo `ℓ^N` of `purity_cyclotomicCharacter_geometricFrobenius_mul`. -/
theorem purity_modularCyclotomicCharacter_geometricFrobenius_mul (N : ℕ) :
    haveI := purity_neZero_natCast_algebraicClosure k₀ l
    ((modularCyclotomicCharacter (AlgebraicClosure k₀)
      (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure k₀) (l ^ N))
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic k₀ (AlgebraicClosure k₀)).toRingEquiv :
        (ZMod (l ^ N))ˣ) : ZMod (l ^ N)) * (Nat.card k₀ : ZMod (l ^ N)) = 1 := by
  have := purity_neZero_natCast_algebraicClosure k₀ l
  rw [← cyclotomicCharacter.toZModPow]
  simpa using
    congrArg (PadicInt.toZModPow N) (purity_cyclotomicCharacter_geometricFrobenius_mul k₀ l)

end Fintype

end AlgebraicGeometry.WeilSheaf
