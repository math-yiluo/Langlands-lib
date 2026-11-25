/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.TateTwistCohomology
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Geometric Frobenius on the coefficient twists

Let `k₀` be a finite field with `q` elements, `k̄` an algebraic closure, `σ : k̄ ≅ k̄` the geometric
Frobenius (the inverse of `x ↦ x ^ q`) and `ℓ ≠ p` a prime. The geometric Frobenius acts on the
Tate twists by `q^{-m}` (blueprint `prose-10-21`), at every coefficient
stage:

* at the finite stages, on `μ_{ℓ^N}(k̄)`: `σ(ζ) = ζ^{c}` with `c q = 1` in `ℤ/ℓ^N`
  (`AlgebraicGeometry.WeilSheaf.modularCyclotomicCharacter_geometricFrobenius_mul`);
* at the integral stage, on `ℤ_ℓ(1)`: the `ℓ`-adic cyclotomic character of `σ` is `q⁻¹`
  (`AlgebraicGeometry.WeilSheaf.cyclotomicCharacter_geometricFrobenius_mul`); its reductions are
  the finite-stage values;
* at the stage `ℚ̄_ℓ`, on the Tate Weil sheaves: `ℚ̄_ℓ(m)` is the constant Weil twist of `ℚ̄_ℓ` by
  the scalar `q^{-m}` (`AlgebraicGeometry.WeilSheaf.exists_tateTwistSheaf_iso_constantTwist`),
  and in particular `ℚ̄_ℓ(-d)` is the twist by `q^d`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace WeilSheaf

variable (k₀ : Type u) [Field k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section Fintype

variable [Fintype k₀]

omit [Fintype k₀] in
variable [Finite k₀] in
/-- `ℓ ≠ p` is nonzero in the algebraic closure of `k₀`. -/
lemma neZero_natCast_algebraicClosure : NeZero ((l : ℕ) : AlgebraicClosure k₀) := ⟨by
  rw [← map_natCast (algebraMap k₀ (AlgebraicClosure k₀)),
    map_ne_zero_iff _ (algebraMap k₀ (AlgebraicClosure k₀)).injective, Ne, ringChar.spec,
    Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime k₀ _) Fact.out]
  exact Fact.out⟩

/-- The arithmetic Frobenius `x ↦ x ^ q` of `k̄` acts on `ℤ_ℓ(1)` by `q`. -/
lemma cyclotomicCharacter_frobenius :
    ((cyclotomicCharacter (AlgebraicClosure k₀) l
      (FiniteField.frobeniusAlgEquivOfAlgebraic k₀ (AlgebraicClosure k₀)).toRingEquiv :
        ℤ_[l]ˣ) : ℤ_[l]) = (Nat.card k₀ : ℤ_[l]) := by
  have := neZero_natCast_algebraicClosure k₀ l
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
theorem cyclotomicCharacter_geometricFrobenius_mul :
    ((cyclotomicCharacter (AlgebraicClosure k₀) l
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic k₀ (AlgebraicClosure k₀)).toRingEquiv :
        ℤ_[l]ˣ) : ℤ_[l]) * (Nat.card k₀ : ℤ_[l]) = 1 := by
  have hinv : (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic k₀
      (AlgebraicClosure k₀)).toRingEquiv = (FiniteField.frobeniusAlgEquivOfAlgebraic k₀
        (AlgebraicClosure k₀)).toRingEquiv⁻¹ := rfl
  rw [hinv, map_inv, ← cyclotomicCharacter_frobenius, Units.inv_mul]

/-- Blueprint `prose-10-21`: Frobenius on coefficient twists

At the finite stages: the geometric Frobenius `σ` of `k̄` acts on `μ_{ℓ^N}(k̄)` by `q⁻¹`, that is,
`σ(ζ) = ζ^c` for the value `c ∈ (ℤ/ℓ^N)ˣ` of the modular cyclotomic character, and `c q = 1`. This
is the reduction modulo `ℓ^N` of `cyclotomicCharacter_geometricFrobenius_mul`. -/
theorem modularCyclotomicCharacter_geometricFrobenius_mul (N : ℕ) :
    haveI := neZero_natCast_algebraicClosure k₀ l
    ((modularCyclotomicCharacter (AlgebraicClosure k₀)
      (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure k₀) (l ^ N))
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic k₀ (AlgebraicClosure k₀)).toRingEquiv :
        (ZMod (l ^ N))ˣ) : ZMod (l ^ N)) * (Nat.card k₀ : ZMod (l ^ N)) = 1 := by
  have := neZero_natCast_algebraicClosure k₀ l
  rw [← cyclotomicCharacter.toZModPow]
  simpa using congrArg (PadicInt.toZModPow N) (cyclotomicCharacter_geometricFrobenius_mul k₀ l)

end Fintype

variable [Finite k₀] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- Blueprint `prose-10-21`: Frobenius on coefficient twists

At the stage `ℚ̄_ℓ`: geometric Frobenius acts on the Tate twist `ℚ̄_ℓ(m)` by `q^{-m}`, for every
`m ∈ ℤ`: as a Weil sheaf, `ℚ̄_ℓ(m)` is the constant Weil twist of the constant sheaf `ℚ̄_ℓ` by a
scalar `u` with `u = q^{-m}` (so by `q^{-1}` on `ℚ̄_ℓ(1)`, by `q^{-m}` on `ℚ̄_ℓ(m)` and by `q^m`
on `ℚ̄_ℓ(-m)`). The scalar is `χ_ℓ(σ)^m`, the image in `ℚ̄_ℓ` of the integral and finite-stage
values above (`AlgebraicGeometry.WeilSheaf.cyclotomicUnit`), so the actions commute with finite
reduction and scalar extension. -/
theorem exists_tateTwistSheaf_iso_constantTwist (m : ℤ) :
    ∃ c : (PadicAlgCl l)ˣ, (c : PadicAlgCl l) = (Nat.card k₀ : PadicAlgCl l) ^ (-m) ∧
      Nonempty (tateTwistSheaf k₀ l X m ≅ (adicConstant k₀ l X).constantTwist c) :=
  ⟨cyclotomicUnit k₀ l ^ m, cyclotomicUnit_zpow_eq m, ⟨tateTwistSheafIso k₀ l X m⟩⟩

/-- Blueprint `prose-10-21`: Frobenius on coefficient twists

In particular geometric Frobenius acts on `ℚ̄_ℓ(-d)` by multiplication by `q^d`, for
`d ∈ ℤ_{≥ 0}`. -/
theorem exists_tateTwistSheaf_neg_iso_constantTwist (d : ℕ) :
    ∃ c : (PadicAlgCl l)ˣ, (c : PadicAlgCl l) = (Nat.card k₀ : PadicAlgCl l) ^ d ∧
      Nonempty (tateTwistSheaf k₀ l X (-d) ≅ (adicConstant k₀ l X).constantTwist c) := by
  simpa using exists_tateTwistSheaf_iso_constantTwist k₀ l X (-d)

end WeilSheaf

end AlgebraicGeometry
