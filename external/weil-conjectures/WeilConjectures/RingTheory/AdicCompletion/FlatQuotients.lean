/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Quotients of an adic completion by powers of the extended ideal

Let `I ⊆ A` be a finitely generated ideal and `C` the `I`-adic completion of `A`. The kernel of
`C → A / Iⁿ` is `(I C)ⁿ`, so `C / (I C)ⁿ ≃ A / Iⁿ`. The related statement that
`S / Jⁿ S` is flat over `C / Jⁿ` when `A → C → S` is flat (Stacks, part of the proof of
Lemma 0C4G), which is `AdicCompletion.flat_quotients_of_flat_restriction` in
`WeilConjectures.RingTheory.CompletionRestrictionFlatQuotients`.

## Main results

- `AdicCompletion.ker_evalₐ_eq_map_pow`: the kernel of `C → A / Iⁿ` is `(I C)ⁿ`.
- `AdicCompletion.quotientMapPowEquiv`: the isomorphism `C / (I C)ⁿ ≃ A / Iⁿ`.
-/

@[expose] public section

namespace AdicCompletion

variable {A : Type*} [CommRing A] {I : Ideal A}

/-- For a finitely generated ideal `I`, the kernel of the evaluation `Â → A / Iⁿ` is
`(I Â)ⁿ`. -/
theorem ker_evalₐ_eq_map_pow (hI : I.FG) (n : ℕ) :
    RingHom.ker (evalₐ I n) = I.map (algebraMap A (AdicCompletion I A)) ^ n := by
  have h1 : (I ^ n : Ideal A) ≤ I ^ n • ⊤ := by simp
  have h2 : (I ^ n • ⊤ : Ideal A) ≤ I ^ n := by simp
  ext x
  rw [RingHom.mem_ker, ← Ideal.map_pow]
  have hx : x ∈ (I ^ n • ⊤ : Submodule A (AdicCompletion I A)) ↔
      x ∈ (I ^ n).map (algebraMap A (AdicCompletion I A)) := by
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
  rw [← hx, pow_smul_top_eq_ker_eval hI, LinearMap.mem_ker]
  constructor
  · intro h
    rw [← factor_evalₐ_eq_eval I x h1, h, _root_.map_zero]
  · intro h
    rw [← factor_eval_eq_evalₐ I x h2, h, _root_.map_zero]

/-- The isomorphism `Â / (I Â)ⁿ ≃ A / Iⁿ` induced by evaluation, for finitely generated `I`. -/
noncomputable def quotientMapPowEquiv (hI : I.FG) (n : ℕ) :
    AdicCompletion I A ⧸ I.map (algebraMap A (AdicCompletion I A)) ^ n ≃+* A ⧸ I ^ n :=
  (Ideal.quotEquivOfEq (ker_evalₐ_eq_map_pow hI n).symm).trans
    (RingHom.quotientKerEquivOfSurjective (f := (evalₐ I n).toRingHom) (surjective_evalₐ I n))

lemma quotientMapPowEquiv_mk (hI : I.FG) (n : ℕ) (x : AdicCompletion I A) :
    quotientMapPowEquiv hI n (Ideal.Quotient.mk _ x) = evalₐ I n x :=
  rfl

end AdicCompletion
