/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section

universe u

namespace Algebra

/-- First-order surjectivity propagates to every augmented polynomial truncation.

Source: Stacks Project, Tag 05D5, surjectivity in the finite-truncation induction.
(blueprint: lem-sbc-formally-smooth-augmentation-truncations-surjective)

Proof: Write I = ker ε and J for the variables ideal. Since f preserves augmentation,
surjectivity modulo I² implies that every element of I is congruent modulo I² to
f(p) for some p in J: the constant coefficient of p must vanish. Therefore every
product of r elements of I is congruent modulo I^(r+1) to an image of a product of
r elements of J. Expanding finite sums gives the same assertion for every element
of I^r. Here coefficients in C can be replaced by their augmentations in B, since
the difference is in I. Start at degree one, where constants represent every class
because c - algebraMap B C (ε c) lies in I. Given a representative modulo I^r,
correct its error in I^r by the polynomial just constructed to obtain a representative
modulo I^(r+1). Degree zero is the zero quotient. This induction proves surjectivity
for every r, including n = 0 and the zero base ring; formal smoothness is not used. -/
theorem bijective_augmented_polynomial_truncations_surjective
    (B C : Type u) [CommRing B] [CommRing C] [Algebra B C]
    (ε : C →ₐ[B] B) (n : ℕ)
    (f : MvPolynomial (Fin n) B →ₐ[B] C)
    (hf : MvPolynomial.idealOfVars (Fin n) B ≤
      (RingHom.ker ε.toRingHom).comap f.toRingHom)
    (h₂ : Function.Surjective
      (Ideal.quotientMapₐ ((RingHom.ker ε.toRingHom) ^ 2) f
        ((pow_le_pow_left' hf 2).trans (Ideal.le_comap_pow f.toRingHom 2)))) :
    ∀ k : ℕ, Function.Surjective
      (Ideal.quotientMapₐ ((RingHom.ker ε.toRingHom) ^ k) f
        ((pow_le_pow_left' hf k).trans (Ideal.le_comap_pow f.toRingHom k))) := by
  let I := RingHom.ker ε.toRingHom
  have first : ∀ c : C, ∃ p : MvPolynomial (Fin n) B, c - f p ∈ I ^ 2 := by
    intro c
    obtain ⟨q, hq⟩ := h₂ (Ideal.Quotient.mk (I ^ 2) c)
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨p, ?_⟩
    have hp : f p - c ∈ I ^ 2 := Ideal.Quotient.eq.1 hq
    simpa only [neg_sub] using (I ^ 2).neg_mem hp
  have graded : ∀ k : ℕ, ∀ c ∈ I ^ k,
      ∃ p : MvPolynomial (Fin n) B, c - f p ∈ I ^ (k + 1) := by
    intro k
    induction k with
    | zero =>
      intro c hc
      refine ⟨MvPolynomial.C (ε c), ?_⟩
      simp only [zero_add, pow_one, I, RingHom.mem_ker, map_sub]
      change ε c - ε (f (MvPolynomial.C (ε c))) = 0
      rw [show f (MvPolynomial.C (ε c)) = algebraMap B C (ε c) from f.commutes (ε c)]
      simp
    | succ k ih =>
      intro c hc
      rw [pow_succ] at hc
      refine Submodule.mul_induction_on hc ?_ ?_
      · intro a ha b hb
        obtain ⟨p, hp⟩ := ih a ha
        obtain ⟨q, hq⟩ := first b
        have hfp : f p ∈ I ^ k := by
          have hdiff : a - (a - f p) ∈ I ^ k :=
            (I ^ k).sub_mem ha ((Ideal.pow_le_pow_right (Nat.le_succ k)) hp)
          simpa only [sub_sub_cancel] using hdiff
        refine ⟨p * q, ?_⟩
        have hleft : (a - f p) * b ∈ I ^ (k + 1 + 1) := by
          rw [pow_succ]
          exact Ideal.mul_mem_mul hp hb
        have hright : f p * (b - f q) ∈ I ^ (k + 1 + 1) := by
          rw [show k + 1 + 1 = k + 2 by omega, pow_add]
          exact Ideal.mul_mem_mul hfp hq
        have heq : a * b - f (p * q) = (a - f p) * b + f p * (b - f q) := by
          rw [map_mul]
          ring
        rw [heq]
        exact (I ^ (k + 1 + 1)).add_mem hleft hright
      · intro a b ha hb
        obtain ⟨p, hp⟩ := ha
        obtain ⟨q, hq⟩ := hb
        refine ⟨p + q, ?_⟩
        have heq : a + b - f (p + q) = (a - f p) + (b - f q) := by
          rw [map_add]
          ring
        rw [heq]
        exact (I ^ (k + 1 + 1)).add_mem hp hq
  have approx : ∀ k : ℕ, ∀ c : C,
      ∃ p : MvPolynomial (Fin n) B, c - f p ∈ I ^ k := by
    intro k
    induction k with
    | zero =>
      intro c
      exact ⟨0, by simp [I]⟩
    | succ k ih =>
      intro c
      obtain ⟨p, hp⟩ := ih c
      obtain ⟨q, hq⟩ := graded k (c - f p) hp
      refine ⟨p + q, ?_⟩
      have heq : c - f (p + q) = c - f p - f q := by
        rw [map_add]
        ring
      rwa [heq]
  intro k y
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨p, hp⟩ := approx k c
  refine ⟨Ideal.Quotient.mk _ p, ?_⟩
  rw [Ideal.quotient_map_mkₐ]
  apply Ideal.Quotient.eq.2
  simpa only [neg_sub] using (I ^ k).neg_mem hp

end Algebra
