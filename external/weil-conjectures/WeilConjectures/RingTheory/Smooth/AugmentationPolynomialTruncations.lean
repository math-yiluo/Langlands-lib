/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.RingTheory.Smooth.AugmentationPolynomialTruncationsSurjective
import WeilConjectures.RingTheory.Smooth.AugmentationPolynomialTruncationsInjective

/-!
# Propagation of first-order augmented polynomial coordinates

Source: Stacks Project, Tag 05D5, the induction on the truncation degree.
(blueprint: lem-sbc-formally-smooth-augmentation-truncations)
-/

@[expose] public section

universe u

namespace Algebra

/-- First-order polynomial coordinates of a formally smooth augmented algebra are
coordinates at every finite order.

Source: Stacks Project, Tag 05D5, induction constructing the inverse σₙ of Ψₙ.
(blueprint: lem-sbc-formally-smooth-augmentation-truncations)

Proof: Put I = ker ε and J = the variables ideal. Bijectivity at degree two identifies
I/I² with the span of the coordinate images over B. Multiplying representatives shows
that products of k coordinate images span Iᵏ/Iᵏ⁺¹. Induction, starting with degree two
(and its degree-one quotient), therefore makes every induced map fₖ surjective.
Degree zero has zero source and target. For k ≥ 2, assume fₖ is invertible. Formal
smoothness lifts the map C → C/Iᵏ → B[X]/Jᵏ across B[X]/Jᵏ⁺¹ → B[X]/Jᵏ; its kernel
is square-zero since 2k ≥ k+1. The lift sends I into J/Jᵏ⁺¹, since its degree-one
reduction is the inverse augmentation map, and hence kills Iᵏ⁺¹. Compose its descended
map with fₖ₊₁. Each variable becomes Xᵢ + δᵢ with δᵢ in Jᵏ/Jᵏ⁺¹. Substitution
Xᵢ ↦ Xᵢ - δᵢ is the inverse: substituting a correction into a monomial of degree k
changes it by terms of degree at least 2k-1 ≥ k+1. Thus this composite is invertible,
so fₖ₊₁ is injective as well as surjective. This completes induction. Rank zero works
with the same argument and empty sums. Neither locality nor Noetherianity is needed. -/
theorem bijective_augmented_polynomial_truncations
    (B C : Type u) [CommRing B] [CommRing C] [Algebra B C]
    [FormallySmooth B C] (ε : C →ₐ[B] B) (n : ℕ)
    (f : MvPolynomial (Fin n) B →ₐ[B] C)
    (hf : MvPolynomial.idealOfVars (Fin n) B ≤
      (RingHom.ker ε.toRingHom).comap f.toRingHom)
    (h₂ : Function.Bijective
      (Ideal.quotientMapₐ ((RingHom.ker ε.toRingHom) ^ 2) f
        ((pow_le_pow_left' hf 2).trans (Ideal.le_comap_pow f.toRingHom 2)))) :
    ∀ k : ℕ, Function.Bijective
      (Ideal.quotientMapₐ ((RingHom.ker ε.toRingHom) ^ k) f
        ((pow_le_pow_left' hf k).trans (Ideal.le_comap_pow f.toRingHom k))) := by
  intro k
  exact ⟨bijective_augmented_polynomial_truncations_injective B C ε n f hf h₂ k,
    bijective_augmented_polynomial_truncations_surjective B C ε n f hf h₂.2 k⟩

end Algebra
