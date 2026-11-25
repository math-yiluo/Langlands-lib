/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.MvPolynomial.Localization

/-!
# Clearing denominators in multivariate polynomials

A polynomial over a localization `K` of `A` at `M` becomes a polynomial over `A` after
multiplication by a suitable element of `M`.
-/

@[expose] public section

namespace MvPolynomial

attribute [local instance] algebraMvPolynomial in
/-- Clearing denominators: a polynomial over a localization `K` of `A` at `M` becomes a polynomial
over `A` after multiplication by a suitable element of `M`. -/
lemma exists_map_eq_C_mul {A K σ : Type*} [CommRing A] [CommRing K] [Algebra A K]
    (M : Submonoid A) [IsLocalization M K] (F : MvPolynomial σ K) :
    ∃ c ∈ M, ∃ G : MvPolynomial σ A, map (algebraMap A K) G = C (algebraMap A K c) * F := by
  obtain ⟨⟨G, ⟨_, c, hc, rfl⟩⟩, h⟩ := IsLocalization.surj (M.map (C (σ := σ))) F
  refine ⟨c, hc, G, ?_⟩
  simp only [algebraMap_def, map_C] at h
  rw [← h, mul_comm]

end MvPolynomial
