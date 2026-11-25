/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
public import WeilConjectures.Mathlib.RingTheory.GradedAlgebra.RingHom

/-!
# The irrelevant ideal under a surjective graded ring homomorphism

We show that a surjective graded ring homomorphism `f : 𝒜 →+*ᵍ ℬ` satisfies the hypothesis
`ℬ₊ ≤ 𝒜₊.map f` under which `Proj` is functorial.
-/

@[expose] public section

open HomogeneousIdeal

namespace GradedRingHom

variable {ι A B σ τ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B] [DecidableEq ι] [AddCommMonoid ι]
  [PartialOrder ι] [CanonicallyOrderedAdd ι]
  {𝒜 : ι → σ} {ℬ : ι → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- A surjective graded ring homomorphism maps the irrelevant ideal onto the irrelevant
ideal; in particular it satisfies the hypothesis `ℬ₊ ≤ 𝒜₊.map f` of `Proj.map`. -/
theorem irrelevant_le_map_of_surjective {f : 𝒜 →+*ᵍ ℬ} (hf : Function.Surjective f) :
    irrelevant ℬ ≤ (irrelevant 𝒜).map f := by
  refine (irrelevant_le ℬ).mpr fun i hi b hb ↦ ?_
  obtain ⟨a, ha, rfl⟩ := exists_mem_of_surjective hf (b := b) hb
  exact Ideal.mem_map_of_mem _ (mem_irrelevant_of_mem 𝒜 hi ha)

end GradedRingHom
