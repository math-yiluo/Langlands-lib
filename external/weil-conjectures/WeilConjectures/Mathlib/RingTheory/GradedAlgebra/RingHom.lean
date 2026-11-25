/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.GradedAlgebra.RingHom

/-!
# The graded components of a graded ring homomorphism

We define `GradedRingHom.gradeZeroRingHom`, the degree-zero component of a graded ring
homomorphism as a ring homomorphism between the degree-zero subrings, and we show that a
surjective graded ring homomorphism is surjective in each degree separately.
-/

@[expose] public section

namespace GradedRingHom

variable {ι A B σ τ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B] [DecidableEq ι] [AddCommMonoid ι]
  {𝒜 : ι → σ} {ℬ : ι → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- The degree-zero component of a graded ring homomorphism, as a ring homomorphism
between the degree-zero subrings. -/
def gradeZeroRingHom (f : 𝒜 →+*ᵍ ℬ) : 𝒜 0 →+* ℬ 0 where
  toFun a := ⟨f a, f.map_mem a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

@[simp]
lemma coe_gradeZeroRingHom_apply (f : 𝒜 →+*ᵍ ℬ) (a : 𝒜 0) :
    (f.gradeZeroRingHom a : B) = f a :=
  rfl

/-- A surjective graded ring homomorphism is surjective in each degree: an element of `ℬ i`
is the image of an element of `𝒜 i`.

Any preimage works after replacing it by its degree-`i` component, since taking graded
components commutes with a graded ring homomorphism. -/
theorem exists_mem_of_surjective {f : 𝒜 →+*ᵍ ℬ} (hf : Function.Surjective f) {i : ι} {b : B}
    (hb : b ∈ ℬ i) : ∃ a ∈ 𝒜 i, f a = b := by
  obtain ⟨a, rfl⟩ := hf b
  refine ⟨DirectSum.decompose 𝒜 a i, SetLike.coe_mem _, ?_⟩
  rw [map_directSumDecompose 𝒜 ℬ f, DirectSum.decompose_of_mem_same ℬ hb]

/-- A surjective graded ring homomorphism induces a surjection on each graded piece. -/
theorem surjective_gradedAddHom {f : 𝒜 →+*ᵍ ℬ} (hf : Function.Surjective f) (i : ι) :
    Function.Surjective (f.gradedAddHom i) := fun b ↦ by
  obtain ⟨a, ha, hab⟩ := exists_mem_of_surjective hf b.2
  exact ⟨⟨a, ha⟩, Subtype.ext hab⟩


end GradedRingHom
