/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineLineConstructible
public import WeilConjectures.AlgebraicGeometry.AffineSpaceClosedPoints

/-!

# Non-closed points have a generic coordinate

Let `K` be a field and `e : Z ⟶ 𝔸(ι; K)` an immersion, `ι` finite. A point of `Z` which is not
closed has a coordinate `Z ⟶ 𝔸¹_K` sending it to the generic point of the affine line
(`AlgebraicGeometry.AffineSpace.exists_isGenericPoint_reindex_of_not_isClosed`): this is how the
slice step of Deligne's induction (SGA 4½, [Th. finitude], 3.7) reaches every non-closed point of
the special fibre.

-/

@[expose] public section

universe u

open CategoryTheory Set

namespace AlgebraicGeometry.AffineSpace

/-- A point of `𝔸¹_K` which is not closed is the generic point. -/
lemma isGenericPoint_of_not_isClosed {K : Type u} [Field K]
    {z : 𝔸(ULift.{u} (Fin 1); Spec (.of K))}
    (hz : ¬ IsClosed ({z} : Set _)) : IsGenericPoint z univ := by
  by_contra h
  exact hz (isClosed_singleton_of_isIso_of_not_isGenericPoint (SpecIso _ (.of K)).hom h)

/-- **A non-closed point has a generic coordinate.** For an immersion `e : Z ⟶ 𝔸(ι; K)` with `ι`
finite, a point of `Z` which is not closed is sent to the generic point of `𝔸¹_K` by one of the
coordinates of `e`. -/
theorem exists_isGenericPoint_reindex_of_not_isClosed {K : Type u} [Field K] {Z : Scheme.{u}}
    {ι : Type u} [Finite ι] (e : Z ⟶ 𝔸(ι; Spec (.of K))) [IsImmersion e] {z : Z}
    (hz : ¬ IsClosed ({z} : Set Z)) :
    ∃ i : ι, IsGenericPoint
      ((e ≫ reindex (fun _ : ULift.{u} (Fin 1) ↦ i) (Spec (.of K))) z) univ := by
  by_contra h
  simp only [not_exists] at h
  have hcl : IsClosed ({e z} : Set _) := by
    refine isClosed_singleton_of_forall_isClosed_singleton_reindex (ι := ULift.{u} (Fin 1))
      ⟨0⟩ _ fun i ↦ ?_
    by_contra hi
    exact h i (by rw [Scheme.Hom.comp_apply]; exact isGenericPoint_of_not_isClosed hi)
  refine hz ?_
  have : e.base ⁻¹' {e z} = {z} := by
    ext w
    simp only [mem_preimage, mem_singleton_iff]
    exact ⟨fun hw ↦ e.isEmbedding.injective hw, fun hw ↦ hw ▸ rfl⟩
  rw [← this]
  exact hcl.preimage e.base.hom.continuous

end AlgebraicGeometry.AffineSpace
