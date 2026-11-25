/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.TraitSlice

/-!

# Coordinate generic slices of affine spaces over the trait

Let `k'` be a field, `S = Spec k'⟦t⟧`, and let `K` be a field over `k'` with an element `x`
(for the slices, `K = k'(x)^alg` with `x` transcendental: `AlgebraicGeometry.traitSliceField`
and `AlgebraicGeometry.traitSliceCoord`).
For a coordinate `i : Fin (n + 1)` of `𝔸ⁿ⁺¹_S`, the morphism `hᵢ : 𝔸ⁿ_{K⟦t⟧} ⟶ 𝔸ⁿ⁺¹_S`
(`AlgebraicGeometry.affineSpaceSlice`) over the trait map `Spec K⟦t⟧ ⟶ S` sends the `i`-th
coordinate to the constant `x` and the other coordinates to the coordinates of `𝔸ⁿ_{K⟦t⟧}` in
order. Mathematically (this is not formalised here), it identifies `𝔸ⁿ_{K⟦t⟧}` with the base
change `𝔸ⁿ⁺¹_S ×_{𝔸¹_S} Spec K⟦t⟧` of `𝔸ⁿ⁺¹_S` along the generic slice `Spec K⟦t⟧ ⟶ 𝔸¹_S` of
the `i`-th coordinate (`AlgebraicGeometry.traitSlice`), the completion of the strict localization
of `𝔸¹_S` at the generic point of its special fibre up to a purely inseparable extension of the
residue field.

On special fibres, `hᵢ` induces `hᵢ,ₛ : 𝔸ⁿ_K ⟶ 𝔸ⁿ⁺¹_{k'}`
(`AlgebraicGeometry.affineSpaceSliceSpecial`), the canonical morphism from the geometric generic
fibre `𝔸ⁿ⁺¹_{k'} ×_{𝔸¹_{k'}} Spec K` of the `i`-th coordinate projection. These are the slices
along which Deligne proves the finiteness of nearby cycles by induction on the relative dimension
(SGA 4½, [Th. finitude], proof of Thm. 3.2 and Lemme 3.3).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K] (n : ℕ) (i : Fin (n + 1))
  (x : K)

/-- The coordinates of the coordinate generic slice `hᵢ : 𝔸ⁿ_{K⟦t⟧} ⟶ 𝔸ⁿ⁺¹_S`: the constant `x`
in position `i`, and the coordinates of `𝔸ⁿ_{K⟦t⟧}` in the other positions. -/
noncomputable def affineSpaceSliceVector :
    ULift.{u} (Fin (n + 1)) → Γ(𝔸(ULift.{u} (Fin n); trait K), ⊤) :=
  fun j ↦ Fin.insertNth (α := fun _ ↦ Γ(𝔸(ULift.{u} (Fin n); trait K), ⊤)) i
    ((𝔸(ULift.{u} (Fin n); trait K) ↘ trait K).appTop
      ((Scheme.ΓSpecIso (.of (PowerSeries K))).inv (PowerSeries.C x)))
    (fun m ↦ AffineSpace.coord (trait K) (ULift.up m)) j.down

/-- The **coordinate generic slice** `hᵢ : 𝔸ⁿ_{K⟦t⟧} ⟶ 𝔸ⁿ⁺¹_S` (`S = Spec k'⟦t⟧`) over the trait
map `Spec K⟦t⟧ ⟶ S`: the `i`-th coordinate is the constant `x`, the others are the coordinates
of `𝔸ⁿ_{K⟦t⟧}`. -/
noncomputable def affineSpaceSlice :
    𝔸(ULift.{u} (Fin n); trait K) ⟶ 𝔸(ULift.{u} (Fin (n + 1)); trait k') :=
  AffineSpace.homOfVector (𝔸(ULift.{u} (Fin n); trait K) ↘ trait K ≫ traitMap k' K)
    (affineSpaceSliceVector n i x)

/-- The coordinate generic slice lies over the trait map `Spec K⟦t⟧ ⟶ Spec k'⟦t⟧`. -/
@[reassoc (attr := simp)]
lemma affineSpaceSlice_over :
    affineSpaceSlice n i x ≫ 𝔸(ULift.{u} (Fin (n + 1)); trait k') ↘ trait k' =
      𝔸(ULift.{u} (Fin n); trait K) ↘ trait K ≫ traitMap k' K :=
  AffineSpace.homOfVector_over _ _

/-- The special fibre `𝔸ⁿ_{K⟦t⟧} ×_{Spec K⟦t⟧} Spec K` of `𝔸ⁿ_{K⟦t⟧}` lies over the special
fibre of `𝔸ⁿ⁺¹_S` through the coordinate generic slice. -/
@[reassoc]
lemma affineSpaceSliceSpecial_w :
    pullback.fst (𝔸(ULift.{u} (Fin n); trait K) ↘ trait K) (traitClosedPoint K) ≫
        affineSpaceSlice n i x ≫ 𝔸(ULift.{u} (Fin (n + 1)); trait k') ↘ trait k' =
      (pullback.snd (𝔸(ULift.{u} (Fin n); trait K) ↘ trait K) (traitClosedPoint K) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k' K))) ≫ traitClosedPoint k' := by
  rw [affineSpaceSlice_over, pullback.condition_assoc, Category.assoc,
    traitClosedPoint_traitMap]

/-- The **coordinate generic slice of the special fibre** `hᵢ,ₛ : 𝔸ⁿ_K ⟶ 𝔸ⁿ⁺¹_{k'}`: the
morphism of special fibres `𝔸ⁿ_{K⟦t⟧} ×_{Spec K⟦t⟧} Spec K ⟶ 𝔸ⁿ⁺¹_S ×_S Spec k'` induced by the
coordinate generic slice `hᵢ`. -/
noncomputable def affineSpaceSliceSpecial :
    pullback (𝔸(ULift.{u} (Fin n); trait K) ↘ trait K) (traitClosedPoint K) ⟶
      pullback (𝔸(ULift.{u} (Fin (n + 1)); trait k') ↘ trait k') (traitClosedPoint k') :=
  pullback.lift (pullback.fst _ _ ≫ affineSpaceSlice n i x)
    (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap k' K)))
    (by rw [Category.assoc, affineSpaceSliceSpecial_w])

/-- The special-fibre slice is compatible with the inclusions of the special fibres. -/
@[reassoc (attr := simp)]
lemma affineSpaceSliceSpecial_fst :
    affineSpaceSliceSpecial (k' := k') n i x ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ affineSpaceSlice n i x :=
  pullback.lift_fst _ _ _

/-- The special-fibre slice lies over the map `Spec K ⟶ Spec k'` of the closed points. -/
@[reassoc (attr := simp)]
lemma affineSpaceSliceSpecial_snd :
    affineSpaceSliceSpecial (k' := k') n i x ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap k' K)) :=
  pullback.lift_snd _ _ _

end AlgebraicGeometry
