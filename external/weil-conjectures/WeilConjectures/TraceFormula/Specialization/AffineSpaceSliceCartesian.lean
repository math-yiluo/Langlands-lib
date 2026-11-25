/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.AffineSpaceSlice

/-!

# The coordinate generic slice is cartesian

For a coordinate `i : Fin (n + 1)`, let `πᵢ : 𝔸ⁿ⁺¹_S ⟶ 𝔸¹_S` be the `i`-th coordinate projection
over `S = Spec k'⟦t⟧` (`AlgebraicGeometry.affineSpaceCoordinate`). The coordinate generic slice
`hᵢ : 𝔸ⁿ_{K⟦t⟧} ⟶ 𝔸ⁿ⁺¹_S` (`AlgebraicGeometry.affineSpaceSlice`) identifies `𝔸ⁿ_{K⟦t⟧}` with the
base change of `πᵢ` along the generic slice `σ : Spec K⟦t⟧ ⟶ 𝔸¹_S`
(`AlgebraicGeometry.traitSlice`): the square
```
𝔸ⁿ_{K⟦t⟧} ──hᵢ──→ 𝔸ⁿ⁺¹_S
    │                │ πᵢ
Spec K⟦t⟧ ───σ───→ 𝔸¹_S
```
is cartesian (`AlgebraicGeometry.isPullback_affineSpaceSlice`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]

variable (k') in
/-- The `i`-th coordinate projection `πᵢ : 𝔸ⁿ⁺¹_S ⟶ 𝔸¹_S` over `S = Spec k'⟦t⟧`. -/
noncomputable def affineSpaceCoordinate (n : ℕ) (i : Fin (n + 1)) :
    𝔸(ULift.{u} (Fin (n + 1)); trait k') ⟶ 𝔸(ULift.{u} (Fin 1); trait k') :=
  AffineSpace.homOfVector (𝔸(ULift.{u} (Fin (n + 1)); trait k') ↘ trait k')
    fun _ ↦ AffineSpace.coord (trait k') (ULift.up i)

@[reassoc (attr := simp)]
lemma affineSpaceCoordinate_over (n : ℕ) (i : Fin (n + 1)) :
    affineSpaceCoordinate k' n i ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' =
      𝔸(ULift.{u} (Fin (n + 1)); trait k') ↘ trait k' :=
  AffineSpace.homOfVector_over _ _

instance (n : ℕ) (i : Fin (n + 1)) : LocallyOfFiniteType (affineSpaceCoordinate k' n i) := by
  have : LocallyOfFiniteType (affineSpaceCoordinate k' n i ≫
      𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k') := by
    rw [affineSpaceCoordinate_over]
    infer_instance
  exact locallyOfFiniteType_of_comp _ (𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k')

instance (n : ℕ) (i : Fin (n + 1)) : QuasiCompact (affineSpaceCoordinate k' n i) := by
  have : QuasiCompact (affineSpaceCoordinate k' n i ≫
      𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k') := by
    rw [affineSpaceCoordinate_over]
    infer_instance
  exact QuasiCompact.of_comp _ (𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k')

instance (n : ℕ) (i : Fin (n + 1)) : IsSeparated (affineSpaceCoordinate k' n i) := by
  have : IsSeparated (affineSpaceCoordinate k' n i ≫
      𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k') := by
    rw [affineSpaceCoordinate_over]
    infer_instance
  exact IsSeparated.of_comp _ (𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k')

/-- The map on global sections of a composite, evaluated at a section. -/
lemma Scheme.Hom.comp_appTop_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (s : Γ(Z, ⊤)) : (f ≫ g).appTop s = f.appTop (g.appTop s) :=
  rfl

/-- The coordinate of the generic slice `σ` is the constant power series `x`. -/
lemma traitSlice_appTop_coord (x : K) (j : ULift.{u} (Fin 1)) :
    (traitSlice (k' := k') x).appTop (AffineSpace.coord (trait k') j) =
      (Scheme.ΓSpecIso (.of (PowerSeries K))).inv (PowerSeries.C x) := by
  rw [traitSlice, Scheme.Hom.comp_appTop_apply, AffineSpace.SpecIso_inv_appTop_coord,
    ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  simp [traitSliceRingHom]

/-- The coordinate of the `i`-th coordinate projection `πᵢ` is the `i`-th coordinate. -/
lemma affineSpaceCoordinate_appTop_coord (n : ℕ) (i : Fin (n + 1)) (j : ULift.{u} (Fin 1)) :
    (affineSpaceCoordinate k' n i).appTop (AffineSpace.coord (trait k') j) =
      AffineSpace.coord (trait k') (ULift.up i) :=
  AffineSpace.homOfVector_appTop_coord _ _ _

/-- The `i`-th coordinate of the coordinate generic slice is the generic slice: `πᵢ ∘ hᵢ = σ`
on `𝔸ⁿ_{K⟦t⟧}`. -/
@[reassoc]
lemma affineSpaceSlice_comp_affineSpaceCoordinate (n : ℕ) (i : Fin (n + 1)) (x : K) :
    affineSpaceSlice n i x ≫ affineSpaceCoordinate k' n i =
      𝔸(ULift.{u} (Fin n); trait K) ↘ trait K ≫ traitSlice x := by
  refine AffineSpace.hom_ext ?_ fun j ↦ ?_
  · rw [Category.assoc, affineSpaceCoordinate_over, affineSpaceSlice_over, Category.assoc,
      traitSlice_over]
  · rw [Scheme.Hom.comp_appTop_apply, Scheme.Hom.comp_appTop_apply,
      affineSpaceCoordinate_appTop_coord, traitSlice_appTop_coord, affineSpaceSlice,
      AffineSpace.homOfVector_appTop_coord, affineSpaceSliceVector, Fin.insertNth_apply_same]

/-- The inverse of the comparison map `𝔸ⁿ_{K⟦t⟧} ⟶ 𝔸ⁿ⁺¹_S ×_{πᵢ, 𝔸¹_S, σ} Spec K⟦t⟧`: the
coordinates are the coordinates of `𝔸ⁿ⁺¹_S` other than the `i`-th one. -/
noncomputable def affineSpaceSliceInv (n : ℕ) (i : Fin (n + 1)) (x : K) :
    pullback (affineSpaceCoordinate k' n i) (traitSlice x) ⟶ 𝔸(ULift.{u} (Fin n); trait K) :=
  AffineSpace.homOfVector (pullback.snd _ _) fun m ↦
    (pullback.fst (affineSpaceCoordinate k' n i) (traitSlice x)).appTop
      (AffineSpace.coord (trait k') (ULift.up (i.succAbove m.down)))

/-- The inverse comparison map lies over the projection to `Spec K⟦t⟧`. -/
@[reassoc (attr := simp)]
lemma affineSpaceSliceInv_over (n : ℕ) (i : Fin (n + 1)) (x : K) :
    affineSpaceSliceInv (k' := k') n i x ≫ 𝔸(ULift.{u} (Fin n); trait K) ↘ trait K =
      pullback.snd _ _ :=
  AffineSpace.homOfVector_over _ _

/-- The coordinates of the inverse comparison map. -/
lemma affineSpaceSliceInv_appTop_coord (n : ℕ) (i : Fin (n + 1)) (x : K)
    (m : ULift.{u} (Fin n)) :
    (affineSpaceSliceInv (k' := k') n i x).appTop (AffineSpace.coord (trait K) m) =
      (pullback.fst (affineSpaceCoordinate k' n i) (traitSlice x)).appTop
        (AffineSpace.coord (trait k') (ULift.up (i.succAbove m.down))) :=
  AffineSpace.homOfVector_appTop_coord _ _ _

/-- **The coordinate generic slice is cartesian**:
`𝔸ⁿ_{K⟦t⟧} = 𝔸ⁿ⁺¹_S ×_{πᵢ, 𝔸¹_S, σ} Spec K⟦t⟧`. -/
lemma isPullback_affineSpaceSlice (n : ℕ) (i : Fin (n + 1)) (x : K) :
    IsPullback (affineSpaceSlice n i x) (𝔸(ULift.{u} (Fin n); trait K) ↘ trait K)
      (affineSpaceCoordinate k' n i) (traitSlice x) := by
  have hsq : CommSq (affineSpaceSlice n i x) (𝔸(ULift.{u} (Fin n); trait K) ↘ trait K)
      (affineSpaceCoordinate k' n i) (traitSlice x) :=
    ⟨affineSpaceSlice_comp_affineSpaceCoordinate n i x⟩
  refine IsPullback.of_iso_pullback hsq ⟨pullback.lift _ _ hsq.w, affineSpaceSliceInv n i x,
    ?_, ?_⟩ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  · refine AffineSpace.hom_ext ?_ fun m ↦ ?_
    · rw [Category.assoc, affineSpaceSliceInv_over, pullback.lift_snd, Category.id_comp]
    · rw [Scheme.Hom.comp_appTop_apply, affineSpaceSliceInv_appTop_coord,
        ← Scheme.Hom.comp_appTop_apply, pullback.lift_fst, affineSpaceSlice,
        AffineSpace.homOfVector_appTop_coord, affineSpaceSliceVector,
        Fin.insertNth_apply_succAbove]
      rfl
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp]
      refine AffineSpace.hom_ext ?_ fun j ↦ ?_
      · rw [Category.assoc, affineSpaceSlice_over, affineSpaceSliceInv_over_assoc,
          ← traitSlice_over, ← pullback.condition_assoc, affineSpaceCoordinate_over]
      · obtain ⟨j⟩ := j
        rw [Scheme.Hom.comp_appTop_apply, affineSpaceSlice, AffineSpace.homOfVector_appTop_coord,
          affineSpaceSliceVector]
        rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨m, rfl⟩
        · rw [Fin.insertNth_apply_same, ← Scheme.Hom.comp_appTop_apply, affineSpaceSliceInv_over,
            ← affineSpaceCoordinate_appTop_coord n j (ULift.up 0), ← Scheme.Hom.comp_appTop_apply,
            pullback.condition, Scheme.Hom.comp_appTop_apply, traitSlice_appTop_coord]
        · rw [Fin.insertNth_apply_succAbove, affineSpaceSliceInv_appTop_coord]
    · rw [Category.assoc, pullback.lift_snd, affineSpaceSliceInv_over, Category.id_comp]

end AlgebraicGeometry
