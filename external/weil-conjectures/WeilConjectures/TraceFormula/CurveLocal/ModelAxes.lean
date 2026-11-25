/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CurveLocal.Model

/-!

# The axes of the strictly local model

The vertical axis `{y} × X` and the horizontal axis `X × {y}` of `X ×_k X` are the base changes of
the `k`-point `y` along the two projections (`CurveLocalModel.isPullback_vertical`,
`CurveLocalModel.isPullback_horizontal`). Hence a point of `T` lies on `V` (resp. `H`) if and
only if its first (resp. second) coordinate is `y`
(`CurveLocalModel.mem_range_v_iff`, `CurveLocalModel.mem_range_hH_iff`). Used in blueprint
`lemma-tangent-cones-on-cover` to see that `T' ∖ (G' ∪ V' ∪ H')` lies over the punctured curve
in both factors.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale.CurveLocalModel

open Scheme

variable {k : Type u} [Field k] [IsAlgClosed k] (M : CurveLocalModel k)

omit [IsAlgClosed k] in
/-- The vertical axis is the base change of `y` along the first projection. -/
lemma isPullback_vertical : IsPullback M.vertical M.f (pullback.fst M.f M.f) M.y := by
  have hr : IsPullback (pullback.fst M.f M.f) (pullback.snd M.f M.f) M.f M.f :=
    IsPullback.of_hasPullback _ _
  refine IsPullback.of_right ?_ ?_ hr.flip
  · have : M.vertical ≫ pullback.snd M.f M.f = 𝟙 M.X := by simp [vertical]
    rw [this]
    have hy : M.y ≫ M.f = 𝟙 _ := M.y_comp
    rw [hy]
    exact IsPullback.id_horiz M.f
  · simp [vertical]

omit [IsAlgClosed k] in
/-- The horizontal axis is the base change of `y` along the second projection. -/
lemma isPullback_horizontal : IsPullback M.horizontal M.f (pullback.snd M.f M.f) M.y := by
  have hr : IsPullback (pullback.fst M.f M.f) (pullback.snd M.f M.f) M.f M.f :=
    IsPullback.of_hasPullback _ _
  refine IsPullback.of_right ?_ ?_ hr
  · have : M.horizontal ≫ pullback.fst M.f M.f = 𝟙 M.X := by simp [horizontal]
    rw [this]
    have hy : M.y ≫ M.f = 𝟙 _ := M.y_comp
    rw [hy]
    exact IsPullback.id_horiz M.f
  · simp [horizontal]

omit [IsAlgClosed k] in
lemma range_y : Set.range M.y.base = {M.y.base (default : Spec (.of k))} := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    rw [Subsingleton.elim w default]
    rfl
  · rintro rfl
    exact ⟨_, rfl⟩

omit [IsAlgClosed k] in
lemma range_vertical :
    Set.range M.vertical.base = (pullback.fst M.f M.f).base ⁻¹' Set.range M.y.base := by
  rw [← M.isPullback_vertical.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, Set.range_eq_univ.2 M.isPullback_vertical.isoPullback.hom.surjective,
    Set.image_univ, Scheme.Pullback.range_fst]

omit [IsAlgClosed k] in
lemma range_horizontal :
    Set.range M.horizontal.base = (pullback.snd M.f M.f).base ⁻¹' Set.range M.y.base := by
  rw [← M.isPullback_horizontal.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, Set.range_eq_univ.2 M.isPullback_horizontal.isoPullback.hom.surjective,
    Set.image_univ, Scheme.Pullback.range_fst]

/-- A point of `T` lies on the vertical axis `V` if and only if its first coordinate is `y`. -/
lemma mem_range_v_iff (z : M.T) : z ∈ Set.range M.v.base ↔
    (pullback.fst M.f M.f).base (M.τ.base z) = M.y.base (default : Spec (.of k)) := by
  rw [Scheme.Pullback.range_snd, Set.mem_preimage, range_vertical, Set.mem_preimage, range_y,
    Set.mem_singleton_iff]

/-- A point of `T` lies on the horizontal axis `H` if and only if its second coordinate is `y`. -/
lemma mem_range_hH_iff (z : M.T) : z ∈ Set.range M.hH.base ↔
    (pullback.snd M.f M.f).base (M.τ.base z) = M.y.base (default : Spec (.of k)) := by
  rw [Scheme.Pullback.range_snd, Set.mem_preimage, range_horizontal, Set.mem_preimage, range_y,
    Set.mem_singleton_iff]

end AlgebraicGeometry.Etale.CurveLocalModel
