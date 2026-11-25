/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethFiniteSupport

/-!

# The special fibre of a generic slice is a fibre of the special coordinate

For a model `M` of finite type over the trait `S = Spec k'⟦t⟧` with a coordinate
`b : 𝒳 ⟶ 𝔸¹_S` and a point `x ∈ K`, the special fibre `𝒳''_s` of the generic slice
`𝒳'' = 𝒳 ×_{𝔸¹_S} Spec K⟦t⟧` is the fibre product `𝒳_s ×_{𝔸¹_{k'}} Spec K` of the special
coordinate `b_s : 𝒳_s ⟶ 𝔸¹_{k'}` and of the point `x : Spec K ⟶ 𝔸¹_{k'}`
(`ProEtale.CondensedRing.NearbyCyclesModel.isPullback_sliceSpecialMap_traitSlicePoint`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]
  {X : Scheme.{u}} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

/-- The special fibre of the generic slice lies over the special coordinate: the map
`𝒳''_s ⟶ 𝒳_s ⟶ 𝔸¹_{k'}` is the projection to `Spec K` followed by the point `x`. -/
@[reassoc]
lemma sliceSpecialMap_specialCoordinate (x : K) (hM : M.IsTraitModelOver q g)
    {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
    (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q) :
    sliceSpecialMap x hM hb ≫ specialCoordinate hM b hb =
      pullback.snd _ _ ≫ traitSlicePoint x := by
  refine (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) (traitClosedPoint k')).hom_ext
    ?_ ?_
  · rw [Category.assoc, specialCoordinate_map, sliceSpecialMap, hM.isPullback_i.lift_fst_assoc,
      Category.assoc, pullback.condition, pullback.condition_assoc, traitClosedPoint_traitSlice,
      Category.assoc]
  · rw [Category.assoc, specialCoordinate_over, sliceSpecialMap, hM.isPullback_i.lift_snd,
      Category.assoc, traitSlicePoint_over]

/-- **The special fibre of a generic slice is a fibre of the special coordinate**: the square
formed by `𝒳''_s ⟶ 𝒳_s`, the special coordinate `b_s : 𝒳_s ⟶ 𝔸¹_{k'}`, the projection
`𝒳''_s ⟶ Spec K` and the point `x : Spec K ⟶ 𝔸¹_{k'}` is cartesian. It is obtained by pasting
the cartesian squares defining `𝒳''_s` and `𝒳''`, and cancelling the cartesian square of the
special coordinate (`IsTraitModelOver.isPullback_specialCoordinate`). -/
lemma isPullback_sliceSpecialMap_traitSlicePoint (x : K) (hM : M.IsTraitModelOver q g)
    {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
    (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q) :
    IsPullback (sliceSpecialMap x hM hb) (pullback.snd _ _) (specialCoordinate hM b hb)
      (traitSlicePoint x) := by
  refine IsPullback.of_right ?_ (sliceSpecialMap_specialCoordinate x hM hb)
    (hM.isPullback_specialCoordinate b hb)
  rw [sliceSpecialMap, hM.isPullback_i.lift_fst, ← traitClosedPoint_traitSlice]
  exact (IsPullback.of_hasPullback _ _).paste_horiz (IsPullback.of_hasPullback _ _)

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
