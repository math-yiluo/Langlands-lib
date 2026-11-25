/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.AffineSpaceSliceModel
public import WeilConjectures.TraceFormula.Specialization.AffineSpaceSliceCartesian
public import WeilConjectures.Compactification.AffineCharts
public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.BasicCharts
public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.Coordinates

/-!

# The standard model of `ℙⁿ` over the trait and its affine charts

Let `S = Spec k'⟦t⟧`. The standard model of the relative projective space `P = ℙⁿ_S`
(`NearbyCyclesModel.projectiveSpaceModel`) is a proper model over the trait. Its affine charts
`eₐ : 𝔸ⁿ_S ⟶ ℙⁿ_S` (`AlgebraicGeometry.AffineSpace.toRelativeProjectiveSpaceChart`) are open
immersions over `S`, hence morphisms of geometric models from the standard model of `𝔸ⁿ_S`
(`NearbyCyclesModel.projectiveSpaceChartHom`), with maps of special fibres
`eₐ,ₛ : 𝔸ⁿ_{k'} ⟶ ℙⁿ_{k'}` (`NearbyCyclesModel.projectiveSpaceChartSpecial`).

Every non-closed point of the special fibre `ℙⁿ⁺¹_{k'}` is the image, under a chart `eₐ,ₛ`, of a
point of a coordinate generic slice `hᵢ,ₛ : 𝔸ⁿ_K ⟶ 𝔸ⁿ⁺¹_{k'}` (`K = k'(x)^alg`,
`NearbyCyclesModel.affineSpaceSliceSpecialFibre`)
(`NearbyCyclesModel.exists_projectiveSpaceChartSpecial_affineSpaceSliceSpecialFibre_eq`): the
charts cover `ℙⁿ⁺¹`, a non-closed point of `ℙⁿ⁺¹_{k'}` has a non-closed preimage in a chart, a
non-closed point of `𝔸ⁿ⁺¹_{k'}` has a coordinate sending it to the generic point of `𝔸¹_{k'}`
(`AlgebraicGeometry.AffineSpace.exists_isGenericPoint_reindex_of_not_isClosed`), and the
coordinate generic slice is the base change of that coordinate along the generic point
(`AlgebraicGeometry.isPullback_affineSpaceSlice`).

These are the charts and slices of the global step of Deligne's proof of the finiteness of nearby
cycles (SGA 4½, [Th. finitude], proof of 3.2).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable (k' : Type u) [Field k']

/-- The structure morphism `ℙⁿ_S ⟶ S` of the relative projective space over the trait
`S = Spec k'⟦t⟧`, with homogeneous coordinates indexed by `Option (Fin n)`. -/
noncomputable abbrev projectiveSpaceStructure (n : ℕ) :
    ℙ(Option (ULift.{u} (Fin n)); trait k') ⟶ trait k' :=
  ℙ(Option (ULift.{u} (Fin n)); trait k') ↘ trait k'

/-- The standard model of the relative projective space `ℙⁿ_S` over the trait. -/
noncomputable abbrev projectiveSpaceModel (n : ℕ) :=
  traitStdModel (projectiveSpaceStructure k' n)

/-- The map of special fibres `𝔸ⁿ_{k'} ⟶ ℙⁿ_{k'}` of the affine chart `eₐ : 𝔸ⁿ_S ⟶ ℙⁿ_S`. -/
noncomputable def projectiveSpaceChartSpecial (n : ℕ) (a : Option (ULift.{u} (Fin n))) :
    (traitStdSpecialFibre (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k')).left ⟶
      (traitStdSpecialFibre (projectiveSpaceStructure k' n)).left :=
  traitStdSpecialHom (M := affineSpaceModel k' n) (projectiveSpaceStructure k' n)
    (IsPullback.of_hasPullback (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k') (traitClosedPoint k'))
    (AffineSpace.toRelativeProjectiveSpaceChart (trait k') a)
    (AffineSpace.toRelativeProjectiveSpaceChart_over (trait k') a)

/-- The **affine chart** `eₐ : 𝔸ⁿ_S ⟶ ℙⁿ_S` as a morphism of geometric models from the standard
model of `𝔸ⁿ_S` to that of `ℙⁿ_S`. -/
noncomputable def projectiveSpaceChartHom (n : ℕ) (a : Option (ULift.{u} (Fin n))) :
    (affineSpaceModel k' n).geometric.Hom (projectiveSpaceModel k' n).geometric
      (AffineSpace.toRelativeProjectiveSpaceChart (trait k') a)
      (projectiveSpaceChartSpecial k' n a) :=
  traitStdHom (M := affineSpaceModel k' n) (projectiveSpaceStructure k' n)
    (IsPullback.of_hasPullback (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k') (traitGenericPoint k'))
    (IsPullback.of_hasPullback (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k') (traitClosedPoint k'))
    (AffineSpace.toRelativeProjectiveSpaceChart (trait k') a)
    (AffineSpace.toRelativeProjectiveSpaceChart_over (trait k') a)

/-- **The charts and the coordinate generic slices reach the non-closed points**: every
non-closed point of the special fibre `ℙⁿ⁺¹_{k'}` is the image of a point of the special fibre
`𝔸ⁿ_K` of a coordinate generic slice under `eₐ,ₛ ∘ hᵢ,ₛ`, for some chart `a` and coordinate `i`. -/
theorem exists_projectiveSpaceChartSpecial_affineSpaceSliceSpecialFibre_eq (n : ℕ)
    (x : (traitStdSpecialFibre (projectiveSpaceStructure k' (n + 1))).left)
    (hx : ¬ IsClosed ({x} : Set
      (traitStdSpecialFibre (projectiveSpaceStructure k' (n + 1))).left)) :
    ∃ (a : Option (ULift.{u} (Fin (n + 1)))) (i : Fin (n + 1))
      (w : (traitStdSpecialFibre (𝔸(ULift.{u} (Fin n); trait (traitSliceField k')) ↘
        trait (traitSliceField k'))).left),
      projectiveSpaceChartSpecial k' (n + 1) a (affineSpaceSliceSpecialFibre k' n i w) = x := by
  classical
  have hcl : IsClosedImmersion (traitClosedPoint k') :=
    IsClosedImmersion.spec_of_surjective _ fun a ↦ ⟨PowerSeries.C a, by simp⟩
  -- A chart through `x`.
  obtain ⟨a, y₀, hy₀⟩ := AffineSpace.exists_mem_range_toRelativeProjectiveSpaceChart (trait k')
    (pullback.fst (projectiveSpaceStructure k' (n + 1)) (traitClosedPoint k') x)
  have hsq := isPullback_traitStdHom_special (M := affineSpaceModel k' (n + 1))
    (projectiveSpaceStructure k' (n + 1))
    (IsPullback.of_hasPullback (𝔸(ULift.{u} (Fin (n + 1)); trait k') ↘ trait k')
      (traitClosedPoint k'))
    (AffineSpace.toRelativeProjectiveSpaceChart (trait k') a)
    (AffineSpace.toRelativeProjectiveSpaceChart_over (trait k') a)
  obtain ⟨y', hy'₁, hy'₂⟩ := Scheme.Pullback.exists_preimage_pullback y₀ x hy₀
  set y := hsq.isoPullback.inv y' with hydef
  have hyx : projectiveSpaceChartSpecial k' (n + 1) a y = x := by
    rw [← hy'₂, hydef, ← Scheme.Hom.comp_apply]
    exact congr($(hsq.isoPullback_inv_snd) y')
  -- The point `y` of the chart is not closed.
  have : IsOpenImmersion (projectiveSpaceChartSpecial k' (n + 1) a) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hsq inferInstance
  have : JacobsonSpace (traitStdSpecialFibre (projectiveSpaceStructure k' (n + 1))).left :=
    LocallyOfFiniteType.jacobsonSpace
      (pullback.snd (projectiveSpaceStructure k' (n + 1)) (traitClosedPoint k'))
  have hy : ¬ IsClosed ({y} : Set _) := by
    rw [← hyx] at hx
    exact not_isClosed_singleton_of_isOpenImmersion (projectiveSpaceChartSpecial k' (n + 1) a) hx
  -- A coordinate sending `y` to the generic point of `𝔸¹_{k'}`.
  have hA := AffineSpace.isPullback_map (n := ULift.{u} (Fin (n + 1))) (traitClosedPoint k')
  obtain ⟨i, hi⟩ := AffineSpace.exists_isGenericPoint_reindex_of_not_isClosed hA.isoPullback.inv hy
  set c := traitSliceCoord k'
  set p := IsLocalRing.closedPoint (traitSliceField k')
  have hcoord : affineSpaceCoordinate k' n i.down
      (pullback.fst (𝔸(ULift.{u} (Fin (n + 1)); trait k') ↘ trait k') (traitClosedPoint k') y) =
      traitSlice c (traitClosedPoint (traitSliceField k') p) := by
    have h₁ : pullback.fst (𝔸(ULift.{u} (Fin (n + 1)); trait k') ↘ trait k')
        (traitClosedPoint k') ≫ affineSpaceCoordinate k' n i.down =
        hA.isoPullback.inv ≫ AffineSpace.reindex (fun _ : ULift.{u} (Fin 1) ↦ i) _ ≫
          AffineSpace.map _ (traitClosedPoint k') := by
      rw [← AffineSpace.map_reindex, hA.isoPullback_inv_fst_assoc]
      rfl
    rw [← Scheme.Hom.comp_apply, h₁, ← Category.assoc, Scheme.Hom.comp_apply,
      hi.eq (isGenericPoint_traitSlicePoint_traitSliceCoord k' p), ← Scheme.Hom.comp_apply,
      ← traitClosedPoint_traitSlice, Scheme.Hom.comp_apply]
  -- The coordinate generic slice reaches `y`.
  have hsl := isPullback_affineSpaceSlice (k' := k') n i.down c
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback _ _ hcoord
  set w₀ := hsl.isoPullback.inv z with hw₀
  have hw₀₁ : affineSpaceSlice n i.down c w₀ =
      pullback.fst (𝔸(ULift.{u} (Fin (n + 1)); trait k') ↘ trait k') (traitClosedPoint k') y := by
    rw [← hz₁, hw₀, ← Scheme.Hom.comp_apply, hsl.isoPullback_inv_fst]
  have hw₀₂ : (𝔸(ULift.{u} (Fin n); trait (traitSliceField k')) ↘ trait (traitSliceField k'))
      w₀ = traitClosedPoint (traitSliceField k') p := by
    rw [← hz₂, hw₀, ← Scheme.Hom.comp_apply, hsl.isoPullback_inv_snd]
  obtain ⟨w, hw₁, -⟩ := Scheme.Pullback.exists_preimage_pullback _ _ hw₀₂
  refine ⟨a, i.down, w, ?_⟩
  rw [← hyx]
  congr 1
  refine (pullback.fst (𝔸(ULift.{u} (Fin (n + 1)); trait k') ↘ trait k')
    (traitClosedPoint k')).isClosedEmbedding.injective ?_
  rw [← hw₀₁, ← hw₁]
  exact congr($(affineSpaceSliceSpecial_fst (k' := k') n i.down c) w)

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
