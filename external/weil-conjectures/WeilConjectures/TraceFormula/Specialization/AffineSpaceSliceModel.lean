/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.AffineSpaceSlice
public import WeilConjectures.TraceFormula.Specialization.NearbyFinitenessCases
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethSlice
public import WeilConjectures.TraceFormula.Specialization.TraitBaseChangeModel

/-!

# The morphism of models over a coordinate generic slice

For `S = Spec k'⟦t⟧`, `K = k'(x)^alg` (`AlgebraicGeometry.traitSliceField`) and a coordinate `i`,
this file packages the coordinate generic slice `hᵢ : 𝔸ⁿ_{K⟦t⟧} ⟶ 𝔸ⁿ⁺¹_S`
(`AlgebraicGeometry.affineSpaceSlice`) as a morphism of the geometric standard models
(`NearbyCyclesModel.affineSpaceSliceHom`), with its maps of total spaces, special fibres and
geometric generic fibres. It is the slice along which Deligne proves the finiteness of nearby
cycles by induction on the relative dimension (SGA 4½, [Th. finitude], proof of Thm. 3.2).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {k' : Type u} [Field k']

variable (k') in
/-- The coordinate generic slice `hᵢ : 𝔸ⁿ_{K⟦t⟧} ⟶ 𝔸ⁿ⁺¹_S` (`K = k'(x)^alg`,
`AlgebraicGeometry.affineSpaceSlice`) as a morphism of the total spaces of the standard models. -/
noncomputable def affineSpaceSliceTotal (n : ℕ) (i : Fin (n + 1)) :
    (affineSpaceModel (traitSliceField k') n).total ⟶ (affineSpaceModel k' (n + 1)).total :=
  affineSpaceSlice n i (traitSliceCoord k')

variable (k') in
/-- The coordinate generic slice of the special fibre `hᵢ,ₛ : 𝔸ⁿ_K ⟶ 𝔸ⁿ⁺¹_{k'}`
(`AlgebraicGeometry.affineSpaceSliceSpecial`) as a morphism of the special fibres of the standard
models. -/
noncomputable def affineSpaceSliceSpecialFibre (n : ℕ) (i : Fin (n + 1)) :
    (traitStdSpecialFibre (𝔸(ULift.{u} (Fin n); trait (traitSliceField k')) ↘
      trait (traitSliceField k'))).left ⟶
      (traitStdSpecialFibre (𝔸(ULift.{u} (Fin (n + 1)); trait k') ↘ trait k')).left :=
  affineSpaceSliceSpecial n i (traitSliceCoord k')

variable (k') in
/-- The coordinate generic slice of the geometric generic fibres
`𝔸ⁿ_{K⟦t⟧} ×_{Spec K⟦t⟧} Spec Ω_K ⟶ 𝔸ⁿ⁺¹_S ×_S Spec Ω`, induced by `hᵢ` and the map
`Spec Ω_K ⟶ Spec Ω` (`AlgebraicGeometry.traitGenericPointMap`) of the geometric generic points of
`Spec K⟦t⟧` and `S`, with fields `Ω_K = (Frac K⟦t⟧)^alg` and `Ω = (Frac k'⟦t⟧)^alg`. -/
noncomputable def affineSpaceSliceGeneric (n : ℕ) (i : Fin (n + 1)) :
    (affineSpaceModel (traitSliceField k') n).generic ⟶
      (affineSpaceModel k' (n + 1)).generic :=
  pullback.lift (pullback.fst _ _ ≫ affineSpaceSliceTotal k' n i)
    (pullback.snd _ _ ≫ traitGenericPointMap k' (traitSliceField k')) (by
      rw [Category.assoc, affineSpaceSliceTotal, affineSpaceSlice_over, pullback.condition_assoc,
        Category.assoc, traitGenericPoint_traitMap])

variable (k') in
/-- The **morphism of geometric models over the coordinate generic slice** `hᵢ`: from the standard
model of `𝔸ⁿ_{K⟦t⟧}` over `Spec K⟦t⟧` to the standard model of `𝔸ⁿ⁺¹_S` over `S`, with the slices
`hᵢ` of the total spaces, `hᵢ,ₛ` of the special fibres, and of the geometric generic fibres. -/
@[simps]
noncomputable def affineSpaceSliceHom (n : ℕ) (i : Fin (n + 1)) :
    (affineSpaceModel (traitSliceField k') n).geometric.Hom
      (affineSpaceModel k' (n + 1)).geometric (affineSpaceSliceTotal k' n i)
      (affineSpaceSliceSpecialFibre k' n i) where
  total := affineSpaceSliceTotal k' n i
  generic := affineSpaceSliceGeneric k' n i
  comm_j := pullback.lift_fst _ _ _
  comm_i := affineSpaceSliceSpecial_fst _ _ _
  comm_ε := pullback.lift_fst _ _ _

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
