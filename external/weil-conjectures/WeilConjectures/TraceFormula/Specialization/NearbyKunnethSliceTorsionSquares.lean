/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethSliceTorsionProduct

/-!

# The change of trait to a generic slice trait for a product

Let `P` be the product over `S = Spec k'⟦t⟧` of models `M`, `N` of finite type, `b` a coordinate
of `M` and `D` a generic slice trait `S'` of `𝔸¹_S`. The geometric slice of `P` along `b` is the
product over `Spec K⟦t⟧` of the slice of `M` and the change of trait of `N`
(`NearbyCyclesModel.sliceFst`, `NearbyCyclesModel.sliceSnd`), and the slice of `P` over `S'` maps
to the slice of `M` over `S'` (`NearbyCyclesModel.coordinateSliceTraitMap`) and to `N`. This file
checks that the changes of trait `τ` to `S'` (`NearbyCyclesModel.coordinateSliceTraitChangeHom`)
of `M`, `P` and the change of trait `Spec K⟦t⟧ ⟶ S` of `N` are compatible with these two product
configurations, on the models of the geometric generic fibres: these are the hypotheses of the
Künneth square `NearbyCyclesModel.map_kunnethMap_comp_pullbackExchange`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {k' : Type u} [Field k'] {X Y Z : Scheme.{u}}
  {X' Y' Z' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {N : NearbyCyclesModel Y Y'.left} {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X}
  {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y} {f₂' : Z'.left ⟶ Y'.left} {φ₁ : P.Hom M f₁ f₁'}
  {φ₂ : P.Hom N f₂ f₂'} {qM : M.total ⟶ trait k'}
  {gM : M.generic ⟶ Spec (.of (traitGenericField k'))} {qN : N.total ⟶ trait k'}
  {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}
  (hM : M.IsTraitModelOver qM gM) (hN : N.IsTraitModelOver qN gN)
  (hpb : IsPullback φ₁.total φ₂.total qM qN)
  (hP : P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM))
  (hgen : φ₂.generic ≫ gN = φ₁.generic ≫ gM) {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = qM) (D : GenericSliceTrait k')

/-- The first projections commute with the changes of trait on total spaces. -/
lemma sliceFst_total_comp_coordinateSliceTraitChangeTotal :
    (sliceFst hM hP hb).toGeneric.total ≫ (coordinateSliceTraitChangeHom hM b hb D).total =
      (coordinateSliceTraitChangeHom hP (φ₁.total ≫ b) (comp_coordinate_fst hb) D).total ≫
        (coordinateSliceTraitMap φ₁ b D).total := by
  apply pullback.hom_ext <;> simp [coordinateSliceTraitChangeTotal]

/-- The first projections commute with the changes of trait on generic fibres. -/
lemma sliceFst_generic_comp_coordinateSliceTraitChangeGeneric :
    (sliceFst hM hP hb).generic ≫ coordinateSliceTraitChangeGeneric b D =
      coordinateSliceTraitChangeGeneric (φ₁.total ≫ b) D ≫
        coordinateSliceTraitMapGeneric φ₁ b D := by
  apply pullback.hom_ext
  · apply pullback.hom_ext <;>
      simp [coordinateSliceTraitChangeGeneric, coordinateSliceTraitChangeTotal]
  · simp [coordinateSliceTraitChangeGeneric]

/-- The first projections commute with the changes of trait on special fibres. -/
lemma sliceFst_special_comp_coordinateSliceTraitChangeSpecial :
    φ₁.baseChangeSpecial (bP := φ₁.total ≫ b) (bM := b) (vP := traitSlice (traitSliceCoord k'))
        (vM := traitSlice (traitSliceCoord k')) (𝟙 _) (Category.comp_id _) (Category.comp_id _) ≫
        coordinateSliceTraitChangeSpecial b D =
      coordinateSliceTraitChangeSpecial (φ₁.total ≫ b) D ≫
        coordinateSliceTraitMapSpecial φ₁ b D := by
  apply pullback.hom_ext
  · apply pullback.hom_ext <;>
      simp [coordinateSliceTraitChangeSpecial, coordinateSliceTraitChangeTotal,
        Hom.baseChangeSpecial]
  · simp [coordinateSliceTraitChangeSpecial, Hom.baseChangeSpecial]

/-- The second projection `P_{S'} ⟶ N` of the slice of the product over the generic slice
trait: the slice of `P` followed by `φ₂`. -/
noncomputable abbrev coordinateSliceTraitSnd :=
  (coordinateSliceTraitHom hP (φ₁.total ≫ b) (comp_coordinate_fst hb) D).comp φ₂.toGeneric

/-- The second projections commute with the changes of trait on total spaces. -/
lemma sliceSnd_total_comp_baseChangeHom_total :
    (sliceSnd hN hpb hP hgen hb).toGeneric.total ≫
        (baseChangeHom hN qN (Category.comp_id qN) (traitMap k' (traitSliceField k'))
          (Category.comp_id _)).toGeneric.total =
      (coordinateSliceTraitChangeHom hP (φ₁.total ≫ b) (comp_coordinate_fst hb) D).total ≫
        (coordinateSliceTraitSnd hP hb D (φ₂ := φ₂)).total := by
  simp [coordinateSliceTraitChangeTotal]

/-- The second projections commute with the changes of trait on generic fibres. -/
lemma sliceSnd_generic_comp_baseChangeGenericMap :
    (sliceSnd hN hpb hP hgen hb).generic ≫
        baseChangeGenericMap hN qN (Category.comp_id qN) (traitMap k' (traitSliceField k'))
          (Category.comp_id _) =
      coordinateSliceTraitChangeGeneric (φ₁.total ≫ b) D ≫
        (coordinateSliceTraitGeneric hP (φ₁.total ≫ b) (comp_coordinate_fst hb) D ≫
          φ₂.generic) := by
  refine hN.isPullback_j.hom_ext ?_ ?_
  · simp [coordinateSliceTraitChangeGeneric, coordinateSliceTraitGeneric,
      coordinateSliceTraitChangeTotal, φ₂.comm_j]
  · simp only [coordinateSliceTraitChangeGeneric, coordinateSliceTraitGeneric, Category.assoc,
      baseChangeGenericMap_g, hgen, IsPullback.lift_snd, pullback.lift_snd_assoc]
    rw [traitGenericPointMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, D.ωK_comp_ωS]
    simp

/-- The second projections commute with the changes of trait on special fibres. -/
lemma sliceSnd_special_comp_baseChangeSpecialMap :
    φ₂.baseChangeSpecial (bP := φ₁.total ≫ b) (bM := qN) (vP := traitSlice (traitSliceCoord k'))
        (vM := traitMap k' (traitSliceField k')) (𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k')
        (comp_coordinate_fst_eq hpb hb) (traitSlice_over (traitSliceCoord k')) ≫
        baseChangeSpecialMap hN qN (Category.comp_id qN) (traitMap k' (traitSliceField k'))
          (Category.comp_id _) =
      coordinateSliceTraitChangeSpecial (φ₁.total ≫ b) D ≫
        (coordinateSliceTraitSpecial hP (φ₁.total ≫ b) (comp_coordinate_fst hb) D ≫ f₂') := by
  refine hN.isPullback_i.hom_ext ?_ ?_
  · simp [coordinateSliceTraitChangeSpecial, coordinateSliceTraitSpecial,
      coordinateSliceTraitChangeTotal, Hom.baseChangeSpecial, φ₂.comm_i]
  · have hY : f₂' ≫ Y'.hom = Z'.hom := by
      rw [← cancel_mono (traitClosedPoint k'), Category.assoc, ← hN.isPullback_i.w,
        reassoc_of% φ₂.comm_i, ← hpb.w, hP.isPullback_i.w]
    simp only [Category.assoc, hY, coordinateSliceTraitSpecial, IsPullback.lift_snd,
      coordinateSliceTraitChangeSpecial, pullback.lift_snd_assoc, baseChangeSpecialMap,
      Hom.baseChangeSpecial, pullback.lift_snd_assoc, Category.comp_id]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, D.κK_comp_κS]

/-! ### The compatibilities in the form of the Künneth square -/

/-- `NearbyCyclesModel.sliceFst_generic_comp_coordinateSliceTraitChangeGeneric` in terms of the
morphisms of models. -/
lemma sliceFst_toGeneric_generic_comp_coordinateSliceTraitChangeHom_generic :
    (sliceFst hM hP hb).toGeneric.generic ≫ (coordinateSliceTraitChangeHom hM b hb D).generic =
      (coordinateSliceTraitChangeHom hP (φ₁.total ≫ b) (comp_coordinate_fst hb) D).generic ≫
        (coordinateSliceTraitMap φ₁ b D).generic := by
  rw [coordinateSliceTraitChangeHom_generic, coordinateSliceTraitChangeHom_generic,
    coordinateSliceTraitMap_generic]
  exact sliceFst_generic_comp_coordinateSliceTraitChangeGeneric hM hP hb D

/-- `NearbyCyclesModel.sliceSnd_generic_comp_baseChangeGenericMap` in terms of the morphisms of
models. -/
lemma sliceSnd_toGeneric_generic_comp_baseChangeHom_generic :
    (sliceSnd hN hpb hP hgen hb).toGeneric.generic ≫
        (baseChangeHom hN qN (Category.comp_id qN) (traitMap k' (traitSliceField k'))
          (Category.comp_id _)).toGeneric.generic =
      (coordinateSliceTraitChangeHom hP (φ₁.total ≫ b) (comp_coordinate_fst hb) D).generic ≫
        (coordinateSliceTraitSnd hP hb D (φ₂ := φ₂)).generic := by
  rw [coordinateSliceTraitChangeHom_generic, Hom.comp_generic, coordinateSliceTraitHom_generic]
  exact sliceSnd_generic_comp_baseChangeGenericMap hN hpb hP hgen hb D

/-- `NearbyCyclesModel.sliceSnd_generic_comp_baseChangeGenericMap` in terms of the maps of the
identified schemes. -/
lemma sliceSnd_generic_comp_baseChangeHom_generic :
    (sliceSnd hN hpb hP hgen hb).generic ≫
        (baseChangeHom hN qN (Category.comp_id qN) (traitMap k' (traitSliceField k'))
          (Category.comp_id _)).generic =
      coordinateSliceTraitChangeGeneric (φ₁.total ≫ b) D ≫
        (coordinateSliceTraitGeneric hP (φ₁.total ≫ b) (comp_coordinate_fst hb) D ≫
          φ₂.generic) :=
  sliceSnd_generic_comp_baseChangeGenericMap hN hpb hP hgen hb D

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
