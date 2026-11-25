/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseSliceInputs

/-!

# The map of bases of a generic slice

For a trait model `M` over the generic base `(F, X₁, ι)` and a coordinate `b` of its total space,
the map `c : X₂ ⟶ X₁` from the base of the generic slice
(`NearbyCyclesModel.IsTraitModelOfGenericBase.genericSliceBaseMap`) is characterised by its
compatibility with the identifications `ε`, since the identification `ε` of the generic slice
model is an epimorphism
(`NearbyCyclesModel.IsTraitModelOfGenericBase.epi_genericSliceModel_ε`). Hence `c` is the
composite `X₂ ≅ 𝒳''_η ⟶ 𝒳_η ⟶ X₁ ×_F η ⟶ X₁` of the generic slice of the generic fibre, the
open immersion of the generic fibre and the projection
(`NearbyCyclesModel.IsTraitModelOfGenericBase.genericSliceBaseMap_eq`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

variable {F : Type u} [Field F] {k' : Type u} [Field k'] {X₁ : Over (Spec (.of F))}
  {X' : Over (Spec (.of k'))} {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
  {K : Type u} [Field K] [Algebra k' K] (x : K)

namespace IsTraitModelOfGenericBase

/-- The identification `ε` of the geometric generic fibre of the generic slice model is an
epimorphism: it is the faithfully flat inclusion `𝒳''_Ω ⟶ 𝒳''_η` followed by `𝒳''_η ≅ X₂`. -/
lemma epi_genericSliceModel_ε (h : M.IsTraitModelOfGenericBase X₁ ι q g)
    {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
    (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q) :
    Epi (genericSliceModel x hb).ε := by
  have := (isTraitModelOfGenericBase_genericSliceModel x hb
    h.isTraitModelOver).isTraitModelOver.epi_lift_traitGenericPointToSpec
  rw [genericSliceModel_ε]
  exact epi_comp' this inferInstance

/-- **The map of bases of a generic slice through the generic fibre**: for any
`w : 𝒳_η ⟶ X₁ ×_F η` with `𝒳_Ω ⟶ 𝒳_η ⟶ X₁` equal to `ε`, the map `c : X₂ ⟶ X₁`
(`NearbyCyclesModel.IsTraitModelOfGenericBase.genericSliceBaseMap`) is
`X₂ ≅ 𝒳''_η ⟶ 𝒳_η ⟶ X₁ ×_F η ⟶ X₁`. -/
lemma genericSliceBaseMap_eq {Z₁ : Over (Spec (.of F))} {Z' : Over (Spec (.of k'))}
    {P : NearbyCyclesModel Z₁.left Z'.left} {qP : P.total ⟶ trait k'}
    {gP : P.generic ⟶ Spec (.of (traitGenericField k'))}
    (hP : P.IsTraitModelOfGenericBase Z₁ ι qP gP) {bP : P.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
    (hbP : bP ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = qP)
    (w : pullback qP (traitGenericSpec k') ⟶ pullback Z₁.hom ι)
    (hw : genericFibreInclusion P qP gP hP.isTraitModelOver.isPullback_j.w ≫ w ≫
      pullback.fst _ _ = P.ε) :
    hP.genericSliceBaseMap x hbP = (genericSliceFibreIso x hbP).inv ≫
      genericSliceFibreMap x hbP ≫ w ≫ pullback.fst _ _ := by
  have := hP.epi_genericSliceModel_ε x hbP
  refine (cancel_epi (genericSliceModel x hbP).ε).1 ?_
  have key : pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ traitGenericPointToSpec K)
      (by rw [pullback.condition, Category.assoc, traitGenericPointToSpec_traitGenericSpec]) ≫
        genericSliceFibreMap x hbP =
      baseChangeGenericMap hP.isTraitModelOver bP hbP (traitSlice x) (traitSlice_over x) ≫
        genericFibreInclusion P qP gP hP.isTraitModelOver.isPullback_j.w := by
    apply pullback.hom_ext
    · simp
    · simp only [Category.assoc, genericSliceFibreMap_snd, pullback.lift_snd_assoc,
        genericFibreInclusion_snd, baseChangeGenericMap_g_assoc,
        traitGenericPointToSpec_traitGenericSpecMap]
  rw [hP.genericSliceModel_ε_comp_genericSliceBaseMap, genericSliceModel_ε, Category.assoc,
    Iso.hom_inv_id_assoc, reassoc_of% key, hw]

end IsTraitModelOfGenericBase

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
