/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth
public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingCompositionLaw
public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingSmooth

/-!

# The dualizing map of the projective line over the trait

The dualizing map `θ_{ℙ¹_S} : Ψ ω_{ℙ¹_η} ⟶ ω_{ℙ¹_{k'}}` of the projective line over the trait
(`NearbyCyclesModel.projectiveLineModel`) is an isomorphism
(`NearbyCyclesModel.NearbyDualizingDataOfGenericBase.isIso_θ_projectiveLineModel`): `ℙ¹_S` is
smooth and proper of relative dimension one with full geometric generic fibre, so
`NearbyCyclesModel.NearbyDualizingDataOfGenericBase.isIso_θ_of_smooth` applies.

## Proper target models and coordinates

`NearbyCyclesModel.exists_twist_of_composition_law_of_isIso` deduces the twist equation of the
generic slice for a model `M` from a morphism of models `M ⟶ P` to a smooth model `P` carrying the
coordinate, through the composition law
`NearbyCyclesModel.NearbyDualizingDataOfGenericBase.θ_comp_law`, which needs `M` and `P` proper
over the trait `S`. No such `P` gives a non-trivial slice: if `P` is proper over `S` with a
coordinate `b : P ⟶ 𝔸¹_S` over `S`, the images of the fibres `P_η`, `P_s` in `𝔸¹_η`, `𝔸¹_{k'}`
are closed and proper over the field, hence finite sets of closed points, while the generic slice
`Spec K⟦t⟧ ⟶ 𝔸¹_S` (`x ↦ X`, `X` transcendental over `k'⟦t⟧`) hits the generic points of `𝔸¹_η`
and of `𝔸¹_{k'}`. So the generic slices of `P` (and of every proper `M` whose coordinate factors
through `P`) are empty. The candidates `ℙ¹_S ×_S 𝔸¹_S = ℙ¹_{𝔸¹_S}` (coordinate the second
projection) are not proper over `S`, and `ℙ¹_S ×_S ℙ¹_S` has no coordinate; restricting to its
open `ℙ¹ × 𝔸¹` does not help, as
`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_iso_map_θ_eq_twist_of_openSubmodel` passes the
twist equation from a model *with* a coordinate to its open sub-models, not from an open
sub-model to a proper model without one. The composition-law route needs a version of
`θ_comp_law` for models proper relative to `𝔸¹_S` (e.g. `M ⟶ ℙ¹_{𝔸¹_S}` proper), which is not
available: the dualizing maps are characterized through the traces of the proper fibres.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme ProjectiveSpace

namespace NearbyCyclesModel

/-- The structure morphism of `ℙ¹_K` over `Spec K` is smooth of relative dimension one. -/
instance smoothOfRelativeDimension_toPoint_overProjectiveLine_point (K : Type u) [Field K] :
    SmoothOfRelativeDimension 1 (toPoint (overProjectiveLine (point K))).left := by
  rw [toPoint_left]
  change SmoothOfRelativeDimension 1 (ProjectiveLine (Spec (.of K)) ↘ Spec (.of K) ≫ 𝟙 _)
  rw [Category.comp_id]
  infer_instance

variable {k' : Type u} [Field k'] {ℓ : ℕ} [Fact ℓ.Prime] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [Fact (ringChar (FractionRing (PowerSeries k'))).Prime]
  [Fact (ringChar (FractionRing (PowerSeries k')) ≠ ℓ)]

/-- **The dualizing map of the projective line over the trait is an isomorphism**: `ℙ¹_S` is
smooth and proper of relative dimension one over the trait, with full geometric generic fibre
(`NearbyCyclesModel.isPullback_projectiveLineModel_ε`), so
`NearbyCyclesModel.NearbyDualizingDataOfGenericBase.isIso_θ_of_smooth` applies. -/
theorem NearbyDualizingDataOfGenericBase.isIso_θ_projectiveLineModel
    (D : NearbyDualizingDataOfGenericBase k' ℓ) :
    IsIso (D.θ (isTraitModelOfGenericBase_projectiveLineModel k')) :=
  D.isIso_θ_of_smooth (isTraitModelOfGenericBase_projectiveLineModel k') 1
    (isPullback_projectiveLineModel_ε k')

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
