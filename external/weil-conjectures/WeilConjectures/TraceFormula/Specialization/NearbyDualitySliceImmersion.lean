/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualityCompactification
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseSliceImmersion

/-!

# Nearby duality on a slice of a scheme embedded in affine space

Let `q : T ⟶ S` be a separated scheme of finite type over the strictly henselian trait
`S = Spec k'⟦t⟧`, with an immersion `c : T ⟶ 𝔸^r_S` over `S`, viewed as the generic standard
model of its generic fibre `T_η` (`NearbyCyclesModel.traitFibreModel`), and `b : T ⟶ 𝔸¹_S` a
coordinate. The slice compatibility of nearby duality
(`NearbyCyclesModel.isIso_map_sliceSpecialMap_nearbyDualityMapOfGenericBase`) has two hypotheses:
the twist equation of the dualizing maps along the slice, which holds because `T` is
quasi-projective over `S` (`NearbyCyclesModel.exists_twist_of_isImmersion`), and nearby duality for
the generic slice model, which holds by Gabber's theorem over generic bases
(`NearbyCyclesModel.isIso_nearbyDualityMapOfGenericBase_of_measure` for the transcendence-degree
measure `AlgebraicGeometry.genericBaseMeasure`). This file discharges both.

## Main results

* `NearbyCyclesModel.isIso_map_sliceSpecialMap_nearbyDualityMapOfGenericBase_traitFibreModel`:
  the pullback of `δ_{T,L}` to the special fibre of the slice of `T` along `b` is an isomorphism
  (blueprint `lemma-nearby-duality-slice`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

namespace NearbyCyclesModel

variable (ℓ : ℕ) [Fact ℓ.Prime] {k' : Type u} [Field k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] {T : Scheme.{u}} {q : T ⟶ trait k'}
  [LocallyOfFiniteType q] [QuasiCompact q] [IsSeparated q]

/-- **Duality for nearby cycles on a slice** (blueprint `lemma-nearby-duality-slice`, the
invertibility part of (E.17)): let `q : T ⟶ S` be a separated scheme of finite type over the
strictly henselian trait `S = Spec k'⟦t⟧` with an immersion `c : T ⟶ 𝔸^r_S` over `S`, viewed as
the generic standard model of its generic fibre (`NearbyCyclesModel.traitFibreModel`), and
`b : T ⟶ 𝔸¹_S` a coordinate. Then for every bounded constructible `L` on `T_η` the pullback of
the duality map `δ_{T,L}` to the special fibre `T''_s` of the generic slice of `T` along `b` is an
isomorphism.

This is `NearbyCyclesModel.isIso_map_sliceSpecialMap_nearbyDualityMapOfGenericBase` with its two
hypotheses discharged: the twist equation by quasi-projectivity of `T` over `S`
(`NearbyCyclesModel.exists_twist_of_isImmersion`, through the standard chart
`𝔸^r_S ⟶ ℙ^r_S`), and nearby duality for the generic slice model by Gabber's theorem over generic
bases (`NearbyCyclesModel.isIso_nearbyDualityMapOfGenericBase_of_measure`). -/
theorem isIso_map_sliceSpecialMap_nearbyDualityMapOfGenericBase_traitFibreModel
    (D : NearbyDualizingDataOfGenericBase k' ℓ) {ι : Type u} [Finite ι]
    (c : T ⟶ 𝔸(ι; trait k')) [IsImmersion c] (hc : c ≫ 𝔸(ι; trait k') ↘ trait k' = q)
    {b : T ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
    (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)
    (L : Dᵇc((traitGenericBase q).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (L((sliceSpecialMap (traitSliceCoord k')
        (isTraitModelOfGenericBase_traitFibreModel q).isTraitModelOver hb)^*⟦
          Profinite.padicAlgClRingObj ℓ⟧).map
      (nearbyDualityMapOfGenericBase ℓ D (isTraitModelOfGenericBase_traitFibreModel q) L).hom) := by
  have hT := isTraitModelOfGenericBase_traitFibreModel q
  have hTM := hT.isTraitModelOver
  have := hTM.locallyOfFiniteType_genericSliceBase (traitSliceCoord k') hb
  have := hTM.quasiCompact_genericSliceBase (traitSliceCoord k') hb
  have := hTM.isSeparated_genericSliceBase (traitSliceCoord k') hb
  have := hTM.locallyOfFiniteType_baseChangeSpecial_traitSlice (traitSliceCoord k') hb
  have := hTM.quasiCompact_baseChangeSpecial_traitSlice (traitSliceCoord k') hb
  have := hTM.isSeparated_baseChangeSpecial_traitSlice (traitSliceCoord k') hb
  let DK := Classical.choice (nonempty_nearbyDualizingDataOfGenericBase (traitSliceField k') ℓ)
  -- the twist equation, from the quasi-projectivity of `T` over `S`
  classical
  have hn : Nat.card (Option ι) = Nat.card ι + 1 := by
    have := Fintype.ofFinite ι
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_option]
  have he : (c ≫ AffineSpace.toRelativeProjectiveSpace ι (trait k')) ≫
      ℙ(Option ι; trait k') ↘ trait k' = q := by
    rw [Category.assoc, AffineSpace.toRelativeProjectiveSpace_over, hc]
  have H := exists_twist_of_isImmersion hb D DK hT (exists_isIso_genericFibre_traitFibreModel _)
    hn (c ≫ AffineSpace.toRelativeProjectiveSpace ι (trait k')) he
  -- nearby duality for the generic slice model, by Gabber's theorem over generic bases
  refine isIso_map_sliceSpecialMap_nearbyDualityMapOfGenericBase ℓ D DK hT hb H (fun L' ↦ ?_) L
  exact isIso_nearbyDualityMapOfGenericBase_of_measure ℓ genericBaseMeasure
    (fun j _ hj ↦ genericBaseMeasure_le_of_isOpenImmersion j hj)
    (fun h _ hb ↦ h.genericBaseMeasure_genericSliceBase_add_one_le hb
      (transcendental_traitSliceCoord _))
    DK _ L'

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
