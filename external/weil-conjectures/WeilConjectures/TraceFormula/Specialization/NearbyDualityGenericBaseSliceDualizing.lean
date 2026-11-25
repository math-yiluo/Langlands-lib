/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseSliceTwistIso

/-!

# The dualizing maps and generic slicing

The dualizing map of a trait model over a generic base restricts, along the slice exchange, to a
dualizing map of its generic slice which is the twist by `ℚ̄_ℓ(0)[2]` of the dualizing map of the
slice model (`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_genericSliceDualizingMap`,
blueprint `lemma-nearby-duality-slice--1`, "the twist (1)" and "the map `θ`"). It is deduced from
the twist equation `p^* θ_M ≫ v = α ≫ Ψ_{M''}(u) ≫ κ ≫ θ_{M''} ▷ T`, taken as a hypothesis (proved
for opens of compactified models embedded in an affine space over the trait in
`TraceFormula.Specialization.NearbyDualityGenericBaseSliceImmersion`): the duality maps are
compared by `CategoryTheory.Verdier.isIso_nearbyDualityMap_twist_comp_inv_iff` and the invariance
under inertia is `NearbyCyclesModel.NearbyDualizingDataOfGenericBase.autAction_comp_θ`, inertia
acting trivially on the twist.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

namespace NearbyCyclesModel


variable {F : Type u} [Field F] {k' : Type u} [Field k'] {X₁ : Over (Spec (.of F))}
  {X' : Over (Spec (.of k'))} {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
  (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
  [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [Fact (ringChar (traitSliceField k')).Prime] [Fact (ringChar (traitSliceField k') ≠ ℓ)]
  [Fact (ringChar (FractionRing (PowerSeries (traitSliceField k')))).Prime]
  [Fact (ringChar (FractionRing (PowerSeries (traitSliceField k'))) ≠ ℓ)]
  (h : M.IsTraitModelOfGenericBase X₁ ι q g) {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)
  [LocallyOfFiniteType (genericSliceBase (traitSliceCoord k') hb).hom]
  [QuasiCompact (genericSliceBase (traitSliceCoord k') hb).hom]
  [IsSeparated (genericSliceBase (traitSliceCoord k') hb).hom]
  [LocallyOfFiniteType (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
  [QuasiCompact (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
  [IsSeparated (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]

namespace IsTraitModelOfGenericBase

/-- **The twist equation** of the generic slice along a coordinate `b` (blueprint
`lemma-nearby-duality-slice--1`, the twist (1) and "the map `θ`"): there are identifications
`u : c^* ω_{X₁} ≅ ω_{X₂} ⊗ T` and `v : p^* ω_{X'} ≅ ω_{𝒳''_s} ⊗ T`, `T = ℚ̄_ℓ(0)[2]`, such that the
restriction of `p^* θ_M` along the slice exchange `α` is the twist of the dualizing map
`θ_{M''}` of the slice: `p^* θ_M ≫ v = α ≫ Ψ_{M''}(u) ≫ κ ≫ θ_{M''} ▷ T`. -/
def TwistEquation (D : NearbyDualizingDataOfGenericBase k' ℓ)
    (DK : NearbyDualizingDataOfGenericBase (traitSliceField k') ℓ) : Prop :=
  ∃ (u : (genericSliceUpperStar (traitSliceCoord k') ℓ h hb).obj (dualizingComplex ℓ X₁) ≅
      dualizingComplex ℓ (genericSliceBase (traitSliceCoord k') hb) ⊗
        boundedConstructibleTateTwist ℓ (genericSliceBase (traitSliceCoord k') hb) 0 2)
    (v : (sliceSpecialUpperStar (traitSliceCoord k') ℓ h hb).obj (dualizingComplex ℓ X') ≅
      dualizingComplex ℓ (baseChangeSpecial b (traitSlice (traitSliceCoord k'))) ⊗
        boundedConstructibleTateTwist ℓ (baseChangeSpecial b (traitSlice (traitSliceCoord k')))
          0 2),
    (sliceSpecialUpperStar (traitSliceCoord k') ℓ h hb).map (D.θ h) ≫ v.hom =
      (genericSliceExchange (traitSliceCoord k') ℓ h hb).app (dualizingComplex ℓ X₁) ≫
        (genericSliceNearbyCycles (traitSliceCoord k') ℓ h hb).map u.hom ≫
        (genericSliceTwistIso ℓ h hb _).hom ≫
        DK.θ (isTraitModelOfGenericBase_genericSliceModel (traitSliceCoord k') hb
          h.isTraitModelOver) ▷ _

/-- **The dualizing maps and generic slicing** (blueprint `lemma-nearby-duality-slice--1`, "the
map `θ`"). There is a dualizing map `θ : Ψ_{M''} c^* ω_{X₁} ⟶ p^* ω_{X'}` of the generic slice
model such that
* `θ` restricts `p^* θ_M` along the slice exchange: `p^* θ_M = θ ∘ α_{ω_{X₁}}`;
* the duality map for `θ` is an isomorphism wherever the duality map `δ_{M''}` of the slice model
  for the family `DK` is;
* `θ` is invariant under the automorphisms of the generic slice model which are the identity on
  its total space and act on `Spec Ω_K` over `η_K` (inertia acts trivially on `ℚ̄_ℓ(1)`).

It is `θ = Ψ_{M''}(u) ≫ κ ≫ θ_{M''} ▷ T ≫ v⁻¹` for identifications
`u : c^* ω_{X₁} ≅ ω_{X₂} ⊗ T` and `v : p^* ω_{X'} ≅ ω_{𝒳''_s} ⊗ T`, `T = ℚ̄_ℓ(0)[2]`, satisfying the
*twist equation* `H` (`NearbyCyclesModel.IsTraitModelOfGenericBase.TwistEquation`):
`p^* θ_M ≫ v = α ≫ Ψ_{M''}(u) ≫ κ ≫ θ_{M''} ▷ T` (for the opens used in the induction it is
`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_iso_map_θ_eq_twist_restrictOpen_of_immersion`);
the duality maps are
compared by `CategoryTheory.Verdier.isIso_nearbyDualityMap_of_iso_twist_iff` and the invariance
is `NearbyCyclesModel.NearbyDualizingDataOfGenericBase.autAction_comp_θ`. -/
theorem exists_genericSliceDualizingMap (D : NearbyDualizingDataOfGenericBase k' ℓ)
    (DK : NearbyDualizingDataOfGenericBase (traitSliceField k') ℓ)
    (H : h.TwistEquation ℓ hb D DK) :
    ∃ θ : (genericSliceNearbyCycles (traitSliceCoord k') ℓ h hb).obj
        ((genericSliceUpperStar (traitSliceCoord k') ℓ h hb).obj (dualizingComplex ℓ X₁)) ⟶
      (sliceSpecialUpperStar (traitSliceCoord k') ℓ h hb).obj (dualizingComplex ℓ X'),
      (sliceSpecialUpperStar (traitSliceCoord k') ℓ h hb).map (D.θ h) =
          (genericSliceExchange (traitSliceCoord k') ℓ h hb).app (dualizingComplex ℓ X₁) ≫ θ ∧
        (∀ A : Dᵇc((genericSliceBase (traitSliceCoord k') hb).left)⟦
            Profinite.padicAlgClRingObj ℓ⟧,
          IsIso (nearbyDualityMapOfGenericBase ℓ DK
            (isTraitModelOfGenericBase_genericSliceModel (traitSliceCoord k') hb
              h.isTraitModelOver) A) →
          IsIso (genericSliceDualityMap (traitSliceCoord k') ℓ h hb θ A)) ∧
        ∀ ψ : (genericSliceModel (traitSliceCoord k') hb).Hom
            (genericSliceModel (traitSliceCoord k') hb) (𝟙 _) (𝟙 _),
          ψ.total = 𝟙 _ →
          (∃ σ : Spec (.of (traitGenericField (traitSliceField k'))) ⟶
              Spec (.of (traitGenericField (traitSliceField k'))),
            σ ≫ traitGenericPointToSpec (traitSliceField k') =
                traitGenericPointToSpec (traitSliceField k') ∧
              ψ.generic ≫ pullback.snd _ _ = pullback.snd _ _ ≫ σ) →
            (genericSliceSelfAction (traitSliceCoord k') ℓ h hb ψ).app _ ≫ θ = θ := by
  obtain ⟨u, v, huv⟩ := H
  refine ⟨(genericSliceNearbyCycles (traitSliceCoord k') ℓ h hb).map u.hom ≫
    (genericSliceTwistIso ℓ h hb _).hom ≫ DK.θ (isTraitModelOfGenericBase_genericSliceModel
      (traitSliceCoord k') hb h.isTraitModelOver) ▷ _ ≫ v.inv,
    eq_comp_comp_comp_inv_of_comp_hom_eq v huv, fun A hA ↦ ?_, fun ψ hψ hσ ↦ ?_⟩
  · exact (Verdier.isIso_nearbyDualityMap_twist_comp_inv_iff _ (genericSliceTwistIso ℓ h hb)
      (fun x y ↦ boundedConstructibleTensorMap_natural _ x y)
      (fun f ↦ NearbyCyclesModel.zeroTwistIso_hom_naturality _ _ 2 f)
      (NearbyCyclesModel.zeroTwistIso_tensor _ _ 2)
      (isInvertible_boundedConstructibleTateTwist_zero ℓ _ 2)
      (isInvertible_boundedConstructibleTateTwist_zero ℓ _ 2) _ u v A).2 hA
  · obtain ⟨σ, hσ, hψσ⟩ := hσ
    exact Verdier.app_comp_twist_eq (genericSliceTwistIso ℓ h hb)
      (genericSliceSelfAction (traitSliceCoord k') ℓ h hb ψ)
      (NearbyCyclesModel.boundedConstructibleAutAction_app_comp_zeroTwistIso_hom _ _ ψ 2) _
      (DK.autAction_comp_θ _ ψ hψ σ hσ hψσ) u v

end IsTraitModelOfGenericBase

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
