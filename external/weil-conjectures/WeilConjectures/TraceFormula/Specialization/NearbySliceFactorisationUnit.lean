/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbySliceFactorisation
public import WeilConjectures.TraceFormula.Specialization.NearbySliceInvariants

/-!

# The slice exchange from the Galois part of the change of geometric generic fibre

If the change of geometric generic fibre `g = φ.toCartesian.generic` of a morphism of models
factors as
`g = r₁ ≫ q ≫ r₂` with `r₁`, `r₂` universal homeomorphisms, the pullback exchange of `φ.toCartesian`
is a split monomorphism at `C` as soon as the unit of `Lq^* ⊣ Rq_*` is a split monomorphism at
`Lr₂^* Lε'^* C` (`NearbyCyclesModel.Hom.isSplitMono_toCart_pullbackExchange_app_of_factor₃`).

For the coordinate slices `hᵢ` this applies to the factorisation
`g = r₁ ≫ q ≫ r₂` of `NearbyCyclesModel.affineSpaceSliceHom_toCart_generic_factor`, with `q` the
base change of the pro-Galois morphism `Spec L^sep ⟶ Spec L`: the slice exchange reduces to the
invertibility of the `fromCart` part and the splitting of the unit of `q`
(`NearbyCyclesModel.isSplitMono_pullbackExchange_app_affineSpaceSliceHom_of_galois`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

namespace NearbyCyclesModel

variable {k' : Type u} [Field k'] [IsSepClosed k']

/-- **The `toCart` part of the slice exchange from the Galois part**: for the coordinate slice
`hᵢ`, the pullback exchange of `toCart` is a split monomorphism at `C` as soon as the unit of
`Lq^* ⊣ Rq_*` is a split monomorphism at `Lr₂^* Lε'^* C`, for the factorisation
`g = r₁ ≫ q ≫ r₂` of `NearbyCyclesModel.affineSpaceSliceHom_toCart_generic_factor`. -/
theorem isSplitMono_toCart_pullbackExchange_app_affineSpaceSliceHom_of_galois (n : ℕ)
    (i : Fin (n + 1))
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (affineSpaceModel k' (n + 1)).total)
      Ab.{u + 1}) (condensedRingObj Λ (affineSpaceModel k' (n + 1)).total)))
    (hq : IsSplitMono ((derivedUpperStarLowerStarAdjunction Λ
      (affineSpaceSliceGaloisMap k' n i)).unit.app
        ((L((affineSpaceSliceThickening k' n i)^*⟦Λ⟧)).obj
          ((L(((affineSpaceSliceHom k' n i).cartesianModel.ε)^*⟦Λ⟧)).obj C)))) :
    IsSplitMono (((affineSpaceSliceHom k' n i).toCartesian.pullbackExchange Λ).app C) :=
  Hom.isSplitMono_toCart_pullbackExchange_app_of_factor₃ Λ _ C _ _ _
    (affineSpaceSliceHom_toCart_generic_factor n i) hq

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- **The slice exchange from the Galois part of the change of geometric generic fibre**: for a
complex `B` on `𝔸ⁿ⁺¹_S`, the pullback exchange of the morphism of models over the coordinate
slice `hᵢ` is a split monomorphism at `B` provided
* the pullback exchange of the cartesian part `fromCart` is invertible at `B`, and
* the unit of `Lq^* ⊣ Rq_*` is a split monomorphism at `Lr₂^* G`, where `G` is the restriction of
  `B` to `𝔸ⁿ_B ×_S Spec Ω`, `r₂ : Z₂ ⟶ 𝔸ⁿ_B ×_S Spec Ω` is the nilpotent thickening and
  `q : Z₁ ⟶ Z₂` the base change of the pro-Galois morphism `Spec L^sep ⟶ Spec L`
  (`NearbyCyclesModel.affineSpaceSliceGaloisMap`, `NearbyCyclesModel.affineSpaceSliceThickening`).

As in `NearbyCyclesModel.isSplitMono_pullbackExchange_app_affineSpaceSliceHom_of_cart'`, the
general statement is transported along the differing instance proofs with `exact_mod_proofs`. -/
theorem isSplitMono_pullbackExchange_app_affineSpaceSliceHom_of_galois (n : ℕ) (i : Fin (n + 1))
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (affineSpaceModel k' (n + 1)).total)
      Ab.{u + 1}) (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (affineSpaceModel k' (n + 1)).total))}
    (hfrom : IsIso (((affineSpaceSliceHom k' n i).fromCartesian.pullbackExchange
      (Profinite.padicAlgClRingObj ℓ)).app B))
    (hq : IsSplitMono ((derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ)
      (affineSpaceSliceGaloisMap k' n i)).unit.app
        ((L((affineSpaceSliceThickening k' n i)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
          ((L(((affineSpaceSliceHom k' n i).cartesianModel.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
            B)))) :
    IsSplitMono (((affineSpaceSliceHom k' n i).pullbackExchange
      (Profinite.padicAlgClRingObj ℓ)).app B) := by
  refine isSplitMono_pullbackExchange_app_affineSpaceSliceHom_of_cart' n i hfrom ?_
  have key := isSplitMono_toCart_pullbackExchange_app_affineSpaceSliceHom_of_galois
    (k' := k') (Profinite.padicAlgClRingObj ℓ) n i
  clear hfrom
  revert B
  exact_mod_proofs key

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
