/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.CartesianModelUnit
public import WeilConjectures.TraceFormula.Specialization.NearbyCartesianModel

/-!

# The slice exchange from the unit of the change of geometric generic fibre

For the coordinate slices of the affine space, the `toCart` hypothesis of
`NearbyCyclesModel.isSplitMono_pullbackExchange_app_affineSpaceSliceHom_of_cart'` reduces to the
splitting of the unit of the change of geometric generic fibre
(`NearbyCyclesModel.isSplitMono_pullbackExchange_app_affineSpaceSliceHom_of_unit`), by
`NearbyCyclesModel.Hom.isSplitMono_toCart_pullbackExchange_app_of_isSplitMono_unit`
(`WeilConjectures.SixFunctors.NearbyCycles.CartesianModelUnit`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {k' : Type u} [Field k'] {ℓ : ℕ} [Fact ℓ.Prime]

/-- **The slice exchange from the unit of the change of geometric generic fibre,
`ℚ̄_ℓ`-coefficients**: for a complex `B` on `𝔸ⁿ⁺¹_S`, the pullback exchange of the morphism of
models over the coordinate slice `hᵢ` is a split monomorphism at `B` provided
* the pullback exchange of the cartesian part `fromCart` is invertible at `B`, and
* the unit `G ⟶ Rg_* Lg^* G` of the change of geometric generic fibre
  `g : 𝔸ⁿ_{K⟦t⟧} ×_{K⟦t⟧} Spec Ω_K ⟶ 𝔸ⁿ_{K⟦t⟧} ×_S Spec Ω` is a split monomorphism at the
  restriction `G` of `B`. -/
theorem isSplitMono_pullbackExchange_app_affineSpaceSliceHom_of_unit (n : ℕ) (i : Fin (n + 1))
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (affineSpaceModel k' (n + 1)).total)
      Ab.{u + 1}) (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (affineSpaceModel k' (n + 1)).total))}
    (hfrom : IsIso (((affineSpaceSliceHom k' n i).fromCartesian.pullbackExchange
      (Profinite.padicAlgClRingObj ℓ)).app B))
    (hunit : IsSplitMono ((derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ)
      (affineSpaceSliceHom k' n i).toCartesian.generic).unit.app
        ((L(((affineSpaceSliceHom k' n i).cartesianModel.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
          B))) :
    IsSplitMono (((affineSpaceSliceHom k' n i).pullbackExchange
      (Profinite.padicAlgClRingObj ℓ)).app B) := by
  refine isSplitMono_pullbackExchange_app_affineSpaceSliceHom_of_cart' n i hfrom ?_
  have key := Hom.isSplitMono_toCart_pullbackExchange_app_of_isSplitMono_unit
    (Profinite.padicAlgClRingObj ℓ) (affineSpaceSliceHom k' n i)
  clear hfrom
  revert B
  exact_mod_proofs key

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
