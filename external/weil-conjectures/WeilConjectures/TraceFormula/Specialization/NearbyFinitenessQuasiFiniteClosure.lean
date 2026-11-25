/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosedLocalization
public import WeilConjectures.TraceFormula.Specialization.NearbyFinitenessQuasiFinite

/-!

# Nearby cycles of lisse extensions supported on a closed subscheme quasi-finite over the trait

Let `S = Spec k'⟦t⟧` be the strictly henselian trait, `c : D ⟶ 𝔸ⁿ_S` a closed immersion, `W` an
open of `D`, `c' : E ⟶ W` a closed immersion and `L` a lisse sheaf on `E`. If `W` lies in the
range of a closed immersion `ι : D' ⟶ D` such that `ι ≫ c ≫ q : D' ⟶ S` is locally quasi-finite
(`q` the structure map of `𝔸ⁿ_S`), then `Ψ (Rc_* j_{W!} Rc'_* L)` is bounded constructible
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_lisse_of_locallyQuasiFinite`).

The proof: `K = j_{W!} Rc'_* L` vanishes on the open complement of the range of `ι`, so the unit
`K ⟶ Rι_* Lι^* K` is an isomorphism and `Rc_* K ≅ R(ι ≫ c)_* Lι^* K`; conclude by the
quasi-finite case
`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_of_locallyQuasiFinite_comp`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k']

variable [IsSepClosed k'] [Fact (ringChar k' ≠ ℓ)]

/-- **Nearby cycles of a lisse extension supported on a closed subscheme quasi-finite over the
trait**: if the open `W` of the closed subscheme `c : D ⟶ 𝔸ⁿ_S` lies in the range of a closed
immersion `ι : D' ⟶ D` with `D'` locally quasi-finite over the trait, then
`Ψ (Rc_* j_{W!} Rc'_* L)` is bounded constructible. The complex `K = j_{W!} Rc'_* L` vanishes off
the range of `ι`, so `Rc_* K ≅ R(ι ≫ c)_* Lι^* K`. -/
theorem boundedConstructible_nearbyCycles_affineSpace_lisse_of_locallyQuasiFinite (n : ℕ)
    (D : Scheme.{u}) (c : D ⟶ (affineSpaceModel k' n).total) [IsClosedImmersion c] (W : D.Opens)
    (E : Scheme.{u}) (c' : E ⟶ W) [IsClosedImmersion c']
    (L : Mod (Sheaf (Scheme.ProEt.topology E) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) E))
    (hL : IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicAlgClRingObj ℓ) E) L)
    {D' : Scheme.{u}} (ι : D' ⟶ D) [IsClosedImmersion ι] (hι : (W : Set D) ⊆ Set.range ι.base)
    (hqf : LocallyQuasiFinite (ι ≫ c ≫ (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k'))) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      (traitStdSpecialFibre (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k')).left)
      (((affineSpaceModel k' n).geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
        ((R((c)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
          (D((W.ι)_!open⟦Profinite.padicAlgClRingObj ℓ⟧).obj
            ((R((c')_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
              ((DerivedCategory.singleFunctor _ 0).obj L))))) := by
  let Λ := Profinite.padicAlgClRingObj ℓ
  let K := D((W.ι)_!open⟦Λ⟧).obj ((R((c')_*⟦Λ⟧)).obj
    ((DerivedCategory.singleFunctor _ 0).obj L))
  have hK : boundedConstructible _ K := boundedConstructible_lisseExtension_closed n D c W E c' L hL
  have : IsNoetherian (affineSpaceModel k' n).total :=
    (isTraitModel_affineSpaceModel (k' := k') n).isNoetherian_total
  have : TopologicalSpace.NoetherianSpace D := c.isClosedEmbedding.isInducing.noetherianSpace
  let U : D.Opens := ⟨(Set.range ι.base)ᶜ, ι.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have : TopologicalSpace.NoetherianSpace U := U.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact U.ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hU : Set.range U.ι.base = (Set.range ι.base)ᶜ := Scheme.Opens.range_ι U
  have hc : IsCompl (Set.range ι.base) (Set.range U.ι.base) := by
    rw [hU]
    exact isCompl_compl
  have hKU : IsZero ((L((U.ι)^*⟦Λ⟧)).obj K) :=
    isZero_leftDerivedUpperStar_obj_openImmersionLowerShriek_of_disjoint Λ W.ι U.ι
      (by
        rw [hU, Scheme.Opens.range_ι]
        exact Set.disjoint_compl_right_iff_subset.2 hι) _
  have := isIso_derivedUpperStarLowerStarAdjunction_unit_app_of_isZero Λ U.ι ι hc hKU
  refine (boundedConstructible _).prop_of_iso
    (((affineSpaceModel k' n).geometric.nearbyCycles Λ).mapIso
      ((rightDerivedLowerStarComp Λ ι c).symm.app _ ≪≫ (R((c)_*⟦Λ⟧)).mapIso
        (asIso ((derivedUpperStarLowerStarAdjunction Λ ι).unit.app K)).symm))
    (boundedConstructible_nearbyCycles_affineSpace_of_locallyQuasiFinite_comp n (ι ≫ c)
      (by rwa [Category.assoc])
      (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ ι K hK))

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
