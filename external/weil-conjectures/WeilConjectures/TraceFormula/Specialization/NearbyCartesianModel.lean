/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.CartesianModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.TraceFormula.Specialization.NearbyFinitenessSlice
public import WeilConjectures.TraceFormula.Specialization.NearbySmoothExchangeLocal
public import WeilConjectures.Tactic.ExactModProofs

/-!

# The cartesian factorization of a morphism of models: special cases

The cartesian factorization itself is `NearbyCyclesModel.Hom.cartesianModel`
(`WeilConjectures.SixFunctors.NearbyCycles.CartesianModel`).

Let `φ : M ⟶ N` be a morphism of models (`NearbyCyclesModel.Hom`) over `f : X ⟶ Y` and
`f' : X' ⟶ Y'`, with morphism of total spaces `t : 𝒳 ⟶ 𝒴`. The *cartesian model*
`NearbyCyclesModel.Hom.cartesianModel` of `φ` is the model of `Y` with special fibre `X'`,
total space `𝒳`, geometric generic fibre the base change `𝒴_η̄ ×_𝒴 𝒳` of the geometric generic
fibre of `N` along `t`, and identification `𝒴_η̄ ×_𝒴 𝒳 ⟶ 𝒴_η̄ ⟶ Y`. The morphism `φ` factors as
```
M ──toCartesian──> cartesianModel ──fromCartesian──> N
```
where `toCartesian` (over `f` and `𝟙 X'`) is the identity on total spaces, and `fromCartesian`
(over `𝟙 Y` and `f'`) has a cartesian square of geometric generic fibres
(`NearbyCyclesModel.Hom.isPullback_fromCartesian`).

By the composition law of pullback exchanges
(`NearbyCyclesModel.Hom.pullbackExchange_comp_app_of_eq`), the pullback exchange of `φ` is a
split monomorphism at `C` as soon as that of `fromCart` is invertible at `C` (a base change
statement for `Rj_*` along `t`) and that of `toCart` is a split monomorphism at `C` (a statement
about the change of geometric generic fibre over a fixed total space)
(`NearbyCyclesModel.Hom.isSplitMono_pullbackExchange_app_of_cartesian`). For the coordinate slices
of the affine space this is
`NearbyCyclesModel.isSplitMono_pullbackExchange_app_affineSpaceSliceHom_of_cart`, and with
`ℚ̄_ℓ`-coefficients
`NearbyCyclesModel.isSplitMono_pullbackExchange_app_affineSpaceSliceHom_of_cart'`.

If `Lε^* C = 0` every pullback exchange is invertible at `C`
(`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_isZero`); this settles the slice exchange
for complexes supported on the special fibre
(`NearbyCyclesModel.isSplitMono_pullbackExchange_app_affineSpaceSliceHom_rightDerivedLowerStar`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section General

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

namespace NearbyCyclesModel

variable {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'}

namespace Hom

variable (φ : M.Hom N f f')

/-- The pullback exchange of `φ.fromCartesian` is invertible at `C` if the base change morphism
`Lt^* Rj_{N*} ⟶ Rj'_* Lpr₁^*` of the cartesian square of `N.j` along the morphism `t` of total
spaces is invertible at `Lε_N^* C`. -/
theorem isIso_fromCart_pullbackExchange_app_of_isIso_baseChangeMap_app
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (hC : IsIso ((baseChangeMap Λ φ.fromCartesian.commSq_j).app ((L((N.ε)^*⟦Λ⟧)).obj C))) :
    IsIso ((φ.fromCartesian.pullbackExchange Λ).app C) :=
  φ.fromCartesian.isIso_pullbackExchange_app_of_isIso_baseChangeMap_app Λ C hC

/-- If `Lε_N^* C` vanishes, the pullback exchange of `φ` is invertible at `C`: the base change
morphism of the square of geometric generic fibres at `Lε_N^* C` is a morphism between zero
objects. -/
theorem isIso_pullbackExchange_app_of_isZero
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (hC : IsZero ((L((N.ε)^*⟦Λ⟧)).obj C)) :
    IsIso ((φ.pullbackExchange Λ).app C) := by
  refine φ.isIso_pullbackExchange_app_of_isIso_baseChangeMap_app Λ C ?_
  have h₁ := (R((N.j)_*⟦Λ⟧) ⋙ L((φ.total)^*⟦Λ⟧)).map_isZero hC
  have h₂ := (L((φ.generic)^*⟦Λ⟧) ⋙ R((M.j)_*⟦Λ⟧)).map_isZero hC
  exact ⟨⟨0, h₁.eq_of_src _ _, h₂.eq_of_src _ _⟩⟩

end Hom

end NearbyCyclesModel

end General

namespace NearbyCyclesModel

variable {k' : Type u} [Field k']

/-- **The slice exchange from the cartesian factorization**: for a complex `B` on `𝔸ⁿ⁺¹_S`, the
pullback exchange of the morphism of models over the coordinate slice `hᵢ`
(`NearbyCyclesModel.affineSpaceSliceHom`) is a split monomorphism at `B` provided
* the pullback exchange of the cartesian part `fromCart` is invertible at `B` (by
  `NearbyCyclesModel.Hom.isIso_fromCart_pullbackExchange_app_of_isIso_baseChangeMap_app`, this
  is base change of `Rj_*` along `hᵢ` at `Lε^* B`), and
* the pullback exchange of the change of geometric generic fibre `toCart` is a split
  monomorphism at `B`. -/
theorem isSplitMono_pullbackExchange_app_affineSpaceSliceHom_of_cart
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (n : ℕ) (i : Fin (n + 1))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (affineSpaceModel k' (n + 1)).total)
      Ab.{u + 1}) (condensedRingObj Λ (affineSpaceModel k' (n + 1)).total)))
    (hfrom : IsIso (((affineSpaceSliceHom k' n i).fromCartesian.pullbackExchange Λ).app B))
    (hto : IsSplitMono (((affineSpaceSliceHom k' n i).toCartesian.pullbackExchange Λ).app B)) :
    IsSplitMono (((affineSpaceSliceHom k' n i).pullbackExchange Λ).app B) :=
  (affineSpaceSliceHom k' n i).isSplitMono_pullbackExchange_app_of_cartesian Λ B hfrom hto

/-- **Complexes supported on the special fibre vanish on the geometric generic fibre**: for a
closed immersion `c : D ⟶ 𝔸ⁿ_S` and a complex `K` on `D` whose restriction to the generic fibre
`c⁻¹ 𝔸ⁿ_η` vanishes, `Lj^* Rc_* K = 0`, since `j : 𝔸ⁿ_η̄ ⟶ 𝔸ⁿ_S` factors through `𝔸ⁿ_η`. -/
lemma isZero_leftDerivedUpperStar_j_affineSpaceModel_obj_rightDerivedLowerStar_obj
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (n : ℕ) {D : Scheme.{u}} (c : D ⟶ (affineSpaceModel k' n).total) [IsClosedImmersion c]
    [QuasiCompact (c ⁻¹ᵁ affineSpaceGenericOpen k' n).ι]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1})
      (condensedRingObj Λ D)))
    (hK : IsZero ((L(((c ⁻¹ᵁ affineSpaceGenericOpen k' n).ι)^*⟦Λ⟧)).obj K)) :
    IsZero ((L(((affineSpaceModel k' n).j)^*⟦Λ⟧)).obj ((R((c)_*⟦Λ⟧)).obj K)) := by
  have h := isZero_leftDerivedUpperStar_ι_obj_rightDerivedLowerStar_obj Λ
    (affineSpaceGenericOpen k' n) c hK
  have hfac := IsOpenImmersion.lift_fac (affineSpaceGenericOpen k' n).ι
    (affineSpaceModel k' n).j (range_j_affineSpaceModel_subset n)
  exact ((L((IsOpenImmersion.lift (affineSpaceGenericOpen k' n).ι (affineSpaceModel k' n).j
    (range_j_affineSpaceModel_subset n))^*⟦Λ⟧)).map_isZero h).of_iso
      ((nonempty_leftDerivedUpperStar_obj_iso_of_eq Λ hfac.symm _).some ≪≫
        (leftDerivedUpperStarComp Λ _ _).app _)

/-- **The slice exchange for complexes supported on the special fibre**: for a closed immersion
`c : D ⟶ 𝔸ⁿ⁺¹_S` and a complex `K` on `D` vanishing on the generic fibre `c⁻¹ 𝔸ⁿ⁺¹_η`, the
pullback exchange of the cartesian part `fromCart` of the morphism of models over the slice `hᵢ`
is invertible at `Rc_* K` (both sides vanish). -/
theorem isIso_fromCart_pullbackExchange_app_affineSpaceSliceHom_rightDerivedLowerStar
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (n : ℕ) (i : Fin (n + 1)) {D : Scheme.{u}} (c : D ⟶ (affineSpaceModel k' (n + 1)).total)
    [IsClosedImmersion c] [QuasiCompact (c ⁻¹ᵁ affineSpaceGenericOpen k' (n + 1)).ι]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1})
      (condensedRingObj Λ D)))
    (hK : IsZero ((L(((c ⁻¹ᵁ affineSpaceGenericOpen k' (n + 1)).ι)^*⟦Λ⟧)).obj K)) :
    IsIso (((affineSpaceSliceHom k' n i).fromCartesian.pullbackExchange Λ).app
      ((R((c)_*⟦Λ⟧)).obj K)) :=
  (affineSpaceSliceHom k' n i).fromCartesian.isIso_pullbackExchange_app_of_isZero Λ _
    (isZero_leftDerivedUpperStar_j_affineSpaceModel_obj_rightDerivedLowerStar_obj Λ (n + 1) c K
      hK)

/-- **The slice exchange for complexes supported on the special fibre**: for a closed immersion
`c : D ⟶ 𝔸ⁿ⁺¹_S` and a complex `K` on `D` vanishing on the generic fibre `c⁻¹ 𝔸ⁿ⁺¹_η`, the
pullback exchange of the morphism of models over the slice `hᵢ` is invertible at `Rc_* K` (both
sides vanish). -/
theorem isIso_pullbackExchange_app_affineSpaceSliceHom_rightDerivedLowerStar
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (n : ℕ) (i : Fin (n + 1)) {D : Scheme.{u}} (c : D ⟶ (affineSpaceModel k' (n + 1)).total)
    [IsClosedImmersion c] [QuasiCompact (c ⁻¹ᵁ affineSpaceGenericOpen k' (n + 1)).ι]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1})
      (condensedRingObj Λ D)))
    (hK : IsZero ((L(((c ⁻¹ᵁ affineSpaceGenericOpen k' (n + 1)).ι)^*⟦Λ⟧)).obj K)) :
    IsIso (((affineSpaceSliceHom k' n i).pullbackExchange Λ).app ((R((c)_*⟦Λ⟧)).obj K)) :=
  (affineSpaceSliceHom k' n i).isIso_pullbackExchange_app_of_isZero Λ _
    (isZero_leftDerivedUpperStar_j_affineSpaceModel_obj_rightDerivedLowerStar_obj Λ (n + 1) c K
      hK)

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- **The slice exchange from the cartesian factorization, `ℚ̄_ℓ`-coefficients**:
`NearbyCyclesModel.isSplitMono_pullbackExchange_app_affineSpaceSliceHom_of_cart` at
`Λ = ℚ̄_ℓ`, with the conclusion of
`NearbyCyclesModel.isSplitMono_pullbackExchange_app_affineSpaceSliceHom`.

Applying the general lemma directly times out in the unifier: the concrete statement and the
instantiated general one differ only by proofs (elaborations of `Precoherent Profinite` inside the
ring object instances), whose comparison unfolds the surrounding derived categories. We
transport along the proofs with `exact_mod_proofs`. -/
theorem isSplitMono_pullbackExchange_app_affineSpaceSliceHom_of_cart' (n : ℕ) (i : Fin (n + 1))
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (affineSpaceModel k' (n + 1)).total)
      Ab.{u + 1}) (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (affineSpaceModel k' (n + 1)).total))}
    (hfrom : IsIso (((affineSpaceSliceHom k' n i).fromCartesian.pullbackExchange
      (Profinite.padicAlgClRingObj ℓ)).app B))
    (hto : IsSplitMono (((affineSpaceSliceHom k' n i).toCartesian.pullbackExchange
      (Profinite.padicAlgClRingObj ℓ)).app B)) :
    IsSplitMono (((affineSpaceSliceHom k' n i).pullbackExchange
      (Profinite.padicAlgClRingObj ℓ)).app B) := by
  have key := @isSplitMono_pullbackExchange_app_affineSpaceSliceHom_of_cart k' _
    (Profinite.padicAlgClRingObj ℓ) _ _ n i
  revert B
  exact_mod_proofs key

/-- **The slice exchange for complexes supported on the special fibre, `ℚ̄_ℓ`-coefficients**:
`NearbyCyclesModel.isIso_pullbackExchange_app_affineSpaceSliceHom_rightDerivedLowerStar` at
`Λ = ℚ̄_ℓ`, transported along the differing instance proofs with `exact_mod_proofs`. -/
theorem isIso_pullbackExchange_app_affineSpaceSliceHom_rightDerivedLowerStar' (n : ℕ)
    (i : Fin (n + 1)) {D : Scheme.{u}} (c : D ⟶ (affineSpaceModel k' (n + 1)).total)
    [IsClosedImmersion c] [QuasiCompact (c ⁻¹ᵁ affineSpaceGenericOpen k' (n + 1)).ι]
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) D))}
    (hK : IsZero ((L(((c ⁻¹ᵁ affineSpaceGenericOpen k' (n + 1)).ι)^*⟦Profinite.padicAlgClRingObj
      ℓ⟧)).obj K)) :
    IsIso (((affineSpaceSliceHom k' n i).pullbackExchange (Profinite.padicAlgClRingObj ℓ)).app
      ((R((c)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K)) := by
  have key := isIso_pullbackExchange_app_affineSpaceSliceHom_rightDerivedLowerStar
    (Profinite.padicAlgClRingObj ℓ) n i c
  revert K
  exact_mod_proofs key

/-- **Nearby cycles on the coordinate generic slices, complexes supported on the special fibre**:
the conclusion of `NearbyCyclesModel.isSplitMono_pullbackExchange_app_affineSpaceSliceHom` holds
at `B = Rc_* K` for a closed immersion `c : D ⟶ 𝔸ⁿ⁺¹_S` and a complex `K` on `D` vanishing on the
generic fibre `c⁻¹ 𝔸ⁿ⁺¹_η`. -/
theorem isSplitMono_pullbackExchange_app_affineSpaceSliceHom_rightDerivedLowerStar (n : ℕ)
    (i : Fin (n + 1)) {D : Scheme.{u}} (c : D ⟶ (affineSpaceModel k' (n + 1)).total)
    [IsClosedImmersion c] [QuasiCompact (c ⁻¹ᵁ affineSpaceGenericOpen k' (n + 1)).ι]
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) D))}
    (hK : IsZero ((L(((c ⁻¹ᵁ affineSpaceGenericOpen k' (n + 1)).ι)^*⟦Profinite.padicAlgClRingObj
      ℓ⟧)).obj K)) :
    IsSplitMono (((affineSpaceSliceHom k' n i).pullbackExchange
      (Profinite.padicAlgClRingObj ℓ)).app ((R((c)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K)) :=
  have := isIso_pullbackExchange_app_affineSpaceSliceHom_rightDerivedLowerStar' n i c hK
  inferInstance

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
