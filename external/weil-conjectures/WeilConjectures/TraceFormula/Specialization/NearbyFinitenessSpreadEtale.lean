/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyFinitenessCriterion

/-!

# Nearby cycles of weakly étale localisations of a model over the trait

Let `q : T ⟶ S` be a scheme over the strictly henselian trait `S = Spec k'⟦t⟧` and
`e : T' ⟶ T` a weakly étale morphism (an open immersion, an étale morphism, or a limit of such,
e.g. the base change of `T` along an étale neighbourhood or a strict localisation of a scheme
`T` maps to). The standard model of `T'` over `S` (`NearbyCyclesModel.traitStdModel (e ≫ q)`)
maps to that of `T` (`NearbyCyclesModel.traitStdEtaleHom`), and the nearby cycles commute with
this localisation (`NearbyCyclesModel.isIso_pullbackExchange_traitStdEtaleHom`):
```
L(e_s)^* Ψ_T B ≅ Ψ_{T'} (Le^* B)
```
for every complex `B` on `T`, by the weakly étale exchange
(`NearbyCyclesModel.Hom.isIso_pullbackExchange_of_weaklyEtale`). In particular the restriction of
`Ψ_T B` along `e_s` is bounded constructible if and only if the nearby cycles of the localised
model are (`NearbyCyclesModel.boundedConstructible_upperStar_nearbyCycles_iff_of_weaklyEtale`).

This is the étale-neighbourhood form of the local input of Deligne's criterion (SGA 4½,
[Th. finitude], proof of 3.2): for a point `y` of the special fibre `P_s` of a proper model `P`,
it suffices to find an open `V ⊆ P` whose special fibre contains `y` and such that the nearby
cycles of the open model `V` are bounded constructible
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_traitStdModel_of_isGenericPoint_of_opens`).
The local input is thereby stated on models of finite type over `S`, rather than on the special
fibre.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {k' : Type u} [Field k'] {T T' : Scheme.{u}} (q : T ⟶ trait k') (e : T' ⟶ T)

/-- The cartesian square of the geometric generic fibre of the standard model of `T'`. -/
lemma isPullback_traitStdModel_j (q' : T' ⟶ trait k') :
    IsPullback (traitStdModel q').j (pullback.snd q' (traitGenericPoint k')) q'
      (traitGenericPoint k') :=
  IsPullback.of_hasPullback _ _

/-- The cartesian square of the special fibre of the standard model of `T'`. -/
lemma isPullback_traitStdModel_i (q' : T' ⟶ trait k') :
    IsPullback (traitStdModel q').i (traitStdSpecialFibre q').hom q' (traitClosedPoint k') :=
  IsPullback.of_hasPullback _ _

/-- The morphism of special fibres `T'_s ⟶ T_s` induced by a morphism `e : T' ⟶ T`, for `T'`
over the trait through `e`. -/
noncomputable abbrev traitStdEtaleSpecial :
    (traitStdSpecialFibre (e ≫ q)).left ⟶ (traitStdSpecialFibre q).left :=
  traitStdSpecialHom q (isPullback_traitStdModel_i (e ≫ q)) e rfl

/-- The morphism of geometric models from the standard model of `T'` (over the trait through
`e ≫ q`) to the standard model of `T`, with total morphism `e`. -/
noncomputable abbrev traitStdEtaleHom :
    (traitStdModel (e ≫ q)).geometric.Hom (traitStdModel q).geometric e
      (traitStdEtaleSpecial q e) :=
  traitStdHom q (isPullback_traitStdModel_j (e ≫ q)) (isPullback_traitStdModel_i (e ≫ q)) e rfl

/-- **Nearby cycles commute with weakly étale localisation of a scheme over the trait**: for a
weakly étale `e : T' ⟶ T`, the pullback exchange `L(e_s)^* Ψ_T ⟶ Ψ_{T'} Le^*` of the morphism of
standard models (`NearbyCyclesModel.traitStdEtaleHom`) is an isomorphism, its square of
geometric generic fibres being cartesian
(`NearbyCyclesModel.Hom.isIso_pullbackExchange_of_weaklyEtale`). -/
theorem isIso_pullbackExchange_traitStdEtaleHom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    [WeaklyEtale e] : IsIso ((traitStdEtaleHom q e).pullbackExchange Λ) := by
  have : WeaklyEtale (traitStdEtaleHom q e).total := by
    exact (inferInstance : WeaklyEtale e)
  exact (traitStdEtaleHom q e).isIso_pullbackExchange_of_weaklyEtale Λ
    (isPullback_traitStdHom_generic q (isPullback_traitStdModel_j (e ≫ q))
      (isPullback_traitStdModel_i (e ≫ q)) e rfl)

/-- **Nearby cycles of a weakly étale localisation**: for a weakly étale `e : T' ⟶ T` and a
complex `B` on `T`, `L(e_s)^* Ψ_T B ≅ Ψ_{T'} (Le^* B)`. -/
noncomputable def upperStarNearbyCyclesIsoOfWeaklyEtale
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    [WeaklyEtale e]
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj Λ T))) :
    (L((traitStdEtaleSpecial q e)^*⟦Λ⟧)).obj (((traitStdModel q).geometric.nearbyCycles Λ).obj B)
      ≅ ((traitStdModel (e ≫ q)).geometric.nearbyCycles Λ).obj ((L((e)^*⟦Λ⟧)).obj B) :=
  have := isIso_pullbackExchange_traitStdEtaleHom q e Λ
  asIso (((traitStdEtaleHom q e).pullbackExchange Λ).app B)

/-- **Bounded constructibility of the nearby cycles on a weakly étale localisation**: for a
weakly étale `e : T' ⟶ T` and a complex `B` on `T`, the restriction `L(e_s)^* Ψ_T B` of the
nearby cycles of `T` along the special fibre of `e` is bounded constructible if and only if the
nearby cycles `Ψ_{T'} (Le^* B)` of the localised model are
(`NearbyCyclesModel.upperStarNearbyCyclesIsoOfWeaklyEtale`). -/
theorem boundedConstructible_upperStar_nearbyCycles_iff_of_weaklyEtale
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    [WeaklyEtale e]
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj Λ T))) :
    boundedConstructible _ ((L((traitStdEtaleSpecial q e)^*⟦Λ⟧)).obj
        (((traitStdModel q).geometric.nearbyCycles Λ).obj B)) ↔
      boundedConstructible _
        (((traitStdModel (e ≫ q)).geometric.nearbyCycles Λ).obj ((L((e)^*⟦Λ⟧)).obj B)) :=
  (boundedConstructible _).prop_iff_of_iso (upperStarNearbyCyclesIsoOfWeaklyEtale q e Λ B)

/-- The special fibre of a weakly étale localisation is weakly étale. -/
instance weaklyEtale_traitStdEtaleSpecial [WeaklyEtale e] :
    WeaklyEtale (traitStdEtaleSpecial q e) :=
  MorphismProperty.of_isPullback (P := @WeaklyEtale)
    (isPullback_traitStdHom_special q (isPullback_traitStdModel_i (e ≫ q)) e rfl) ‹_›

/-- The special fibre of an open immersion is an open immersion. -/
instance isOpenImmersion_traitStdEtaleSpecial [IsOpenImmersion e] :
    IsOpenImmersion (traitStdEtaleSpecial q e) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (isPullback_traitStdHom_special q (isPullback_traitStdModel_i (e ≫ q)) e rfl) ‹_›

/-- The image of the special fibre `T'_s ⟶ T_s` of an open immersion `e : T' ⟶ T` is the
preimage of the image of `e` under the inclusion `i : T_s ⟶ T` of the special fibre. -/
lemma range_traitStdEtaleSpecial [IsOpenImmersion e] :
    Set.range (traitStdEtaleSpecial q e) = (traitStdModel q).i ⁻¹' Set.range e :=
  Scheme.range_snd_of_isPullback
    (isPullback_traitStdHom_special q (isPullback_traitStdModel_i (e ≫ q)) e rfl)

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
