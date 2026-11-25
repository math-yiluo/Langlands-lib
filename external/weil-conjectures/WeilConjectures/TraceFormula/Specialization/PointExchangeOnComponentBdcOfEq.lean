/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.ComponentSpecialFibre
public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingMap
public import WeilConjectures.TraceFormula.Specialization.PointExchangeOnComponent

/-!

# The exchange `ν_X` on pushforwards, for an abstract `ν`

`pointCompactSupportExchangeOfOpenImmersion_app_lowerStar_of_eq` is the identity of
`pointCompactSupportExchangeOfOpenImmersion_app_lowerStar` for any `ν` equal to
`pointCompactSupportExchangeOfOpenImmersion x u k'` (`hν`), with all the shape data of
`openPointExchangeAux_app_comp_aux_of_eq` given explicitly (as in `ExchangeOnProperBdc`). It is
instantiated for the morphism of deformation models `pointComponentModelHom` over `g : B ⟶ X` with
`b ≫ g = x` (the thickened point `B` of a fixed locus,
`pointCompactSupportExchangeOfOpenImmersion_app_lowerStar_component`).

The case `ν_X = pointCompactSupportExchangeOfSeparated` is in `PointExchangeOnSeparatedBdc` and
`PointExchangeOnComponentBdc`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Point

set_option hygiene false in
/-- The coefficients `ℚ̄_ℓ`. -/
local notation "Λℓ" => Profinite.padicAlgClRingObj ℓ

variable {k : Type u} [Field k] {X Y : Over (Spec (.of k))} (x : RationalPoint X) (u : X ⟶ Y)
  [IsOpenImmersion u.left] (k' : Type u) [Field k'] [Algebra k k']

instance isOpenImmersion_pointModelHom_total : IsOpenImmersion (pointModelHom x u k').total :=
  isOpenImmersion_deformationTotalMap u _ k' (ker_eq_comap_of_isOpenImmersion x u)

variable {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- The nearby cycles of the deformation to the normal cone preserve `Dᵇc`. -/
lemma preservesBoundedConstructible_deformationModel (Z : Over (Spec (.of k)))
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] (z : RationalPoint Z) :
    (deformationModel Z z.left.ker k').PreservesBoundedConstructible Λℓ :=
  (deformationModel Z z.left.ker k').preservesBoundedConstructible_of_isTraitModel (ℓ := ℓ)
    (isTraitModel_deformationModel Z _ k') (deformationModel_exists_comp_ε Z _ k')

set_option hygiene false in
/-- `Dᵇc` is preserved by the nearby cycles of the deformation of `X` along `x`. -/
local notation "hPX" => preservesBoundedConstructible_deformationModel (ℓ := ℓ) k' X x

set_option hygiene false in
/-- `Dᵇc` is preserved by the nearby cycles of the deformation of `Y` along `x ≫ u`. -/
local notation "hPY" => preservesBoundedConstructible_deformationModel (ℓ := ℓ) k' Y (x ≫ u)

variable [IsProper Y.hom] {B : Over (Spec (.of k))} {B' : Scheme.{u}}
  {MB : NearbyCyclesModel B.left B'} {g : B ⟶ X}
  {g' : B' ⟶ (deformationSpecialFibre X x.left.ker k').left}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType B.hom]
  [QuasiCompact B.hom] [IsSeparated B.hom]
  (φg : MB.Hom (deformationModel X x.left.ker k') g.left g')

/-- **The exchange `ν_X` on pushforwards from `B`, for `ν = ν_X`**: the identity of
`pointCompactSupportExchangeOfOpenImmersion_app_lowerStar` for any `ν` equal to
`pointCompactSupportExchangeOfOpenImmersion x u k'`, the shape data of
`openPointExchangeAux_app_comp_aux_of_eq` being those of the definition of `ν_X`, given
explicitly. -/
theorem pointCompactSupportExchangeOfOpenImmersion_app_lowerStar_of_eq
    (ν : Correspondence.IsContractingAt.PointCompactSupportExchange (ℓ := ℓ) X k' x)
    (hν : ν = pointCompactSupportExchangeOfOpenImmersion x u k') (N : Dᵇc(B.left)⟦Λℓ⟧) :
    ∀ hC, type_of% (
      openPointExchangeAux_app_comp_aux_of_eq
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λℓ ℓ u)
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λℓ ℓ
        (pointSpecialMap x u k'))
      ((pointModelHom x u k').boundedConstructiblePullbackExchange ℓ hPX hPY)
      ((pointModelHom x u k').isIso_boundedConstructiblePullbackExchange_of_isOpenImmersion ℓ
        hPX hPY (isPullback_deformationGenericMap u (ker_compatible_of_isOpenImmersion x u) k'))
      (lowerShriekCompOfEq ℓ (pointSpecialMap x u k') (toPoint _) (comp_toPoint _) ≪≫
        Functor.isoWhiskerRight
          (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ
            (pointSpecialMap x u k')) _)
      (lowerShriekCompOfEq ℓ u (toPoint Y) (comp_toPoint u) ≪≫ Functor.isoWhiskerRight
        (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ u) _)
      (ObjectProperty.fullyFaithfulι (boundedConstructible (condensedRingObj Λℓ (point k').left)))
      (ObjectProperty.fullyFaithfulι (boundedConstructible (condensedRingObj Λℓ Y.left)))
      (lowerShriekCompOfEq ℓ (deformationSpecialFibreToCompactified Y (x ≫ u) k')
        (toPoint _) (comp_toPoint _))
      (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ
        (deformationSpecialFibreToCompactified Y (x ≫ u) k'))
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ
        (toPoint (compactifiedSpecialFibre Y (x ≫ u) k')))
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint Y))
      (NearbyCyclesModel.boundedConstructibleNearbyCyclesCompatibility hPY)
      (boundedConstructibleOpenImmersionLowerShriekCompatibility Λℓ ℓ
        (deformationSpecialFibreToCompactified Y (x ≫ u) k'))
      (boundedConstructibleLowerStarCompatibility ℓ
        (toPoint (compactifiedSpecialFibre Y (x ≫ u) k')))
      (boundedConstructibleLowerStarCompatibility ℓ (toPoint Y))
      (NearbyCyclesModel.boundedConstructibleNearbyCyclesCompatibility
        (NearbyCyclesModel.preservesBoundedConstructible_traitModel (k := k) (k' := k') ℓ))
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λℓ
        (deformationSpecialFibreToCompactified Y (x ≫ u) k').left).ofNatIsoRight
          (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λℓ _).symm)
      (leftDerivedUpperStarId Λℓ Y.left).symm
      ((deformationToCompactifiedModelHom Y (x ≫ u) k').pullbackExchange Λℓ)
      (isIso_deformationToCompactifiedModelHom_pullbackExchange Y (x ≫ u) k')
      ((compactifiedToPointModelHom Y (x ≫ u) k').pushforwardExchange Λℓ)
      (isIsoOn_compactifiedToPointModelHom_pushforwardExchange Y (x ≫ u) k') ν hν
      (NearbyCyclesModel.boundedConstructibleNearbyCyclesCompatibility hPX)
      (boundedConstructibleOpenImmersionLowerShriekCompatibility Λℓ ℓ u)
      (boundedConstructibleOpenImmersionLowerShriekCompatibility Λℓ ℓ (pointSpecialMap x u k'))
      (lowerShriekExchangeOfInv (openImmersionAdjunction ℓ u.left)
        (openImmersionAdjunction ℓ (pointSpecialMap x u k').left)
        ((pointModelHom x u k').pullbackExchange Λℓ))
      (fun K ↦ map_mateEquiv_inv_liftExchange _ _ _ _ _ _ _ _ _ _ K)
      (boundedConstructibleLowerStarCompatibility ℓ g)
      (closedExtension (openImmersionAdjunction ℓ u.left) (rfl : g.left ≫ u.left = _))
      (closedExtension (Adjunction.id.ofNatIsoRight (leftDerivedUpperStarId Λℓ Y.left).symm)
        (rfl : (g.left ≫ u.left) ≫ 𝟙 Y.left = _))
      (lowerStarCompOfEq (rfl : ((g.left ≫ u.left) ≫ 𝟙 Y.left) ≫ (toPoint Y).left = _))
      (φg.pushforwardExchange Λℓ)
      (closedExtension (openImmersionAdjunction ℓ (pointSpecialMap x u k').left)
        (rfl : g' ≫ (pointSpecialMap x u k').left = _))
      (closedExtension (openImmersionAdjunction ℓ
        (deformationSpecialFibreToCompactified Y (x ≫ u) k').left) rfl)
      (lowerStarCompOfEq rfl)
      ((pointCompModelHom x u k' φg).pushforwardExchange Λℓ) N
      ⟨_, boundedConstructible_rightDerivedLowerStar_obj ℓ (g ≫ u) N⟩
      (Iso.refl _) hC) :=
  fun hC ↦ openPointExchangeAux_app_comp_aux_of_eq
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λℓ ℓ u)
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λℓ ℓ
      (pointSpecialMap x u k'))
    ((pointModelHom x u k').boundedConstructiblePullbackExchange ℓ hPX hPY)
    ((pointModelHom x u k').isIso_boundedConstructiblePullbackExchange_of_isOpenImmersion ℓ
      hPX hPY (isPullback_deformationGenericMap u (ker_compatible_of_isOpenImmersion x u) k'))
    (lowerShriekCompOfEq ℓ (pointSpecialMap x u k') (toPoint _) (comp_toPoint _) ≪≫
      Functor.isoWhiskerRight
        (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ
          (pointSpecialMap x u k')) _)
    (lowerShriekCompOfEq ℓ u (toPoint Y) (comp_toPoint u) ≪≫ Functor.isoWhiskerRight
      (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ u) _)
    (ObjectProperty.fullyFaithfulι (boundedConstructible (condensedRingObj Λℓ (point k').left)))
    (ObjectProperty.fullyFaithfulι (boundedConstructible (condensedRingObj Λℓ Y.left)))
    (lowerShriekCompOfEq ℓ (deformationSpecialFibreToCompactified Y (x ≫ u) k')
      (toPoint _) (comp_toPoint _))
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ
      (deformationSpecialFibreToCompactified Y (x ≫ u) k'))
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ
      (toPoint (compactifiedSpecialFibre Y (x ≫ u) k')))
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint Y))
    (NearbyCyclesModel.boundedConstructibleNearbyCyclesCompatibility hPY)
    (boundedConstructibleOpenImmersionLowerShriekCompatibility Λℓ ℓ
      (deformationSpecialFibreToCompactified Y (x ≫ u) k'))
    (boundedConstructibleLowerStarCompatibility ℓ
      (toPoint (compactifiedSpecialFibre Y (x ≫ u) k')))
    (boundedConstructibleLowerStarCompatibility ℓ (toPoint Y))
    (NearbyCyclesModel.boundedConstructibleNearbyCyclesCompatibility
      (NearbyCyclesModel.preservesBoundedConstructible_traitModel (k := k) (k' := k') ℓ))
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λℓ
      (deformationSpecialFibreToCompactified Y (x ≫ u) k').left).ofNatIsoRight
        (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λℓ _).symm)
    (leftDerivedUpperStarId Λℓ Y.left).symm
    ((deformationToCompactifiedModelHom Y (x ≫ u) k').pullbackExchange Λℓ)
    (isIso_deformationToCompactifiedModelHom_pullbackExchange Y (x ≫ u) k')
    ((compactifiedToPointModelHom Y (x ≫ u) k').pushforwardExchange Λℓ)
    (isIsoOn_compactifiedToPointModelHom_pushforwardExchange Y (x ≫ u) k') ν hν
    (NearbyCyclesModel.boundedConstructibleNearbyCyclesCompatibility hPX)
    (boundedConstructibleOpenImmersionLowerShriekCompatibility Λℓ ℓ u)
    (boundedConstructibleOpenImmersionLowerShriekCompatibility Λℓ ℓ (pointSpecialMap x u k'))
    (lowerShriekExchangeOfInv (openImmersionAdjunction ℓ u.left)
      (openImmersionAdjunction ℓ (pointSpecialMap x u k').left)
      ((pointModelHom x u k').pullbackExchange Λℓ))
    (fun K ↦ map_mateEquiv_inv_liftExchange _ _ _ _ _ _ _ _ _ _ K)
    (boundedConstructibleLowerStarCompatibility ℓ g)
    (closedExtension (openImmersionAdjunction ℓ u.left) (rfl : g.left ≫ u.left = _))
    (closedExtension (Adjunction.id.ofNatIsoRight (leftDerivedUpperStarId Λℓ Y.left).symm)
      (rfl : (g.left ≫ u.left) ≫ 𝟙 Y.left = _))
    (lowerStarCompOfEq (rfl : ((g.left ≫ u.left) ≫ 𝟙 Y.left) ≫ (toPoint Y).left = _))
    (φg.pushforwardExchange Λℓ)
    (closedExtension (openImmersionAdjunction ℓ (pointSpecialMap x u k').left)
      (rfl : g' ≫ (pointSpecialMap x u k').left = _))
    (closedExtension (openImmersionAdjunction ℓ
      (deformationSpecialFibreToCompactified Y (x ≫ u) k').left) rfl)
    (lowerStarCompOfEq rfl)
    ((pointCompModelHom x u k' φg).pushforwardExchange Λℓ) N
    ⟨_, boundedConstructible_rightDerivedLowerStar_obj ℓ (g ≫ u) N⟩
    (Iso.refl _) hC

end Point

section Component

variable {k : Type u} [Field k] {X B : Over (Spec (.of k))} {x : RationalPoint X}
  {b : RationalPoint B} (k' : Type u) [Field k'] [Algebra k k'] (g : B ⟶ X) (hbg : b ≫ g = x)

/-- The morphism of deformation models `𝒟_B ⟶ 𝒳` over `g : B ⟶ X` with `b ≫ g = x`, for the
deformations of `B` along `ker b` and of `X` along `ker x`. -/
noncomputable abbrev pointComponentModelHom :=
  deformationModelHom g (map_siteIdeal_ker_le_of_comp_eq g hbg) k'

variable {Y : Over (Spec (.of k))} (u : X ⟶ Y) [IsOpenImmersion u.left] [IsProper Y.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] {ℓ : ℕ} [Fact ℓ.Prime]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]

/-- **The exchange `ν_X` on pushforwards from a thickened point `B`** (`b ≫ g = x`):
`pointCompactSupportExchangeOfOpenImmersion_app_lowerStar_of_eq` for `pointComponentModelHom`. -/
theorem pointCompactSupportExchangeOfOpenImmersion_app_lowerStar_component
    (ν : Correspondence.IsContractingAt.PointCompactSupportExchange (ℓ := ℓ) X k' x)
    (hν : ν = pointCompactSupportExchangeOfOpenImmersion x u k')
    (N : Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    type_of% (pointCompactSupportExchangeOfOpenImmersion_app_lowerStar_of_eq x u k'
      (pointComponentModelHom k' g hbg) ν hν N) :=
  pointCompactSupportExchangeOfOpenImmersion_app_lowerStar_of_eq x u k' _ ν hν N

end Component

end AlgebraicGeometry.ProEtale.CondensedRing
