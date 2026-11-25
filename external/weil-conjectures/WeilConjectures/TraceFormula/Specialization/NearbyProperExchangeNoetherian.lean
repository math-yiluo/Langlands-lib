/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyProperExchange

/-!

# The proper exchange from a model with a thickened special fibre

The proper exchange of nearby cycles with `ℚ̄_ℓ`-coefficients
(`NearbyCyclesModel.Hom.isIso_pushforwardExchange_app_of_isProper`) asks both models to be of
finite type over the trait. For the source model `M` this is only used through the facts that its
total space and geometric generic fibre are noetherian, that `i_M` is a closed immersion and that
`j_M` is affine. These facts hold for models whose special fibre is a thickening of the fibre over
the closed point, such as the source of the power map of deformations
(`ProEtale.CondensedRing.powSourceModel`), which is not of finite type over the trait in the
sense of `NearbyCyclesModel.IsTraitModel`.

## Main results

- `NearbyCyclesModel.Hom.isIso_baseChangeMap_commSq_i_app_lowerStar_of_isNoetherian`
- `NearbyCyclesModel.Hom.isIso_pushforwardExchange_app_of_isProper_of_isNoetherian`

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel.Hom

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k']

-- the derived categories of module objects are slow to elaborate
/-- `NearbyCyclesModel.Hom.isIso_baseChangeMap_commSq_i_app_lowerStar` with the source model
only assumed to have noetherian total space and geometric generic fibre, closed special fibre and
affine inclusion of the geometric generic fibre. -/
theorem isIso_baseChangeMap_commSq_i_app_lowerStar_of_isNoetherian {X X' Y Y' : Scheme.{u}}
    {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'} {f : X ⟶ Y}
    {f' : X' ⟶ Y'} (φ : M.Hom N f f') [IsNoetherian M.generic] [IsNoetherian M.total]
    [IsClosedImmersion M.i] [IsAffineHom M.j]
    (hN : ∃ a : Y' ⟶ Spec (.of k'), N.IsTraitModel (X' := Over.mk a)) [IsProper φ.total]
    (hi : IsPullback M.i f' φ.total N.i)
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.generic) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.generic)))
    (hL : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.generic) L) :
    IsIso ((baseChangeMap (Profinite.padicAlgClRingObj ℓ) φ.commSq_i).app
      ((R((M.j)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj L)) := by
  obtain ⟨aN, hN⟩ := hN
  have : IsNoetherian N.total := hN.isNoetherian_total
  have : IsClosedImmersion N.i := hN.isClosedImmersion_i
  have : IsProper f' := MorphismProperty.of_isPullback (P := @IsProper) hi inferInstance
  obtain ⟨E, L₀, ⟨e⟩⟩ := exists_padicAlgCl_iso_integralModel_obj ℓ M.generic L hL
  obtain ⟨a, ha⟩ := L₀.property.1.1
  have : L₀.obj.IsGE a := ha
  have : ((R((M.j)_*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj L₀.obj).IsGE a :=
    ((M.j)_*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).isGE_rightDerivedFunctor_obj L₀.obj _
  have hc : IsDerivedAdicComplete (ℓ : ℤ)
      ((R((M.j)_*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj L₀.obj) := by
    have := (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1)
      M.j).rightAdjoint_preservesLimits.{0, 0}
    exact (isDerivedAdicComplete_of_boundedConstructible M.generic ℓ E L₀.obj
      L₀.property).map' _
  have he := plusEtaleOrigin_derivedReduction_rightDerivedLowerStar_obj ℓ E M.j L₀.obj a
    (boundedConstructible_derivedReduction_obj M.generic ℓ E _ L₀.property).plusEtaleOrigin
  have := preservesLimitsOfShape_leftDerivedUpperStar_of_isClosedImmersion
    (Profinite.padicIntegersRingObj ℓ E.1) N.i
  have := preservesLimitsOfShape_leftDerivedUpperStar_of_isClosedImmersion
    (Profinite.padicIntegersRingObj ℓ E.1) M.i
  have h₀ := isIso_baseChangeMap_app_of_isProper_of_isDerivedAdicComplete ℓ E hi _ a hc he
  have := isGE_leftDerivedFunctor_extendScalars_obj
    (padicIntegersRingObjToContinuousMapRingObj ℓ E) L₀.obj a
  have h₁ := isIso_derivedPushHom_app_padicIntegers_of_isGE ℓ E M.j L₀.obj a
  have h₂ := isIso_derivedPushHom_app_padicSubfieldRingObjToPadicAlgCl_of_isGE ℓ E M.j
    ((Mod.extendScalars (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E)
      M.generic)).leftDerivedFunctor.obj L₀.obj) a
  have e' := (Mod.extendScalars (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
      M.total)).leftDerivedFunctor.mapIso
        (asIso ((derivedPushHom (padicIntegersRingObjToContinuousMapRingObj ℓ E) M.j).app
          L₀.obj)) ≪≫
    asIso ((derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) M.j).app
      ((Mod.extendScalars (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E)
        M.generic)).leftDerivedFunctor.obj L₀.obj)) ≪≫
    (R((M.j)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).mapIso e
  have key := isIso_baseChangeMap_app_padicAlgCl_of_isIso_integral ℓ hi.toCommSq E _ a h₀ e'
  cast_proofs key

/-- `NearbyCyclesModel.Hom.isIso_pushforwardExchange_app_of_isProper` with the source model only
assumed to have noetherian total space and geometric generic fibre, closed special fibre and
affine inclusion of the geometric generic fibre. -/
theorem isIso_pushforwardExchange_app_of_isProper_of_isNoetherian
    [Fact (ringChar k' ≠ ℓ)] {k : Type u} [Field k] [Fact (ringChar k ≠ ℓ)] {X Y : Scheme.{u}}
    [IsNoetherian Y] (aY : Y ⟶ Spec (.of k))
    {X' Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'} {f : X ⟶ Y}
    {f' : X' ⟶ Y'} (φ : M.Hom N f f') [IsNoetherian M.generic] [IsNoetherian M.total]
    [IsClosedImmersion M.i] [IsAffineHom M.j]
    (hN : ∃ a : Y' ⟶ Spec (.of k'), N.IsTraitModel (X' := Over.mk a))
    [IsProper φ.total] [IsProper f]
    (hi : IsPullback M.i f' φ.total N.i) (hε : IsPullback M.ε φ.generic f N.ε)
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    (hK : boundedConstructible _ K) :
    IsIso ((φ.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)).app K) := by
  obtain ⟨aN, hN'⟩ := hN
  have : IsNoetherian N.generic := hN'.isNoetherian_generic
  obtain ⟨q, -, -, -, -, -, -⟩ := hN'.exists_isPullback
  have h₁ := isIso_baseChangeMap_app_padicAlgCl_of_isProper ℓ aY
    (N.j ≫ q ≫ traitToBase k' k') φ.commSq_ε hε K hK
  have h₂ := φ.isIso_baseChangeMap_commSq_i_app_lowerStar_of_isNoetherian ⟨aN, hN'⟩ hi _
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ M.ε K hK)
  have h₃ := φ.isIso_pushforwardExchange_app_of_isIso_baseChangeMap
    (Profinite.padicAlgClRingObj ℓ) K (by cast_proofs h₁) (by cast_proofs h₂)
  cast_proofs h₃

end NearbyCyclesModel.Hom

end AlgebraicGeometry.ProEtale.CondensedRing
