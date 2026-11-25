/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.Exchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperComplete
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedUpperStarProducts
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedAdicCompleteConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeAmbient
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionLowerStarEtaleOrigin
public import WeilConjectures.TraceFormula.Specialization.TraitModelRestrict
public import WeilConjectures.Tactic.ExactModProofs

/-!

# Proper base change along the special fibre at generic direct images

Let `φ : M ⟶ N` be a morphism of nearby-cycles models of finite type over the trait
`S = Spec k'⟦t⟧` (`NearbyCyclesModel.IsTraitModel`) whose morphism of total spaces `t` is proper
and whose square of special fibres is cartesian. For a bounded constructible `ℚ̄_ℓ`-complex `L`
on the geometric generic fibre of `M`, the base change morphism
`Li_N^* Rt_* ⟶ Rt_{s*} Li_M^*` is invertible at the generic direct image `Rj_{M*} L`
(`NearbyCyclesModel.Hom.isIso_baseChangeMap_commSq_i_app_lowerStar`). This is the step
`ī^* Rt̄_* ≃ Rt_{s*} ī'^*` of the proof of blueprint `prose-E-03` (2).

The complex `Rj_{M*} L` is not bounded constructible, so the proper base change theorem for
bounded constructible complexes does not apply. The proof passes to an integral model `L₀` of
`L` (`ProEtale.exists_padicAlgCl_iso_integralModel`): `L₀` is derived `ℓ`-adically complete
(`ProEtale.isDerivedAdicComplete_of_boundedConstructible`), hence so is `Rj_{M*} L₀`, and the
first derived reduction of `Rj_{M*} L₀` is the direct image of a complex of étale origin, so of
étale origin. Proper base change for such complexes
(`ProEtale.CondensedRing.isIso_baseChangeMap_app_of_isProper_of_isDerivedAdicComplete`), along
the special fibres, whose pullbacks preserve countable products
(`ProEtale.CondensedRing.preservesLimitsOfShape_leftDerivedUpperStar_of_isClosedImmersion`),
gives the integral statement, and the coefficient changes `𝒪_E → E → ℚ̄_ℓ` commute with the
direct images of bounded below complexes and with base change morphisms.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {k' : Type u} [Field k'] {X : Scheme.{u}} {X' : Over (Spec (.of k'))}

/-- The geometric generic fibre of a model of finite type over the trait is a noetherian scheme:
it is of finite type over the field `Ω`. -/
lemma IsTraitModel.isNoetherian_generic {M : NearbyCyclesModel X X'.left}
    (hM : M.IsTraitModel) : IsNoetherian M.generic := by
  obtain ⟨q, g, _, _, _, hj, -⟩ := hM.exists_isPullback
  have : LocallyOfFiniteType g :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hj ‹_›
  have : QuasiCompact g := MorphismProperty.of_isPullback (P := @QuasiCompact) hj ‹_›
  have : IsLocallyNoetherian M.generic := LocallyOfFiniteType.isLocallyNoetherian g
  have : CompactSpace M.generic := QuasiCompact.compactSpace_of_compactSpace g
  exact ⟨⟩

/-- The special fibre of a model of finite type over the trait is a closed immersion. -/
lemma IsTraitModel.isClosedImmersion_i {M : NearbyCyclesModel X X'.left} (hM : M.IsTraitModel) :
    IsClosedImmersion M.i := by
  obtain ⟨q, g, _, _, _, -, hi⟩ := hM.exists_isPullback
  have : IsClosedImmersion (traitClosedPoint k') :=
    IsClosedImmersion.spec_of_surjective _ fun a ↦ ⟨PowerSeries.C a, by simp⟩
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) hi.flip inferInstance

/-- The inclusion of the geometric generic fibre of a model of finite type over the trait is an
affine morphism. -/
lemma IsTraitModel.isAffineHom_j {M : NearbyCyclesModel X X'.left} (hM : M.IsTraitModel) :
    IsAffineHom M.j := by
  obtain ⟨q, g, _, _, _, hj, -⟩ := hM.exists_isPullback
  exact MorphismProperty.of_isPullback (P := @IsAffineHom) hj.flip inferInstance

variable {ℓ : ℕ} [Fact ℓ.Prime]

-- the derived categories of module objects are slow to elaborate
/-- **Proper base change along the special fibre at a generic direct image** (the step
`ī^* Rt̄_* ≃ Rt_{s*} ī'^*` of the proof of blueprint `prose-E-03` (2); SGA 7
XIII 2.1.7): for a morphism `φ : M ⟶ N` of models of finite type over the trait whose morphism of
total spaces is proper and whose square of special fibres is cartesian, the base change morphism
`Li_N^* Rt_* ⟶ Rf'_* Li_M^*` is invertible at the direct image `Rj_{M*} L` of a bounded
constructible `ℚ̄_ℓ`-complex `L` on the geometric generic fibre of `M`. -/
theorem Hom.isIso_baseChangeMap_commSq_i_app_lowerStar {X' Y Y' : Scheme.{u}}
    {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'} {f : X ⟶ Y}
    {f' : X' ⟶ Y'} (φ : M.Hom N f f')
    (hM : ∃ a : X' ⟶ Spec (.of k'), M.IsTraitModel (X' := Over.mk a))
    (hN : ∃ a : Y' ⟶ Spec (.of k'), N.IsTraitModel (X' := Over.mk a)) [IsProper φ.total]
    (hi : IsPullback M.i f' φ.total N.i)
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.generic) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.generic)))
    (hL : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.generic) L) :
    IsIso ((baseChangeMap (Profinite.padicAlgClRingObj ℓ) φ.commSq_i).app
      ((R((M.j)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj L)) := by
  obtain ⟨aM, hM⟩ := hM
  obtain ⟨aN, hN⟩ := hN
  have := hM.isNoetherian_generic
  have := hM.isNoetherian_total
  have : IsNoetherian N.total := hN.isNoetherian_total
  have := hM.isClosedImmersion_i
  have : IsClosedImmersion N.i := hN.isClosedImmersion_i
  have := hM.isAffineHom_j
  have : IsProper f' := MorphismProperty.of_isPullback (P := @IsProper) hi inferInstance
  obtain ⟨E, L₀, ⟨e⟩⟩ := exists_padicAlgCl_iso_integralModel_obj ℓ M.generic L hL
  obtain ⟨a, ha⟩ := L₀.property.1.1
  have : L₀.obj.IsGE a := ha
  have : ((R((M.j)_*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj L₀.obj).IsGE a :=
    ((M.j)_*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).isGE_rightDerivedFunctor_obj L₀.obj _
  -- the generic direct image of `L₀` is derived complete
  have hc : IsDerivedAdicComplete (ℓ : ℤ)
      ((R((M.j)_*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj L₀.obj) := by
    have := (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1)
      M.j).rightAdjoint_preservesLimits.{0, 0}
    exact (isDerivedAdicComplete_of_boundedConstructible M.generic ℓ E L₀.obj
      L₀.property).map' _
  -- its first derived reduction is of étale origin
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

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
