/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralAcyclic

/-!
# Pushforward commutes with `E ⊗_{𝒪_E} -`

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E`, and
`f : X ⟶ Y` a quasi-compact quasi-separated morphism of schemes. The underived comparison
**(Push)** `E_Y ⊗ f_* M ⟶ f_*(E_X ⊗ M)` for the inclusion `𝒪̲_E ⟶ E̲` is an isomorphism for every
`𝒪_{E,X}`-module object `M`
(`ProEtale.CondensedRing.isIso_pushHom_padicIntegersRingObjToContinuousMapRingObj`).

Indeed both sides are sequential colimits of the multiplications by `ℓ` on `f_* M`
(`AlgebraicGeometry.ProEtale.isColimitPadicIntegersExtendScalarsCocone`, and `f_*` commutes with
filtered colimits, `AlgebraicGeometry.ProEtale.preservesColimitsOfShape_lowerStar`), and the
comparison is compatible with the cocone maps: in degree `0` these are the units of extension
of scalars, which the mate (Push) respects (`CategoryTheory.unit_mateEquiv_symm`), and in
general this follows by cancelling the multiplication by `ℓ`, a monomorphism on `E`-modules.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) {X Y : Scheme.{u}}
  (f : X ⟶ Y)

/-- The unit of extension of scalars along `𝒪_{E,X} ⟶ E_X` is the cocone map `e_0`. -/
lemma extendScalarsCoconeι_zero_padicIntegers
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)) :
    Mod.extendScalarsCoconeι (padicIntegersToPadicSubfield X ℓ E)
        (padicIntegersToPadicSubfieldInvPow ℓ E X) M 0 =
      Mod.extendUnitHom (padicIntegersToPadicSubfield X ℓ E) M := by
  rw [Mod.extendScalarsCoconeι, Mod.extendUnitHom, padicIntegersToPadicSubfieldInvPow,
    Profinite.padicIntegersRingObjToContinuousMapRingObjInvPow_zero, IsMonHom.one_hom]

/-- (Push) is compatible with the units of extension of scalars:
`(f_* M ⟶ E_Y ⊗ f_* M ⟶ f_*(E_X ⊗ M)) = f_*(M ⟶ E_X ⊗ M)`. -/
lemma extendUnitHom_comp_pushHom_app
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)) :
    Mod.extendUnitHom (padicIntegersToPadicSubfield Y ℓ E) ((f)_*⟦_⟧.obj M) ≫
        ((pushHom (padicIntegersRingObjToContinuousMapRingObj ℓ E) f).app M).hom =
      (f)_*[Ab.{u + 1}].map (Mod.extendUnitHom (padicIntegersToPadicSubfield X ℓ E) M) := by
  have h := unit_mateEquiv_symm
    (Mod.extendRestrictAdjunction
      (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E) X))
    (Mod.extendRestrictAdjunction
      (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E) Y))
    (TwoSquare.mk _ _ _ _
      (comapLowerStarIso (padicIntegersRingObjToContinuousMapRingObj ℓ E) f).inv) M
  have h' := congrArg Mod.Hom.hom h
  refine h'.symm.trans ?_
  change (f)_*[Ab.{u + 1}].map _ ≫ 𝟙 _ = _
  rw [Category.comp_id]
  rfl

/-- (Push) is compatible with the cocone maps `e_k : M ⟶ E ⊗ M` exhibiting `E ⊗ M` as
`colim(M --ℓ--> M --ℓ--> ⋯)`. -/
lemma extendScalarsCoconeι_comp_pushHom_app
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)) (k : ℕ) :
    Mod.extendScalarsCoconeι (padicIntegersToPadicSubfield Y ℓ E)
        (padicIntegersToPadicSubfieldInvPow ℓ E Y) ((f)_*⟦_⟧.obj M) k ≫
        ((pushHom (padicIntegersRingObjToContinuousMapRingObj ℓ E) f).app M).hom =
      (f)_*[Ab.{u + 1}].map (Mod.extendScalarsCoconeι (padicIntegersToPadicSubfield X ℓ E)
        (padicIntegersToPadicSubfieldInvPow ℓ E X) M k) := by
  induction k with
  | zero =>
    rw [extendScalarsCoconeι_zero_padicIntegers, extendScalarsCoconeι_zero_padicIntegers]
    exact extendUnitHom_comp_pushHom_app ℓ E f M
  | succ k ih =>
    have : Mono (ℓ • 𝟙 ((Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).obj M).X) :=
      Mod.mono_nsmul_id_of_isColimit _ (isColimitPadicIntegersExtendScalarsCocone ℓ E X M)
    have : Mono ((f)_*[Ab.{u + 1}].map
        (ℓ • 𝟙 ((Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).obj M).X)) :=
      inferInstance
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id] at this
    have key : ℓ • (Mod.extendScalarsCoconeι (padicIntegersToPadicSubfield Y ℓ E)
        (padicIntegersToPadicSubfieldInvPow ℓ E Y) ((f)_*⟦_⟧.obj M) (k + 1) ≫
        ((pushHom (padicIntegersRingObjToContinuousMapRingObj ℓ E) f).app M).hom) =
        ℓ • (f)_*[Ab.{u + 1}].map (Mod.extendScalarsCoconeι (padicIntegersToPadicSubfield X ℓ E)
          (padicIntegersToPadicSubfieldInvPow ℓ E X) M (k + 1)) := by
      rw [← Preadditive.nsmul_comp, Mod.nsmul_extendScalarsCoconeι_succ _
        (nsmul_padicIntegersToPadicSubfieldInvPow_succ ℓ E Y), ih, ← Functor.map_nsmul,
        Mod.nsmul_extendScalarsCoconeι_succ _ (nsmul_padicIntegersToPadicSubfieldInvPow_succ ℓ E X)]
    have e {W Z : Sheaf (ProEt.topology Y) Ab.{u + 1}} (g : W ⟶ Z) : g ≫ (ℓ • 𝟙 Z) = ℓ • g := by
      rw [Preadditive.comp_nsmul, Category.comp_id]
    exact this.right_cancellation _ _ ((e _).trans (key.trans (e _).symm))

variable [QuasiCompact f] [QuasiSeparated f]

/-- **(Push) for `𝒪_E ⟶ E` is an isomorphism** for a quasi-compact quasi-separated `f`:
`E_Y ⊗_{𝒪_{E,Y}} f_* M ≅ f_*(E_X ⊗_{𝒪_{E,X}} M)`, both sides being the sequential colimit of the
multiplications by `ℓ` on `f_* M`. -/
instance isIso_pushHom_padicIntegersRingObjToContinuousMapRingObj
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)) :
    IsIso ((pushHom (padicIntegersRingObjToContinuousMapRingObj ℓ E) f).app M) := by
  have := preservesColimitsOfShape_lowerStar f ℕ
  let hY := isColimitPadicIntegersExtendScalarsCocone ℓ E Y ((f)_*⟦_⟧.obj M)
  let hX := Mod.isColimitSmulSequenceCoconeMap (f)_*[Ab.{u + 1}] _
    (isColimitPadicIntegersExtendScalarsCocone ℓ E X M)
  have h : ((pushHom (padicIntegersRingObjToContinuousMapRingObj ℓ E) f).app M).hom =
      (hY.coconePointUniqueUpToIso hX).hom := hY.hom_ext fun k ↦ by
    rw [IsColimit.comp_coconePointUniqueUpToIso_hom]
    exact extendScalarsCoconeι_comp_pushHom_app ℓ E f M k
  have : IsIso ((Mod.forget _).map
      ((pushHom (padicIntegersRingObjToContinuousMapRingObj ℓ E) f).app M)) := by
    change IsIso ((pushHom (padicIntegersRingObjToContinuousMapRingObj ℓ E) f).app M).hom
    rw [h]
    infer_instance
  exact isIso_of_reflects_iso _ (Mod.forget _)

end AlgebraicGeometry.ProEtale.CondensedRing
