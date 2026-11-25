/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.RightDerivedLowerStarFilteredColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ContinuousMapCoefficientSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ForgetRightDerivedLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralFlat
public import Mathlib.CategoryTheory.Monoidal.Linear
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import WeilConjectures.CategoryTheory.ModuleObjects.Linear
public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEnd
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.FourierTransform.ArtinSchreier
public import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule

/-!
# `E ⊗_{𝒪_E}` of injective `𝒪_E`-modules is `f_*`-acyclic

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E`, and
`f : X ⟶ Y` a quasi-compact quasi-separated morphism of schemes. For an injective
`𝒪_{E,X}`-module object `I`, the underlying abelian sheaf of `E_X ⊗_{𝒪_{E,X}} I` is
`f_*`-acyclic (`AlgebraicGeometry.ProEtale.rightAcyclic_lowerStar_extendScalars_of_injective`):
it is the sequential colimit `colim(I --ℓ--> I --ℓ--> ⋯)`
(`AlgebraicGeometry.ProEtale.isColimitPadicIntegersExtendScalarsCocone`), the underlying abelian
sheaf of `I` is injective, `𝒪_{E,X}` being flat over `ℤ`, and filtered colimits of `f_*`-acyclic
sheaves are `f_*`-acyclic (`AlgebraicGeometry.ProEtale.rightAcyclic_lowerStar_of_isColimit`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) (X : Scheme.{u})

/-- Pullback from the coefficient point is additive, since it is the composite of two
left adjoints between abelian sheaf categories.
Source: inverse image of abelian sheaves (blueprint: lem-kernel-condensed-projector-scalars). -/
instance additive_upperStarFromPoint : (upperStarFromPoint X).Additive :=
  have adj : upperStarFromPoint X ⊣ _ := pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  have : (upperStarFromPoint X).IsLeftAdjoint := adj.isLeftAdjoint
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint (upperStarFromPoint X)
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
    adj.leftAdjoint_preservesColimits
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (upperStarFromPoint X)
  Functor.additive_of_preservesBinaryBiproducts (upperStarFromPoint X)

/-- The map `p_X^*(ℓ⁻ᵏ φ) : 𝒪_{E,X} ⟶ E_X`. -/
noncomputable abbrev padicIntegersToPadicSubfieldInvPow (k : ℕ) :
    condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X ⟶
      condensedRingObj (Profinite.continuousMapRingObj E.1) X :=
  (upperStarFromPoint X).map (Profinite.padicIntegersRingObjToContinuousMapRingObjInvPow.{u} ℓ E k)

/-- `ℓ • p_X^*(ℓ⁻ᵏ⁻¹ φ) = p_X^*(ℓ⁻ᵏ φ)`. -/
lemma nsmul_padicIntegersToPadicSubfieldInvPow_succ (k : ℕ) :
    ℓ • padicIntegersToPadicSubfieldInvPow ℓ E X (k + 1) =
      padicIntegersToPadicSubfieldInvPow ℓ E X k := by
  rw [← (upperStarFromPoint X).map_nsmul,
    Profinite.nsmul_padicIntegersRingObjToContinuousMapRingObjInvPow_succ]

/-- `E_X = colim(𝒪_{E,X} --ℓ--> 𝒪_{E,X} --ℓ--> ⋯)`, along the maps `p_X^*(ℓ⁻ᵏ φ)`. -/
noncomputable def isColimitPadicIntegersToPadicSubfieldSmulSequenceCocone :
    IsColimit (Mod.smulSequenceCocone ℓ (padicIntegersToPadicSubfieldInvPow ℓ E X)
      (nsmul_padicIntegersToPadicSubfieldInvPow_succ ℓ E X)) := by
  have adj : upperStarFromPoint X ⊣ _ := pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
    adj.leftAdjoint_preservesColimits
  exact Mod.isColimitSmulSequenceCoconeMap (upperStarFromPoint X) _
    (Profinite.isColimitPadicIntegersRingObjSmulSequenceCocone ℓ E)

/-- **`E_X ⊗_{𝒪_{E,X}} M = colim(M --ℓ--> M --ℓ--> ⋯)`** for every `𝒪_{E,X}`-module `M`. -/
noncomputable def isColimitPadicIntegersExtendScalarsCocone
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)) :
    IsColimit (Mod.extendScalarsCocone (padicIntegersToPadicSubfield X ℓ E)
      (nsmul_padicIntegersToPadicSubfieldInvPow_succ ℓ E X) M) :=
  have := AB5OfSize_of_univLE.{0, 0} (Sheaf (ProEt.topology X) Ab.{u + 1})
  Mod.isColimitExtendScalarsCocone _
    (isColimitPadicIntegersToPadicSubfieldSmulSequenceCocone ℓ E X)
    (Mod.linear_of_isColimit _ (isColimitPadicIntegersToPadicSubfieldSmulSequenceCocone ℓ E X)
      (congrArg (upperStarFromPoint X).map
        (Profinite.padicIntegersRingObjToContinuousMapRingObjInvPow_zero ℓ E))) M

variable {X} {Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]

/-- For a quasi-compact quasi-separated `f` and an injective `𝒪_{E,X}`-module `I`, the underlying
abelian sheaf of `E_X ⊗_{𝒪_{E,X}} I` is `f_*`-acyclic. -/
lemma rightAcyclic_lowerStar_extendScalars_of_injective
    (I : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)) [Injective I] :
    ((f)_*[Ab.{u + 1}]).rightAcyclic
      ((Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).obj I).X :=
  have : Injective I.X := (Mod.forget (D := Sheaf (ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)).injective_obj_of_injective
      (inferInstance : Injective I)
  rightAcyclic_lowerStar_of_isColimit f (D := Mod.smulSequence I.X ℓ)
    (isColimitPadicIntegersExtendScalarsCocone ℓ E X I)
    fun _ ↦ (Functor.rightAcyclic_of_injective I.X : ((f)_*[Ab.{u + 1}]).rightAcyclic I.X)

end AlgebraicGeometry.ProEtale
