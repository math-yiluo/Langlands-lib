/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicIntegralModelPair
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.CategoryTheory.NatIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionMapExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicSubfieldFinite
public import WeilConjectures.Tactic.ExactModProofs

/-!
# Projection maps under extension of scalars: hypotheses

Two auxiliary statements for the `ℚ̄_ℓ` projection formula
(`ProEtale.CondensedRing.isIso_projectionMap_padicAlgClRingObj_of_integral`): bounded
constructible complexes are bounded below, and
`ProEtale.CondensedRing.isIso_projectionMap_app_app_extendScalars` with explicit hypotheses.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace Profinite

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : _root_.PadicAlgCl.FiniteIntermediateField ℓ)

/-! ### Named coefficient rings

The statements of the two coefficient changes of the projection formula are stated with these
names rather than with `padicIntegersRingObj ℓ E.1` and `continuousMapRingObj E.1`. Their
elaborated types stay small, and so does the export of their library-suggestion data, which
walks the unshared statement trees (minutes per statement otherwise). -/

/-- The ring object `𝒪̲_E` of condensed abelian groups for a finite subextension `E`. -/
noncomputable abbrev integersRingObj : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  padicIntegersRingObj.{u} ℓ E.1

/-- The ring object `E̲` of condensed abelian groups for a finite subextension `E`. -/
noncomputable abbrev subfieldRingObj : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  continuousMapRingObj.{u} E.1

/-- The inclusion `𝒪̲_E ⟶ E̲`. -/
noncomputable abbrev integersRingObjToSubfieldRingObj :
    integersRingObj.{u} ℓ E ⟶ subfieldRingObj ℓ E :=
  AlgebraicGeometry.ProEtale.padicIntegersRingObjToContinuousMapRingObj.{u} ℓ E

/-- The inclusion `E̲ ⟶ ℚ̲̄_ℓ`. -/
noncomputable abbrev subfieldRingObjToPadicAlgClRingObj :
    subfieldRingObj.{u} ℓ E ⟶ padicAlgClRingObj ℓ :=
  padicSubfieldRingObjToPadicAlgCl.{u} ℓ E

end Profinite

namespace AlgebraicGeometry.ProEtale

/-- A bounded constructible complex is bounded below. -/
lemma exists_isGE_of_boundedConstructible {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)}
    (hK : boundedConstructible R K) : ∃ n : ℤ, K.IsGE n := by
  obtain ⟨⟨n, hn⟩, -⟩ := hK.1
  exact ⟨n, hn⟩

namespace CondensedRing

open Scheme PadicAlgCl

/-- `isIso_projectionMap_app_app_extendScalars` with explicit hypotheses, the projection map with
coefficients `Λ` last. -/
lemma isIso_projectionMap_app_app_extendScalars_of_isIso
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
    [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]
    [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (h₁ : IsIso ((derivedPushHom a f).app K))
    (h₂ : IsIso ((derivedPushHom a f).app
      (((curriedTensor _).obj K).obj (((f)^*⟦Λ⟧).leftDerivedFunctor.obj M))))
    (h₀ : IsIso (((projectionMap Λ f).app K).app M)) :
    IsIso (((projectionMap Λ' f).app
      ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj K)).app
        ((Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctor.obj M)) :=
  isIso_projectionMap_app_app_extendScalars a f K M

end CondensedRing

end AlgebraicGeometry.ProEtale
