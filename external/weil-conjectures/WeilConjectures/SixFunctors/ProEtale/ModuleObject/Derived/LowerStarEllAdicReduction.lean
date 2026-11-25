/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicIntegralModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicSubfieldFinite

/-!
# Finiteness of `Rf_*` for `E` and `ℚ̄_ℓ` from the integral case

Let `ℓ` be a prime and `f : X ⟶ Y` a quasi-compact quasi-separated morphism of schemes, with `X`
topologically noetherian. The second paragraph of the proof of blueprint
`proposition-six-operations-dctf--5` deduces the preservation of bounded constructible complexes by
`Rf_*` for the coefficient rings `E` (a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`) and `ℚ̄_ℓ` from the
one for the rings of integers `𝒪_E`. This file formalizes this deduction:

* `boundedConstructible_rightDerivedLowerStar_obj_continuousMapRingObj_of_padicIntegers`:
  if `Rf_*` preserves `Dᵇc(-)⟦𝒪_E⟧`, it preserves `Dᵇc(-)⟦E⟧`. A bounded constructible
  `E`-complex is `E ⊗ᴸ_{𝒪_E} K₀` for an integral model `K₀`
  (`ProEtale.exists_boundedConstructibleExtendScalars_obj_iso`), the comparison **(Push)**
  `E ⊗ᴸ Rf_* K₀ ⟶ Rf_*(E ⊗ᴸ K₀)` is an isomorphism on bounded below objects
  (`ProEtale.CondensedRing.isIso_derivedPushHom_app_padicIntegers_of_isGE`), and `E ⊗ᴸ -`
  preserves bounded constructible complexes
  (`ProEtale.boundedConstructible_derivedExtendScalars_obj`).
* `boundedConstructible_rightDerivedLowerStar_obj_padicAlgCl_of_continuousMapRingObj`:
  if `Rf_*` preserves `Dᵇc(-)⟦E⟧` for every finite subextension `E`, it preserves
  `Dᵇc(-)⟦ℚ̄_ℓ⟧`. A bounded constructible `ℚ̄_ℓ`-complex descends to some `E`
  (`ProEtale.constructibleCocone_essSurjObj`), the comparison (Push) for `E ⟶ ℚ̄_ℓ` is an
  isomorphism on bounded below objects
  (`ProEtale.CondensedRing.isIso_derivedPushHom_app_padicSubfieldRingObjToPadicAlgCl_of_isGE`),
  and `ℚ̄_ℓ ⊗ᴸ_E -` preserves bounded constructible complexes
  (`ProEtale.boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj`).
* `boundedConstructible_rightDerivedLowerStar_obj_padicAlgCl_of_padicIntegers`:
  the composite of the two.

## Implementation notes

These statements are made above
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, since the
comparisons (Push) and the integral models are proved in files importing it. They take the
integral finiteness as a hypothesis, so that they do not depend on the `sorry`ed finiteness
theorems of that file.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] {X Y : Scheme.{u}} [TopologicalSpace.NoetherianSpace X]
  (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]

/-- **`Rf_*` on `E`-complexes from `Rf_*` on `𝒪_E`-complexes** (blueprint
`proposition-six-operations-dctf--5`, second paragraph of the proof): if `Rf_*` carries bounded
constructible `𝒪_E`-complexes to bounded constructible complexes, then so it does for
`E`-complexes. -/
theorem boundedConstructible_rightDerivedLowerStar_obj_continuousMapRingObj_of_padicIntegers
    (E : FiniteIntermediateField ℓ)
    (h : ∀ K₀ : Dᵇc(X)⟦Profinite.padicIntegersRingObj ℓ E.1⟧,
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y)
        ((R((f)_*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj K₀.obj))
    (K : Dᵇc(X)⟦Profinite.continuousMapRingObj E.1⟧) :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E.1) Y)
      ((R((f)_*⟦Profinite.continuousMapRingObj E.1⟧)).obj K.obj) := by
  obtain ⟨K₀, ⟨e⟩⟩ := exists_boundedConstructibleExtendScalars_obj_iso X ℓ E K
  obtain ⟨⟨a, _⟩, -⟩ := K₀.property.1
  have := isIso_derivedPushHom_app_padicIntegers_of_isGE ℓ E f K₀.obj a
  exact (boundedConstructible _).prop_of_iso
    (asIso ((derivedPushHom (padicIntegersRingObjToContinuousMapRingObj ℓ E) f).app K₀.obj) ≪≫
      (R((f)_*⟦Profinite.continuousMapRingObj E.1⟧)).mapIso
        ((boundedConstructible _).ι.mapIso e))
    (boundedConstructible_derivedExtendScalars_obj Y ℓ E ⟨_, h K₀⟩)

/-- **`Rf_*` on `ℚ̄_ℓ`-complexes from `Rf_*` on `E`-complexes** (blueprint
`proposition-six-operations-dctf--5`, second paragraph of the proof): if `Rf_*` carries bounded
constructible `E`-complexes to bounded constructible complexes for every finite subextension
`E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, then so it does for `ℚ̄_ℓ`-complexes. -/
theorem boundedConstructible_rightDerivedLowerStar_obj_padicAlgCl_of_continuousMapRingObj
    (h : ∀ (E : FiniteIntermediateField ℓ) (K : Dᵇc(X)⟦Profinite.continuousMapRingObj E.1⟧),
      boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E.1) Y)
        ((R((f)_*⟦Profinite.continuousMapRingObj E.1⟧)).obj K.obj))
    (K : Dᵇc(X)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y)
      ((R((f)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K.obj) := by
  obtain ⟨E, K_E, ⟨e⟩⟩ := constructibleCocone_essSurjObj X ℓ K
  obtain ⟨⟨a, _⟩, -⟩ := K_E.property.1
  have := isIso_derivedPushHom_app_padicSubfieldRingObjToPadicAlgCl_of_isGE ℓ E f K_E.obj a
  exact (boundedConstructible _).prop_of_iso
    (asIso ((derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f).app K_E.obj) ≪≫
      (R((f)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).mapIso ((boundedConstructible _).ι.mapIso e))
    (boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj Y ℓ E ⟨_, h E K_E⟩)

/-- **`Rf_*` on `ℚ̄_ℓ`-complexes from `Rf_*` on `𝒪_E`-complexes** (blueprint
`proposition-six-operations-dctf--5`, second paragraph of the proof): if `Rf_*` carries bounded
constructible `𝒪_E`-complexes to bounded constructible complexes for every finite subextension
`E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, then so it does for `ℚ̄_ℓ`-complexes. -/
theorem boundedConstructible_rightDerivedLowerStar_obj_padicAlgCl_of_padicIntegers
    (h : ∀ (E : FiniteIntermediateField ℓ) (K₀ : Dᵇc(X)⟦Profinite.padicIntegersRingObj ℓ E.1⟧),
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y)
        ((R((f)_*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj K₀.obj))
    (K : Dᵇc(X)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y)
      ((R((f)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K.obj) :=
  boundedConstructible_rightDerivedLowerStar_obj_padicAlgCl_of_continuousMapRingObj ℓ f
    (fun E ↦ boundedConstructible_rightDerivedLowerStar_obj_continuousMapRingObj_of_padicIntegers
      ℓ f E (h E)) K

end AlgebraicGeometry.ProEtale.CondensedRing
