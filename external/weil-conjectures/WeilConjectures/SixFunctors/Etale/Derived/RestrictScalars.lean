/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.CoextendScalars
public import WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtension

/-!
# Restriction of scalars commutes with the derived direct image

For a flat ring morphism `φ : Λ →+* Λ'`, restriction of scalars from étale sheaves of
`Λ'`-modules to étale sheaves of `Λ`-modules has an exact left adjoint, the extension of scalars
`Λ' ⊗_Λ -`, so it preserves K-injective complexes. It is exact and commutes with the direct image
`g_*` on the nose (both forget the `Λ'`-action on the sections over `V ×_Y Z`), hence it commutes
with the derived direct image: `Rg_* ⋙ Res ≅ Res ⋙ Rg_*`.

The case of the blueprint is `Λ = 𝔽_ℓ` and `Λ'` a finite `𝔽_ℓ`-algebra, which is free, hence
flat, over the field `𝔽_ℓ`: the derived direct image of a sheaf of `Λ'`-modules is computed by
that of its underlying sheaf of `𝔽_ℓ`-modules.

## Main statements

- `AlgebraicGeometry.Etale.preservesKInjectiveComplexes_restrictScalars`: restriction of scalars
  along a flat ring morphism preserves K-injective complexes.
- `AlgebraicGeometry.Etale.rightDerivedLowerStarCompDerivedRestrictScalarsIso`: restriction of
  scalars commutes with `Rg_*` (`corollary-open-direct-image-over-field--1`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {φ : Λ →+* Λ'}

/-- Extension of scalars of étale sheaves of modules along a flat ring morphism is left exact:
it is the sheafification of the objectwise extension of scalars, which is left exact for flat
`φ`. -/
lemma preservesFiniteLimits_etaleSheafExtendScalars (hφ : φ.Flat) (X : Scheme.{u}) :
    PreservesFiniteLimits (ProEtale.etaleSheafExtendScalars φ X) := by
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat.{u + 1} hφ
  have : PreservesFiniteLimits ((Functor.whiskeringRight X.Etaleᵒᵖ _ _).obj
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)) := by
    constructor
    intro J _ _
    infer_instance
  unfold ProEtale.etaleSheafExtendScalars Sheaf.composeAndSheafify
  have := comp_preservesFiniteLimits
    ((Functor.whiskeringRight X.Etaleᵒᵖ _ _).obj
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ))
    (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))
  exact comp_preservesFiniteLimits _ _

/-- Restriction of scalars of étale sheaves along a flat ring morphism preserves K-injective
complexes: its left adjoint, extension of scalars, is exact. -/
lemma preservesKInjectiveComplexes_restrictScalars (hφ : φ.Flat) (X : Scheme.{u}) :
    (Sheaf.restrictScalars X.smallEtaleTopology φ).PreservesKInjectiveComplexes := by
  have := preservesFiniteLimits_etaleSheafExtendScalars hφ X
  have : (ProEtale.etaleSheafExtendScalars φ X).Additive :=
    (ProEtale.etaleSheafExtendScalarsAdjunction φ X).left_adjoint_additive
  have : (ProEtale.etaleSheafExtendScalars φ X).IsLeftAdjoint :=
    (ProEtale.etaleSheafExtendScalarsAdjunction φ X).isLeftAdjoint
  have : (ProEtale.etaleSheafExtendScalars φ X).PreservesHomology :=
    Functor.preservesHomology_of_preservesMonos_and_cokernels _
  exact (ProEtale.etaleSheafExtendScalarsAdjunction φ X).preservesKInjectiveComplexes

variable (φ)

/-- Blueprint `corollary-open-direct-image-over-field--1`: Changing finite coefficient rings in
a direct image.

Let `φ : Λ →+* Λ'` be a flat ring morphism (in the blueprint, `Λ = 𝔽_ℓ` and `Λ'` a finite
`𝔽_ℓ`-algebra) and let `g : Z ⟶ Y` be a morphism of schemes. Forgetting the `Λ'`-action
identifies the derived direct image of a complex of sheaves of `Λ'`-modules with the derived
direct image of the underlying complex of sheaves of `Λ`-modules:
`Res ∘ Rg_* ≅ Rg_* ∘ Res` on the unbounded derived categories. -/
noncomputable def rightDerivedLowerStarCompDerivedRestrictScalarsIso (hφ : φ.Flat)
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    ((g)_*[ModuleCat.{u + 1} Λ']).rightDerivedFunctor ⋙ derivedRestrictScalars φ Y ≅
      derivedRestrictScalars φ Z ⋙ ((g)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctor :=
  have := preservesKInjectiveComplexes_restrictScalars hφ Z
  Functor.isoWhiskerLeft _ (Sheaf.restrictScalars Y.smallEtaleTopology
      φ).rightDerivedFunctorIsoMapDerivedCategory.symm ≪≫
    Functor.rightDerivedFunctorCompIso' _ _ (lowerStarCompRestrictScalarsIso φ g) ≪≫
    (Functor.rightDerivedFunctorCompIso' _ _ (Iso.refl _)).symm ≪≫
    Functor.isoWhiskerRight
      (Sheaf.restrictScalars Z.smallEtaleTopology φ).rightDerivedFunctorIsoMapDerivedCategory _

end Etale

end AlgebraicGeometry
