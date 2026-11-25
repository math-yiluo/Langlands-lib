/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.CategoryTheory.Sites.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula

/-!
# Extension of scalars of pro-étale sheaves of modules

For a ring morphism `φ : R →+* S` and a scheme `X`, extension of scalars
`S ⊗_R - : Sh(X_proét, R) ⥤ Sh(X_proét, S)` is the sheafified postcomposition with
`ModuleCat.extendScalars φ`. It is left adjoint to restriction of scalars. These are the
transition functors `𝒪_E ⟶ 𝒪_{E'}` between the `ℓ`-adic coefficient stages, through which
the `ℚ̄_ℓ` stage of `sk-thm-sf-pf-proetale` is reached.

## Main definitions

- `AlgebraicGeometry.ProEtale.sheafExtendScalars φ X`: extension of scalars.
- `AlgebraicGeometry.ProEtale.sheafExtendScalarsAdjunction φ X`: it is left adjoint to
  restriction of scalars.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

variable {R S : Type (u + 1)} [CommRing R] [CommRing S] (φ : R →+* S) (X : Scheme.{u})

/-- Extension of scalars `S ⊗_R -` of pro-étale sheaves of modules along `φ : R →+* S`. -/
noncomputable def sheafExtendScalars :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R) ⥤
      Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} S) :=
  Sheaf.composeAndSheafify _ (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)

/-- Extension of scalars of pro-étale sheaves of modules is left adjoint to restriction of
scalars. -/
noncomputable def sheafExtendScalarsAdjunction :
    sheafExtendScalars φ X ⊣
      sheafCompose (Scheme.ProEt.topology X) (ModuleCat.restrictScalars.{u + 1} φ) :=
  Sheaf.adjunction _ (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)

instance : (sheafExtendScalars φ X).IsLeftAdjoint :=
  (sheafExtendScalarsAdjunction φ X).isLeftAdjoint

variable {X} {Y : Scheme.{u}} (g : Y ⟶ X)

/-- Restriction of scalars commutes with the direct image `g_*`: both composites restrict a
sheaf along base change and forget the `S`-module structure to an `R`-module structure. -/
noncomputable def lowerStarCompSheafComposeRestrictScalarsIso :
    ProEtale.lowerStar (ModuleCat.{u + 1} S) g ⋙
        sheafCompose (Scheme.ProEt.topology X) (ModuleCat.restrictScalars.{u + 1} φ) ≅
      sheafCompose (Scheme.ProEt.topology Y) (ModuleCat.restrictScalars.{u + 1} φ) ⋙
        ProEtale.lowerStar (ModuleCat.{u + 1} R) g :=
  Iso.refl _

/-- Extension of scalars commutes with the pullback `g^*`: `g^* (S ⊗_R F) ≅ S ⊗_R g^* F`, the
conjugate of `AlgebraicGeometry.ProEtale.lowerStarCompSheafComposeRestrictScalarsIso`. -/
noncomputable def sheafExtendScalarsCompUpperStarIso :
    sheafExtendScalars φ X ⋙ ProEtale.upperStar (ModuleCat.{u + 1} S) g ≅
      ProEtale.upperStar (ModuleCat.{u + 1} R) g ⋙ sheafExtendScalars φ Y :=
  (conjugateIsoEquiv
    ((ProEtale.upperStarLowerStarAdjunction _ g).comp (sheafExtendScalarsAdjunction φ Y))
    ((sheafExtendScalarsAdjunction φ X).comp (ProEtale.upperStarLowerStarAdjunction _ g))).symm
    (lowerStarCompSheafComposeRestrictScalarsIso φ g).symm

variable (X)

/-- Extension of étale sheaves of modules along `φ`. -/
noncomputable def etaleSheafExtendScalars :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} S) :=
  Sheaf.composeAndSheafify _ (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)

/-- Extension of étale sheaves of modules is left adjoint to restriction of scalars. -/
noncomputable def etaleSheafExtendScalarsAdjunction :
    etaleSheafExtendScalars φ X ⊣
      sheafCompose X.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} φ) :=
  Sheaf.adjunction _ (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)

/-- Restriction of scalars commutes with the comparison restriction `ν_*`. -/
noncomputable def comparisonLowerStarCompSheafComposeRestrictScalarsIso :
    ν_*(X)[ModuleCat.{u + 1} S] ⋙
        sheafCompose X.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} φ) ≅
      sheafCompose (Scheme.ProEt.topology X) (ModuleCat.restrictScalars.{u + 1} φ) ⋙
        ν_*(X)[ModuleCat.{u + 1} R] :=
  Iso.refl _

/-- Extension of scalars commutes with the comparison `ν^*`:
`ν^*(S ⊗_R F) ≅ S ⊗_R ν^* F`. -/
noncomputable def etaleSheafExtendScalarsCompComparisonUpperStarIso :
    etaleSheafExtendScalars φ X ⋙ ν^*(X)[ModuleCat.{u + 1} S] ≅
      ν^*(X)[ModuleCat.{u + 1} R] ⋙ sheafExtendScalars φ X :=
  (conjugateIsoEquiv
    ((comparisonAdjunction _ X).comp (sheafExtendScalarsAdjunction φ X))
    ((etaleSheafExtendScalarsAdjunction φ X).comp (comparisonAdjunction _ X))).symm
    (comparisonLowerStarCompSheafComposeRestrictScalarsIso φ X).symm

variable {φ} in
/-- Extension of scalars along a flat ring morphism is exact on pro-étale sheaves: it is the
sheafification of the levelwise extension of scalars, which is left exact for flat `φ`. -/
lemma preservesFiniteLimits_sheafExtendScalars (hφ : φ.Flat) :
    Limits.PreservesFiniteLimits (sheafExtendScalars φ X) := by
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat.{u + 1} hφ
  have : Limits.PreservesFiniteLimits ((Functor.whiskeringRight X.ProEtᵒᵖ _ _).obj
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)) := by
    constructor
    intro J _ _
    infer_instance
  unfold sheafExtendScalars Sheaf.composeAndSheafify
  have := Limits.comp_preservesFiniteLimits
    ((Functor.whiskeringRight X.ProEtᵒᵖ _ _).obj
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ))
    (presheafToSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} S))
  exact Limits.comp_preservesFiniteLimits _ _

end AlgebraicGeometry.ProEtale
