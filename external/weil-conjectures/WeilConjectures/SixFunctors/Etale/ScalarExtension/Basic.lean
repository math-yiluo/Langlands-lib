/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Extension of scalars of étale sheaves of modules

For a morphism `φ : R →+* S` of commutative rings, extension of scalars `S ⊗_R -` of étale
sheaves of modules (`AlgebraicGeometry.Etale.sheafExtendScalars`) is the sheafification of the
sectionwise extension of scalars. It is left adjoint to restriction of scalars
(`AlgebraicGeometry.Etale.sheafExtendScalarsAdjunction`) and commutes with the pullbacks
(`AlgebraicGeometry.Etale.sheafExtendScalarsCompUpperStarIso`).

This is the same functor as `AlgebraicGeometry.ProEtale.etaleSheafExtendScalars`, stated in a
file with light imports.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

variable {R S : Type (u + 1)} [CommRing R] [CommRing S] (φ : R →+* S)

/- Mathlib's instance is stated for `extendScalars.{u₁, u₂, max u₂ w}`, and unifying
`u + 1 =?= max (u + 1) ?w` gets stuck. -/
instance instIsLeftAdjointModuleCatExtendScalars_basic
    (φ : R →+* S) : (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ).IsLeftAdjoint :=
  (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ).isLeftAdjoint

section

variable (X : Scheme.{u})

/-- Extension of scalars `S ⊗_R -` of étale sheaves of modules along `φ : R →+* S`. -/
noncomputable def sheafExtendScalars :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} S) :=
  Sheaf.composeAndSheafify _ (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)

/-- Extension of scalars of étale sheaves of modules is left adjoint to restriction of
scalars. -/
noncomputable def sheafExtendScalarsAdjunction :
    sheafExtendScalars φ X ⊣
      sheafCompose X.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} φ) :=
  Sheaf.adjunction _ (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)

instance : (sheafExtendScalars φ X).IsLeftAdjoint :=
  (sheafExtendScalarsAdjunction φ X).isLeftAdjoint

/-- Restriction of scalars of étale sheaves is additive. -/
instance additive_sheafComposeRestrictScalars :
    (sheafCompose X.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} φ)).Additive where
  map_add {F G a b} := by
    ext U x
    rfl

/-- Extension of scalars of étale sheaves is additive, being a left adjoint. -/
instance additive_sheafExtendScalars : (sheafExtendScalars φ X).Additive :=
  (sheafExtendScalarsAdjunction φ X).left_adjoint_additive

end

variable {X Y : Scheme.{u}}

/-- Extension of scalars of étale sheaves commutes with pullback, `g^*(S ⊗_R F) ≅ S ⊗_R g^* F`:
both functors are left adjoint to `G ↦ g_* G` viewed as a sheaf of `R`-modules. -/
noncomputable def sheafExtendScalarsCompUpperStarIso (g : Y ⟶ X) :
    sheafExtendScalars φ X ⋙ Etale.upperStar (ModuleCat.{u + 1} S) g ≅
      Etale.upperStar (ModuleCat.{u + 1} R) g ⋙ sheafExtendScalars φ Y :=
  ((sheafExtendScalarsAdjunction φ X).comp
      (Etale.upperStarLowerStarAdjunction _ g)).leftAdjointUniq
    (((Etale.upperStarLowerStarAdjunction _ g).comp
      (sheafExtendScalarsAdjunction φ Y)).ofNatIsoRight
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)))

end AlgebraicGeometry.Etale
