/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.CategoryTheory.Sites.Point.IsMonoidalW
public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import WeilConjectures.CategoryTheory.Sites.SheafComposePushforwardMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtension

/-!
# Extension of scalars of pro-étale sheaves is monoidal

For a morphism of commutative rings `φ : R →+* S`, extension of scalars
`S ⊗_R - : Sh(X_proét, R) ⥤ Sh(X_proét, S)` is strong monoidal, and for a morphism of schemes
`g : Y ⟶ X` the isomorphism `g^* (S ⊗_R F) ≅ S ⊗_R g^* F` of
`AlgebraicGeometry.ProEtale.sheafExtendScalarsCompUpperStarIso` is monoidal.

## Main results

- `AlgebraicGeometry.ProEtale.monoidal_sheafExtendScalars`: extension of scalars is strong
  monoidal, its oplax structure being that of the left adjoint of the lax monoidal restriction
  of scalars.
- `AlgebraicGeometry.ProEtale.isMonoidal_sheafExtendScalarsCompUpperStarIso_hom`: the
  commutation with `g^*` is monoidal.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale

open Scheme

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

-- `GrothendieckTopology.W.monoidal` gives the monoidality of `W` directly; the instance going
-- through enough points of the site is tried first and makes the search time out.
attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints

variable {R S : Type (u + 1)} [CommRing R] [CommRing S] (φ : R →+* S) (X : Scheme.{u})

/-- Restriction of scalars of pro-étale sheaves is additive. -/
instance additive_sheafComposeRestrictScalars :
    (sheafCompose (Scheme.ProEt.topology X)
      (ModuleCat.restrictScalars.{u + 1} φ)).Additive where
  map_add {F G a b} := by
    ext U x
    rfl

/-- Extension of scalars of pro-étale sheaves is additive, being a left adjoint. -/
instance additive_sheafExtendScalars : (sheafExtendScalars φ X).Additive :=
  (sheafExtendScalarsAdjunction φ X).left_adjoint_additive

/-- Restriction of scalars of pro-étale sheaves is lax monoidal. -/
noncomputable instance laxMonoidal_sheafComposeRestrictScalars :
    (sheafCompose (Scheme.ProEt.topology X)
      (ModuleCat.restrictScalars.{u + 1} φ)).LaxMonoidal :=
  sheafComposeLaxMonoidal _ _

/-- Extension of scalars of pro-étale sheaves is oplax monoidal, being left adjoint to the lax
monoidal restriction of scalars. -/
noncomputable instance oplaxMonoidal_sheafExtendScalars :
    (sheafExtendScalars φ X).OplaxMonoidal :=
  composeAndSheafifyOplaxMonoidal _ (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)

/-- The adjunction between extension and restriction of scalars of pro-étale sheaves is
monoidal. -/
instance isMonoidal_sheafExtendScalarsAdjunction :
    (sheafExtendScalarsAdjunction φ X).IsMonoidal :=
  isMonoidal_sheafAdjunction _ (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)

instance isIso_δ_sheafExtendScalars (F G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)) :
    IsIso (Functor.OplaxMonoidal.δ (sheafExtendScalars φ X) F G) :=
  isIso_δ_composeAndSheafify _ (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ) F G

instance isIso_η_sheafExtendScalars :
    IsIso (Functor.OplaxMonoidal.η (sheafExtendScalars φ X)) :=
  isIso_η_composeAndSheafify _ (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)

/-- Extension of scalars of pro-étale sheaves is strong monoidal. -/
noncomputable instance monoidal_sheafExtendScalars : (sheafExtendScalars φ X).Monoidal :=
  .ofOplaxMonoidal _

variable {X} {Y : Scheme.{u}} (g : Y ⟶ X)

/-- The identification `g_* ⋙ res ≅ res ⋙ g_*` of
`AlgebraicGeometry.ProEtale.lowerStarCompSheafComposeRestrictScalarsIso` is monoidal. -/
instance isMonoidal_lowerStarCompSheafComposeRestrictScalarsIso_hom :
    NatTrans.IsMonoidal (lowerStarCompSheafComposeRestrictScalarsIso φ g).hom := by
  have := Functor.isMonoidal_sheafPushforwardContinuousCompSheafComposeIso_hom
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g) (Scheme.ProEt.topology X)
    (Scheme.ProEt.topology Y) (A := ModuleCat.{u + 1} S) (ModuleCat.restrictScalars.{u + 1} φ)
  exact this

/-- The isomorphism `g^* (S ⊗_R F) ≅ S ⊗_R g^* F` of
`AlgebraicGeometry.ProEtale.sheafExtendScalarsCompUpperStarIso` is monoidal, being the conjugate
of the monoidal identification `g_* ⋙ res ≅ res ⋙ g_*`. -/
instance isMonoidal_sheafExtendScalarsCompUpperStarIso_hom :
    NatTrans.IsMonoidal (sheafExtendScalarsCompUpperStarIso φ g).hom := by
  have : NatTrans.IsMonoidal (lowerStarCompSheafComposeRestrictScalarsIso φ g).symm.hom :=
    inferInstanceAs (NatTrans.IsMonoidal (lowerStarCompSheafComposeRestrictScalarsIso φ g).inv)
  unfold sheafExtendScalarsCompUpperStarIso
  exact isMonoidal_conjugateEquiv_symm _ _ _

end AlgebraicGeometry.ProEtale
