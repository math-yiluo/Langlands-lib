/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.BrownExceptionalAdjoint
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.Compactification.BaseChange
public import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.Compactification.BoundaryRefinement

/-! # The specified comparison maps for open restriction

Source: blueprint proposition-composition-open-restriction-compactifications-f, clauses (1)--(2).
These are the original maps, separated from the exceptional-adjoint theorem so that
its geometric compact-support comparison can be proved independently.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Restriction of the existing exact termwise inverse image to the recorded localizing
closures. The witness certifies membership only; no functor is chosen.
Source: blueprint proposition-composition-open-restriction-compactifications-f (1)
(blueprint: def-sfb-mate-open-restriction-maps). -/
def mateOpenPullback {U X : Scheme.{u}} (j : U ⟶ X)
    (h : ∀ K : (localizingClosureProEtale Λ X).FullSubcategory,
      localizingClosureProEtale Λ U ((upperStar Λ j).mapDerivedCategory.obj K.obj)) :
    (localizingClosureProEtale Λ X).FullSubcategory ⥤
      (localizingClosureProEtale Λ U).FullSubcategory :=
  (localizingClosureProEtale Λ U).lift
    ((localizingClosureProEtale Λ X).ι ⋙ (upperStar Λ j).mapDerivedCategory) h

/-- Restriction of actual levelwise extension by zero to the localizing closures.
Source: blueprint proposition-composition-open-restriction-compactifications-f (1)
(blueprint: def-sfb-mate-open-restriction-maps). -/
def mateOpenExtension {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (h : ∀ K : (localizingClosureProEtale Λ U).FullSubcategory,
      localizingClosureProEtale Λ X
        ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj K.obj)) :
    (localizingClosureProEtale Λ U).FullSubcategory ⥤
      (localizingClosureProEtale Λ X).FullSubcategory :=
  (localizingClosureProEtale Λ X).lift
    ((localizingClosureProEtale Λ U).ι ⋙
      (openImmersionLowerShriek Λ j).mapDerivedCategory) h

/-- Canonical composition of open extensions: the left-adjoint comparison of the exact
open adjunctions and the coefficient-compatible inverse-image compositor.
Source: blueprint proposition-composition-open-restriction-compactifications-f (2), composite
adjunction calculation (blueprint: def-sfb-mate-open-restriction-maps). -/
def mateOpenExtensionComp {U X Z : Scheme.{u}} (j : U ⟶ X) (i : X ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion i] :
    (openImmersionLowerShriek Λ j).mapDerivedCategory ⋙
        (openImmersionLowerShriek Λ i).mapDerivedCategory ≅
      (openImmersionLowerShriek Λ (j ≫ i)).mapDerivedCategory :=
  Adjunction.leftAdjointUniq
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).comp
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i))
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ (j ≫ i)).ofNatIsoRight
      (Functor.mapDerivedCategoryNatIso (upperStarComp Λ j i) ≪≫
        (Functor.mapDerivedCategoryCompIso (upperStar Λ i) (upperStar Λ j)).symm))

/-- The canonical identification of compact-support image for the trivial open
compactification (j,id) with levelwise extension by zero. The identity direct-image
identification is the derived one normalized on ordinary module sheaves.
Source: blueprint proposition-composition-open-restriction-compactifications-f (1), trivial
compactification (blueprint: def-sfb-mate-open-restriction-maps). -/
def mateOpenTrivialLowerShriek {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    rightDerivedLowerShriekOfCompactification Λ (Compactification.ofIsOpenImmersion j) ≅
      (openImmersionLowerShriek Λ j).mapDerivedCategory :=
  Functor.isoWhiskerLeft (openImmersionLowerShriek Λ j).mapDerivedCategory
      (refinementDerivedLowerStarId Λ X) ≪≫
    Functor.rightUnitor _

end AlgebraicGeometry.ProEtale.CondensedRing
