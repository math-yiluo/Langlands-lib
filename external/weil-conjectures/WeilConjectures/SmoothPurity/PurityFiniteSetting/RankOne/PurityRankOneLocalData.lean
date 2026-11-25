/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.SmoothPurity.SupportLongExact
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineDatum
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.EtaleOpenCohomologyComparison
public import WeilConjectures.CategoryTheory.Abelian.ExtRightDerivedCocycleComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonDerived
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.FieldTheory.RatFunc.AsPolynomial

import WeilConjectures.AlgebraicGeometry.Sites.Kummer

/-!
# The finite rank-one Kummer residue

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-a1-kummer,
`example-closed-support` (blueprint: example-closed-support).

The boundary below is specified by the snake boundary of the actual section complexes
of every injective resolution. In particular its sign is fixed. Module-valued derived
sections retain the coefficient action, so the normalization and its uniqueness are linear.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting.RankOne

/-- Evaluation on a site object, the section functor used in the support definition.
Source: blueprint proof Step 4 (blueprint: example-closed-support). -/
abbrev sections {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (A : Type (u + 1)) [CommRing A] (W : C) :=
  sheafToPresheaf J (ModuleCat.{u + 1} A) ⋙ (evaluation _ _).obj (op W)

/-- The recorded open immersion is the inclusion of its basic open.
Source: blueprint affine-line datum (blueprint: example-closed-support). -/
instance openImmersion_isOpenImmersion (Y : Scheme.{u}) :
    IsOpenImmersion (openImmersion Y) :=
  inferInstanceAs (IsOpenImmersion (((Line Y).basicOpen (coordinate Y)).ι))

/-- The standard punctured-line object of the small etale site.
Source: blueprint proof Step 1 (blueprint: example-closed-support). -/
def openObject (Y : Scheme.{u}) : (Line Y).Etale :=
  Scheme.Etale.mk (openImmersion Y)

/-- Restriction from the affine line to its punctured open, whose complement is the origin.
Source: blueprint proof Step 4 (blueprint: example-closed-support). -/
def restriction (Y : Scheme.{u}) : openObject Y ⟶ Scheme.Etale.mk (𝟙 (Line Y)) :=
  MorphismProperty.Over.homMk (openImmersion Y)
    (by change openImmersion Y ≫ 𝟙 (Line Y) = openImmersion Y; simp)

end WeilConjectures.PurityFiniteSetting.RankOne
