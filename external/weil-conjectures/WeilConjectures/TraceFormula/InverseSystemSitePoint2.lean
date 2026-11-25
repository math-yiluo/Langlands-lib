/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import WeilConjectures.CategoryTheory.Grothendieck.GrothendieckTopos
public import WeilConjectures.TraceFormula.InverseSystemSitePoint
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.ObjectProperty.FunctorCategory.PreservesLimits
import Mathlib.CategoryTheory.Functor.TypeValuedFlat
import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Inverse-system site points

Source: Stacks Project, Sites, Tags 00YC and 00YA, with the inverse-system
construction in Tag 00YQ (blueprint: lem-trf-inverse-system-site-point).

The inverse system is represented by a functor from the opposite of a directed
poset.  Its colimit of representables is the functor `inverseSystemHomFunctor`,
and the colimit of sections along it is the functor
`inverseSystemSectionColimitFunctor`.  The site is a precoverage satisfying the
site axioms `Precoverage.IsSiteForCoverings`, with sheaves for the generated
Grothendieck topology, as in the dependency def-weil-pbc-sites-and-cohomology.
-/

@[expose] public section

set_option autoImplicit false

-- This proof-only module intentionally exports no declarations.
set_option linter.privateModule false

universe w u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

private noncomputable def homMk {C : Type u} [Category.{u} C]
    {I : Type u} [PartialOrder I] (U : Iᵒᵖ ⥤ C) {i : I} {X : C}
    (f : U.obj (op i) ⟶ X) : (inverseSystemHomFunctor U).obj X :=
  (colimit.ι (inverseSystemRepresentableDiagram U) i).app X f

end CategoryTheory
