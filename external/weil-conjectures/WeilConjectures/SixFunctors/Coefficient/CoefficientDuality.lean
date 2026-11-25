/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import Mathlib.Algebra.Module.Injective
public import Mathlib.RingTheory.Artinian.Defs

/-! # Coefficient duality on the module derived category

Source: Weil blueprint, lemma-perfect-complexes-geometric-point--8, paragraphs 1--3;
Stacks Project, Tags 08J7 and 07VI (blueprint: def-sf-coefficient-duality).
The module category is the module category of the one-object ringed site.
Its natural small-Hom derived localization is supplied by its Grothendieck instance.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace WeilConjectures

/-- Derived coefficient duality is internal Hom into the tensor unit `R[0]`.
The closed structure is the derived tensor--Hom adjunction, obtained by deriving
Hom into K-injective resolutions, as in the one-object case of Tag 08J7.
Source: blueprint lemma-perfect-complexes-geometric-point--8, first clause; Stacks 08J7
(blueprint: def-sf-coefficient-duality). -/
noncomputable def coefficientDerivedDual (R : Type u) [CommRing R]
    [HasDerivedCategory.{u} (ModuleCat.{u} R)] :
    (DerivedCategory (ModuleCat.{u} R))ᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} R) :=
  MonoidalClosed.internalHom.flip.obj (𝟙_ (DerivedCategory (ModuleCat.{u} R)))

end WeilConjectures
