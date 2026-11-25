/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs

/-!

# Derived lower shriek on module objects over `Λ`

This is the module-object counterpart of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek`, for the
coefficient ring objects `Λ_X = p_X^* Λ` of a commutative condensed ring `Λ`.

As there, the derived functors entering `Rf_!` are not given definitions of their own: they
are the generic derived-functor constructions of the folder
`WeilConjectures.CategoryTheory.DerivedCategory`, written `D(-)`, `D+(-)`, `R(-)` and `R+(-)`,
applied to the underived functors `(c.i)_!open⟦Λ⟧` and `(c.g)_*⟦Λ⟧` on module objects. The
extension by zero `i_!` is exact on module objects, so it is derived levelwise, while the
pushforward `g_*` is derived via K-injective resolutions.

## Main definitions

- `ProEtale.CondensedRing.rightDerivedLowerShriekOfCompactification` : `Rf_!` with
  respect to a compactification `c`, with scoped notation `Rf_!(c)⟦Λ⟧`, and its bounded below
  version `ProEtale.CondensedRing.rightDerivedLowerShriekOfCompactificationPlus`, with
  scoped notation `Rf_!(c)⟦Λ⟧+`.

- `ProEtale.CondensedRing.rightDerivedLowerShriek` : `Rf_!` for the chosen compactification
  `HasCompactification.compactification f`, with scoped notation `R(f)_!⟦Λ⟧`, and its bounded
  below version `ProEtale.CondensedRing.rightDerivedLowerShriekPlus`, with scoped notation
  `R(f)_!⟦Λ⟧+`.

## Main results

- `ProEtale.CondensedRing.rightDerivedLowerShriekOfCompactificationPlusCompatibility` and
  `ProEtale.CondensedRing.rightDerivedLowerShriekPlusCompatibility` : the bounded below
  `Rf_!` is the restriction of the unbounded `Rf_!` along the inclusions
  `DerivedCategory.Plus.ι` of the bounded below derived categories.

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Abelian Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}}

section OfCompactification

variable {f : X ⟶ Y} (c : Compactification f)

/-- The derived lower shriek `Rf_! : D(Mod_{Λ_X}) ⥤ D(Mod_{Λ_Y})` attached to a
compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`, on the unbounded derived categories of module
objects: the functor `Di_!` induced on derived categories by the *exact* extension by zero
`i_!`, followed by the total right derived pushforward `Rg_*`.

Warning: as in the finite-coefficient case, it is deliberately *not* the total right derived
functor of the composite `i_! ⋙ g_* = f_!`. -/
noncomputable abbrev rightDerivedLowerShriekOfCompactification :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y)) :=
  D((c.i)_!open⟦Λ⟧) ⋙ R((c.g)_*⟦Λ⟧)

/-- The derived lower shriek `Rf_! : D⁺(Mod_{Λ_X}) ⥤ D⁺(Mod_{Λ_Y})` attached to a
compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`, on the *bounded below* derived categories of
module objects: the bounded below counterpart of
`rightDerivedLowerShriekOfCompactification`. -/
noncomputable abbrev rightDerivedLowerShriekOfCompactificationPlus :
    DerivedCategory.Plus (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ⥤
      DerivedCategory.Plus (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y)) :=
  D+((c.i)_!open⟦Λ⟧) ⋙ R+((c.g)_*⟦Λ⟧)

@[inherit_doc rightDerivedLowerShriekOfCompactification]
scoped notation "Rf_!(" c ")⟦" Λ "⟧" =>
  rightDerivedLowerShriekOfCompactification Λ c

@[inherit_doc rightDerivedLowerShriekOfCompactificationPlus]
scoped notation "Rf_!(" c ")⟦" Λ "⟧+" =>
  rightDerivedLowerShriekOfCompactificationPlus Λ c

/-- The bounded below derived lower shriek attached to a compactification
`c = (X ⟶[i] Z ⟶[g] Y)` is the restriction of the unbounded one along the inclusions of the
bounded below derived categories: on the `Di_!` factor this is
`Functor.mapDerivedCategoryPlusCompatibility` (`i_!` is exact), on the `Rg_*` factor it is
`Functor.rightDerivedFunctorPlusCompatibility`. -/
noncomputable def rightDerivedLowerShriekOfCompactificationPlusCompatibility :
    Rf_!(c)⟦Λ⟧+ ⋙ DerivedCategory.Plus.ι ≅ DerivedCategory.Plus.ι ⋙ Rf_!(c)⟦Λ⟧ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft D+((c.i)_!open⟦Λ⟧)
      ((c.g)_*⟦Λ⟧).rightDerivedFunctorPlusCompatibility ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((c.i)_!open⟦Λ⟧).mapDerivedCategoryPlusCompatibility
      R((c.g)_*⟦Λ⟧) ≪≫
    Functor.associator _ _ _

end OfCompactification

section Chosen

variable (f : X ⟶ Y) [HasCompactification f]

/-- The derived lower shriek `Rf_! : D(Mod_{Λ_X}) ⥤ D(Mod_{Λ_Y})` along a morphism
`f : X ⟶ Y` admitting a compactification, on the unbounded derived categories of module
objects: the functor `rightDerivedLowerShriekOfCompactification` attached to the chosen
compactification `HasCompactification.compactification f`. -/
noncomputable def rightDerivedLowerShriek :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y)) :=
  Rf_!(HasCompactification.compactification f)⟦Λ⟧

@[inherit_doc rightDerivedLowerShriek]
scoped notation "R(" f ")_!⟦" Λ "⟧" => rightDerivedLowerShriek Λ f

/-- The derived lower shriek `Rf_! : D⁺(Mod_{Λ_X}) ⥤ D⁺(Mod_{Λ_Y})` on the *bounded
below* derived categories of module objects, for the chosen compactification. -/
noncomputable def rightDerivedLowerShriekPlus :
    DerivedCategory.Plus (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ⥤
      DerivedCategory.Plus (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y)) :=
  Rf_!(HasCompactification.compactification f)⟦Λ⟧+

@[inherit_doc rightDerivedLowerShriekPlus]
scoped notation "R(" f ")_!⟦" Λ "⟧+" => rightDerivedLowerShriekPlus Λ f

omit [IsCommMonObj Λ] in
lemma rightDerivedLowerShriek_eq :
    R(f)_!⟦Λ⟧ = Rf_!(HasCompactification.compactification f)⟦Λ⟧ := rfl

omit [IsCommMonObj Λ] in
lemma rightDerivedLowerShriekPlus_eq :
    R(f)_!⟦Λ⟧+ = Rf_!(HasCompactification.compactification f)⟦Λ⟧+ := rfl

/-- The bounded below derived lower shriek on module objects is the restriction of the
unbounded one along the inclusions of the bounded below derived categories. -/
noncomputable def rightDerivedLowerShriekPlusCompatibility :
    R(f)_!⟦Λ⟧+ ⋙ DerivedCategory.Plus.ι ≅ DerivedCategory.Plus.ι ⋙ R(f)_!⟦Λ⟧ :=
  rightDerivedLowerShriekOfCompactificationPlusCompatibility Λ
    (HasCompactification.compactification f)

end Chosen

end AlgebraicGeometry.ProEtale.CondensedRing
