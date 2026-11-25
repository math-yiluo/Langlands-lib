/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Defs

/-!

# Derived Lower Shriek

This is the pro-étale counterpart of
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`.

As there, the derived functors entering `Rf_!` are not given definitions of their own:
they are the generic derived-functor constructions of the folder
`WeilConjectures.CategoryTheory.DerivedCategory`, written `D(-)`, `D+(-)`, `R(-)` and
`R+(-)`, applied to the underived six-functor notations `(c.i)_!open[A]` and `(c.g)_*[A]`.
Those notations are scoped in the `CategoryTheory.Functor` namespace, hence the
`open scoped CategoryTheory.Functor` below.

# Main Results

- `AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactification` : `Rf_!` with
  respect to a compcatification `c`, with scoped notation `Rf_!(c)[A]`.

- `AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationPlus` : `Rf_!`
  on bounded below derived category with respect to a compcatification `c`, with scoped
  notation `Rf_!(c)[A]+`.

- `AlgebraicGeometry.ProEtale.rightDerivedLowerShriek` : `Rf_!`
  specifying to the chosen compcatification `HasCompactification.compactification`, with
  scoped notation `R(f)_![A]`.

- `AlgebraicGeometry.ProEtale.rightDerivedLowerShriekPlus` : `Rf_!` on bounded below derived
  category specifying to the chosen compcatification `HasCompactification.compactification`,
  with scoped notation `R(f)_![A]+`.

- `AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationPlusCompatibility` and
  `AlgebraicGeometry.ProEtale.rightDerivedLowerShriekPlusCompatibility` : the bounded below
  `Rf_!` is the restriction of the unbounded `Rf_!` along the inclusions
  `DerivedCategory.Plus.ι` of the bounded below derived categories.

- `AlgebraicGeometry.ProEtale.rightDerivedLowerShriekCongr` : the transport `Rf_! ≅ Rg_!`
  along an equality `f = g`.

- `AlgebraicGeometry.ProEtale.compactlySupportedCohomology` : `H_c`, with scoped notation
  `H_c(f)[A](i)`.

-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section DerivedLowerShriek

variable {X Y : Scheme.{u}}

section OfCompactification

namespace ProEtale

variable {f : X ⟶ Y} (c : Compactification f)

/-- Blueprint `proposition-construction-independence-rf-shriek`: Compact-support candidate attached
to a compactification, `Rf^c_{!,n} = Rf̄_* j_!` (restricted to the étale-origin complexes in
`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationEtaleOrigin`).

The derived lower shriek `Rf_! : D(X_proét) ⥤ D(Y_proét)` attached to a compactification
`c = (X ⟶[i] Z ⟶[g] Y)` of `f`, on the unbounded derived categories of pro-étale sheaves:
the functor `Di_!` induced on derived categories by the *exact* extension by zero `i_!`,
followed by the total right derived pushforward `Rg_*`.

Warning: It is deliberately *not* the total right derived functor of the composite
`i_! ⋙ g_* = ProEtale.lowerShriek`. In general, `i_!` does not sends injective sheaves to
`g_*`-acyclic ones, and `Rf_!` is not the derived functor of `f_!`, through its zeroth
homology is `f_!`. Deligne made explicit calculations on $A^1$, see SGA. -/
noncomputable abbrev rightDerivedLowerShriekOfCompactification :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) :=
  D((c.i)_!open[A]) ⋙ R((c.g)_*[A])

/-- The derived lower shriek `Rf_! : D⁺(X_proét) ⥤ D⁺(Y_proét)` attached to a
compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`, on the *bounded below* derived categories
of pro-étale sheaves: the bounded below counterpart of
`rightDerivedLowerShriekOfCompactification`, with `Di_!` the functor
`Functor.mapDerivedCategoryPlus` induced by the exact `i_!` and `R⁺g_*` the bounded below
right derived pushforward. -/
noncomputable abbrev rightDerivedLowerShriekOfCompactificationPlus :
    DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) A) ⥤
      DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Y) A) :=
  D+((c.i)_!open[A]) ⋙ R+((c.g)_*[A])

@[inherit_doc rightDerivedLowerShriekOfCompactification]
scoped notation "Rf_!("c")[" A "]" =>
  rightDerivedLowerShriekOfCompactification A c

@[inherit_doc rightDerivedLowerShriekOfCompactificationPlus]
scoped notation "Rf_!("c")[" A "]+" =>
  rightDerivedLowerShriekOfCompactificationPlus A c

/-- The bounded below derived lower shriek attached to a compactification
`c = (X ⟶[i] Z ⟶[g] Y)` is the restriction of the unbounded one along the inclusions of the
bounded below derived categories: on the `Di_!` factor this is
`Functor.mapDerivedCategoryPlusCompatibility` (`i_!` is exact), on the `Rg_*` factor it is
`Functor.rightDerivedFunctorPlusCompatibility`. -/
noncomputable def rightDerivedLowerShriekOfCompactificationPlusCompatibility :
    Rf_!(c)[A]+ ⋙ DerivedCategory.Plus.ι ≅ DerivedCategory.Plus.ι ⋙ Rf_!(c)[A] :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft D+((c.i)_!open[A])
      ((c.g)_*[A]).rightDerivedFunctorPlusCompatibility ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((c.i)_!open[A]).mapDerivedCategoryPlusCompatibility
      R((c.g)_*[A]) ≪≫
    Functor.associator _ _ _

end ProEtale

end OfCompactification

variable (f : X ⟶ Y) [HasCompactification f]

namespace ProEtale

/-- The derived lower shriek `Rf_! : D(X_proét) ⥤ D(Y_proét)` along a morphism `f : X ⟶ Y`
admitting a compactification, on the unbounded derived categories of pro-étale sheaves: the
functor `rightDerivedLowerShriekOfCompactification` attached to the chosen compactification
`HasCompactification.compactification f`. This is blueprint
`proposition-construction-independence-rf-shriek`. -/
noncomputable def rightDerivedLowerShriek :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) :=
  Rf_!(HasCompactification.compactification f)[A]

@[inherit_doc rightDerivedLowerShriek]
scoped notation "R(" f ")_![" A "]" =>
  rightDerivedLowerShriek A f

/-- The derived lower shriek `Rf_! : D⁺(X_proét) ⥤ D⁺(Y_proét)` on the *bounded below*
derived categories of pro-étale sheaves: the functor
`rightDerivedLowerShriekOfCompactificationPlus` attached to the chosen compactification
`HasCompactification.compactification f`. -/
noncomputable def rightDerivedLowerShriekPlus :
    DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) A) ⥤
      DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Y) A) :=
  Rf_!(HasCompactification.compactification f)[A]+

@[inherit_doc rightDerivedLowerShriekPlus]
scoped notation "R(" f ")_![" A "]+" =>
  rightDerivedLowerShriekPlus A f

lemma rightDerivedLowerShriek_eq : R(f)_![A] =
    Rf_!(HasCompactification.compactification f)[A] := rfl

lemma rightDerivedLowerShriekPlus_eq : R(f)_![A]+ =
    Rf_!(HasCompactification.compactification f)[A]+ := rfl

/-- The bounded below derived lower shriek `Rf_! : D⁺(X_proét) ⥤ D⁺(Y_proét)` is the
restriction of the unbounded `Rf_! : D(X_proét) ⥤ D(Y_proét)` along the inclusions of the
bounded below derived categories. -/
noncomputable def rightDerivedLowerShriekPlusCompatibility :
    R(f)_![A]+ ⋙ DerivedCategory.Plus.ι ≅ DerivedCategory.Plus.ι ⋙ R(f)_![A] :=
  rightDerivedLowerShriekOfCompactificationPlusCompatibility A
    (HasCompactification.compactification f)

/-- Transport of the derived exceptional direct image along an equality of morphisms:
`Rf_! ≅ Rg_!` for `f = g`. -/
noncomputable def rightDerivedLowerShriekCongr {f g : X ⟶ Y} (h : f = g)
    [HasCompactification f] [HasCompactification g] : R(f)_![A] ≅ R(g)_![A] :=
  -- not `eqToIso`: the kernel would compare `Rf_!` and `Rg_!` when reducing the transport
  by subst h; exact Iso.refl _

@[simp]
lemma rightDerivedLowerShriekCongr_rfl {f : X ⟶ Y} [HasCompactification f] :
    rightDerivedLowerShriekCongr A (rfl : f = f) = Iso.refl _ :=
  rfl

end ProEtale

end DerivedLowerShriek

end AlgebraicGeometry

namespace AlgebraicGeometry

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section DerivedGlobalSections

namespace ProEtale

variable (X : Scheme.{u})

/-- The derived global sections `RΓ(X, -) : D(X_proét) ⥤ D(A)`: the total right derived
functor of the global sections functor on pro-étale sheaves, which exists since the small
pro-étale site has a terminal object. -/
noncomputable def rightDerivedGlobalSections :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) ⥤ DerivedCategory A :=
  R(Sheaf.Γ (Scheme.ProEt.topology X) A)

end ProEtale

end DerivedGlobalSections

section CompactlySupportedCohomology

namespace ProEtale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

/-- Blueprint `lemma-perfect-complexes-geometric-point`: Compact-support cohomology (for `f = a_X`
the structure morphism of `X` over `Spec k`, and `A` the category of `A_{E,n}`-modules).
Also blueprint `def-trf-coefficient-conventions` (on the small pro-étale site; the étale model
is `AlgebraicGeometry.Etale.compactlySupportedGlobalSections`).

The compactly supported derived global sections along a morphism `f : X ⟶ Y`
admitting a compactification, *defined* as the composite

`RΓc(X/Y, -) := RΓ(Y, Rf_! -) : D(X_proét) ⥤ D(A)`.

The intermediate object `Rf_! K ∈ D(Y_proét)` and the coefficient complex
`RΓc(X/Y, K) ∈ D(A)` are not definitionally the same. For the structure morphism of the
geometric fiber of a scheme separated of finite type over a finite field this is the
`RΓc(X, K) = RΓ(s, Ra_{X!} K)` of the trace-formula interface. -/
noncomputable def compactlySupportedGlobalSections :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) ⥤ DerivedCategory A :=
  R(f)_![A] ⋙ rightDerivedGlobalSections A Y

/-- The compactly supported cohomology along a morphism `f : X ⟶ Y` admitting a
compactification, `Hᶜⁱ(X/Y, K) := Hⁱ(RΓc(X/Y, K))`: the `i`-th homology object of the
compactly supported derived global sections. Finiteness is a theorem, not part of the
definition. -/
noncomputable def compactlySupportedCohomology (i : ℤ) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) ⥤ A :=
  compactlySupportedGlobalSections A f ⋙ DerivedCategory.homologyFunctor A i

@[inherit_doc compactlySupportedCohomology]
scoped notation "H_c(" f ")[" A "](" i ")" =>
  compactlySupportedCohomology A f i

end ProEtale

end CompactlySupportedCohomology

end AlgebraicGeometry
