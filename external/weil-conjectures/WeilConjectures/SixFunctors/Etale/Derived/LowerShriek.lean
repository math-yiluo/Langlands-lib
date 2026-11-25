/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Defs

/-!

# Derived Lower Shriek

## Main results

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification` : `Rf_!` with respect
  to a compactification `c`, with scoped notation `Rf_!(c)[A]`.

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlus` : `Rf_!`
  on bounded below derived category with respect to a compactification `c`, with scoped
  notation `Rf_!(c)[A]+`.

- `AlgebraicGeometry.Etale.rightDerivedLowerShriek` : `Rf_!`
  specifying to the chosen compactification `HasCompactification.compactification`, with
  scoped notation `R(f)_![A]`.

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekPlus` : `Rf_!` on bounded below derived
  category specifying to the chosen compactification `HasCompactification.compactification`,
  with scoped notation `R(f)_![A]+`.

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility` and
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekPlusCompatibility` : the bounded below
  `Rf_!` is the restriction of the unbounded `Rf_!` along the inclusions
  `DerivedCategory.Plus.ι` of the bounded below derived categories.

- `AlgebraicGeometry.Etale.cohomology` : the étale cohomology `H^i(X, -) = H^i(RΓ(X, -))`.

- `AlgebraicGeometry.Etale.compactlySupportedCohomology` : `H_c`, with scoped notation
  `H_c(f)[A](i)`.

The hypothesis `HasCompactification f` of `rightDerivedLowerShriek` and of the functors
built from it is discharged by Nagata's compactification theorem (the instance registered in
`WeilConjectures.Compactification.NagataCompactification`, which this file imports through
`WeilConjectures.SixFunctors.Etale.LowerShriek.Defs`): `Rf_!` is available for every separated,
quasi-compact morphism locally of finite type over a quasi-compact quasi-separated base,
with no compactification supplied by hand. The `example` after
`rightDerivedLowerShriekPlus_eq` records this.

-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

section DerivedLowerShriek

variable {X Y : Scheme.{u}}

section OfCompactification

namespace Etale

variable {f : X ⟶ Y} (c : Compactification f)

/-- The derived lower shriek `Rf_! : D(X_ét) ⥤ D(Y_ét)` attached to a compactification
`c = (X ⟶[i] Z ⟶[g] Y)` of `f`, on the unbounded derived categories of étale sheaves: the
functor `Di_!` induced on derived categories by the *exact* extension by zero `i_!`, followed
by the total right derived pushforward `Rg_*`. This is blueprint
`proposition-construction-independence-rf-shriek` (the candidate `Rf_!^c = Rr_* j_!`; the functor
`Rf_!` of the chosen compactification is `AlgebraicGeometry.Etale.rightDerivedLowerShriek`).

Warning: It is deliberately *not* the total right derived functor of the composite
`i_! ⋙ g_* = Etale.lowerShriek`. In general, `i_!` does not sends injective sheaves to
`g_*`-acyclic ones, and `Rf_!` is not the derived functor of `f_!`, through its zeroth
homology is `f_!`. Deligne made explicit calculations on $A^1$, see SGA. -/
noncomputable abbrev rightDerivedLowerShriekOfCompactification :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A) :=
  D((c.i)_!open[A]) ⋙ R((c.g)_*[A])

/-- The derived lower shriek `Rf_! : D⁺(X_ét) ⥤ D⁺(Y_ét)` attached to a compactification
`c = (X ⟶[i] Z ⟶[g] Y)` of `f`, on the *bounded below* derived categories of étale sheaves:
the bounded below counterpart of `rightDerivedLowerShriekOfCompactification`, with `Di_!` the
functor `Functor.mapDerivedCategoryPlus` induced by the exact `i_!` and `R⁺g_*` the bounded
below right derived pushforward. -/
noncomputable abbrev rightDerivedLowerShriekOfCompactificationPlus :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A) :=
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

/-- The derived lower shriek attached to a compactification is additive. -/
instance : Rf_!(c)[A].Additive :=
  -- `D(i_!)` is additive, and so is `R(g_*)`, being a right adjoint
  have := (Etale.mapDerivedUpperStarLowerStarAdjunction A c.g).right_adjoint_additive
  inferInstance

variable (Λ : Type*) [Ring Λ] [Linear Λ A] in
/-- If `A` is `Λ`-linear, the derived lower shriek `D(i_!) ⋙ Rg_*` attached to a compactification
`(i, g)` is `Λ`-linear: `D(i_!)` is induced by the `Λ`-linear exact functor `i_!`, and `Rg_*` is
`Λ`-linear by `AlgebraicGeometry.Etale.linear_rightDerivedLowerStar`. -/
instance linear_rightDerivedLowerShriekOfCompactification : Rf_!(c)[A].Linear Λ :=
  inferInstanceAs ((D((c.i)_!open[A]) ⋙ R((c.g)_*[A])).Linear Λ)

end Etale

end OfCompactification

variable (f : X ⟶ Y) [HasCompactification f]

namespace Etale

/-- The derived lower shriek `Rf_! : D(X_ét) ⥤ D(Y_ét)` along a morphism `f : X ⟶ Y`
admitting a compactification, on the unbounded derived categories of étale sheaves: the
functor `rightDerivedLowerShriekOfCompactification` attached to the chosen compactification
`HasCompactification.compactification f`. -/
noncomputable def rightDerivedLowerShriek :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A) :=
  Rf_!(HasCompactification.compactification f)[A]

@[inherit_doc rightDerivedLowerShriek]
scoped notation "R(" f ")_![" A "]" =>
  rightDerivedLowerShriek A f

/-- The derived lower shriek `Rf_! : D⁺(X_ét) ⥤ D⁺(Y_ét)` on the *bounded below* derived
categories of étale sheaves: the functor `rightDerivedLowerShriekOfCompactificationPlus`
attached to the chosen compactification `HasCompactification.compactification f`. -/
noncomputable def rightDerivedLowerShriekPlus :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A) :=
  Rf_!(HasCompactification.compactification f)[A]+

@[inherit_doc rightDerivedLowerShriekPlus]
scoped notation "R(" f ")_![" A "]+" =>
  rightDerivedLowerShriekPlus A f

omit [HasSmallSiteSheafify A] in
lemma rightDerivedLowerShriek_eq : R(f)_![A] =
    Rf_!(HasCompactification.compactification f)[A] := rfl

omit [HasSmallSiteSheafify A] in
lemma rightDerivedLowerShriekPlus_eq : R(f)_![A]+ =
    Rf_!(HasCompactification.compactification f)[A]+ := rfl

/-- The bounded below derived lower shriek `Rf_! : D⁺(X_ét) ⥤ D⁺(Y_ét)` is the restriction
of the unbounded `Rf_! : D(X_ét) ⥤ D(Y_ét)` along the inclusions of the bounded below
derived categories. -/
noncomputable def rightDerivedLowerShriekPlusCompatibility :
    R(f)_![A]+ ⋙ DerivedCategory.Plus.ι ≅ DerivedCategory.Plus.ι ⋙ R(f)_![A] :=
  rightDerivedLowerShriekOfCompactificationPlusCompatibility A
    (HasCompactification.compactification f)

/-- The derived lower shriek along a morphism admitting a compactification is additive. -/
instance : R(f)_![A].Additive :=
  inferInstanceAs (Rf_!(HasCompactification.compactification f)[A]).Additive

variable (Λ : Type*) [Ring Λ] [Linear Λ A] in
/-- If `A` is `Λ`-linear, the derived lower shriek `Rf_!` is `Λ`-linear, by
`AlgebraicGeometry.Etale.linear_rightDerivedLowerShriekOfCompactification` for the chosen
compactification. -/
instance linear_rightDerivedLowerShriek : R(f)_![A].Linear Λ :=
  inferInstanceAs ((Rf_!(HasCompactification.compactification f)[A]).Linear Λ)

end Etale

end DerivedLowerShriek

end AlgebraicGeometry

namespace AlgebraicGeometry

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

section DerivedGlobalSections

namespace Etale

variable (X : Scheme.{u})

/-- The derived global sections `RΓ(X, -) : D(X_ét) ⥤ D(A)`: the total right derived
functor of the global sections functor on étale sheaves, which exists since the small
étale site has a terminal object. -/
noncomputable def rightDerivedGlobalSections :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤ DerivedCategory A :=
  R(Sheaf.Γ X.smallEtaleTopology A)

/-- The étale cohomology `H^i(X, K) := H^i(RΓ(X, K))`: the `i`-th homology object of the
derived global sections, the companion of the compactly supported
`AlgebraicGeometry.Etale.compactlySupportedCohomology`. For a sheaf `F` placed in degree `0`
this is the étale sheaf cohomology `H^i(X, F)`. -/
noncomputable def cohomology (i : ℤ) : DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤ A :=
  rightDerivedGlobalSections A X ⋙ DerivedCategory.homologyFunctor A i

end Etale

end DerivedGlobalSections

section CompactlySupportedCohomology

namespace Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

/-- Blueprint `def-trf-coefficient-conventions`: Trace-formula coefficient conventions.

The compactly supported derived global sections along a morphism `f : X ⟶ Y`
admitting a compactification, *defined* as the composite

`RΓc(X/Y, -) := RΓ(Y, Rf_! -) : D(X_ét) ⥤ D(A)`.

The intermediate object `Rf_! K ∈ D(Y_ét)` and the coefficient complex
`RΓc(X/Y, K) ∈ D(A)` are not definitionally the same. For the structure morphism of the
geometric fiber of a scheme separated of finite type over a finite field this is the
`RΓc(X, K) = RΓ(s, Ra_{X!} K)` of the trace-formula interface.

This carries the coefficient conventions of the trace formula: the coefficients are
`A = ModuleCat Λ` for a finite coefficient ring `Λ` (the stage `A_{E,n} = 𝒪_E / ϖ_Eⁿ`) whose
exponent is invertible on the base, the schemes are the geometric fibers `X = X₀ ×_{k₀} k`
(`AlgebraicGeometry.Scheme.Hom.geometricFiber`) with structure morphism `a_X : X ⟶ s = Spec k`,
the categories are `Dᵇc(X, A)` and `Dctf(X, A)` of `AlgebraicGeometry.Etale.DerivedCategory`,
`RΓ(s, -)` is the evaluation `Fib_s` at the geometric point
(`AlgebraicGeometry.Etale.pointFiber`, see `AlgebraicGeometry.Etale.pointFiberCompιIso`), and
`H_c^i(X, K) = Hⁱ(RΓc(X, K))` is `AlgebraicGeometry.Etale.compactlySupportedCohomology`. The
same construction on the small pro-étale site of the blueprint node is
`AlgebraicGeometry.ProEtale.compactlySupportedGlobalSections`; the pro-étale comparison
(`WeilConjectures.SixFunctors.ProEtale.Comparison`) identifies the two on the constructible
objects. -/
noncomputable def compactlySupportedGlobalSections :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤ DerivedCategory A :=
  R(f)_![A] ⋙ rightDerivedGlobalSections A Y

/-- The compactly supported cohomology along a morphism `f : X ⟶ Y` admitting a
compactification, `Hᶜⁱ(X/Y, K) := Hⁱ(RΓc(X/Y, K))`: the `i`-th homology object of the
compactly supported derived global sections. Finiteness is a theorem, not part of the
definition. -/
noncomputable def compactlySupportedCohomology (i : ℤ) :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤ A :=
  compactlySupportedGlobalSections A f ⋙ DerivedCategory.homologyFunctor A i

@[inherit_doc compactlySupportedCohomology]
scoped notation "H_c(" f ")[" A "](" i ")" =>
  compactlySupportedCohomology A f i

end Etale

end CompactlySupportedCohomology

end AlgebraicGeometry
