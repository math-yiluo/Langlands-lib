/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.SixFunctors.OpenClosed.Exact

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

variable {U Z X : Scheme.{u}} (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i]

/-- **The open–closed short complex is short exact**, for sheaves of `Λ`-modules: the
specialization of `AlgebraicGeometry.Etale.shortExact_openClosedShortComplex` at
`A = ModuleCat.{u + 1} Λ`, where every hypothesis on the coefficient category is inferred.
It has no content beyond that statement. -/
theorem Etale.shortExact_openClosedShortComplex_moduleCat (Λ : Type (u + 1)) [Ring Λ]
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    (Etale.openClosedShortComplex (ModuleCat.{u + 1} Λ) j i
      (disjoint_range_of_range_eq_compl j i hij) M).ShortExact :=
  Etale.shortExact_openClosedShortComplex _ j i M hij

/-! ### Smoke tests for the coefficient hypotheses

That the sheaf categories with these coefficients are Grothendieck abelian is what the
derived-category files consume; here it is checked to be inferable. -/

variable (Λ : Type (u + 1)) [Ring Λ]

example : IsGrothendieckAbelian.{u + 1} (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  inferInstance

example : IsGrothendieckAbelian.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  inferInstance

end AlgebraicGeometry
