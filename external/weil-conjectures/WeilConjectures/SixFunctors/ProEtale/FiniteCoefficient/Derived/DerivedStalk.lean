/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar

/-!
# The derived geometric stalk on the pro-étale site

For a geometric point `x̄ : Spec Ω ⟶ X` (`Ω` separably closed) and `K ∈ D(X_proét)`, the
derived geometric stalk is `K_x̄ = RΓ(Spec Ω, Lx̄^* K)`, computed entirely on pro-étale sites:
the derived pro-étale pullback along `x̄` followed by derived pro-étale global sections on
`Spec Ω`. The point `Spec Ω` need not be of finite type over the base field.

Compare `AlgebraicGeometry.ProEtale.geometricStalk`, which computes the stalk through the
site comparison `ν : X_proét ⟶ X_ét` as the étale geometric stalk of `Rν_* K`.

## Main definitions

- `AlgebraicGeometry.ProEtale.derivedGeometricStalk`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace ProEtale

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- Blueprint `pur9-def-derived-stalk`: Derived geometric stalk.

For a geometric point `x̄ : Spec Ω ⟶ X`, with `Ω` separably closed, the derived geometric
stalk `K ↦ K_x̄ := RΓ(Spec Ω_proét, Lx̄^* K) : D(X_proét) ⥤ D(A)`: the derived pro-étale
pullback `L((x̄)^*[A])` along `x̄` followed by the derived pro-étale global sections
`AlgebraicGeometry.ProEtale.rightDerivedGlobalSections` on `Spec Ω`. The blueprint takes
`A` to be the category of `A_{E,n}`-modules. -/
noncomputable def derivedGeometricStalk (x : Spec (.of Ω) ⟶ X) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) ⥤ DerivedCategory A :=
  L((x)^*[A]) ⋙ rightDerivedGlobalSections A (Spec (.of Ω))

end ProEtale

end AlgebraicGeometry
