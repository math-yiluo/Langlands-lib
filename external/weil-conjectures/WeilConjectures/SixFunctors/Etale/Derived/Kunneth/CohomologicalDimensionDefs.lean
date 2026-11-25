/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

/-!
# Finite cohomological dimension: definitions

The predicates `AlgebraicGeometry.Etale.HasFiniteCohomologicalDimension` (on a scheme) and
`AlgebraicGeometry.Etale.HasFiniteCohomologicalDimensionMorphism` (on a morphism). Their basic
properties are in `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.CohomologicalDimension`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

section Defs

variable (X : Scheme.{u})

/-- Blueprint `definition-cohomological-dimension` (for sheaves of `Λ`-modules): the scheme `X`
has *finite cohomological dimension* for sheaves of `Λ`-modules if there is a `d` with
`H^q(X, F) = 0` for every étale sheaf `F` of `Λ`-modules and every `q > d`. For a torsion ring `Λ`
every such sheaf is a torsion abelian sheaf, so this follows from finiteness of the torsion étale
cohomological dimension `cd(X)` of the blueprint. -/
def HasFiniteCohomologicalDimension : Prop :=
  ∃ d : ℤ, ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ), d < q →
    IsZero ((cohomology (ModuleCat.{u + 1} Λ) X q).obj
      ((DerivedCategory.singleFunctor _ 0).obj F))

variable {X} in
/-- Blueprint `definition-cohomological-dimension` (for morphisms, and sheaves of `Λ`-modules): the
morphism `f` has
*finite cohomological dimension* for sheaves of `Λ`-modules if there is a `d` with
`R^q f_* F = 0` for every étale sheaf `F` of `Λ`-modules and every `q > d`. -/
def HasFiniteCohomologicalDimensionMorphism {Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∃ d : ℤ, ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ), d < q →
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((DerivedCategory.singleFunctor _ 0).obj F)))

end Defs

end Etale

end AlgebraicGeometry
