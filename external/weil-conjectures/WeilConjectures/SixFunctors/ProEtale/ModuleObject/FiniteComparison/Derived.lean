/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar

/-!

# The derived comparison of the two finite-coefficient models

For a finite discrete commutative ring `T`, the abelian equivalence
`ProEtale.finiteCoefficientModEquivalence` between module objects over the condensed ring
`C(-, T)` pulled back to `X_proét` and pro-étale sheaves of `T`-modules is additive, and induces an
equivalence of derived categories (`ProEtale.finiteCoefficientDerivedEquivalence`). This is the
bridge from the condensed finite-coefficient model to the `ModuleCat` model of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient`, which is compared with the étale site.

-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (X : Scheme.{u}) (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  [DiscreteTopology T] [Finite T]

instance additive_finiteCoefficientModEquivalence_functor :
    (finiteCoefficientModEquivalence X T).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The derived version of `finiteCoefficientModEquivalence`. -/
noncomputable def finiteCoefficientDerivedEquivalence :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj T) X)) ≌
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} T))) :=
  (finiteCoefficientModEquivalence X T).mapDerivedCategory

end AlgebraicGeometry.ProEtale
