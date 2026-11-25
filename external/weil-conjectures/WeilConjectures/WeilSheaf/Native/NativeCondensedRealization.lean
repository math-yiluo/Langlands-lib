/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.CondensedModelWeil
public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelDerived

/-!
# The condensed realization of pro-étale Weil sheaves

Forgetting the Weil structure of a pro-étale Weil sheaf on `X` and passing to the condensed
model (`AlgebraicGeometry.ProEtale.adicSheafEquivCondensedMod`) gives an exact functor
`ProEtaleWeilSheaf.condensedRealization` from pro-étale Weil sheaves on `X` to module objects
over `ℚ̲̄_ℓ` on the pro-étale site of the geometric fiber `X̄`. Its levelwise extension
`ProEtaleWeilSheaf.derivedCondensedRealization` to derived categories is the functor along
which statements about Weil complexes are transferred from the condensed `ℓ`-adic formalism.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- The condensed realization of a pro-étale Weil sheaf: forget its Weil structure and pass to
the condensed model on the geometric fiber `X̄`. -/
noncomputable abbrev condensedRealization :=
  Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X) ⋙
    (adicSheafEquivCondensedMod l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor

example : (condensedRealization k₀ l X).Additive := inferInstance

example : PreservesFiniteLimits (condensedRealization k₀ l X) := inferInstance

example : PreservesFiniteColimits (condensedRealization k₀ l X) := inferInstance

/-- The condensed realization on derived categories. -/
noncomputable abbrev derivedCondensedRealization :=
  (condensedRealization k₀ l X).mapDerivedCategory

end AlgebraicGeometry.ProEtaleWeilSheaf
