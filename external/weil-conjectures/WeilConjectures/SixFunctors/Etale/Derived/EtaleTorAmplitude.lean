/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.Additive

/-!
# Tor amplitude for etale sheaves

Source: literature/blueprint/master/blueprint/sec-smooth-purity/
`sk-prop-sf-kunneth-ordinary/def-kun-tor-amplitude.md`
(blueprint: def-kun-tor-amplitude); Stacks Project, Tags 08FZ and 0F1M.

The bounded interval predicate is the existing
`AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn` in
`WeilConjectures.SixFunctors.Etale.Derived.Coefficients`: for every sheaf in degree zero,
it requires vanishing of the derived tensor cohomology in degrees `q < a ∨ b < q`.
It permits empty intervals. We add only the lower-bounded variant.

A bounded complex of flat sheaves supported in `[a,b]` has this Tor amplitude;
that property is not an additional clause of either definition. Boundedness alone
is insufficient, as noted in the blueprint.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Tor amplitude in `[a, ∞)`: for every etale sheaf of `Λ`-modules placed in degree zero,
all cohomology sheaves of its derived tensor with `E` vanish below `a`.
Source: blueprint `sec-smooth-purity/sk-prop-sf-kunneth-ordinary/def-kun-tor-amplitude.md`
(blueprint: def-kun-tor-amplitude), and Stacks Project, Tag 0F1M, first paragraph of proof.
The bounded variant is the existing `DerivedCategory.hasTorAmplitudeIn`. -/
def DerivedCategory.hasTorAmplitudeGE (Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u})
    (a : ℤ) : ObjectProperty (DerivedCategoryModule Λ T) :=
  fun E ↦ ∀ (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (i : ℤ), i < a →
    IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj
      (((derivedTensor (ModuleCat.{u + 1} Λ) T).obj E).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj M)))

end AlgebraicGeometry.Etale
