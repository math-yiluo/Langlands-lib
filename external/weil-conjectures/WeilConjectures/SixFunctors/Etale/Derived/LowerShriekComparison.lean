/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import WeilConjectures.Compactification.RefinementPullback
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComparison.CompositionLaw
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComparison.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComparison.IdentityLaw
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChange

/-!

# Comparison of derived lower shrieks along a refinement of compactifications

Let `f : X ⟶ Y` be a morphism of schemes, let `c` and `d` be compactifications of `f` and let
`r : c.Refinement d` be a refinement, i.e. a morphism `q = r.hom : c.Z ⟶ d.Z` with
`c.i ≫ q = d.i` and `q ≫ d.g = c.g`. This file constructs the comparison

`Rf_!(d)[A]+ ⟶ Rf_!(c)[A]+`

of the bounded below derived lower shrieks attached to the two compactifications, under the
hypothesis that the square

```
X --c.i--> c.Z
|          |
𝟙          q
|          |
X --d.i--> d.Z
```

is cartesian, i.e. `q ⁻¹ (X) = X`.

Note the direction: the comparison goes from the *coarser* compactification `d` to the
*finer* one `c`. Neither direction is formal — the adjunctions produce a cospan of natural
transformations into `D(d.i)_! ⋙ Dq^* ⋙ Rq_* ⋙ R(d.g)_*`, and one of the two legs has to be
inverted to obtain an arrow. Inverting the leg coming from the base change comparison for
`j_!` is what the cartesian hypothesis buys, and it produces the direction above; inverting
the other leg is proper base change and produces the opposite direction.

The composite is, with `q = r.hom`:

```
D(d.i)_! ⋙ R(d.g)_*
  ⟶ D(d.i)_! ⋙ Dq^* ⋙ Rq_* ⋙ R(d.g)_*   (unit of `Dq^* ⊣ Rq_*`)
  ⟶ D(c.i)_! ⋙ Rq_* ⋙ R(d.g)_*          (inverse of base change for `j_!`)
  ⟶ D(c.i)_! ⋙ R(c.g)_*                 (composition of derived pushforwards)
```

## Main definitions

- `AlgebraicGeometry.Etale.refinementLowerStarComp`: the composition isomorphism
  `(r.hom)_* ⋙ (d.g)_* ≅ (c.g)_*` of pushforwards attached to a refinement.

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusComparison`: the
  comparison `Rf_!(d)[A]+ ⟶ Rf_!(c)[A]+` above. (blueprint: `BA43-RHO`)

## Main results

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusComparison_id`: the
  identity law, i.e. the comparison attached to the identity refinement of a
  compactification is the identity.

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusComparison_comp`:
  the composition law, i.e. the comparison attached to a composite `r.comp s` of
  refinements is the composite of the two comparisons. Since the comparison runs from the
  coarser to the finer compactification, it is contravariant in the refinement and the
  order of the composite is reversed.

## Implementation notes

Only the bounded below variant is constructed here. The unbounded variant is
`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationComparison`, in
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded`.

That the comparison is an isomorphism is proper base change and is not proved here.

The identity law is proved by factoring the comparison for the identity refinement through
the whiskering by `D(c.i)_!⁺`: the *inverse* of the base change isomorphism for the identity
refinement is the whiskering of the identity isomorphism `D(𝟙 c.Z)^*⁺ ≅ 𝟭` of
`AlgebraicGeometry.Etale.upperStarIdDerivedPlus`
(`AlgebraicGeometry.Etale.refinementLowerShriekBaseChangeDerivedPlusIso_inv_id`), which
turns the comparison into a natural transformation of `R(c.g)_*⁺` with itself, and there the
universal property of a right derived functor applies. The two ingredients are that the
derived unit of `D(𝟙 c.Z)^* ⊣ R(𝟙 c.Z)_*` is, modulo that same identity isomorphism
`D(𝟙 c.Z)^*⁺ ≅ 𝟭` of the pullback, the inverse of the identity isomorphism
`R(𝟙 c.Z)_*⁺ ≅ 𝟭` of `AlgebraicGeometry.Etale.lowerStarIdDerivedPlus`, and that the
composition isomorphism cancels the latter.

The composition law repeats that architecture one level up, and is assembled from three
cocycle laws: the base change isomorphisms compose
(`AlgebraicGeometry.Etale.refinementLowerShriekBaseChangeDerivedPlusIso_inv_comp`), the
derived units compose modulo the composition isomorphism
`AlgebraicGeometry.Etale.upperStarCompDerivedPlus` of the derived pullbacks
(`AlgebraicGeometry.Etale.derivedPlus_unit_comp_upperStarCompDerivedPlus`), and the
composition isomorphisms of the derived pushforwards are associative
(`Functor.rightDerivedFunctorPlusCompIso'_assoc`, applied through the underived
associativity `AlgebraicGeometry.Etale.refinementLowerStarComp_comp`).

This module imports its parts: the definitions are in
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComparison.Defs`, the identity law in
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComparison.IdentityLaw` and the composition
law in `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComparison.CompositionLaw`.

-/
