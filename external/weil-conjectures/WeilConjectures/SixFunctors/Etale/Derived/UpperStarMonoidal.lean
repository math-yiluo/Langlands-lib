/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Claude
-/
module

public import WeilConjectures.Algebra.Homology.HomotopyCategory.DerivabilityStructure
public import WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidal
public import WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.DerivesTwo
public import WeilConjectures.Mathlib.CategoryTheory.EssentialImage
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Derived
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.KFlat
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Vanishing
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.KFlat
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal

/-!
# The derived pullback and the derived tensor product

Let `g : Z ⟶ Y` be a morphism of schemes. We show that the two bifunctors
`(K, M) ↦ Lg^*K ⊗ᴸ Lg^*M` and `(K, M) ↦ Lg^*(K ⊗ᴸ M)`, of type
`D(Y_ét) ⥤ D(Y_ét) ⥤ D(Z_ét)`, are
the total left derived functors of `(A, B) ↦ g^*A ⊗ g^*B` and `(A, B) ↦ g^*(A ⊗ B)`
respectively. Deriving the oplax monoidal structure of `g^*`, we obtain the comparison
`Lg^*(K ⊗ᴸ M) ⟶ Lg^*K ⊗ᴸ Lg^*M`, which is an isomorphism since `g^*` is strong monoidal.

Since `g^*` is exact, the counit of `Lg^*` is an isomorphism everywhere, so
`Lg^*(K ⊗ᴸ M)` is computed with the K-flat left derivability structure on `K(Y_ét)`.
This does not suffice for `Lg^*K ⊗ᴸ Lg^*M`, since `g^*` need not send K-flat complexes to
K-flat complexes. We use instead, for the second factor, the complexes whose pullback by `g`
is K-flat (`AlgebraicGeometry.Etale.kFlatUpperStar`). They contain the functorial flat
resolutions when `g^*` preserves flat sheaves, so they form a left derivability structure by
`HomotopyCategory.isLeftDerivabilityStructure_quasiIsoLocalizerMorphism`.

## Main definitions and results

- `AlgebraicGeometry.Etale.kFlatUpperStar g`: the complexes on `Y_ét` whose pullback by `g`
  is K-flat, and `AlgebraicGeometry.Etale.isLeftDerivabilityStructure_kFlatUpperStar`:
  they form a left derivability structure.
- `AlgebraicGeometry.Etale.derivedTensorLeftDerivedUpperStar g` and
  `AlgebraicGeometry.Etale.leftDerivedUpperStarDerivedTensor g`: the bifunctors
  `(K, M) ↦ Lg^*K ⊗ᴸ Lg^*M` and `(K, M) ↦ Lg^*(K ⊗ᴸ M)`, with the counits
  `AlgebraicGeometry.Etale.derivedTensorLeftDerivedUpperStarCounit` and
  `AlgebraicGeometry.Etale.leftDerivedUpperStarDerivedTensorCounit`.
- `AlgebraicGeometry.Etale.isLeftDerivedFunctor₂_derivedTensor_leftDerivedUpperStar`:
  `(K, M) ↦ Lg^*K ⊗ᴸ Lg^*M` is the total left derived functor of `(A, B) ↦ g^*A ⊗ g^*B`.
- `AlgebraicGeometry.Etale.isLeftDerivedFunctor₂_leftDerivedUpperStar_derivedTensor`:
  `(K, M) ↦ Lg^*(K ⊗ᴸ M)` is the total left derived functor of `(A, B) ↦ g^*(A ⊗ B)`.
- `AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison g`: the comparison
  `Lg^*(K ⊗ᴸ M) ⟶ Lg^*K ⊗ᴸ Lg^*M`, obtained by deriving the oplax monoidal structure of `g^*`
  with `CategoryTheory.Functor.leftDerived₂NatTrans`.
- `AlgebraicGeometry.Etale.leftDerivedUpperStarTensorNatIso g`: it is a natural isomorphism,
  with components `AlgebraicGeometry.Etale.leftDerivedUpperStarTensorIso g K M`, and
  `AlgebraicGeometry.Etale.derivedTensorRightCompLeftDerivedUpperStarIso g M`, the same for
  fixed `M` as an isomorphism of functors of `K`.
- `AlgebraicGeometry.Etale.derivedTensorRightPullback g`: tensoring with a complex pulled
  back along `g`, `N ↦ (K ↦ K ⊗ᴸ g^* N)`.
- `AlgebraicGeometry.Etale.leftDerivedUpperStarUnitIso g`: the canonical `Lg^* Λ_Y ≅ Λ_Z`.
- `AlgebraicGeometry.Etale.leftDerivedUpperStarMonoidal`: `Lg^*` is a monoidal functor, with
  comonoidal structure the tensor comparison, and
  `AlgebraicGeometry.Etale.nonempty_monoidal_leftDerivedUpperStar`.
- `AlgebraicGeometry.Etale.isZero_derivedTensor_obj_obj_of_isZero_left` and
  `AlgebraicGeometry.Etale.isZero_derivedTensor_obj_obj_of_isZero_right`: `K ⊗ᴸ M` vanishes
  when `K` or `M` does.

The results depend on `sorryAx` through `AlgebraicGeometry.Etale.derivedTensor` and
`AlgebraicGeometry.Etale.isLeftDerivedFunctor₂_derivedTensor`.

## TODO

- Nothing here is specific to étale sheaves: the same statements hold for an exact functor
  `F` between abelian monoidal categories with functorial flat resolutions, `F` preserving flat
  objects. They should be proved in that generality and specialised here. This includes the
  comparison `leftDerivedUpperStarTensorComparison`, which only uses the oplax monoidal
  structure of `F`, and `leftDerivedUpperStarTensorNatIso`, which uses that `F` is strong
  monoidal.

## File structure

This module only imports its parts:
- `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.KFlat`: the complexes whose
  pullback is K-flat;
- `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Vanishing`: tensoring with
  K-flat complexes, and vanishing of `K ⊗ᴸ M`;
- `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Derived`: the two derived
  bifunctors;
- `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison`: the tensor and unit
  comparisons.
-/
