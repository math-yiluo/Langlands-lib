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
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMon.Comparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMon.Derived
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMon.KFlat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMon.Vanishing
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.KFlat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal

/-!
# The derived pullback and the derived tensor product

This is the pro-étale counterpart of `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal`,
restricted to the tensor comparison of the derived pullback.

Let `g : Z ⟶ Y` be a morphism of schemes. We show that the two bifunctors
`(K, M) ↦ Lg^*K ⊗ᴸ Lg^*M` and `(K, M) ↦ Lg^*(K ⊗ᴸ M)`, of type
`D(Y_proét) ⥤ D(Y_proét) ⥤ D(Z_proét)`, are
the total left derived functors of `(A, B) ↦ g^*A ⊗ g^*B` and `(A, B) ↦ g^*(A ⊗ B)`
respectively. Deriving the oplax monoidal structure of `g^*`, we obtain the comparison
`Lg^*(K ⊗ᴸ M) ⟶ Lg^*K ⊗ᴸ Lg^*M`, which is an isomorphism since `g^*` is strong monoidal.

Since `g^*` is exact, the counit of `Lg^*` is an isomorphism everywhere, so
`Lg^*(K ⊗ᴸ M)` is computed with the K-flat left derivability structure on `K(Y_proét)`.
This does not suffice for `Lg^*K ⊗ᴸ Lg^*M`, since `g^*` need not send K-flat complexes to
K-flat complexes. We use instead, for the second factor, the complexes whose pullback by `g`
is K-flat (`AlgebraicGeometry.ProEtale.kFlatUpperStar`). They contain the functorial flat
resolutions when `g^*` preserves flat sheaves, so they form a left derivability structure by
`HomotopyCategory.isLeftDerivabilityStructure_quasiIsoLocalizerMorphism`.

## Main definitions and results

- `AlgebraicGeometry.ProEtale.kFlatUpperStar g`: the complexes on `Y_proét` whose pullback by `g`
  is K-flat, and `AlgebraicGeometry.ProEtale.isLeftDerivabilityStructure_kFlatUpperStar`:
  they form a left derivability structure.
- `AlgebraicGeometry.ProEtale.derivedTensorLeftDerivedUpperStar g` and
  `AlgebraicGeometry.ProEtale.leftDerivedUpperStarDerivedTensor g`: the bifunctors
  `(K, M) ↦ Lg^*K ⊗ᴸ Lg^*M` and `(K, M) ↦ Lg^*(K ⊗ᴸ M)`, with the counits
  `AlgebraicGeometry.ProEtale.derivedTensorLeftDerivedUpperStarCounit` and
  `AlgebraicGeometry.ProEtale.leftDerivedUpperStarDerivedTensorCounit`.
- `AlgebraicGeometry.ProEtale.isLeftDerivedFunctor₂_derivedTensor_leftDerivedUpperStar`:
  `(K, M) ↦ Lg^*K ⊗ᴸ Lg^*M` is the total left derived functor of `(A, B) ↦ g^*A ⊗ g^*B`.
- `AlgebraicGeometry.ProEtale.isLeftDerivedFunctor₂_leftDerivedUpperStar_derivedTensor`:
  `(K, M) ↦ Lg^*(K ⊗ᴸ M)` is the total left derived functor of `(A, B) ↦ g^*(A ⊗ B)`.
- `AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorComparison g`: the comparison
  `Lg^*(K ⊗ᴸ M) ⟶ Lg^*K ⊗ᴸ Lg^*M`, obtained by deriving the oplax monoidal structure of `g^*`
  with `CategoryTheory.Functor.leftDerived₂NatTrans`.
- `AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorNatIso g`: it is a natural isomorphism,
  with components `AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorIso g K M`.
- `AlgebraicGeometry.ProEtale.leftDerivedUpperStarUnitIso g`: the canonical `Lg^* Λ_Y ≅ Λ_Z`.
- `AlgebraicGeometry.ProEtale.isZero_derivedTensor_obj_obj_of_isZero_left` and
  `AlgebraicGeometry.ProEtale.isZero_derivedTensor_obj_obj_of_isZero_right`: `K ⊗ᴸ M` vanishes
  when `K` or `M` does.

The results depend on `sorryAx` through `AlgebraicGeometry.ProEtale.derivedTensor` and
`AlgebraicGeometry.ProEtale.isLeftDerivedFunctor₂_derivedTensor`.

## TODO

- The statements here are those of the étale file for a different site; both should be
  deduced from a single statement for an exact functor between abelian monoidal categories with
  functorial flat resolutions preserving flat objects.

## File structure

This module only imports its parts:
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMon.KFlat`: the
  complexes whose pullback is K-flat;
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMon.Vanishing`:
  tensoring with K-flat complexes, and vanishing of `K ⊗ᴸ M`;
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMon.Derived`: the
  two derived bifunctors;
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMon.Comparison`: the
  tensor and unit comparisons.
-/
