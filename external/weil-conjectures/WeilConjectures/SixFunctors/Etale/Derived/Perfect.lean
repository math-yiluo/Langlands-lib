/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.Dual
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.Invertible
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.Pullback

/-!

# Perfect complexes of étale sheaves and their coefficient duals

Let `A` be a monoidal Grothendieck abelian coefficient category and `X` a scheme, so that the
derived category `D(X_ét)` of `A`-valued étale sheaves on `X` is monoidal closed, with tensor
product `- ⊗ᴸ -` and internal hom `RHom(-, -)`. The *coefficient dual* of a complex is
`K^∨ = RHom(K, Λ_X)`.

## Main definitions

- `AlgebraicGeometry.Etale.DerivedCategory.coefficientDual`: `K ↦ K^∨ = RHom(K, Λ_X)`.
- `AlgebraicGeometry.Etale.DerivedCategory.coefficientEvaluation`: the evaluation
  `K ⊗ᴸ K^∨ ⟶ Λ_X`.
- `AlgebraicGeometry.Etale.DerivedCategory.coefficientDualIsoOfExactPairing`: `K^∨ ≅ L` for a
  left dual `L` of `K`.

## Main statements

- `AlgebraicGeometry.Etale.DerivedCategory.isDualizable_coefficientDual`
  (`theorem-poincare-duality--4`): `K^∨` is dualizable for a
  dualizable `K`.
- `AlgebraicGeometry.Etale.DerivedCategory.nonempty_iso_coefficientDual_coefficientDual`
  (`theorem-poincare-duality--4`): biduality `K ≅ K^∨∨` for a dualizable `K`.
- `AlgebraicGeometry.Etale.DerivedCategory.nonempty_iso_coefficientDual_tensor`
  (`theorem-poincare-duality--4`, `theorem-poincare-duality--5`): the comparison
  `K^∨ ⊗ᴸ M ≅ RHom(K, M)`.
- `AlgebraicGeometry.Etale.DerivedCategory.nonempty_iso_derivedHom_tensor`
  (`theorem-poincare-duality--2`): the internal hom commutes with an invertible twist.
- `AlgebraicGeometry.Etale.DerivedCategory.nonempty_iso_leftDerivedUpperStar_derivedHom`
  (`theorem-poincare-duality-frobenius--1`): the internal hom with
  a dualizable first variable commutes with pullback.

## Implementation notes

In the `ℓ`-adic formalism a complex is called *perfect* when it is, locally on the small étale
site, quasi-isomorphic to a bounded complex of finite projective `Λ_X`-modules. That this
coincides with dualizability for `- ⊗ᴸ -` is a theorem about module coefficients, not a
definition, and it is not available for a general coefficient category `A`; perfectness is
therefore *rendered here as* dualizability, `CategoryTheory.IsDualizable` of
`WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic`. A Tate twist `Λ_X(m)` is
likewise rendered as an invertible object, `CategoryTheory.IsInvertible`.

Canonical comparison maps are not constructed in this repository, so every isomorphism
assertion below is of the form `Nonempty (_ ≅ _)`; the naturality clauses of the blueprint,
and the compatibilities with finite reduction, scalar extension and shifts, are consequently
not stated. The proofs sketched in the blueprint go through the local description of a perfect
complex as a bounded complex of finite free modules, which turns the internal hom into a tensor
product.

With perfectness rendered as dualizability, the biduality statements are formal consequences of
the rigid monoidal structure: `RHom(K, -) ≅ L ⊗ᴸ -` for a left dual `L` of `K`
(`CategoryTheory.MonoidalClosed.ihomIsoTensorLeft`). They use one further input, that the right
dual of `K` is also a left dual (`nonempty_exactPairing_swap`). This follows from the symmetry
of the derived tensor product, which has not been constructed yet.

This module only imports its parts, so that `import`s of
`WeilConjectures.SixFunctors.Etale.Derived.Perfect` keep working:

- `WeilConjectures.SixFunctors.Etale.Derived.Perfect.Dual`
- `WeilConjectures.SixFunctors.Etale.Derived.Perfect.Invertible`
- `WeilConjectures.SixFunctors.Etale.Derived.Perfect.Pullback`
-/
