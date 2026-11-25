/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.NumberTheory.Padics.Complex
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.ConstructibleSheaf.Presentation
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Kunneth

/-!
# Finiteness, perfectness, flat models and Künneth

The four finiteness inputs the purity chapter takes from the six-functor formalism:

* `Rf_*` and `Rf_!` preserve bounded constructibility, with a cohomological-dimension bound
  in terms of the fibre dimension (`sk-prop-sf-finiteness`);
* compactly supported cohomology is a perfect complex of `Λ`-modules
  (`lemma-perfect-complexes-geometric-point`);
* finite Tor amplitude in `[a, b]` is the same as admitting a bounded flat model concentrated
  in `[a, b]` (`lemma-flat-models-generators`);
* the Künneth formula and the projection formula in ordinary étale cohomology
  (`proposition-ordinary-external-kunneth--1`).

Throughout, `Λ` is a finite coefficient ring whose exponent is invertible on the schemes in
question (`AlgebraicGeometry.HasInvertibleExponent`) and the schemes are of finite type over a
field: without the invertibility the Artin–Schreier sequence already defeats constructibility
of `R¹f_*` in characteristic `p`.

This module only imports its parts, so that `import`s of
`WeilConjectures.SixFunctors.Etale.Derived.Finiteness` keep working:

- `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage`: finiteness of `Rf_*` and
  `Rf_!`;
- `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel`: bounded flat models;
- `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Kunneth`: Künneth and the projection
  formula.

The perfectness of compactly supported cohomology is proved in
`WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CompactSupport`, which is *not* imported
here: it rests on the stability of `Dctf` under `Rf_!`
(`WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage`), which imports this module.
-/
