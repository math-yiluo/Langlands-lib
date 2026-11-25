/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Category
public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.Constant
public import WeilConjectures.WeilSheaf.Dual
public import WeilConjectures.WeilSheaf.Fourier
public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.WeilSheaf.OpenImmersion
public import WeilConjectures.WeilSheaf.Stalk

/-!
# The interface of `ℓ`-adic Weil sheaves

The blueprint develops `ℓ`-adic Weil sheaves, their weights, their Fourier transform and the
six operations in the blocks `chap-Purity-of-real-sheaves`, `chap-The-Fourier-transform`,
`chap-The-six-operations-on-Dbctf`, `chap-The-trace-formula` and
`chap-Verdier-and-Poincare-duality`. This file gathers, by importing them, the files that phrase
that vocabulary, so that the blocks that share it share one copy.

`AlgebraicGeometry.WeilSheaf` and `AlgebraicGeometry.WeilComplex` are defined in
`WeilConjectures.WeilSheaf.Category`, following the blueprint (`definition-weil-structure`):
a Weil sheaf is a constructible `ℓ`-adic sheaf of `ℚ̄_ℓ`-modules on the small pro-étale site of
the geometric fiber `X̄ = X ×_{k₀} k̄` (`AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf`,
built on the constant sheaf `ℚ̄_ℓ,X̄` of continuous `ℓ`-adic functions) with an isomorphism
`Fr_X^* F ≅ F` for the geometric Galois Frobenius `Fr_X`; Weil complexes are the bounded
objects with constructible cohomology of the derived category of pro-étale Weil sheaves, a
triangulated category. The constant Weil sheaf `ℚ̄_ℓ` (`WeilConjectures.WeilSheaf.Constant`) is
nonzero on every nonempty scheme. The geometric stalks with their local Frobenius, the trace
function and the global sections are constructed in `WeilConjectures.WeilSheaf.Stalk`; the six
operations are built from the pro-étale ones in `WeilConjectures.WeilSheaf.LowerStar`,
`WeilConjectures.WeilSheaf.OpenImmersion`, `WeilConjectures.WeilSheaf.LowerShriek`,
`WeilConjectures.WeilSheaf.Dual` and `WeilConjectures.WeilSheaf.Fourier`. Finiteness and
compatibility statements that these constructions need, and that are not yet proved, are stated
as separate lemmas with `sorry`.

The weight formalism they are phrased against is honest as well:
`FrobeniusModule` (`WeilConjectures.ZetaLinearAlgebra.FrobeniusModule`) is an honest
finite-dimensional vector space with an automorphism, and purity and upper weight bounds are
honest conditions on the eigenvalues of that automorphism under an embedding `ι : ℚ̄_ℓ →+* ℂ`.

## Conventions

Throughout, `k₀` is a finite field with `q = Nat.card k₀` elements and `l` is a prime different
from the characteristic of `k₀`, carried as `[Fact (ringChar k₀ ≠ l)]`; both hypotheses are
arguments of `AlgebraicGeometry.WeilSheaf` itself, so every statement about Weil sheaves
carries them. The embedding `ι : ℚ̄_ℓ →+* ℂ` is an explicit argument rather than a choice: no
such embedding is constructed anywhere in mathlib. A lisse Weil sheaf is punctually pure of
weight `w` if every eigenvalue `α` of the local Frobenius at a closed point `x` satisfies
`|ι α| = q_x ^ (w / 2)`, with `q_x = q ^ deg x` the residue cardinality
`AlgebraicGeometry.Scheme.Hom.residueCard`; replacing equality by `≤` gives
`AlgebraicGeometry.WeilSheaf.HasWeightsAtMost`. Weights of cohomology are taken relative to `q`
instead, which `FrobeniusModule.IsPureOfWeightOver` names.

## Main declarations

- `AlgebraicGeometry.WeilSheaf` and `AlgebraicGeometry.WeilComplex`: the abelian category of
  constructible Weil `ℚ̄_ℓ`-sheaves on a `k₀`-scheme and the triangulated category of Weil
  complexes.
- `AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight`,
  `AlgebraicGeometry.WeilSheaf.HasWeightsAtMost` and `AlgebraicGeometry.WeilSheaf.IsReal`: the
  weight conditions and the reality condition.
- `AlgebraicGeometry.WeilSheaf.higherLowerShriek` and
  `AlgebraicGeometry.WeilComplex.derivedLowerShriek`: the higher direct images with compact
  support `Rʳf₀!` and the total derived one `Rf₀!`.
- `AlgebraicGeometry.WeilComplex.compactlySupportedCohomology` and
  `AlgebraicGeometry.WeilSheaf.compactlySupportedCohomology`: compactly supported cohomology
  `H_c^r(X ⊗ k̄, K) = Hʳ(Spec k̄, Ra_! K)` with its geometric Frobenius
  (`WeilConjectures.WeilSheaf.Cohomology`).
- `AlgebraicGeometry.WeilSheaf.directImage`, `AlgebraicGeometry.WeilSheaf.extensionByZero` and
  `AlgebraicGeometry.WeilSheaf.extensionByZeroToDirectImage`: the two extensions along an open
  immersion and the canonical map between them.
- `AlgebraicGeometry.artinSchreier` and `AlgebraicGeometry.fourierTransform`: the
  Artin–Schreier sheaves and the Fourier–Deligne transform of the affine line.
-/
