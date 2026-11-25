/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.SixFunctors.Etale.Derived.Composition
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Exchange
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.Stability
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

/-!

# External products and the Künneth formulas on the étale site

Let `A` be a monoidal Grothendieck abelian coefficient category. For two schemes `X`, `Y` over
a base `B`, with projections `p : X ×_B Y ⟶ X` and `q : X ×_B Y ⟶ Y`, the *external product*
of `K ∈ D(X_ét)` and `M ∈ D(Y_ét)` is

`K ⊠ M = Lp^* K ⊗ᴸ Lq^* M ∈ D((X ×_B Y)_ét)`.

This file introduces the external product and states the Künneth package of the six-functor
formalism: the ordinary Künneth formula with an identity factor, the relative product theorem
for `Rf_!`, the four product comparison maps, and the Künneth–Verdier isomorphism.

## Main definitions

- `AlgebraicGeometry.Etale.externalProduct`: `K ⊠ M = Lp^* K ⊗ᴸ Lq^* M`.
- `AlgebraicGeometry.Etale.HasKunnethComparisons` (`lemma-external-duality-trace-morphism`): the
  four product comparison assertions `Ku_!`, `α`, `β`, `κ`, one per field.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_externalProduct_rightDerivedLowerStar`
  (`lemma-kunneth-one-identity-factor--1`): `Rf_* M ⊠ Q ≅ R(f × id_Z)_* (M ⊠ Q)`
  over a field, for a finite coefficient ring of invertible exponent.
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_externalProduct`
  (`lemma-kunneth-formula-compact-supports`): `R(f ×_B g)_! (K ⊠ M) ≅ Rf_! K ⊗ᴸ Rg_! M`.
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_mapOverBase_externalProduct`
  (`lemma-external-duality-trace-morphism` (i)): the `!`-Künneth isomorphism
  `Ku_! : R(f₁ × f₂)_! (M₁ ⊠ M₂) ≅ Rf₁_! M₁ ⊠ Rf₂_! M₂` for a finite coefficient ring.
- `AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_externalProduct`:
  `L(i ×_B j)^* (K ⊠ L) ≅ Li^* K ⊠ Lj^* L`.
- `AlgebraicGeometry.Etale.nonempty_iso_externalProduct_closedImmersion`:
  `(i ×_B j)_* (i ×_B j)^* (K ⊠ L) ≅ i_* i^* K ⊠ j_* j^* L` for closed immersions `i`, `j`.
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_externalProduct_closedImmersion`
  (`lemma-kunneth-formula-compact-supports`): the relative product theorem for complexes supported
  on closed subschemes.
- `AlgebraicGeometry.Etale.nonempty_iso_compactlySupported_externalProduct_closedImmersion`
  (`lemma-kunneth-formula-compact-supports`): the Künneth formula for `RΓ_c(Z × W, -)` over a field.
- `AlgebraicGeometry.Etale.hasKunnethComparisons` (`lemma-external-duality-trace-morphism`): the
four
  comparison maps are isomorphisms.

## Implementation notes

The fibre-product morphisms `X ×_B Y ⟶ B`, `f₁ × f₂` and `f × 𝟙_Z` are not étale notions and
are not defined here: they are `CategoryTheory.Limits.pullback.toBase`,
`CategoryTheory.Limits.pullback.mapOverBase` and
`CategoryTheory.Limits.pullback.mapOverBaseRight` of
`WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.

Constructing the canonical comparison maps is out of scope here, so all comparisons are
stated in the form `Nonempty (_ ≅ _)`; the blueprint's naturality clauses, and the
compatibilities of the relative product theorem with base change, finite reduction, scalar
extension and the identification `Rf_! ≅ Rf_*` for proper `f`, are therefore **not stated**.
The absolute case of a product over the base `S` is the special case `B = S` of the
definitions below.

A morphism admitting a compactification is separated and locally of finite type
(`AlgebraicGeometry.HasCompactification.isSeparated` and `.locallyOfFiniteType`), so the
blueprint hypothesis "separated of finite type" is spelled `[HasCompactification f]`
together with `[QuasiCompact f]` wherever `Rf_!` occurs, and as the triple
`[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]` otherwise.

This module only imports its parts: `externalProduct` is defined in
`WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs`, the relative product theorem is in
`WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative`, the `!`-Künneth isomorphism in
`WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek` and the comparison maps in
`WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons`.

-/
