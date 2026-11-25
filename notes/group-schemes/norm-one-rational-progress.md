# Norm-one tori: rational lattices and split rank zero

This focused source-to-declaration ledger, dated 4 November 2026, records two
proofs in the Library in the algebraic group-scheme program. It supplements the
[field-torus and rational-center ledger](field-tori-central-progress.md)
in thematic families 2, 5 and 6. All eight families and the concrete
Deligne, GL and unitary milestones retain their outstanding obligations.
The publication audit below uses Library
`442ff746325df5b6d721fee75d430a65c33d09f0`.

## Actual groups and hypotheses

Let `k` and `K` be fields in an arbitrary common universe `u`, with a
specified `Algebra k K` and `[FiniteDimensional k K]`. Both results take
the explicit premise `Algebra.IsSeparable k K`. They impose no
characteristic, perfectness, normality or Galois condition and no further
restriction on extension degree; degree one is included.

Write `N` for
`WeilGm.normOneCommGroupScheme (CommRingCat.of k) K`, whose underlying
group scheme is `WeilGm.normOne (CommRingCat.of k) K`. These are the
existing actual determinant-norm kernel in the general-base
`Grp (Over S)` architecture. The published
[`WeilRestrictionNormOne`](../../Langlands/GroupScheme/Torus/WeilRestrictionNormOne.md)
construction identifies its test points with tensor units of norm one.
Its `normOne_isTorus_of_finite_separable` already proves torus status
under these finite-separable field hypotheses.

Characters and cocharacters below are the actual group-scheme Hom groups
`N → Gm` and `Gm → N`, written additively. Zero denotes the trivial
homomorphism. Equality concerns whole scheme morphisms, retaining all
tests, including nonreduced schemes. The extension `K` is a field;
finite separable product algebras are outside these two targets.

## Ground-field character and cocharacter vanishing

[`Langlands.GroupScheme.WeilGm.normOneRationalLattices`](../../Langlands/GroupScheme/Torus/WeilRestrictionNormOneRationalProof.lean)
([implemented argument](../../Langlands/GroupScheme/Torus/WeilRestrictionNormOneRationalProof.md))
proves the exact published
[`normOneRationalLatticesStatement k K`](../../Langlands/GroupScheme/Torus/WeilRestrictionNormOneRationalStatements.lean)
([precise statement](../../Langlands/GroupScheme/Torus/WeilRestrictionNormOneRationalStatements.md)).
It concludes both

```text
∀ χ : characterLattice N, χ = 0
∀ ν : cocharacterLattice N, ν = 0.
```

The proof chooses `AlgebraicClosure k` as an auxiliary coefficient field.
Its normality and polynomial splitting meet the hypotheses of the
published `WeilGm.normOneGaloisFixedLattices`. That theorem makes the
fixed character and cocharacter lattices of the base-changed actual
norm-one group zero. Canonical base changes of ground-field morphisms
are fixed, by the corresponding
`characterLattice.galoisRepresentation_baseChange` and
`cocharacterLattice.galoisRepresentation_baseChange` theorems.
The two `algebraBaseChange_injective` theorems then reflect zero back
to the original Hom groups.

Thus the coefficient field is auxiliary to the implementation, rather
than an exported input. The proof uses fixedness and injectivity; it
does not need every invariant morphism to descend. Its provenance is
this internal composition of published constructions and results.


## Split rank zero through actual closed subtori

[`Langlands.GroupScheme.WeilGm.normOneAnisotropy`](../../Langlands/GroupScheme/Torus/WeilRestrictionNormOneAnisotropyProof.lean)
([implemented argument](../../Langlands/GroupScheme/Torus/WeilRestrictionNormOneAnisotropyProof.md))
proves the exact published
[`normOneAnisotropyStatement k K`](../../Langlands/GroupScheme/Torus/WeilRestrictionNormOneAnisotropyStatement.lean)
([statement and source conventions](../../Langlands/GroupScheme/Torus/WeilRestrictionNormOneAnisotropyStatement.md)).
Its conclusion is

```text
IsAnisotropic (WeilGm.normOne (CommRingCat.of k) K).
```

The existing predicate in
[`Rational.SplitTorus`](../../Langlands/GroupScheme/Rational/SplitTorus.lean)
means `splitRank = 0`. Equivalently, every closed inclusion of a finite
split torus into the actual group has an empty coordinate index type.

The reusable helper
[`Langlands.GroupScheme.isAnisotropic_of_cocharacter_eq_zero`](../../Langlands/GroupScheme/Torus/CocharacterAnisotropy.lean)
([proof explanation](../../Langlands/GroupScheme/Torus/CocharacterAnisotropy.md))
establishes this comparison for any commutative group scheme over a
field. It requires neither torus status, smoothness nor finite type.
For a closed inclusion `i : Gm^I → N`, a coordinate cocharacter followed
by `i` is zero under the vanishing premise. Monomorphism cancellation
on all tests makes the coordinate cocharacter itself zero. Composing
with its matching projection gives `id_Gm = 0`; `gmEndEquiv k` turns
this into the impossible equality `1 = 0` in `ℤ`. Therefore `I` is empty.
The helper asserts this sufficient criterion, without a converse or
an image-torus construction for arbitrary cocharacters.

The norm-one proof supplies the helper's premise by the same
algebraic-closure, fixedness and injectivity argument used above. It
imports those published dependencies directly and does not depend on
the separate rational-lattice proof.

## Source correspondence and convention difference

Both norm-one conclusions are internal derived results; neither is
claimed to be a verbatim theorem from the sources below. The original
source comparison fixes the meaning of the anisotropy conclusion.

| Registered source | Exact passage | Correspondence |
| --- | --- | --- |
| `borel-tits-1965-groupes-reductifs` | Definition 4.23 and adjacent Theorem 4.21, printed p.93 / PDF p.40 | The rank-zero convention used by `IsAnisotropic`; the adjacent theorem identifies the common rank of maximal split tori. |
| `milne-2017-algebraic-groups` | Definition 25.3 and footnote 1, printed p.545 / PDF p.561 | The different convention excluding noncentral split tori. For a commutative group every subtorus is central, so that condition alone does not give the present conclusion. |
| `milne-2017-algebraic-groups-errata-2026-11-02` | Complete registered HTML snapshot, Chapter 25 | No correction to Definition 25.3 or its footnote was found. |

The source SHA-256 values are respectively
`ec6674ba292deaadd77a449f4bad3750db79c0b87b117a892ef6b09bb16357ad`,
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`
and `a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`.
The cited statement Markdown retains the exact source audit and the
internal derivation. The implemented proofs above discharge that
derivation for the actual norm-one group.

## Checks and first appearance in the Library

Each proof was checked for Lake build, exact target, unchanged statement
and unchanged inputs, and its current file hashes were checked.

| Proof | First appeared at Library commit |
| --- | --- |
| `WeilGm.normOneRationalLattices` | `146a43c03e57296c496825ab3176b07715c492b7` |
| `WeilGm.normOneAnisotropy` | `442ff746325df5b6d721fee75d430a65c33d09f0` |


The statement files of both proofs, the rational proof files and all four anisotropy
proof and helper files match the versions that first entered the Library. A
compilation of the three proof/helper modules completed with zero
errors and warnings.

These close the two exact norm-one targets. General invariant-descent
surjectivity, the Galois lattice equivalence, the based-root-datum star
action, rational conjugacy, central and derived comparisons and the
remaining field and relative structure theorems retain their own
construction and proof obligations. No rational-point quotient,
compactness or integral-model conclusion is inferred from these results.
