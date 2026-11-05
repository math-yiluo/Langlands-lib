# Norm-one tori: rational lattices and split rank zero

Author: Worker 1107, 4 November 2026.

This focused source-to-declaration ledger records two independently accepted,
published proofs in the algebraic group-scheme program
`2b5e4a00-9d44-49a4-9c89-979fb5b6233e`, revision 2. It supplements the
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
Workers 1107 and 1337 authored the proof unit, using Worker 1107's
shared draft.

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
the separate rational-lattice proof. Worker 1107 supplied the proof
draft and Worker 1563 prepared its submission.

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

## Independent acceptance and publication

Worker 1107 checked the independent reports, original machine receipts,
publication records and current file hashes. Each proof has an accepted
`lean.proof@1` receipt for Lake build, exact target, unchanged statement
and frozen inputs.

| Proof | Candidate | Machine receipt | Independent review | Publication commit |
| --- | --- | --- | --- | --- |
| `WeilGm.normOneRationalLattices` | `e32d27b0-067e-42d9-8f48-bc3a1cb8c239` | `a6553112-d77e-4b13-9b9f-5fc7703ee687` | `e6ca02be-2360-4087-b3b1-785f279bca00`, Reviewer 12893 | `146a43c03e57296c496825ab3176b07715c492b7` |
| `WeilGm.normOneAnisotropy` | `47f4ae37-9a68-4ac5-b846-0ff752ec58f7` | `96f12faa-7d06-41a7-9c37-d298fb3328e5` | `e59a42d8-1aeb-4904-b812-189dcff07506`, Reviewer 12976 | `442ff746325df5b6d721fee75d430a65c33d09f0` |

The integrations are respectively `164b65581b924e738c68341deefe169f`
and `eb58070dc640494f9ade91c762dd32b8`. Their fresh integrated builds
establish source compilation; the original exact-target receipts and
independent reviews establish the separate proof-acceptance evidence.
The proof tasks are respectively
`446953a2-cfcc-4f09-9138-5d3543cee92c` and
`d7f1369f-1373-4528-86ba-f1d228d6d834`.

The corresponding accepted published statement candidates are
`a4a66378-95fe-4f4c-a298-16f809f470e5` and
`44b2faab-0f89-498e-8d2e-a7765a0e2f9d`. Their current pairs match the
accepted bytes. The rational proof pair and all four anisotropy
proof/helper files likewise match their frozen bundles. A recovery
compilation of the three proof/helper modules completed with zero
errors and warnings.

These close the two exact norm-one targets. General invariant-descent
surjectivity, the Galois lattice equivalence, the based-root-datum star
action, rational conjugacy, central and derived comparisons and the
remaining field and relative structure theorems retain their own
construction and proof obligations. No rational-point quotient,
compactness or integral-model conclusion is inferred from these results.
