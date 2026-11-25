# Renard Chapter V: the published GL standard-parabolic comparison

This note, dated 2 November 2026, records a verified algebraic specialization
in the common group-scheme framework. The whole-book coverage keeps its general
reductive scope.

## Source correspondence

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The following original passages were read for this comparison:

| Locator, printed / PDF page | Source assertion and comparison boundary |
| --- | --- |
| V.3.8, 111 / 117 | Fix a maximal split torus and a minimal parabolic. Standardness means containing that minimal parabolic; semistandardness means containing the torus. The published GL comparison uses the actual diagonal torus and a cocharacter with strictly decreasing coordinates. Its cocharacter signs and choice-free subgroup intersections are derived formulations. The general unique-Levi assertions remain separate. |
| V.3.9, 112 / 118 | Every parabolic is conjugate to a standard parabolic. The proof recorded here does not establish this general conjugacy assertion. |
| V.4.2, 118 / 124 | Subsets of simple roots specify standard parabolic triples, and the source also asserts exhaustiveness, uniqueness from the subgroup data, and convexity. The GL target below identifies its actual standard subgroup functors with block functors and uniquely indexes simple-root subsets by block shapes. It does not establish all those general assertions or classify every algebraic parabolic. |

Renard works over a nonarchimedean local field. The published GL result works
over every field, with no characteristic or cardinality restriction. This
broader algebraic scope comes from the existing matrix, character-lattice and
dynamic subgroup constructions. It makes no assertion about a rational-point
topology.

## Exact published target

The proposition
[`Langlands.GroupScheme.GeneralLinearStandardParabolicStatement`](../../Langlands/GroupScheme/Rational/GeneralLinearStandardParabolicStatement.md)
quantifies over every field `k`, every natural rank `N`, and every actual
diagonal-torus cocharacter `ν` that is generic and has strictly decreasing
integer coordinates. It includes ranks zero and one.

The theorem
[`Langlands.GroupScheme.generalLinearStandardParabolic`](../../Langlands/GroupScheme/Rational/GeneralLinearStandardParabolicProof.md)
proves that complete unchanged proposition:

| Component | Exact content |
| --- | --- |
| Simple roots | `simpleRelativeRoots i ν` is the range of the actual adjacent characters `GeneralLinear.simpleRootCharacter k`. |
| All-test subgroup comparisons | For each ordered positive block shape `B`, at `J := GeneralLinear.blockSimpleRoots k B`, the actual `standardParabolic`, `standardLevi` and `standardUnipotent` equal `blockShapeParabolic`, `blockShapeLevi` and `blockShapeUnipotent`. These are subgroup-functor equalities on every test scheme. |
| Canonical rational points | Each of the three standard point subgroups is the comap of its existing matrix block subgroup under exactly `pointsEquiv` at the identity test scheme followed by coefficient transport along `Scheme.ΓSpecIso`. No replacement point isomorphism is chosen. |
| Block indexing | Every subset of the actual simple roots is `GeneralLinear.blockSimpleRoots k B` for exactly one ordered positive block shape `B`. This indexes subsets; the target does not assert a classification of every algebraic parabolic. |

The proof retains the target's genericity hypothesis. Its helper arguments
need only the stated strict decrease. It adds no structural theorem premise,
positive-rank assumption, or field restriction.

## Implemented proof

The entry theorem assembles three published helper modules:

- [`GeneralLinearSimpleRootsProof`](../../Langlands/GroupScheme/Rational/GeneralLinearSimpleRootsProof.md)
  computes actual root pairings as differences of integer coordinates.
  Positive roots have increasing indices. Pairing with the auxiliary weights
  `-i` gives every positive root height at least one; adjacent roots have height
  one and cannot split. Each nonadjacent positive root splits at its next
  coordinate, with equality checked in the actual character lattice.
- [`GeneralLinearStandardBlocksProof`](../../Langlands/GroupScheme/Rational/GeneralLinearStandardBlocksProof.md)
  derives antitone coordinates, equality at uncut edges, and strict decrease
  at cuts from the standard sign conditions. The existing cut correspondence
  and induction along coordinates identify their equality classes and order
  with the blocks. The canonical block cocharacter satisfies the conditions,
  so the intersection families are inhabited. Published dynamic matrix
  formulas then identify all three subgroup functors.
- [`GeneralLinearCanonicalPointsProof`](../../Langlands/GroupScheme/Rational/GeneralLinearCanonicalPointsProof.md)
  identifies the published rational-point homomorphism with the target's
  specified coefficient map and repackages the existing three dynamic
  membership comparisons as literal comap equalities. This helper works over
  every commutative ring.

The entry theorem then applies the existing
`GeneralLinear.existsUnique_blockSimpleRoots` to obtain unique block indexing.
The proof uses the shared constructions throughout.

## In the Library

| Module | First appeared at Library commit |
| --- | --- |
| Statement | `5730d31ad8127eb9e13a5c1e47edacef54dfa8e3` |
| Exact proof and three helper pairs | `7543113c99690e18b45f3b22d252e8cf77c3964e` |

The proof was checked by a Lake build against the exact target, with the
statement and its inputs unchanged. All eight proof/helper files were read; the
files of the Library at `db0cc8965906a94cb14e43355a0c6076a0701379` agree with
those first published. The SHA-256 hashes of the entry pairs, unchanged in the
present Library:

| Entry pair | Lean SHA256 | Markdown SHA256 |
| --- | --- | --- |
| `GeneralLinearStandardParabolicStatement` | `67ded8d9899fcecaf19d3f91809bc9d8bd99c6510f0a30b2118fb03968191a42` | `b9876e69cd733470f99ec7883ed718d87f371210f804c1cb6f24af11e69c919c` |
| `GeneralLinearStandardParabolicProof` | `0af499e7e16a1cdb54edd968116d53a50d8ef97e7162f231a27cdd81cc53c921` | `554f0b5464594106c4d3a84a767efb842eda98dcbf77eaacc75f496a916ae9d7` |

This note adds no Lean declaration.

## Retained obligations

The general reductive results in structural rows S09, S10 and S15 of
[the Chapter V source ledger](chapter-v-structural-inputs.md) retain their stated
scope. In particular, the general Weyl/root-system comparison, unique Levi and
conjugacy results, full parabolic classification and convexity require their
own exact declarations and proofs or explicit structural hypotheses.

The algebraic rational-point comaps above still require topology
and representation adapters when used in topological induction or Jacquet
constructions. They do not establish S22 compact containment, compactness of
parabolic quotients, a common maximal compact subgroup, or any
representation-theoretic conclusion. The
[whole-book ledger](coverage.md) records all other source obligations at their
scopes.
