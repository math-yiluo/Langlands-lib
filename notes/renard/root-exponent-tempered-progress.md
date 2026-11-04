# Renard V.3 and VII.1–VII.2: actual roots, exponents and normalization

Worker 6, 4 November 2026. This focused map supplements the
[whole-book ledger](coverage.md) and the
[Chapter V structural-input ledger](chapter-v-structural-inputs.md).
It records three verified publications and the remaining gates to the
all-parabolic temperedness criterion. It is not a complete inventory of
V.3, VII.1 or VII.2, and supplies no new Lean proof.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
PDF page numbers below are one-based and equal printed page numbers plus six.
The source passages and the current Lean/Markdown pairs were read for the
claims below. The publication receipts were checked separately from
compilation, and the three published pairs match the files at Library
`6d810cf8b71c5da9cf2722e850d66305665461f5`.

## Selected source assertions and exact interfaces

| Passage, printed / PDF page | Published interface and retained obligation |
| --- | --- |
| V.3.4, 110 / 116: nonzero ambient Lie roots, radical roots and reduction by divisibility within the actual root set | `Langlands.GroupScheme.RenardRootConventionStatement` compares actual dynamic-radical Lie weights with positive relative roots and their indivisible parts. This is a published **statement**, with its proof still open. Divisibility is not primitivity in the entire character lattice. |
| V.3.12, 112 / 118: the simple system of the reduced positive roots of a minimal parabolic | The same statement compares indecomposables in the reduced positive set with `simpleRelativeRoots`, whose definition uses all positive relative roots. It does not identify all indivisible positive roots with simple roots. Bases, fundamental weights, coroots and central decompositions retain separate obligations. |
| V.3.14, 113 / 119: choose a contained minimal parabolic whose maximal split torus contains the specified Levi split component; restrict the simple roots outside the Levi index | `ParabolicRootPresentationData.IsCompatible` and `ParabolicRootPresentation p l a` record actual choices for specified maps. `pres.restrictedRoots` is the existing restricted-simple-root set. This construction does not prove existence or independence of those choices. |
| First two V.3.15 displays, 113 / 119: positive and nonnegative sums over the restricted roots | `pres.positiveCone` and `pres.nonnegCone` instantiate the existing finite-sum constructions in the full real character space. Membership, empty-index and elementary cone laws are implemented. The subsequent coroot-inequality chambers are different sets and are not substituted here. |
| VI.1.2, 135–136 / 141–142: normalized Jacquet quotient and the inverse modular-function convention | `Langlands.Aubert.General.RepresentedParabolic.jacquetFunctor` uses the actual coinvariant quotient and inverse-half Haar twist on literal point images. Its split-component action formula makes the factor explicit. This focused construction does not establish the section's exactness, adjunction or preservation assertions. |
| VII.1.1, 220 / 226: compact-open characteristic spaces, normalized exponents and their set | `normalizedJacquetWeightSpace`, `IsNormalizedJacquetExponent` and `normalizedJacquetExponents` apply the published weight-space machinery to the actual quotient. Membership uses one power uniform over all torus points. Definitions and intrinsic laws extend to smooth inputs; the direct-sum, admissibility and finite-length conclusions are separate. |
| VII.2.1, 227 / 233: admissibility and the nonnegative root-cone condition for every exponent at every parabolic | The pending explicitly normalized definition described below uses these actual constructions. No publication or complete source correspondence for that predicate is asserted here. The three remarks and the subsequent induction theorem remain open in this map. |

The Chapter V construction is over arbitrary fields, visibly extending the
source's local-field setting. A presentation records actual maps
`p : P ⟶ G`, `l : M ⟶ P` and `a : A.toGrp ⟶ M`, together with an actual maximal
split torus, generic cocharacter, simple-root index and factor map. Compatibility
requires parabolicity, a rational Levi, a split component, equalities of the
standard parabolic and Levi subgroup functors on every test scheme, and
factorization through the torus. It also requires a contained minimal dynamic
parabolic and a single standard cocharacter realizing both supplied images.
An empty family of standard cocharacters cannot supply that witness.
No equality between the standard empty-index parabolic and the dynamic
parabolic is silently used.

The cones lie in
`RealTorusSpace.Vstar A = ℝ ⊗[ℤ] characterLattice A`.
Local finite type gives finite Lie-root support, hence finite simple and
restricted roots. An empty complementary-root index yields `{0}` in the full
space, including its central directions. The proved component-isomorphism
pullback laws in this construction keep the ambient torus, generic cocharacter
and simple-root index fixed. They do not establish independence across
arbitrary presentations.

The exponent interface fixes a represented geometric radical `r : U ⟶ P`
and the multiplication-isomorphism witness for that same `l,r`. It derives
closedness, Levi normalization, centrality and continuity of the actual point
maps, then reuses the existing normalized Jacquet functor. Its comparison
`isNormalizedJacquetExponent_iff_standard` requires explicit equalities of the
radical image, Levi image and transported split-component point map.
It is not an unconditional standard-reduction theorem.

The point topology is the canonical `RationalPointFamily.pointTopology`.
The field topology is Hausdorff; local compactness and nonarchimedeanness of
the ambient point group are explicit hypotheses. The smooth complex
representation carrier has a universe independent of the field/group
universe. Neither finite-dimensional carriers nor scalar central characters
are required.

## Verified publications

Each receipt below has `accepted = true`, `public = true`, an unqualified
independent semantic approval and a published integration. A definition
receipt covers its construction and intrinsic laws; the statement receipt
does not prove its proposition.

| Pair and exact declaration | Candidate, independent review and publication |
| --- | --- |
| [ArbitraryParabolic](../../Langlands/Representation/Exponents/ArbitraryParabolic.md), `Langlands.Aubert.General.RepresentedParabolic.IsNormalizedJacquetExponent` | Definition `678ceb15-602f-4aaf-b1c2-3bc9c4ee24c0`; Reviewer 12310, review `f305b203-8d2e-4735-ad66-1e76371db9d7`; integration `d757143185e04f3c8a8456056ecf2a12`, commit `7596502b4fe9738072198e7f23076fa02293f254`. |
| [ParabolicRootPresentation](../../Langlands/GroupScheme/Rational/ParabolicRootPresentation.md), `Langlands.GroupScheme.ParabolicRootPresentation.nonnegCone` | Definition `e204b3f2-bd58-49e9-95dc-f9e1888f50bf`; Reviewer 12327, review `c0ce4017-c01f-4c43-86ba-9d04327e46a5`; integration `38571d24640344bfb006ae105b655720`, commit `6d810cf8b71c5da9cf2722e850d66305665461f5`. |
| [RenardRootConventionStatement](../../Langlands/GroupScheme/Rational/RenardRootConventionStatement.md), `Langlands.GroupScheme.RenardRootConventionStatement` | Statement `3204db6d-d854-4955-bed8-74b6e65a3cf9`; Reviewer 12337, review `c7efa60d-01f4-458c-ae8b-a5953c24a3dd`; integration `1d435d5d66a8493488125f8b84ec2210`, commit `6d810cf8b71c5da9cf2722e850d66305665461f5`. |

The arbitrary-parabolic wrapper imports Worker 1507's existing generic and
standard-family weight machinery unchanged. This map credits that reuse
without assigning any of the remaining proof obligations to its author.

## The two real-part conventions

V.3.20 starts on printed p.115/PDF p.121 with the exponential parameter
`s ↦ q^(-s)`. On printed p.116/PDF p.122 it defines the real part of an
unramified character through the real part of a lift under that map.
Later on the same page it writes the real part of a general character as
the raw natural logarithm of its modulus. These formulas differ under the
fixed positive valuation.

The current [SplitTorusRealPart](../../Langlands/Representation/Plancherel/SplitTorusRealPart.md)
module gives the two parameters separate names and the exact relation

```text
rawLogRealPart hA χ =
  (-Real.log (LocalField.residueCardinality k : ℝ)) • normalizedRealPart hA χ.
```

Since `q > 1`, the scalar is negative. The
[SplitTorusNormFormula](../../Langlands/Representation/Plancherel/SplitTorusNormFormula.md)
module gives the all-point normalized formula
`‖χ(a)‖ = q ^ (-pair (normalizedRealPart hA χ) (valuation a))`
for smooth characters. These named implementations fix the convention used
by the pending definition; they do not identify membership of the two
parameters in the same nonnegative root cone.

An exact comparison with a corrected, consistent reading of V.3.20 and
VII.2.1 remains a source-correspondence obligation. A normalized predicate
alone cannot close VII.2.1 source-definition coverage.
The coroot-pairing positivity used for the Langlands-classification parameters
of VII.4 also retains its own construction and comparison obligations.

## Pending units and proof gates

At this dated check, statement candidate
`5fe091ee-4eaf-4aa5-ab1a-0c994c44ec86` has accepted machine validation and
Reviewer 12375's unqualified semantic approval in review
`b4a378ef-5647-434d-b7e8-6cd9a0392f75`, but remains staged and nonpublic.
Its aggregate `Langlands.GroupScheme.ParabolicRootPresentationStatement`
asserts existence for every specified actual `p,l,a`, independence of
restricted roots and both cones across arbitrary compatible presentations,
and both-direction pullback transport under compatible component isomorphisms.
All presentation fields may vary in its comparisons. The focused statement
task is `324d4a6a-1bb2-4eb5-8cc7-0e8e01fa19ee`.
Neither its approval nor this map supplies a proof or publication.

Definition candidate `9571e30c-ad43-4382-ab43-19ed1aad72c0` has accepted
machine validation and awaits semantic review
`a9f9c9b2-dc1e-4579-b239-9620c4d194ed`. The focused construction task is
`f04b8f7d-2ba7-4d50-b374-4ecb7b1f15a1`.
Its `Langlands.Aubert.General.RepresentedParabolic.IsNormalizedExponentTempered`
requires admissibility and the normalized exponent condition for every
specified actual parabolic, rational Levi and split component. For each
triple it requires a nonempty compatible-presentation type and tests
**every** presentation, matching represented radical and exponent.
The rational-Levi predicate already supplies existence of a matching
radical. Missing presentations cannot make this condition true.
The candidate includes six direct extraction laws, not a structural,
analytic or representation-theoretic criterion.

The dependency order still requires:

1. Proof of the published `RenardRootConventionStatement`, with focused
   successor task `90eeb314-6b62-4150-bf19-095a45c0ff33`.
2. Publication and then proof of the presentation existence, full
   independence and transport targets. Fixed-presentation pullback laws
   do not replace these targets.
3. Acceptance and publication of the normalized temperedness construction,
   followed by exact source-convention and standard-reduction comparisons.
   Actual topology and subgroup-image comparisons remain explicit.
4. The source's separate representation-theoretic assertions: the VII.1.1
   direct-sum and finite-exponent results, Casselman's criterion, all three
   VII.2.1 remarks, induction and restriction behavior, and the later
   tempered-support and classification results. In particular a scalar
   central character is relevant only when one exists; it is not a premise
   of the all-parabolic definition.

The listed task identifiers locate work. They are not proof receipts,
ownership changes or authority to resume held tasks. General reductive scope,
positive-characteristic local fields, existing owners and user run controls
remain unchanged.
