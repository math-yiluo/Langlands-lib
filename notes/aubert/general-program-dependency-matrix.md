# General Aubert duality: declaration and dependency matrix

This matrix covers all five families of the standalone program
`46df6a68-5db4-4428-8044-05151d6ce1f6` (Task 3640), revision 1. Declaration
names, proof status and premise boundaries are pinned to Library commit
`4bd8ef92a8f330864b325814d41cb38bf51b7794`, checked on 13 November 2026.
This refresh replaces the version pinned to
`7dc9118a3eb340e83e65d6e4174763b7a61e573c`. The eight canonical Theorem 1.7,
Corollary 1.10 and induced-Weyl targets are now published statements.
Their forward-bridge statement and the canonical smooth-complex and
full-support endpoint constructions have machine validation and independent
review approval, but await integration. The bridge proof remains separate.
None of these statuses discharges a representation-theoretic premise.

Published term transitivity
and the top term now reduce involutivity to induced K0 Weyl conjugacy alone.
Corollary 1.10(a) has the same single-input reduction. Irreducibility of `E#`
now has a published reduction, while its class formula and the required
representation-theoretic inputs remain unproved. The canonical operator
construction supplies its topology, root and subgroup-regularity data from
published declarations, retaining exactly the dynamic induction and Jacquet
finite-length inputs. The canonical standard-Levi operator and actual relative
Weyl/Coxeter package are now public too. The exact rational-point/matrix GL
operator comparison is proved, including existence of its per-index
finite-length premises. Its field scope remains `PadicField`; it does not
prove the general dynamic finite-length targets. The conditional bridge from
generic irreducibility to same-Levi generic isomorphism is also now proved.

Earlier refreshes recorded the proof of Aubert's Theorem 2.3 in the
existing matrix GL models (`A.aubertTheorem23`) and the alternate
special-vertex route to cuspidal Jacquet-factor extraction. Renard VI.3.5
remains the only unproved input of the recorded routes to support
decomposition, induction-Jacquet stability and Sharp support retention.

Earlier refreshes recorded the following. Between
`de0bad590ef480242ebae25ab2b43072096ee2a5` and `e7487341` the coatom
Jacquet-length budget was proved. Between
`5263a53b575d66cc4ebc5364c0d990d1b111c7f7` and `de0bad59` the rational
Jacquet compatibility target was proved. Between
`e449cde988d4e97ab280b8d4d11262887ccc26e0` and `5263a53b` the rational
geometric K0 expansion and the rank-one geometric Jacquet target were proved.
The [earlier coverage snapshot](general-program-coverage.md) records an older
state still, and its missing-target inventory is not the current status.

The [corrected source map](general-program-source-map.md) supplies the original
reading record and correction ledger. This matrix reuses that reviewed source
account and the companion declaration maps linked below. It makes no
additional original-literature reading claim. It records constructions,
proposition targets, retained premises and proof status. It does not establish
completion of any of the five families.

## Scope and interpretation

Write `R` for the namespace
`Langlands.Aubert.General.RationalPointFamily`, `A` for `Langlands.Aubert`
and `GS` for `Langlands.GroupScheme`. An unqualified rational declaration in
the tables belongs to `R`. Links name the actual Lean files; their same-stem
Markdown explains the source correspondence.

The closed rational targets quantify over every nonarchimedean local field,
connected reductive group, maximal split torus and generic cocharacter. They
use actual rational points with canonical `pointTopology` and actual simple
relative roots, including the empty set. Field and representation universes
`u` and `v` are independent; the representation carrier is in
`max (u + 1) v`. No restriction to split, quasisplit, characteristic-zero or
GL groups is introduced.

The actual Weyl group has denominator the point centralizer,
`N_G(T₀)/Z_G(T₀)`. Its Levi subgroups use `N_{L_I}(T₀)/Z_G(T₀)`, with
`L_∅ = Z_G(T₀)`. A finite Coxeter group on unrelated labels cannot replace the
point normalizer and centralizer comparisons.

### Status vocabulary

The status of each main target is one of the following.

- **Proved.** The Library contains a theorem whose type is exactly the target
  proposition, with no further parameters. The theorem is named.
- **Closes by composition.** Published theorems compose to the exact target
  with no parameters beyond the target's binders. A private compilation is
  not a publication: the owning task must still publish the proof.
- **Reduced.** A published theorem proves the target from named propositions,
  and at least one of them is unproved. The unproved inputs are listed. Where
  a chain of published reductions leaves only a named unproved proposition,
  the row says so.
- **Open.** No published reduction exists.

In every table, “None” means no hypotheses beyond the target's binders.
It does not discharge the finite-length, admissibility or other per-instance
premises quantified inside that target.

Worker 3640 recompiled the exact rational term-transitivity and top-term
targets, the conditional involutivity and Corollary 1.10(a) targets from Weyl
conjugacy, the Sharp irreducibility composite described below, and the
matrix-model GL composites on 13 November. Environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` reported zero errors or warnings;
all eleven inspected axiom lists contained only `propext`, `Classical.choice`
and `Quot.sound`. This is development evidence, not independent acceptance.
The earlier VI.3.5 and special-vertex composites recorded in Family 3 were
checked for the 11 November refresh against environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6` with zero errors and the same three
axioms. Those older composites were not recompiled for this refresh.

For the preceding refresh at `7dc9118a`, Worker 3640 recompiled
`GeneralLinearRationalIndexing`, `CanonicalRationalOperator` and the private
composite audit in the same approved environment, with zero errors or
warnings, including the new two-input generic-isomorphism composite.
The GL dependency diagnostic also compiled successfully. Its
[separate inventory](gl-rational-comparison-dependencies.md) records the
method, exact declarations and limits of that development evidence.

Proof status was checked by a scripted scan for theorems whose stated type
is a target proposition, followed by reading signatures and the paired
Markdown, including implication aliases that such a scan can miss. The
earlier 13 November scan and follow-up covered the tabulated declarations
through `b128d289`. A file comparison with the current pinned Library found
no changes to those existing Aubert target/proof pairs. The added published
canonical structure, GL statement/proof/transport and generic-isomorphism
bridge pairs were read for that preceding refresh. The six prerequisite statements
were also searched for exact proofs; their status below is unchanged.
That complete project-declaration traversal covers the exact GL comparison
and its statement only; earlier main-theorem dependency accounts retain
their stated scope.
Staged, reviewed or approved candidates that are not yet integrated are
mentioned separately and are never counted as proofs.

For this refresh, a comparison from `7dc9118a` to `4bd8ef92` found every
existing Aubert Lean/Markdown pair unchanged. The additions are
`CanonicalRationalTheorem17Targets` and the generic helper
`SemidirectIntersection`; neither adds a proof of an existing main target.
Of all published Lean files naming any of the six representation
prerequisites, only the new canonical target module was added or changed.
It assumes the dynamic finite-length propositions rather than proving them.
The six gates below therefore remain open. The separately published
cuspidal-support additions do not change the recorded Aubert target/proof
pairs. The GL dependency inventory remains pinned to `7dc9118a`; no new
transitive dependency audit is claimed for this refresh.

Worker 3640 also recompiled `CanonicalRationalComplex` and
`CanonicalRationalComplexEndpoints` in the approved environment above,
with zero errors or warnings. Their pending construction status is recorded
in Family 3. Development checks and review approval do not publish them.

Only the itemized external assertions S01–S23 in the
[Renard Chapter V ledger](../renard/chapter-v-structural-inputs.md) may form the
permitted external structural boundary. D01–D08, including D07's Haar and
root-product modulus formulas, remain in-book proof obligations. A named
intermediate predicate is not automatically one of the permitted S rows.

## Structural statements now proved

The following group-scheme propositions, which earlier snapshots treated as
retained structural inputs, have premise-free proofs at this commit:

| Proposition | Proof |
| --- | --- |
| `GS.StandardCocharacterStatement` | `GS.standardCocharacter` |
| `GS.RelativeRootSystemStatement` | `GS.relativeRootSystem` |
| `GS.StandardParabolicOrderStatement` | `GS.standardParabolicOrder` |
| `GS.StandardParabolicEndpointsStatement` | `GS.standardParabolicEndpoints` |
| `GS.StandardLeviIntersectionStatement` | `GS.standardLeviIntersection` |
| `GS.StandardLeviConjugationStatement` | `GS.standardLeviConjugation` |
| `GS.RelativeWeylCoxeterStatement` | `GS.relativeWeylCoxeter` |
| `GS.StandardParabolicPointsStatement` | `GS.standardParabolicPointsStatement_proof` |
| `GS.GenericCentralizerStatement` | `GS.genericCentralizer` |
| `GS.RationalBruhatStatement` | `GS.rationalBruhat` |
| `Langlands.BruhatTits.DynamicParabolicQuotientCompactStatement` | `Langlands.BruhatTits.dynamicParabolicQuotientCompact` |

`R.rationalWeylComparison` proves the point normalizer and centralizer
comparisons. These are proved propositions. Their use inside a final main
proof still needs the per-instance premises of each rational target, such as
closed subgroups, compact limits and finite-length preservation, to be
supplied at that target's scope. This matrix does not audit how the proofs
above map to the S rows.

## Operator premises and representation inputs

The [rational formal-target map](rational-formal-target-map.md) gives the full
binder groups.

| Input group | Actual declarations or conditions | Meaning for closure |
| --- | --- | --- |
| Standard family and roots | `GS.StandardCocharacterStatement`, `HasRelativeRootSystem`, connected reductivity, maximal split torus and generic cocharacter | Constructs the actual standard parabolic, Levi and radical family and finite simple-root indexing. The statement-level inputs are proved (table above). |
| Ambient topology | Local compactness, nonarchimedean group structure and Hausdorffness of canonical rational points; closed standard `P` and `U`; continuity of the derived Levi projections; `IsLimitOfCompactSubgroups` for each `U` | Supplied by published declarations in `canonicalRationalAlternatingOperator`, as detailed below. Compact-limit means every compact subset lies in a compact subgroup. |
| Ambient finite length | Separate `hiFl` and `hrFl`: actual normalized induction and Jacquet functors preserve finite length | Representation-theoretic obligations, carried by `DynamicInductionFiniteLengthStatement` and `DynamicJacquetFiniteLengthStatement`. |
| Restricted Levi family | `StandardLeviIntersectionStatement`, closed `M`, continuous inside-Levi projections, compact-limit restricted radicals, separate `hiLFl` and `hrLFl` | `canonicalRationalLeviAlternatingOperator` supplies these from published structure and the same two global dynamic finite-length inputs. `R.rationalLeviFiniteLengthStatement` proves `RationalLeviFiniteLengthStatement`. |
| Actual Weyl transport | `StandardLeviConjugationStatement`, point normalizer and centralizer comparisons, an actual finite Coxeter system, `RootLengthComparison`, `PositiveSimpleReflectionComparison`, `minimalityLengthCriterion`, `associatedSubsetLaws` | `CanonicalRationalStructure` assembles the actual canonical Coxeter system and these comparisons, with no representation input. |
| Smooth dual | Actual `ContragredientPreservesFiniteLength` and the exactness/cofinality inputs to `contragredientK0` | Representation-theoretic finiteness for the smooth dual. |

The six representation prerequisites in
[PrerequisiteStatements](../../Langlands/Representation/Aubert/General/PrerequisiteStatements.lean)
are all **open**, each with a focused proof task. Their namespace is
`Langlands.Aubert.General`:

| Proposition | Proof task |
| --- | --- |
| `RationalPointsFiniteLengthAdmissibleStatement` | `aa8bb3a4-42d3-47db-9a48-98eb87ad9327` |
| `DynamicLeviFiniteLengthAdmissibleStatement` | `96949545-6354-4d63-93f7-0e5ca1e6fdfe` |
| `RationalPointsContragredientFiniteLengthStatement` | `3591f7ea-ad5b-4993-a0a0-e6e74f09a28b` |
| `DynamicLeviContragredientFiniteLengthStatement` | `05a3f022-0da7-4f43-9fe8-de5b6d368de4` |
| `DynamicInductionFiniteLengthStatement` | `174d2de0-fa21-41b4-b091-f1b86481790b` |
| `DynamicJacquetFiniteLengthStatement` | `73e60be8-481a-4cea-b464-eed3bd89be7f` |

The six statements are representation-theoretic obligations, not structural
inputs. Admissibility, Howe finite length, adjunctions, geometric
filtrations, cuspidal support and induced-class Weyl invariance must be
proved wherever they are used.

The new conditional Jacquet–Cartan construction
`Langlands.Aubert.General.rationalPointsJacquetCartanDatum_of_availability_of_renardCartan`
in
[RationalJacquetCartanAvailability](../../Langlands/Representation/Aubert/General/RationalJacquetCartanAvailability.lean)
needs `BruhatTitsAvailabilityStatement` and `AvailableRenardCartanStatement`.
Its wall contraction is supplied by the published
`uniformizerPowers_conj_mem_of_standard` and
`isCartanLatticeModel_rational_of_standard` in
[RationalUniformizerContraction](../../Langlands/Representation/Aubert/General/RationalUniformizerContraction.lean).
This reduces a structural construction's inputs; it is not a proof of any
of the six representation prerequisites.

## Families 1 and 2: actual operator and formal identities

Source locators: Aubert 1995, Definition 1.5 and Theorem 1.7, printed
pp.2181–2183, and Corollary 1.10, p.2183. The operator is the unadjusted sum
`∑ I, (-1)^|I| i_I r_I` on the actual exact finite-length Grothendieck group.
The constructions `rationalAlternatingOperator`,
`rationalAlternatingOperator_ofRepresentation`,
`standardParabolicFiniteLength` and the restricted
`rationalLeviAlternatingOperator` are published in
[RationalAlternatingOperator](../../Langlands/Representation/Aubert/General/RationalAlternatingOperator.lean)
and
[RationalLeviFiniteLength](../../Langlands/Representation/Aubert/General/RationalLeviFiniteLength.lean).

The published
[CanonicalRationalOperator](../../Langlands/Representation/Aubert/General/CanonicalRationalOperator.lean)
adds `canonicalRationalAlternatingOperator` and
`canonicalRationalAlternatingOperator_ofRepresentation`. The main constructor
supplies affineness and smoothness from connected reductivity, the canonical
rational-point topology and its local compactness, nonarchimedean and
Hausdorff properties, `GS.standardCocharacter`, `GS.relativeRootSystem`,
closed standard subgroups, continuous Levi projections and compact-limit
radicals. Its exact-K0 prerequisite is
`canonicalStandardParabolicFiniteLength`; this helper still has ambient
topology typeclass arguments, all supplied by the main constructor.
Exactly two explicit representation inputs remain:
`Langlands.Aubert.General.DynamicInductionFiniteLengthStatement.{u, max (u + 1) v}`
and the corresponding `DynamicJacquetFiniteLengthStatement`.
The class formula uses the actual induction-Jacquet functors with
coefficient `(-1)^|I|`, including the empty-root case. This construction
neither proves those two targets nor changes the premises of the existing
rational proposition targets.

The published companion
[CanonicalRationalStructure](../../Langlands/Representation/Aubert/General/CanonicalRationalStructure.lean)
adds `canonicalRationalLeviAlternatingOperator` on every actual standard
Levi `M_J`, with roots indexed by `J`. It supplies closedness, continuity of
the restricted projections, compact-limit restricted radicals and their
finite-length packages, retaining the same two dynamic finite-length
inputs at carrier universe `max (u + 1) v`. The adapters
`rationalLeviAlternatingOperator_eq_canonical` and
`rationalAlternatingOperator_eq_canonical` are `rfl` by proof irrelevance.
They rewrite operators when the global dynamic inputs are given; they do
not infer those global inputs from the old per-index premises.

The same module constructs `canonicalPointCoxeterData`,
`canonicalCoxeterMatrix` and `canonicalCoxeterSystem` on the actual quotient
`N_G(T₀)/Z_G(T₀)`. It supplies point normalizer/centralizer comparisons,
finiteness, root-length and simple-reflection comparisons, the actual Levi
Weyl identifications, minimality and associated-subset laws, and
`canonicalAssociatedLeviConjugation` for every prescribed normalizer lift.
This Weyl section takes no representation input. It also covers empty roots.

The published statement module
[CanonicalRationalTheorem17Targets](../../Langlands/Representation/Aubert/General/CanonicalRationalTheorem17Targets.lean)
declares the following eight canonical targets. Each name is in `R`.
They retain both global dynamic finite-length inputs; smooth-dual
commutation additionally retains per-group contragredient finite length.
The canonical Jacquet target fixes the canonical Coxeter system.

| Canonical target | Existing target used by the planned forward bridge |
| --- | --- |
| `CanonicalRationalContragredientCommutationStatement` | `RationalContragredientCommutationStatement` |
| `CanonicalRationalInductionCompatibilityStatement` | `RationalInductionCompatibilityStatement` |
| `CanonicalRationalJacquetCompatibilityStatement` | `RationalJacquetCompatibilityStatement` |
| `CanonicalRationalInvolutivityStatement` | `RationalInvolutivityStatement` |
| `CanonicalRationalCuspidalEigenvalueStatement` | `RationalCuspidalEigenvalueStatement` |
| `CanonicalRationalCorollary110aStatement` | `RationalCorollary110aStatement` |
| `CanonicalRationalCorollary110bStatement` | `RationalCorollary110bStatement` |
| `CanonicalRationalInducedK0WeylConjugacyStatement` | `RationalInducedK0WeylConjugacyStatement` |

These are statements only. The distinct
`CanonicalRationalTargetBridgesStatement` is the conjunction of the eight
existing-to-canonical whole-proposition implications in this table.
Its candidate `756e4d22-f4b1-438b-be63-55c2cf2b7d24` has machine validation
and independent statement-review approval, but is not integrated or public
at this check. Worker 29 owns its exact proof successor, to be published
after the statement is public. His compiled private proof is development
evidence only.

Once that exact bridge proof is independently accepted and published, its
projections compose with published proofs of the existing targets. For
example, the fifth projection can use `rationalCuspidalEigenvalue`, and the
third can use `rationalJacquetCompatibility`. Open existing targets still
need their proofs; the bridge supplies none of their representation-theoretic
inputs. Worker 29's scope is the bridge statement and proof. The agreed
plan uses this exact reuse rather than adding duplicate canonical proof
tasks, and preserves every existing proof owner. This updates the planning
remarks in the published target Markdown without changing any declaration.
No reverse implication is claimed: old per-index premises do not supply the
global dynamic finite-length inputs, and the canonical Jacquet target fixes
one Coxeter system.

| Main target | Status at `4bd8ef92` | Remaining inputs and evidence | Proof task |
| --- | --- | --- | --- |
| `RationalCuspidalEigenvalueStatement` | Proved: `rationalCuspidalEigenvalue` | None. | — |
| `RationalGeometricK0ExpansionStatement` | Proved: `rationalGeometricK0Expansion` | None. The proof applies `rationalGeometricK0Expansion_of_standardParabolicPoints` to `GS.standardParabolicPointsStatement_proof`. | `f722f1c6-147e-453e-8664-02b7822b7bce` (completed) |
| `RationalJacquetCompatibilityStatement` | Proved: `rationalJacquetCompatibility` | None. The proof applies `rationalJacquetCompatibility_of_rationalGeometricK0Expansion` to `rationalGeometricK0Expansion`. | `47650cf4-dbb8-4197-8730-4f9848d22955` (completed) |
| `RationalInductionCompatibilityStatement` | Reduced | `rationalInductionCompatibility_of_expansion_and_inducedWeyl` needs the geometric expansion (proved) and `RationalInducedK0WeylConjugacyStatement`. | `475f7a39-11ad-4748-87b3-cfaef16a59cb` |
| `RationalInducedK0WeylConjugacyStatement` and `RationalInducedClassWeylConjugacyStatement` | Reduced | The two are equivalent by published theorems. `rationalInducedK0WeylConjugacy_of_genericIso` needs the two admissibility prerequisites and `RationalSameLeviGenericInductionIsoStatement` (proof task `ba00e20e-ea55-4b97-89cc-2e9127ada887`). | `f85448c5-077a-467f-8121-66e53755fae0`, `03e05250-cda0-4d0b-a3de-d0291194f10b` |
| `RationalTermTransitivityStatement` | Proved: `rationalTermTransitivity` | None. Actual normalized induction and Jacquet restriction in stages identify the ambient and Levi terms on exact K0. | — |
| `RationalTopTermStatement` | Proved: `rationalTopTerm` | None. The full-index term is the identity, also for an empty simple-root set. | — |
| `RationalInvolutivityStatement` | Reduced | `rationalInvolutivityStatement_of_inducedK0WeylConjugacy` needs only `RationalInducedK0WeylConjugacyStatement`. It supplies induction compatibility from the proved geometric expansion and this input; intersection, Levi finite length, term transitivity and the top term are proved. | `2f01b264-fb0e-4029-901c-009044feaa97` |
| `RationalContragredientCommutationStatement` | Reduced | `rationalContragredientCommutation_of_schemeWeylDuality` needs induced-class Weyl conjugacy and the two admissibility prerequisites. Its Coxeter, conjugation, opposite-transport and natural-duality inputs are proved. A second reduction needs `RationalContragredientTermComparisonStatement`. | `54d4578e-fc6b-4995-abf4-1ca845f4ebab` |
| `RationalCorollary110aStatement` | Reduced | `rationalCorollary110aStatement_of_inducedK0WeylConjugacy` needs only `RationalInducedK0WeylConjugacyStatement`. The intermediate theorem `rationalCorollary110aStatement_of_inductionCompatibility` needs induction compatibility alone and supplies inside-Levi finite length from the published proof. | `892c3af1-7d30-4200-b80a-f90740c269d2` |
| `RationalCorollary110bStatement` | Reduced | `rationalCorollary110bFromRankOneInputs` needs `RationalRankOneSelfAssociationStatement`, `RationalRankOneJacquetModulesStatement` and induced K0 Weyl conjugacy. The second reduces to cuspidal Jacquet-factor extraction alone (below). | `053e93d1-59ac-48f0-bbe0-38b26225fe46` |
| `RationalRankOneSelfAssociationStatement` | Reduced | The published bridge `rationalRankOneSelfAssociation_of_maximalLeviSupercuspidalReducibility` needs only Renard VII.1.3, `MaximalLeviSupercuspidalReducibilityStatement` (proof task `004e00e1-5995-4dc1-884e-a5f512150d0c`). | `46f751c8-0d69-40a6-ab67-4c19be8fc4c9` |
| `RationalRankOneLengthTwoStatement` | Reduced | `rationalRankOneLengthTwo_of_extraction` needs only cuspidal Jacquet-factor extraction. It composes `rationalRankOneLengthTwoFromInputs`, `rationalMaximalCuspidalJacquetDetectionFromExtraction` and the proved budget `rationalMaximalCuspidalJacquetBudget` (proof task `cdc95bfc-a501-4693-a1d3-fcc890aee15b`). Published direct reductions now include `rationalRankOneLengthTwo_of_wholeStatement`, `rationalRankOneLengthTwo_of_specialVertexInputs` and `rationalRankOneLengthTwo_of_jointBasis`. Their respective single inputs remain unproved (Family 3). | `c53e3363-ffa5-4f01-ae77-aca8e1f49117` |
| `RationalRankOneJacquetModulesStatement` | Reduced | `rationalRankOneJacquetModules_of_extraction` needs only cuspidal Jacquet-factor extraction. Either VI.3.5 or the special-vertex inputs suffices (Family 3). The older reduction `rationalRankOneJacquetModules_of_lengthTwo_extraction_geometry` also needs length two. | `1244dad8-89c0-4c13-95f7-1942ccf77842` |

Proved helpers used above: `rationalNaturalInductionDuality`,
`rationalNaturalJacquetDuality`, `rationalLeviFiniteLengthStatement`,
`rationalWeylComparison`, and the structural proofs listed earlier.

The term and involutivity results are in
[RationalTermTransitivityProof](../../Langlands/Representation/Aubert/General/RationalTermTransitivityProof.lean);
the Corollary 1.10(a) reductions are in
[RationalCorollary110aAssembly](../../Langlands/Representation/Aubert/General/RationalCorollary110aAssembly.lean).

On the generic-isomorphism branch, the nonzero-intertwiner target
`RationalSameLeviGenericNonzeroIntertwinerStatement` is proved by
`rationalSameLeviGenericNonzeroIntertwiner`. Generic irreducibility has the
published reduction
`rationalSameLeviGenericInductionIrreducibilityFromInputs`, whose type is
`RationalSameLeviGenericInductionIrreducibilityFromInputsStatement`.
It needs both
`Langlands.Renard.AlgebraicFamily.InducedIrreducibilityOpenStatement`
(Renard VI.8.4, proof task `2113598c-9c21-461a-9a44-f46066850c3e`)
and `Langlands.Renard.AlgebraicFamily.IrreducibleInducedTwistExistenceStatement`
(the existence consequence of Konno, Theorem 4.2); neither is proved at this
commit. The conditional bridge
`RationalSameLeviGenericInductionIsoFromIrreducibilityStatement` is now
proved by `rationalSameLeviGenericInductionIso_of_irreducibility` in
[RationalSameLeviGenericIsoFromIrreducibilityProof](../../Langlands/Representation/Aubert/General/RationalSameLeviGenericIsoFromIrreducibilityProof.lean).
It intersects the two principal opens by multiplying their nonzero
polynomials, then applies Schur's lemma to the published nonzero intertwiner.
Thus the generic isomorphism branch retains the two irreducibility inputs;
the bridge proof itself is no longer an open obligation. These declarations are in
[RationalSameLeviGenericIntertwinerProof](../../Langlands/Representation/Aubert/General/RationalSameLeviGenericIntertwinerProof.lean),
[RationalSameLeviGenericIrreducibilityReduction](../../Langlands/Representation/Aubert/General/RationalSameLeviGenericIrreducibilityReduction.lean)
and
[RationalSameLeviGenericIsoFromIrreducibilityStatement](../../Langlands/Representation/Aubert/General/RationalSameLeviGenericIsoFromIrreducibilityStatement.lean).

## Family 3: corrected actual complex and terminal comparison

Source: Aubert 1995, pp.2186–2187, corrected by the erratum, pp.4687–4690,
and the two-sided filtration and actual-map repair in Ban–Jantzen §4,
pp.160–162. The
[complex source map](smooth-complex-construction-source-map.md) and
[support/filtration source map](support-filtration-consequences-source-map.md)
explain the source correspondence. The actual complex, its differential,
initial identification and terminal cokernel `E#` are published constructions
in
[RationalStandardComplex](../../Langlands/Representation/Aubert/General/RationalStandardComplex.lean)
and
[RationalCorrectedTheorem36](../../Langlands/Representation/Aubert/General/RationalCorrectedTheorem36.lean).

Two additional construction candidates have machine validation and
independent semantic-review approval but are **not integrated or public**
at this check:

- `0f6c1e24-4998-4e3a-bbdd-a40500235460`, module
  `CanonicalRationalComplex`, supplies the published structural, topology
  and root-finiteness inputs to the actual smooth complex. It assembles ten
  aliases for the degree objects, signed differential, incoming image,
  terminal quotient and projection, retained Sharp object and functor,
  initial map and equivalence, and first differential, with five intrinsic
  square-zero and quotient laws.
- `ab63d266-7f7a-413f-beba-b5e4d8aa125f`, module
  `CanonicalRationalComplexEndpoints`, constructs
  `canonicalRationalSharpUnivIso`, the natural isomorphism from the retained
  cokernel functor at the full actual simple-root subset to the identity.
  It also proves injectivity of the actual degree-zero projection and
  bijectivity of its literal composite with the initial map:
  `canonicalRationalTerminalProjection_zero_injective` and
  `canonicalRationalInitialTerminalMap_bijective`. These specialize the
  published degree-zero laws in `RationalFixedLeviComparisonProof`.

Both candidates apply to every smooth complex representation, without a
finite-length or support-category premise, over the same arbitrary local
fields and actual reductive groups. They retain an arbitrary chosen root
order, independent universes and empty roots. At the full-root parameter
the retained degree is `|S| - |S| = 0`; this endpoint makes no positive-degree
exactness assertion. The endpoint includes the unchanged prerequisite pair
from the first candidate, to be integrated first or together with it.
Neither construction proves corrected exactness, the associated-Levi
comparison or any of the Family 4 consequences.

| Main target | Status at `4bd8ef92` | Remaining inputs and evidence | Proof task |
| --- | --- | --- | --- |
| `RationalCorrectedTheorem36Statement` | Reduced | `rationalCorrectedTheorem36_of_inputs` needs `RationalCorrectedExactnessInputs`: Bruhat (proved), graded vanishing, graded transition (proved), support induction-Jacquet stability (reduced to VI.3.5 alone, below) and exactness detection. | `613611a4-9c0e-43e3-82aa-f91d2044cfe2` |
| `RationalCorrectedGradedVanishingStatement` | Open | No published reduction. | `277860be-2aeb-4a85-8ccb-f1e2e5c573b9` |
| `RationalCorrectedGradedTransitionStatement` | Proved: `rationalCorrectedGradedTransitionStatement` | None. | — |
| `RationalFixedLeviComparisonStatement` | Proved: `rationalFixedLeviComparison` | None. | — |
| `RationalAssociatedLeviComparisonStatement` | Reduced | `rationalAssociatedLeviComparisonStatement_of_published` needs only graded vanishing. Its other six inputs (Bruhat, dynamic quotient compactness, surviving support, orbit-radical intersection, squared orbit modulus, graded transition) are proved. | `f7d95940-33d0-49d3-93d6-8d5ff8d89373` |
| `RationalJacquetCuspidalStatement` | Reduced | `rationalJacquetCuspidal_of_jacquetVanishing` needs support Jacquet vanishing. Either VI.3.5 or the special-vertex inputs suffices. | `b752450b-5e2d-4cb3-95f4-3812331c0b8a` |

The nine support-category targets are in
[RationalSupportCategoryTargets](../../Langlands/Representation/Aubert/General/RationalSupportCategoryTargets.lean).

| Support target | Status at `4bd8ef92` | Remaining inputs | Proof task |
| --- | --- | --- | --- |
| `RationalCuspidalSeriesExistenceStatement` | Proved: `rationalCuspidalSeriesExistence` | None. | — |
| `RationalSupportCategoryAssociationInvarianceStatement` | Proved: `rationalSupportCategoryAssociationInvariance` | None. | — |
| `RationalCuspidalSupportAssociationStatement` | Reduced | Cuspidal Jacquet-factor extraction. Either VI.3.5 or the special-vertex inputs suffices. | `fc414cb1-5832-4033-a2aa-d7c27f5e4691` |
| `RationalSupportCategoryIrreducibleJacquetDetectionStatement` | Reduced | Cuspidal Jacquet-factor extraction. Either VI.3.5 or the special-vertex inputs suffices. | `b7887025-20b3-4c11-9fad-0e70bdf59da6` |
| `RationalSupportCategoryJacquetVanishingStatement` | Reduced | Dynamic quotient compactness (proved) and support association. Either VI.3.5 or the special-vertex inputs suffices. | `bc64458d-2bc4-438a-9992-ba06185affa7` |
| `RationalSupportCategoryDecompositionStatement` | Reduced | `RationalCuspidalInducedEmbeddingStatement` (task `198824c2-4e2f-40c1-94a0-07fa748bede9`), `RationalInducedCuspidalSupportCategoryStatement` (task `c79b0cd0-661f-4239-9f65-483d6f319480`) and support association. The first follows from VI.3.5 by `rationalCuspidalInducedEmbedding_of_wholeStatement`; its other published reduction needs `RationalLeviJacquetCuspidalRemainderSplittingStatement`, which also has only VI.3.5 reductions. The second follows from VI.3.5 by `rationalInducedCuspidalSupportCategory_of_wholeStatement`, and from the extraction inputs by `rationalInducedCuspidalSupportCategory_of_extractionInputs`. Only VI.3.5 remains. | `8452c8a4-3686-47c2-80cf-c4ff4e16b3b2` |
| `RationalSupportCategoryInductionJacquetStatement` | Reduced | Decomposition, `RationalLeviJacquetCuspidalRemainderSplittingStatement` and support association. The splitting follows from VI.3.5 by `rationalLeviJacquetCuspidalRemainderSplitting_of_wholeStatement`. Only VI.3.5 remains. | `09268952-5848-4585-90e4-0a12121c60ef` |
| `RationalSupportCategoryZeroDetectionStatement` | Open | No published reduction. | `db02aabd-9901-4fae-9583-ec28c66aec3c` |
| `RationalSupportCategoryExactnessDetectionStatement` | Open | No published reduction. | `d70a1edd-5a84-4b03-aecf-2818901809d4` |

`RationalCuspidalJacquetFactorExtractionStatement` has proof task
`e6add7c5-44c5-45ea-afe9-7f48c98fb927`. Its published reduction
`rationalCuspidalJacquetFactorExtraction_of_inputs` needs
`RationalCuspidalExtractionInputsStatement`. Two published theorems derive
those inputs, and both of their premises are unproved:

- `rationalCuspidalExtractionInputs_of_wholeStatement` derives them from
  Renard VI.3.5, the whole-category cuspidal splitting
  `Langlands.CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement`
  (module `Langlands.Representation.CuspidalSupport.RationalWholeCuspidalDecompositionStatement`,
  proof task `4bee987a-093b-4054-bd65-7360168351d2`).
- `rationalCuspidalExtractionInputs_of_specialVertexInputs` (module
  [RationalCuspidalExtractionFromSpecialVertex](../../Langlands/Representation/Aubert/General/RationalCuspidalExtractionFromSpecialVertex.lean))
  derives them from the special-vertex inputs
  `Langlands.CuspidalSupport.RationalSpecialVertexCompactInputsStatement`.
  The published `CuspidalSupport.rationalSpecialVertexCompactInputs_of_jointBasis`
  derives those from
  `Langlands.BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement`
  (proof task `8c39faa0-2a70-4fc4-a027-914987aba924`). This route does not use
  VI.3.5. The module also publishes
  `rationalCuspidalJacquetFactorExtraction_of_specialVertexInputs` and
  `rationalCuspidalJacquetFactorExtraction_of_jointBasis`.

The stronger joint-basis target now has the published reduction
`Langlands.BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence_of_availability_and_basis`
in
[JointBasisFinalAssembly](../../Langlands/BruhatTits/SpecialCompact/JointBasisFinalAssembly.lean).
It needs `Langlands.Geometry.Building.BruhatTitsAvailabilityStatement` and
`Langlands.BruhatTits.SpecialCompact.AvailableSimultaneousStandardBasisStatement`,
both unproved. Availability and a simultaneous standard basis must hold at
the common geometric witness; separate existential witnesses do not suffice.

"Only VI.3.5 remains" in the rows of Families 1–4, and the VI.3.5 alternative
in "Either VI.3.5 or the special-vertex inputs suffices", mean the following.
For the 11 November refresh, Worker 3640 compiled, as described under the
status vocabulary, theorems
that derive each of these targets at universes `u, v` from the single
hypothesis `RationalWholeCuspidalCategoryDecompositionStatement.{u, max (u + 1) v}`:
extraction, support association, irreducible Jacquet detection, support
Jacquet vanishing, Jacquet cuspidality, induced cuspidal support,
decomposition, induction-Jacquet stability and Sharp support retention. They
use only the published theorems
`rationalCuspidalExtractionInputs_of_wholeStatement`,
`rationalCuspidalJacquetFactorExtraction_of_inputs`,
`rationalCuspidalSupportAssociation_of_cuspidalJacquetFactorExtraction`,
`rationalSupportCategoryIrreducibleJacquetDetection_of_cuspidalFactors`,
`rationalSupportCategoryJacquetVanishing_of_dynamicCompact_and_association`
with `Langlands.BruhatTits.dynamicParabolicQuotientCompact`,
`rationalJacquetCuspidal_of_jacquetVanishing`,
`rationalInducedCuspidalSupportCategory_of_wholeStatement`,
`rationalCuspidalInducedEmbedding_of_wholeStatement`,
`rationalSupportCategoryDecomposition_of_inducedCuspidal`,
`rationalLeviJacquetCuspidalRemainderSplitting_of_wholeStatement`,
`rationalSupportCategoryInductionJacquet_of_decomposition_splitting_and_association`
and `rationalSharpSupportRetention_of_inductionJacquet`. The same draft
derives the rank-one Jacquet-module target from that hypothesis alone,
adding `rationalRankOneJacquetModules_of_extraction`. It also derives the
rank-one length-two target from that hypothesis alone, adding
`rationalMaximalCuspidalJacquetDetectionFromExtraction`,
`rationalRankOneLengthTwoFromInputs` and the proved
`rationalMaximalCuspidalJacquetBudget`. The published theorem
`rationalRankOneLengthTwo_of_wholeStatement` now has the same type and route.

Its special-vertex alternative means the following. A second private
composite checked for that earlier refresh derives extraction, support association,
irreducible Jacquet detection, support Jacquet vanishing, Jacquet
cuspidality, induced cuspidal support, the rank-one Jacquet modules and
rank-one length two at universes `u, v` from the single hypothesis `RationalSpecialVertexCompactInputsStatement.{u}`. It uses
`rationalCuspidalJacquetFactorExtraction_of_specialVertexInputs`,
`rationalCuspidalExtractionInputs_of_specialVertexInputs`,
`rationalInducedCuspidalSupportCategory_of_extractionInputs`,
`rationalRankOneLengthTwo_of_extraction` and the extraction-based reductions
listed above. Composing with
`CuspidalSupport.rationalSpecialVertexCompactInputs_of_jointBasis` gives the
same targets from `JointSpecialCompactBasisExistenceStatement.{u}`. Support
decomposition, induction-Jacquet stability and Sharp support retention are not
on this route: the cuspidal induced embedding and the Levi-Jacquet remainder
splitting have only VI.3.5 reductions.

For rank-one length two, the direct special-vertex and joint-basis
compositions are now public in
[RationalRankOneLengthTwoSpecialVertex](../../Langlands/Representation/Aubert/General/RationalRankOneLengthTwoSpecialVertex.lean).
This replaces reliance on a private composite for those two reductions.

The terminal cokernel `E#` survives; there is no final zero asserting its
vanishing. Proposition 3.2 remains unresolved, and neither its failed proof
nor the original application establishes any row of this matrix.

## Family 4: finite length, irreducibility and actual involution

Source: Corollary 3.9, printed p.2189, with the corrected complex and erratum
p.4690. All six targets are in
[RationalSharpConsequenceTargets](../../Langlands/Representation/Aubert/General/RationalSharpConsequenceTargets.lean).

| Main target | Status at `4bd8ef92` | Remaining inputs | Proof task |
| --- | --- | --- | --- |
| `RationalSharpFiniteLengthStatement` | Open | No published reduction. | `0da1c37e-a39a-42e1-b90d-135db6c6e5c3` |
| `RationalSharpClassFormulaStatement` | Open | No published reduction. | `13e2abdc-2be7-4191-b74b-9eae99a56fcc` |
| `RationalSharpSupportRetentionStatement` | Reduced | `rationalSharpSupportRetention_of_inductionJacquet` needs support induction-Jacquet stability. Only VI.3.5 remains (Family 3). | `d441ca88-a2fa-4174-93e0-97d1b9fca9ba` |
| `RationalSharpIrreducibleStatement` | Reduced | `rationalSharpIrreducibleStatement_of_inputs` needs dynamic induction and Jacquet finite length, induction compatibility, involutivity and the Sharp class formula. The compiled composition described below replaces compatibility and involutivity by induced K0 Weyl conjugacy. | `44d0ed8c-18a6-44f8-8836-dc351694e9d9` |
| `RationalSharpCuspidalSeriesStatement` | Open | No published reduction. | `6316db5a-5618-43bb-a920-eadd3a912b88` |
| `RationalSharpInvolutionStatement` | Reduced | `rationalSharpInvolutionStatement_of_inputs` needs dynamic induction and Jacquet finite length, K0 involutivity, the class formula and cuspidal-series retention. K0 involutivity now reduces to induced K0 Weyl conjugacy alone. | `9d570c9e-e376-4437-8d15-3cbe9e9a0027` |

The irreducibility implication and its proof are published in
[SharpIrreducibleReduction](../../Langlands/Representation/Aubert/General/SharpIrreducibleReduction.lean).
Worker 3640 compiled its composition with
`rationalInductionCompatibility_of_expansion_and_inducedWeyl`,
`rationalGeometricK0Expansion` and
`rationalInvolutivityStatement_of_inducedK0WeylConjugacy`.
The resulting exact `RationalSharpIrreducibleStatement.{u, v}` needs only
the two dynamic finite-length targets at universes `u, max (u + 1) v`,
`RationalInducedK0WeylConjugacyStatement.{u, v}` and
`RationalSharpClassFormulaStatement.{u, v}`.
Finite length of the actual terminal cokernel is derived internally using
`Langlands.Aubert.General.sharpFiniteLengthTarget_of_inductionJacquet`;
`RationalSharpFiniteLengthStatement` is not an input of this reduction.
No exact rational proof or reduction theorem for that standalone target was
found, so its row remains open. The reduction does not prove the class formula.

Corrected exactness, termwise exactness, length and Euler arguments, support
and nonvanishing must be supplied where used. Equality of exact-K0 classes
does not imply isomorphism of modules.

## Family 5: actual GL specialization and the whole graded ring

Source: Aubert 1995, Definition 2.1, Remark 2.2 and Theorem 2.3, printed
pp.2184–2185. The [GL target map](gl-specialization-source-map.md),
[general-specialization addendum](gl-general-specialization.md) and
[point-topology comparison](gl-algebraic-point-specialization.md) give the
model and dependency boundaries.

| Target | Status at `4bd8ef92` | Evidence or remaining inputs |
| --- | --- | --- |
| `R.GL.blockRootSubsetEquiv` and its comparisons | Published construction and proofs | Equivalence of GL block shapes with finite subsets of the actual simple relative roots; `blockRootSubsetEquiv_card`, `blockRootSubsetEquiv_sign`, `rootSet_blockRootSubsetEquiv`, and the parabolic, Levi and unipotent comap comparisons. These hold over any field, in every natural rank. |
| `Langlands.Parabolic.GeneralLinearModulusCompatibility` | Proved: `Langlands.Parabolic.generalLinearModulusCompatibility` | Full Haar-to-block modulus comparison in every rank, including rank zero. |
| `A.generalAlternatingOperator_eq` with its modulus premise discharged | Closes by composition | `A.generalAlternatingOperator_eq F T n (fun B => Parabolic.generalLinearModulusCompatibility F T B)` identifies the general unadjusted operator on the GL block families with `A.alternatingOperator` in every rank. The comparison is for `PadicField` models. |
| `R.GL.RationalAlternatingOperatorComparisonStatement` | Proved: `R.GL.rationalAlternatingOperatorComparison` | No extra premises. For `PadicField` models and every natural rank, including zero, supplies the actual rational-point topology and per-index premises and intertwines the two operators by exact-K0 pullback. It quantifies every strictly decreasing diagonal cocharacter. |
| `A.BinaryProductExactnessStatement` | Proved: `A.binaryProductExactness` | — |
| `A.GradedInductionRingLawsStatement` | Proved: `A.gradedInductionRingLaws` | — |
| `A.SegmentPolynomialComparisonStatement` | Proved: `A.segmentPolynomialComparison` | — |
| `A.AdjustedSegmentExchangeStatement` | Proved: `A.adjustedSegmentExchange` | — |
| `A.AdjustedInvolutivityStatement` | Proved: `A.adjustedInvolutivity` | — |
| `A.AdjustedHomogeneousMultiplicativityStatement` | Proved: `A.adjustedHomogeneousMultiplicativity` | — |
| `A.AdjustedMultiplicativityStatement` | Closes by composition | `A.gradedOperator_multiplicative_of_homogeneous` applied to the homogeneous proof. |
| `A.AubertTheorem23Statement` | Proved: `A.aubertTheorem23` | None. The proof combines multiplicativity as above, the comparison from `A.gradedOperatorRingHom_eq_zelevinsky` with `A.gradedAdjustedOperator_unit` and the segment exchange, and Zelevinsky involutivity from the comparison and adjusted involutivity. It keeps the three parameters `hx`, `hl` and `hp` of the statement. Proof task `1850a779-27e5-4d34-a280-4b0c58e22a7a` (Task 5362). |
| `A.ZelevinskyInvolutivityStatement`, `A.AubertZelevinskyComparisonStatement` | Close by composition | They are the second and third conjuncts of Theorem 2.3: `(A.aubertTheorem23 F T hx hl hp).2.1` and `.2.2`. |
| `A.SegmentMonomialSpanningStatement`, `A.SegmentMonomialBasisStatement` | Close by composition | With `b := A.segmentMonomialBasis F T hx hl (A.segmentPolynomialComparison F T hx hl)`, the pair `⟨b.linearIndependent, b.span_eq⟩` proves the basis statement and `b.span_eq` proves the spanning statement (`Module.Basis.linearIndependent`, `Module.Basis.span_eq`; `A.segmentMonomialBasis_apply` identifies the basis vectors with `A.segmentMonomial` by `rfl`). No standalone theorem with either type is published yet. Theorem 2.3 does not need them: it uses the polynomial comparison directly. |

The segment socle and special quotient are exchanged by the unadjusted
operator with sign `(-1)^(n-k)` (`A.segmentSocleHead`), and without sign by the
adjusted operator (`A.adjustedSegmentExchange`).

The actual simple-root construction is public in
[GeneralLinearRationalIndexing](../../Langlands/Representation/Aubert/General/GeneralLinearRationalIndexing.lean).
For a strictly decreasing diagonal cocharacter, it identifies the general
sign with `(-1)^(N-B.length)` and all three literal subgroups with the
canonical inverse images of the existing matrix subgroups. The explicit
`upperCocharacter` supplies that chamber in every rank, including zero.
The algebraic indexing comparisons alone do not transport the normalized
functors or exact-K0 operator. That transport is now supplied by the exact
theorem in
[GeneralLinearRationalComparisonProof](../../Langlands/Representation/Aubert/General/GeneralLinearRationalComparisonProof.lean),
proving the published
[comparison statement](../../Langlands/Representation/Aubert/General/GeneralLinearRationalComparisonStatement.lean).

For every `F : PadicField p`, compatible topological data `T`, natural rank
`N` and diagonal cocharacter with strictly decreasing weights, the theorem
proves all three parts of that statement:

1. The actual rational-point group with canonical evaluation topology is
   locally compact, Hausdorff and nonarchimedean.
2. All operator premises exist, including closed subgroups, continuous Levi
   projections, compact-limit radicals and finite-length preservation of
   both normalized functors at carrier universe `max (u + 1) v`.
3. For arbitrary proofs of those premises, exact-K0 pullback along
   `GroupScheme.GeneralLinear.rationalPointsContinuousMulEquiv` intertwines
   `A.alternatingOperator` and the actual `rationalAlternatingOperator`.

The proof uses the published full modulus comparison and the generic
transport helpers in
[OperatorTransport](../../Langlands/Representation/Aubert/General/OperatorTransport.lean):
`GroupTransport.continuous_projection_transport`,
`GroupTransport.inductionPreservesFiniteLength_transport`,
`GroupTransport.jacquetPreservesFiniteLength_transport` and
`GroupTransport.alternatingOperator_transport` (in namespace
`Langlands.Aubert.General`).
The last helper transports the complete finite signed sum, including its
index equivalence. The endpoint is the actual exact Grothendieck group,
with all short-exact-sequence relations. No rational operator premise is
left as an additional hypothesis of this GL target. Its per-instance
finite-length proofs are GL-specific, and do not prove either global
dynamic finite-length target for arbitrary local fields and reductive groups.
The row for `A.generalAlternatingOperator_eq` remains a distinct block-family
comparison.

Worker 97, with Worker 29, published this exact proof in Task 5922. It is
accepted and public, as is the comparison statement. Its transitive GL
representation-theory dependencies are recorded below and in the
[exact dependency inventory](gl-rational-comparison-dependencies.md).
This closes the actual rational-point/matrix operator bridge in the stated
`PadicField` scope. It does not replace the whole-graded-ring theorem,
monomial comparison or support-sign adjustment by a generator calculation.

## Bottlenecks

Several open inputs each block many main targets.

1. **Renard VI.3.5 whole-category cuspidal splitting**
   (`4bee987a-093b-4054-bd65-7360168351d2`). It is the only remaining input of
   support decomposition, induction-Jacquet stability and Sharp support
   retention. Through induction-Jacquet stability it is also an input of
   Theorem 3.6. It alone also suffices for cuspidal Jacquet-factor extraction
   (`e6add7c5-44c5-45ea-afe9-7f48c98fb927`), support association, irreducible
   Jacquet detection, Jacquet vanishing, Jacquet cuspidality, induced cuspidal
   support, the rank-one Jacquet modules and the rank-one length-two target.
   Through the rank-one Jacquet modules it feeds Corollary 1.10(b).
2. **Special-vertex inputs or joint special-compact basis existence**
   (`8c39faa0-2a70-4fc4-a027-914987aba924`). Either one suffices, in place of
   VI.3.5, for the extraction targets listed in item 1 (all except
   decomposition, induction-Jacquet stability and Sharp support retention).
   The joint-basis route now reduces further to Bruhat–Tits availability
   and the available simultaneous standard basis, both unproved.
3. **Admissibility** (`aa8bb3a4-42d3-47db-9a48-98eb87ad9327`,
   `96949545-6354-4d63-93f7-0e5ca1e6fdfe`) **and generic same-Levi induction
   isomorphism** (`ba00e20e-ea55-4b97-89cc-2e9127ada887`). Together they give
   induced K0 Weyl conjugacy. That in turn feeds induction compatibility,
   involutivity, Corollary 1.10(a), contragredient commutation,
   Corollary 1.10(b), Sharp irreducibility and Sharp involution.
   Generic irreducibility itself reduces to Renard VI.8.4 and the existence
   of an irreducible induced twist; the implication from generic
   irreducibility to generic isomorphism is now proved by
   `rationalSameLeviGenericInductionIso_of_irreducibility`; it retains that
   irreducibility premise.
4. **Corrected graded vanishing** (`277860be-2aeb-4a85-8ccb-f1e2e5c573b9`).
   It is the only remaining input of the associated-Levi comparison, and an
   input of Theorem 3.6.
5. **Renard VII.1.3** (`004e00e1-5995-4dc1-884e-a5f512150d0c`). It is the only
   remaining input of rank-one self-association.
6. **Dynamic induction and Jacquet finite length**
   (`174d2de0-fa21-41b4-b091-f1b86481790b`,
   `73e60be8-481a-4cea-b464-eed3bd89be7f`). These are exactly the retained
   inputs of both the canonical ambient and standard-Levi operator
   constructions. The GL comparison supplies only its GL instances. They also enter the
   published reductions for Sharp irreducibility and involution. A proof of
   a rational proposition with these facts inside its binders does not
   discharge them for the canonical operator.
7. **Targets with no published reduction**: support zero and exactness
   detection, Sharp finite length, the Sharp class formula and Sharp
   cuspidal-series retention.

## Classification accounting

This program permits Langlands and Zelevinsky classification. An upstream
consumer decides separately whether a published proof satisfies its own route
constraints. A final audit must traverse both declaration types and proof
values and identify each classification declaration by exact name.

- `R.rationalCuspidalEigenvalue`: its reviewed route uses no Langlands
  classification, character independence or geometric lemma, under its
  visible premises.
- `R.rationalGeometricK0Expansion`: its paired
  [Markdown](../../Langlands/Representation/Aubert/General/RationalGeometricK0Expansion.md)
  states that the proof bodies of the theorem, its two assembly declarations,
  the modules of its chain and `GS.standardParabolicPointsStatement_proof`
  invoke no adjointness, cuspidal support, character independence or Langlands
  classification.
- `R.rationalJacquetCompatibility`: its paired
  [Markdown](../../Langlands/Representation/Aubert/General/RationalJacquetCompatibilityProof.md)
  reports a reachable-constant check. It uses the geometric lemma through
  `R.rationalGeometricK0Expansion` and no adjointness, Langlands
  classification or character independence. The only reachable declarations
  in cuspidal-support or classification modules are the generic helpers that
  Markdown names.
- `R.rationalMaximalCuspidalJacquetBudget`: its paired
  [Markdown](../../Langlands/Representation/Aubert/General/RationalMaximalCuspidalJacquetBudgetProof.md)
  states that the named proof bodies use no adjointness, cuspidal-support
  theorem, character independence or Langlands classification. It uses the
  geometric lemma through `R.rationalMaximalSourceGeometricFiltration`.
- `R.rationalTermTransitivity` and `R.rationalTopTerm`: their paired
  [Markdown](../../Langlands/Representation/Aubert/General/RationalTermTransitivityProof.md)
  records actual stage isomorphisms and the endpoint identity, with no
  Langlands classification, character independence, geometric lemma,
  adjointness theorem or cuspidal-support theorem. The conditional
  involutivity reduction from Weyl conjugacy additionally uses the proved
  geometric expansion and the finite signed-intersection calculation;
  its Weyl-conjugacy premise remains unproved.
- The paired Markdown of
  [RationalCorollary110aAssembly](../../Langlands/Representation/Aubert/General/RationalCorollary110aAssembly.md)
  records no classification, character-independence, geometric-lemma or
  cuspidal-support theorem in the compatibility-input adapter. The
  Weyl-input adapter additionally uses `R.rationalGeometricK0Expansion`.
  The paired Markdown of
  [SharpIrreducibleReduction](../../Langlands/Representation/Aubert/General/SharpIrreducibleReduction.md)
  records none of those theorems or an adjointness theorem in that
  reduction's body or the helpers it names. The composite in Family 4
  adds the geometric expansion through compatibility and involutivity.
  These are accounts of the conditional bodies; the eventual proofs of
  their representation-theoretic premises must be audited separately.
- The paired Markdown of
  [RationalRankOneLengthTwoSpecialVertex](../../Langlands/Representation/Aubert/General/RationalRankOneLengthTwoSpecialVertex.md)
  reports a traversal of declaration types and values for both direct
  reductions. It records geometric filtrations, cuspidal Jacquet detection,
  first adjointness and compact-coefficient projectivity, but no Langlands
  classification, representation-character independence, second
  adjointness, VI.3.5 splitting or fixed-level cuspidal finiteness.
  The special-vertex or joint-basis premise remains unproved.
- The new exact `R.GL.rationalAlternatingOperatorComparison` and its
  statement were separately traversed by declaration type and value,
  including opaque values. The theorem reaches 31,418 project constants in
  2,529 project modules; the statement reaches 30,841 in 2,480. Both closures
  reach the same 67 constants (56 theorems) defined in ten
  `Langlands.Representation.Classification` modules. They include
  `Langlands.Classification.normalizedInductionFiniteLength`,
  `Langlands.Parabolic.normalizedJacquetFiniteLength`,
  `Langlands.Classification.irreducibleProductEmbedding` and
  `Langlands.Classification.irreducibleProductFiniteLength`. These are GL
  finite-length, Jacquet-length and supercuspidal-embedding dependencies;
  module names alone do not identify a use of the Langlands quotient
  classification theorem. The
  [inventory](gl-rational-comparison-dependencies.md) lists every reached
  classification-module declaration and distinguishes the four additional
  classification modules that are only imported. No segment-classification
  declaration is reached. This exact inventory, rather than a blanket
  classification-independence claim, supplies the GL comparison's account.
- Family 5: the published proofs of the segment exchange, adjusted
  involutivity and homogeneous multiplicativity each list, in their paired
  Markdown, the declarations they reach in `Langlands.Classification` and
  `Langlands.Representation.Classification.*` modules. Examples are
  `Langlands.Classification.segmentZelevinskyConstituentExistence`,
  `Langlands.Classification.normalizedInductionFiniteLength` and
  `Langlands.Classification.irreducibleProductEmbedding`. Theorem 2.3
  therefore depends transitively on GL classification results. The exact
  inventories are in
  [AdjustedSegmentExchangeProof](../../Langlands/Representation/Aubert/AdjustedSegmentExchangeProof.md),
  [AdjustedInvolutivityProof](../../Langlands/Representation/Aubert/AdjustedInvolutivityProof.md)
  and
  [AdjustedHomogeneousMultiplicativityProof](../../Langlands/Representation/Aubert/AdjustedHomogeneousMultiplicativityProof.md).
  The paired Markdown of `A.aubertTheorem23`,
  [AubertTheorem23Proof](../../Langlands/Representation/Aubert/AubertTheorem23Proof.md),
  lists the 437 declarations in 58 `Langlands.Representation.Classification`
  modules that its proof reaches. It makes no claim of classification
  independence.
- For every other main target, the transitive verdict remains undetermined
  until a complete proof exists. In particular, any route to induced-class
  Weyl invariance must be audited through its actual proof declarations.

## Remaining assembly

Families 1–4 remain open. Their actual canonical ambient, standard-Levi
and Weyl constructions are public, but the global representation inputs
and the remaining main proofs above still need to be supplied. The eight
canonical theorem targets are published statements. Their forward-bridge
statement is reviewed but awaits integration; Worker 29 retains its exact
proof successor. The planned exact reuse preserves existing target owners
and leaves their open inputs unchanged. The canonical smooth-complex and
full-support endpoint candidates are reviewed constructions awaiting
integration, without closing corrected exactness or Family 4.
In Family 5, the existing matrix-model targets are proved or close by
composition, and the actual rational-point/matrix operator bridge is now
proved in the stated `PadicField` scope, including rank zero. The full
graded-ring comparison and its monomial basis/spanning content remain part
of the program; their matrix-model evidence is the published Theorem 2.3
and the exact composites listed above. No arbitrary-local-field GL
comparison is asserted by the `PadicField` theorem. Remaining work includes
closing the bottlenecks, publishing the needed composites through their
owning tasks and discharging each per-instance representation premise.
Every listed proof task retains its existing owner. Supporting helper
publications, conditional reductions and a reviewed status note do not
complete their parent targets.

Worker 76 assembled the 3 November matrix, reusing Worker 164's structural
boundary, Worker 320's correction guidance, Workers 165/1186's rational
formal-target map, Workers 194/379's corrected-complex and support accounts,
and Workers 585/34's GL construction and dependency accounts. Worker 3640
(formerly Worker 18) refreshed the status four times on 10 November 2026, at
`e449cde`, `5263a53b`, `de0bad59` and `e7487341`, and again on 11 November
2026 at `642008d6`, and on 13 November at `b128d289` with the published
term/top, Corollary 1.10(a), Sharp irreducibility and direct special-vertex
reductions of Workers 3940/3941, 4220/36 and 3915, alongside Worker 3640's
operator and GL indexing constructions. The refresh at `7dc9118a` added
Worker 29's canonical Levi/Weyl assembly, Worker 97's exact GL comparison
with Worker 29, Worker 5266's generic-isomorphism bridge and the conditional
Jacquet–Cartan/contraction construction. Worker 3640 performed that GL
dependency traversal. This refresh at `4bd8ef92` records Worker 29's public
canonical targets, his reviewed forward-bridge statement and planned exact
proof, and Worker 3640's reviewed smooth-complex and full-support endpoint
constructions. These attributions do not extend any original-source reading
record or supply proof acceptance.
