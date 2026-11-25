# General Aubert duality: declaration and dependency matrix

The [16 November canonical-identity and Sharp update](general-program-proof-update-2026-11-16.md)
records fourteen further exact proofs in the Library, their retained
premises, the Family 1/2 reduction statements and the later fixed-Levi proof.
It supersedes the corresponding statuses below and in the 14 November update;
the other rows retain their historical pins.

The [14 November proof publication update](general-program-proof-update-2026-11-14.md)
records nine exact proofs in the Library: the canonical bridges, six
conditional reductions and the whole rational GL Theorem 2.3 target. It
supersedes those proof statuses in the historical tables below and records
the seven further reductions and the Family 1/2 statements, all now proved.

The [13 November publication and dependency update](general-program-publication-update-2026-11-13.md)
records the subsequent publication of the canonical smooth complex, endpoints
and bridge statements, the new canonical Family 3/4 and whole-graded GL
targets, and their proofs. That bounded addendum supersedes the statuses for
those modules below; the other rows retain this matrix's historical commit.

This matrix covers all five families of the general Aubert duality
program. Declaration names, proof status and premise boundaries are pinned
to Library commit `4bd8ef92a8f330864b325814d41cb38bf51b7794`; an earlier
version was pinned to `7dc9118a3eb340e83e65d6e4174763b7a61e573c`. At the pin
the eight canonical Theorem 1.7, Corollary 1.10 and induced-Weyl targets were
statements of the Library; their forward-bridge statement and the canonical
smooth-complex and full-support endpoint constructions entered the Library
later, and the bridge is proved (see the updates above). Checked again
against the Library as it is, none of the targets marked Open or Reduced in
the tables below has an unconditional proof; the targets marked Open there
now have reductions. None of these statuses discharges a
representation-theoretic premise.

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
reading record and correction ledger. This matrix reuses that source
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
  with no parameters beyond the target's binders. A compilation outside the
  Library is not a proof in the Library.
- **Reduced.** A published theorem proves the target from named propositions,
  and at least one of them is unproved. The unproved inputs are listed. Where
  a chain of published reductions leaves only a named unproved proposition,
  the row says so.
- **Open.** No published reduction exists.

In every table, “None” means no hypotheses beyond the target's binders.
It does not discharge the finite-length, admissibility or other per-instance
premises quantified inside that target.

The exact rational term-transitivity and top-term targets, the conditional
involutivity and Corollary 1.10(a) targets from Weyl conjugacy, the Sharp
irreducibility composite described below, and the matrix-model GL composites
were recompiled at the pin in the Library's Lean environment with zero errors
or warnings; all eleven inspected axiom lists contained only `propext`,
`Classical.choice` and `Quot.sound`. This is development evidence, not a
check of the proofs against their targets. The earlier VI.3.5 and
special-vertex composites recorded in Family 3 were checked at an earlier
commit with zero errors and the same three axioms, and were not recompiled
at the pin.

For the preceding version at `7dc9118a`, `GeneralLinearRationalIndexing`,
`CanonicalRationalOperator` and the composite audit were recompiled in the
same environment, with zero errors or
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
Files outside the Library are mentioned separately and never counted as
proofs.

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

`CanonicalRationalComplex` and `CanonicalRationalComplexEndpoints` were also
recompiled, with zero errors or warnings; they entered the Library after the
pin (see the 13 November update).

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
were all **open** at the pin and are still unproved. Their namespace is
`Langlands.Aubert.General`:

| Proposition |
| --- |
| `RationalPointsFiniteLengthAdmissibleStatement` |
| `DynamicLeviFiniteLengthAdmissibleStatement` |
| `RationalPointsContragredientFiniteLengthStatement` |
| `DynamicLeviContragredientFiniteLengthStatement` |
| `DynamicInductionFiniteLengthStatement` |
| `DynamicJacquetFiniteLengthStatement` |

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
existing-to-canonical whole-proposition implications in this table; the
Library proves it (`canonicalRationalTargetBridges`).

The bridge's projections compose with published proofs of the existing targets. For
example, the fifth projection can use `rationalCuspidalEigenvalue`, and the
third can use `rationalJacquetCompatibility`. Open existing targets still
need their proofs; the bridge supplies none of their representation-theoretic
inputs. This reuse avoids duplicate canonical proofs; it changes no
declaration.
No reverse implication is claimed: old per-index premises do not supply the
global dynamic finite-length inputs, and the canonical Jacquet target fixes
one Coxeter system.

| Main target | Status at `4bd8ef92` | Remaining inputs and evidence |
| --- | --- | --- |
| `RationalCuspidalEigenvalueStatement` | Proved: `rationalCuspidalEigenvalue` | None. |
| `RationalGeometricK0ExpansionStatement` | Proved: `rationalGeometricK0Expansion` | None. The proof applies `rationalGeometricK0Expansion_of_standardParabolicPoints` to `GS.standardParabolicPointsStatement_proof`. |
| `RationalJacquetCompatibilityStatement` | Proved: `rationalJacquetCompatibility` | None. The proof applies `rationalJacquetCompatibility_of_rationalGeometricK0Expansion` to `rationalGeometricK0Expansion`. |
| `RationalInductionCompatibilityStatement` | Reduced | `rationalInductionCompatibility_of_expansion_and_inducedWeyl` needs the geometric expansion (proved) and `RationalInducedK0WeylConjugacyStatement`. |
| `RationalInducedK0WeylConjugacyStatement` and `RationalInducedClassWeylConjugacyStatement` | Reduced | The two are equivalent by published theorems. `rationalInducedK0WeylConjugacy_of_genericIso` needs the two admissibility prerequisites and `RationalSameLeviGenericInductionIsoStatement`. |
| `RationalTermTransitivityStatement` | Proved: `rationalTermTransitivity` | None. Actual normalized induction and Jacquet restriction in stages identify the ambient and Levi terms on exact K0. |
| `RationalTopTermStatement` | Proved: `rationalTopTerm` | None. The full-index term is the identity, also for an empty simple-root set. |
| `RationalInvolutivityStatement` | Reduced | `rationalInvolutivityStatement_of_inducedK0WeylConjugacy` needs only `RationalInducedK0WeylConjugacyStatement`. It supplies induction compatibility from the proved geometric expansion and this input; intersection, Levi finite length, term transitivity and the top term are proved. |
| `RationalContragredientCommutationStatement` | Reduced | `rationalContragredientCommutation_of_schemeWeylDuality` needs induced-class Weyl conjugacy and the two admissibility prerequisites. Its Coxeter, conjugation, opposite-transport and natural-duality inputs are proved. A second reduction needs `RationalContragredientTermComparisonStatement`. |
| `RationalCorollary110aStatement` | Reduced | `rationalCorollary110aStatement_of_inducedK0WeylConjugacy` needs only `RationalInducedK0WeylConjugacyStatement`. The intermediate theorem `rationalCorollary110aStatement_of_inductionCompatibility` needs induction compatibility alone and supplies inside-Levi finite length from the published proof. |
| `RationalCorollary110bStatement` | Reduced | `rationalCorollary110bFromRankOneInputs` needs `RationalRankOneSelfAssociationStatement`, `RationalRankOneJacquetModulesStatement` and induced K0 Weyl conjugacy. The second reduces to cuspidal Jacquet-factor extraction alone (below). |
| `RationalRankOneSelfAssociationStatement` | Reduced | The published bridge `rationalRankOneSelfAssociation_of_maximalLeviSupercuspidalReducibility` needs only Renard VII.1.3, `MaximalLeviSupercuspidalReducibilityStatement`. |
| `RationalRankOneLengthTwoStatement` | Reduced | `rationalRankOneLengthTwo_of_extraction` needs only cuspidal Jacquet-factor extraction. It composes `rationalRankOneLengthTwoFromInputs`, `rationalMaximalCuspidalJacquetDetectionFromExtraction` and the proved budget `rationalMaximalCuspidalJacquetBudget`. Published direct reductions now include `rationalRankOneLengthTwo_of_wholeStatement`, `rationalRankOneLengthTwo_of_specialVertexInputs` and `rationalRankOneLengthTwo_of_jointBasis`. Their respective single inputs remain unproved (Family 3). |
| `RationalRankOneJacquetModulesStatement` | Reduced | `rationalRankOneJacquetModules_of_extraction` needs only cuspidal Jacquet-factor extraction. Either VI.3.5 or the special-vertex inputs suffices (Family 3). The older reduction `rationalRankOneJacquetModules_of_lengthTwo_extraction_geometry` also needs length two. |

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
(Renard VI.8.4)
and `Langlands.Renard.AlgebraicFamily.IrreducibleInducedTwistExistenceStatement`
(the existence consequence of Konno, Theorem 4.2); neither is proved (each
has only conditional reductions in the Library). The conditional bridge
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

Two further constructions entered the Library after the pin:

- module
  `CanonicalRationalComplex`, supplies the published structural, topology
  and root-finiteness inputs to the actual smooth complex. It assembles ten
  aliases for the degree objects, signed differential, incoming image,
  terminal quotient and projection, retained Sharp object and functor,
  initial map and equivalence, and first differential, with five intrinsic
  square-zero and quotient laws.
- module
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

| Main target | Status at `4bd8ef92` | Remaining inputs and evidence |
| --- | --- | --- |
| `RationalCorrectedTheorem36Statement` | Reduced | `rationalCorrectedTheorem36_of_inputs` needs `RationalCorrectedExactnessInputs`: Bruhat (proved), graded vanishing, graded transition (proved), support induction-Jacquet stability (reduced to VI.3.5 alone, below) and exactness detection. |
| `RationalCorrectedGradedVanishingStatement` | Open | No published reduction. |
| `RationalCorrectedGradedTransitionStatement` | Proved: `rationalCorrectedGradedTransitionStatement` | None. |
| `RationalFixedLeviComparisonStatement` | Proved: `rationalFixedLeviComparison` | None. |
| `RationalAssociatedLeviComparisonStatement` | Reduced | `rationalAssociatedLeviComparisonStatement_of_published` needs only graded vanishing. Its other six inputs (Bruhat, dynamic quotient compactness, surviving support, orbit-radical intersection, squared orbit modulus, graded transition) are proved. |
| `RationalJacquetCuspidalStatement` | Reduced | `rationalJacquetCuspidal_of_jacquetVanishing` needs support Jacquet vanishing. Either VI.3.5 or the special-vertex inputs suffices. |

The nine support-category targets are in
[RationalSupportCategoryTargets](../../Langlands/Representation/Aubert/General/RationalSupportCategoryTargets.lean).

| Support target | Status at `4bd8ef92` | Remaining inputs |
| --- | --- | --- |
| `RationalCuspidalSeriesExistenceStatement` | Proved: `rationalCuspidalSeriesExistence` | None. |
| `RationalSupportCategoryAssociationInvarianceStatement` | Proved: `rationalSupportCategoryAssociationInvariance` | None. |
| `RationalCuspidalSupportAssociationStatement` | Reduced | Cuspidal Jacquet-factor extraction. Either VI.3.5 or the special-vertex inputs suffices. |
| `RationalSupportCategoryIrreducibleJacquetDetectionStatement` | Reduced | Cuspidal Jacquet-factor extraction. Either VI.3.5 or the special-vertex inputs suffices. |
| `RationalSupportCategoryJacquetVanishingStatement` | Reduced | Dynamic quotient compactness (proved) and support association. Either VI.3.5 or the special-vertex inputs suffices. |
| `RationalSupportCategoryDecompositionStatement` | Reduced | `RationalCuspidalInducedEmbeddingStatement`, `RationalInducedCuspidalSupportCategoryStatement` and support association. The first follows from VI.3.5 by `rationalCuspidalInducedEmbedding_of_wholeStatement`; its other published reduction needs `RationalLeviJacquetCuspidalRemainderSplittingStatement`, which also has only VI.3.5 reductions. The second follows from VI.3.5 by `rationalInducedCuspidalSupportCategory_of_wholeStatement`, and from the extraction inputs by `rationalInducedCuspidalSupportCategory_of_extractionInputs`. Only VI.3.5 remains. |
| `RationalSupportCategoryInductionJacquetStatement` | Reduced | Decomposition, `RationalLeviJacquetCuspidalRemainderSplittingStatement` and support association. The splitting follows from VI.3.5 by `rationalLeviJacquetCuspidalRemainderSplitting_of_wholeStatement`. Only VI.3.5 remains. |
| `RationalSupportCategoryZeroDetectionStatement` | Open | No published reduction. |
| `RationalSupportCategoryExactnessDetectionStatement` | Open | No published reduction. |

`RationalCuspidalJacquetFactorExtractionStatement` is unproved. Its published reduction
`rationalCuspidalJacquetFactorExtraction_of_inputs` needs
`RationalCuspidalExtractionInputsStatement`. Two published theorems derive
those inputs, and both of their premises are unproved:

- `rationalCuspidalExtractionInputs_of_wholeStatement` derives them from
  Renard VI.3.5, the whole-category cuspidal splitting
  `Langlands.CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement`
  (module `Langlands.Representation.CuspidalSupport.RationalWholeCuspidalDecompositionStatement`).
- `rationalCuspidalExtractionInputs_of_specialVertexInputs` (module
  [RationalCuspidalExtractionFromSpecialVertex](../../Langlands/Representation/Aubert/General/RationalCuspidalExtractionFromSpecialVertex.lean))
  derives them from the special-vertex inputs
  `Langlands.CuspidalSupport.RationalSpecialVertexCompactInputsStatement`.
  The published `CuspidalSupport.rationalSpecialVertexCompactInputs_of_jointBasis`
  derives those from
  `Langlands.BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement`
  This route does not use
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
For an earlier version of this matrix, theorems were compiled, as described
under the status vocabulary,
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
and `rationalSharpSupportRetention_of_inductionJacquet`. The same composite
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

| Main target | Status at `4bd8ef92` | Remaining inputs |
| --- | --- | --- |
| `RationalSharpFiniteLengthStatement` | Open | No published reduction. |
| `RationalSharpClassFormulaStatement` | Open | No published reduction. |
| `RationalSharpSupportRetentionStatement` | Reduced | `rationalSharpSupportRetention_of_inductionJacquet` needs support induction-Jacquet stability. Only VI.3.5 remains (Family 3). |
| `RationalSharpIrreducibleStatement` | Reduced | `rationalSharpIrreducibleStatement_of_inputs` needs dynamic induction and Jacquet finite length, induction compatibility, involutivity and the Sharp class formula. The compiled composition described below replaces compatibility and involutivity by induced K0 Weyl conjugacy. |
| `RationalSharpCuspidalSeriesStatement` | Open | No published reduction. |
| `RationalSharpInvolutionStatement` | Reduced | `rationalSharpInvolutionStatement_of_inputs` needs dynamic induction and Jacquet finite length, K0 involutivity, the class formula and cuspidal-series retention. K0 involutivity now reduces to induced K0 Weyl conjugacy alone. |

The irreducibility implication and its proof are published in
[SharpIrreducibleReduction](../../Langlands/Representation/Aubert/General/SharpIrreducibleReduction.lean).
Its composition was compiled with
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
| `A.AubertTheorem23Statement` | Proved: `A.aubertTheorem23` | None. The proof combines multiplicativity as above, the comparison from `A.gradedOperatorRingHom_eq_zelevinsky` with `A.gradedAdjustedOperator_unit` and the segment exchange, and Zelevinsky involutivity from the comparison and adjusted involutivity. It keeps the three parameters `hx`, `hl` and `hp` of the statement. |
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

This exact proof and the comparison statement are in the Library. Its transitive GL
representation-theory dependencies are recorded below and in the
[exact dependency inventory](gl-rational-comparison-dependencies.md).
This closes the actual rational-point/matrix operator bridge in the stated
`PadicField` scope. It does not replace the whole-graded-ring theorem,
monomial comparison or support-sign adjustment by a generator calculation.

## Bottlenecks

Several open inputs each block many main targets.

1. **Renard VI.3.5 whole-category cuspidal splitting**
   (`RationalWholeCuspidalCategoryDecompositionStatement`). It is the only remaining input of
   support decomposition, induction-Jacquet stability and Sharp support
   retention. Through induction-Jacquet stability it is also an input of
   Theorem 3.6. It alone also suffices for cuspidal Jacquet-factor extraction
   (`RationalCuspidalJacquetFactorExtractionStatement`), support association, irreducible
   Jacquet detection, Jacquet vanishing, Jacquet cuspidality, induced cuspidal
   support, the rank-one Jacquet modules and the rank-one length-two target.
   Through the rank-one Jacquet modules it feeds Corollary 1.10(b).
2. **Special-vertex inputs or joint special-compact basis existence**
   (`JointSpecialCompactBasisExistenceStatement`). Either one suffices, in place of
   VI.3.5, for the extraction targets listed in item 1 (all except
   decomposition, induction-Jacquet stability and Sharp support retention).
   The joint-basis route now reduces further to Bruhat–Tits availability
   and the available simultaneous standard basis, both unproved.
3. **Admissibility** (`RationalPointsFiniteLengthAdmissibleStatement`,
   `DynamicLeviFiniteLengthAdmissibleStatement`) **and generic same-Levi
   induction isomorphism** (`RationalSameLeviGenericInductionIsoStatement`). Together they give
   induced K0 Weyl conjugacy. That in turn feeds induction compatibility,
   involutivity, Corollary 1.10(a), contragredient commutation,
   Corollary 1.10(b), Sharp irreducibility and Sharp involution.
   Generic irreducibility itself reduces to Renard VI.8.4 and the existence
   of an irreducible induced twist; the implication from generic
   irreducibility to generic isomorphism is now proved by
   `rationalSameLeviGenericInductionIso_of_irreducibility`; it retains that
   irreducibility premise.
4. **Corrected graded vanishing** (`RationalCorrectedGradedVanishingStatement`).
   It is the only remaining input of the associated-Levi comparison, and an
   input of Theorem 3.6.
5. **Renard VII.1.3** (`MaximalLeviSupercuspidalReducibilityStatement`). It is the only
   remaining input of rank-one self-association.
6. **Dynamic induction and Jacquet finite length**
   (`DynamicInductionFiniteLengthStatement`,
   `DynamicJacquetFiniteLengthStatement`). These are exactly the retained
   inputs of both the canonical ambient and standard-Levi operator
   constructions. The GL comparison supplies only its GL instances. They also enter the
   published reductions for Sharp irreducibility and involution. A proof of
   a rational proposition with these facts inside its binders does not
   discharge them for the canonical operator.
7. **Targets with no published reduction at the pin**: support zero and
   exactness detection, Sharp finite length, the Sharp class formula and
   Sharp cuspidal-series retention. The Library now has reductions of all
   five (see the 14 and 16 November updates).

## Classification accounting

This program permits Langlands and Zelevinsky classification. An upstream
consumer decides separately whether a published proof satisfies its own route
constraints. A final audit must traverse both declaration types and proof
values and identify each classification declaration by exact name.

- `R.rationalCuspidalEigenvalue`: its route uses no Langlands
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
canonical theorem targets are statements of the Library, and their
forward-bridge statement is proved; the planned reuse leaves their open
inputs unchanged. The canonical smooth-complex and full-support endpoint
constructions are in the Library, without closing corrected exactness or
Family 4.
In Family 5, the existing matrix-model targets are proved or close by
composition, and the actual rational-point/matrix operator bridge is now
proved in the stated `PadicField` scope, including rank zero. The full
graded-ring comparison and its monomial basis/spanning content remain part
of the program; their matrix-model evidence is the published Theorem 2.3
and the exact composites listed above. No arbitrary-local-field GL
comparison is asserted by the `PadicField` theorem. Remaining work includes
closing the bottlenecks, putting the needed composites into the Library and
discharging each per-instance representation premise. Supporting helpers,
conditional reductions and status notes do not complete the targets
they serve.

Earlier versions of this matrix were pinned to Library commits `e449cde`,
`5263a53b`, `de0bad59`, `e7487341`, `642008d6`, `b128d289` and `7dc9118a`.
