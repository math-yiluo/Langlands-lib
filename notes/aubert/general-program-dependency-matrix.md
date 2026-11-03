# General Aubert duality: declaration and dependency matrix

This intermediate matrix concerns all five families of standalone program
`46df6a68-5db4-4428-8044-05151d6ce1f6`, revision 1. Declaration names and
premise boundaries below are pinned to Library commit
`24243ad1d7d77cd0f3cd88510b523cb2a13a1142`, checked on 3 November 2026.
The [earlier coverage snapshot](general-program-coverage.md) records the older
`0ebc0efd383ff160084af3b33ab2b7806f7a1dde` state. Its missing-target inventory
must not be read as the status of the present declarations.

The [corrected source map](general-program-source-map.md) supplies the original
reading record and correction ledger. This matrix reuses that reviewed source
account and the companion declaration maps linked below; it makes no additional
original-literature reading claim. It records constructions, proposition
targets, retained premises and the exact proof evidence adopted here. It does
not establish completion of any of the five families.

## Scope and interpretation

Write `R` for the namespace
`Langlands.Aubert.General.RationalPointFamily`, and `A` for
`Langlands.Aubert`. An unqualified rational declaration in the tables belongs
to `R`. Links name the actual Lean files; their same-stem Markdown explains
the source correspondence.

The closed rational targets quantify over every nonarchimedean local field,
connected reductive group, maximal split torus and generic cocharacter. They
use actual rational points with canonical `pointTopology`, and actual simple
relative roots, including the empty set. Field and representation universes
`u` and `v` are independent; the representation carrier is in
`max (u + 1) v`. Their construction adapters can have weaker field assumptions.
No restriction to split, quasisplit, characteristic-zero or GL groups is
introduced here.

The actual Weyl group has denominator the point centralizer:
`N_G(T₀)/Z_G(T₀)`. Its Levi subgroups use
`N_{L_I}(T₀)/Z_G(T₀)`, with `L_∅ = Z_G(T₀)`. The predicates
`HasPointNormalizerComparison` and `HasPointCentralizerComparison` compare the
actual point subgroups with the scheme constructions. A finite Coxeter group
on unrelated labels cannot replace these comparisons.

“No exact proof adopted” means that this matrix does not yet adopt an
independently accepted and published proof of that main target. It is not an
assertion that no relevant helper or later submission exists. A public
`Prop` definition states a target; its publication is not proof of that target.
Conditional constructors and reduction theorems are recorded at their actual
scope.

Only the itemized external assertions S01–S23 in the
[Renard Chapter V ledger](../renard/chapter-v-structural-inputs.md) may form the
permitted external structural boundary. D01–D08, including D07's Haar and
root-product modulus formulas, remain in-book proof obligations. A named
intermediate predicate is not automatically one of the permitted S rows.
Each eventual main proof must map the structural assertions it actually
consumes to exact ledger rows, and discharge its other premises.

## Operator premises and representation inputs

The [rational formal-target map](rational-formal-target-map.md) gives the full
binder groups. The following distinction is needed to read the main table.

| Input group | Actual declarations or conditions | Meaning for closure |
| --- | --- | --- |
| Standard family and roots | `Langlands.GroupScheme.StandardCocharacterStatement`, `HasRelativeRootSystem`, connected reductivity, maximal split torus and generic cocharacter | Constructs the actual standard parabolic, Levi and radical family and finite simple-root indexing. The exact external-row mapping and any derived comparisons remain explicit. |
| Ambient topology | Local compactness, nonarchimedean group structure and Hausdorffness of canonical rational points; closed standard `P` and `U`; continuity of the derived Levi projections; `IsLimitOfCompactSubgroups` for each `U` | Supplies the hypotheses of the existing exactness and normalization adapters. Compact-limit means every compact subset is contained in a compact subgroup, not just an unspecified exhaustion. |
| Ambient finite length | Separate `hiFl` and `hrFl`, asserting preservation of finite length by actual normalized induction and Jacquet functors | Representation-theoretic obligations. The local-field and reductivity binders do not prove them. |
| Restricted Levi family | `StandardLeviIntersectionStatement`, closed `M`, continuous inside-Levi projections, compact-limit restricted radicals, separate `hiLFl` and `hrLFl` | Constructs Levi-in-Levi terms. The restricted finite-length assertions are representation-theoretic, even when an adapter derives them from other preservation results. |
| Actual Weyl transport | `StandardLeviConjugationStatement`, the point normalizer and centralizer comparisons, an actual finite Coxeter system, `RootLengthComparison`, `PositiveSimpleReflectionComparison`, `minimalityLengthCriterion` and `associatedSubsetLaws` | Identifies longest representatives and associated Levis. These mixed structural and derived inputs need exact S-row mapping or proofs; they are not one blanket external assumption. |
| Smooth dual | Actual `ContragredientPreservesFiniteLength`, together with the exactness/cofinality inputs to `contragredientK0` | Representation-theoretic finiteness must be discharged for the smooth dual. |

The separately named general representation targets include
`Langlands.Aubert.General.RationalPointsFiniteLengthAdmissibleStatement`,
`DynamicLeviFiniteLengthAdmissibleStatement`,
`RationalPointsContragredientFiniteLengthStatement`,
`DynamicLeviContragredientFiniteLengthStatement`,
`DynamicInductionFiniteLengthStatement` and
`DynamicJacquetFiniteLengthStatement` in
[PrerequisiteStatements](../../Langlands/Representation/Aubert/General/PrerequisiteStatements.lean).
Their presence does not turn these six obligations into structural inputs.
Admissibility, Howe finite length, first and second adjunction, geometric
filtrations, cuspidal support and induced-class Weyl invariance retain their
representation-theoretic proof obligations wherever used.

## Families 1 and 2: actual operator and formal identities

Source locators are Aubert 1995, Definition 1.5 and Theorem 1.7,
printed pp.2181–2183, and Corollary 1.10, p.2183. The operator is the
unadjusted sum `∑ I, (-1)^|I| i_I r_I` on the actual exact finite-length
Grothendieck group, with relations from all short exact sequences.

| Required result and current declarations | Structure and topology retained | Representation and formal ingredients | Proof evidence adopted; classification verdict |
| --- | --- | --- | --- |
| Actual operator: `rationalAlternatingOperator`, `rationalAlternatingOperator_ofRepresentation`, `standardParabolicFiniteLength`; restricted `rationalLeviAlternatingOperator` | Ambient standard/root/topology premises above; restricted family premises for the Levi operator | Exact normalized functors and actual exact K0; separate ambient and restricted finite-length preservation. Finite subset sum with the literal `(-1)^I.card` sign. | Published constructions and conditional class formula in [RationalAlternatingOperator](../../Langlands/Representation/Aubert/General/RationalAlternatingOperator.lean) and [RationalLeviFiniteLength](../../Langlands/Representation/Aubert/General/RationalLeviFiniteLength.lean). Universal preservation closure remains open here. Classification use of that final closure is undetermined. |
| Smooth-dual commutation: `RationalContragredientCommutationStatement` | Ambient operator premises | Actual smooth-dual K0 map and contragredient finite-length preservation; comparison of normalized induction–Jacquet terms with their smooth duals | [Target](../../Langlands/Representation/Aubert/General/RationalContragredientTarget.lean). No exact proof adopted; transitive classification use and version undetermined. |
| Induction compatibility: `RationalInductionCompatibilityStatement` | Ambient and restricted Levi premises | Actual normalized induction K0, induction/Jacquet transitivity and geometric comparison; finite Weyl cancellation | [Target](../../Langlands/Representation/Aubert/General/RationalInductionTarget.lean). No exact proof adopted; transitive classification use and version undetermined. |
| Longest-representative Jacquet compatibility: `RationalJacquetCompatibilityStatement` | Ambient, restricted and actual Weyl-transport premises | Actual conjugation K0 from the associated Levi `J'` to `J`, normalized Jacquet/induction comparison and cancellation. Every lift of the specified longest representative is quantified. | [Target](../../Langlands/Representation/Aubert/General/RationalJacquetTarget.lean). No exact proof adopted; transitive classification use and version undetermined. |
| Involutivity: `RationalInvolutivityStatement` | Ambient operator premises in the target; reductions can require the additional restricted and Weyl premises | Equality `D.comp D = LinearMap.id` on the whole exact K0. Induction compatibility, transitivity, actual top term and finite cancellation must be justified in a reduction route. | [Target](../../Langlands/Representation/Aubert/General/RationalInvolutivityTarget.lean). Conditional reductions do not close it. No exact proof adopted; transitive classification use and version undetermined. |
| Cuspidal eigenvalue: `RationalCuspidalEigenvalueStatement`; proof `rationalCuspidalEigenvalue` | The ambient standard/root/topology, `hiFl` and `hrFl` premises remain in the exact target | Proper normalized Jacquet modules vanish by the displayed cuspidality condition. The actual full endpoint gives the remaining class, with sign `(-1)^card (SimpleRoot i ν)`, including cardinality zero. | Exact published proof adopted; see the evidence table below. Its reviewed declaration route uses no Langlands classification, character independence or geometric lemma. This verdict is conditional on the visible premises and is not a proof of their discharge. |
| Corollary 1.10(a): `RationalCorollary110aStatement` | Ambient operator premises, `StandardLeviIntersectionStatement` and closed actual Levis `hM` for object-level inside-Levi cuspidality | Ambient `hiFl`/`hrFl` and the stated irreducibility and cuspidality conditions are retained. The proposed proof uses the actual Levi cuspidal eigenvalue and induction compatibility; any additional restricted-operator hypotheses of these helpers must be discharged at this target's scope. | [Corollary targets](../../Langlands/Representation/Aubert/General/RationalCorollaryTargets.lean). No exact proof adopted; transitive classification use and version undetermined. |
| Corollary 1.10(b): `RationalCorollary110bStatement` | Ambient operator premises, `StandardLeviIntersectionStatement` and closed actual Levis `hM` for object-level inside-Levi cuspidality; no Weyl/Coxeter/root-transport premise | Ambient `hiFl`/`hrFl` are retained. The proposed proof uses separately named `RationalRankOneLengthTwoStatement`, `RationalRankOneSelfAssociationStatement`, `RationalRankOneJacquetModulesStatement`, actual induced-class Weyl invariance, exact-K0 additivity and the actual top term. Additional hypotheses of these helpers must be discharged at this target's scope. | Same [target file](../../Langlands/Representation/Aubert/General/RationalCorollaryTargets.lean). Supporting reductions are not the final exchange proof. No exact proof adopted; transitive classification use and version undetermined. |

Neither corollary target takes restricted projection-continuity,
restricted compact-limit, `hiLFl` or `hrLFl` premises. Their inside-Levi
cuspidality predicate uses actual normalized Jacquet objects without
constructing a restricted K0 operator. The Weyl, root-sign, length,
association and conjugation inputs in the separately named rank-one
prerequisites are proof-route obligations, not assumptions of
`RationalCorollary110bStatement`. Applying those prerequisites requires
establishing their extra hypotheses from the corollary's actual binders.

The geometric and Weyl-invariance representation inputs are separately named
`RationalGeometricK0ExpansionStatement` in
[RationalGeometricK0Target](../../Langlands/Representation/Aubert/General/RationalGeometricK0Target.lean)
and `RationalInducedK0WeylConjugacyStatement` /
`RationalInducedClassWeylConjugacyStatement` in
[RationalInducedWeylConjugacyTarget](../../Langlands/Representation/Aubert/General/RationalInducedWeylConjugacyTarget.lean).
In particular, the permitted Ban–Jantzen route to induced-class invariance
uses classification, character independence and the geometric lemma.
Naming that route supplies none of those proofs. An alternative route must
be audited through its actual proof declarations.

## Supporting results: what the verified receipts establish

These four records were checked against their complete pairs, independent
review reports and publication records. Frozen sources, publication sources
and the inspected Library pairs agreed in the saved byte comparisons.
The first, second and fourth rows have accepted `lake-build` and
`exact-target` proof checks with no review qualifications. The Howe row has
statement checks only.

| Exact declaration | Immutable record, publication and independent reviewer | Established scope and retained boundary |
| --- | --- | --- |
| `Langlands.Aubert.General.jacquetFiniteGenerationOfCompactQuotient : JacquetFiniteGenerationOfCompactQuotientStatement` | Proof `1c18fc3e-af9e-4b0d-8f67-4ae07a117a29`; commit `fe38b3e353a7b1fb30017218b2ee1f7f87f979fd`; Reviewer 9650 | Compact `P\G` and finite generation over the actual ambient group algebra imply finite generation of the normalized Jacquet module. The helper starting from finite length still concludes only finite generation. It proves neither admissibility nor Howe finite length nor `DynamicJacquetFiniteLengthStatement`. |
| `Langlands.Jacquet.iwahoriContractionJacquet : IwahoriContractionJacquetStatement` | Proof `840880fa-3c5d-49d8-85ab-919048b0a80a`; commit `405ff58c5df69766419c9941161444531c1979ae`; Reviewer 9941 | Five conditional clauses concerning compression, generalized kernel, stable image, and unnormalized and normalized admissibility. An actual `HasIwahoriContractionBasis` and the source's sufficiently-contracting operator/kernel/image and canonical-section independence comparisons remain. It does not close general finite length. |
| `Langlands.SmoothRep.RationalPointsFinitelyGeneratedAdmissibleFiniteLengthStatement` | Statement `dd7122a6-5978-4011-b1cf-2536d55e27d7`; commit `405ff58c5df69766419c9941161444531c1979ae`; Reviewer 10001 | The actual canonical rational-point target says finite group-algebra generation plus admissibility imply finite length, with independent field/carrier universes. This is a public statement, not an accepted proof of the implication. No final exact Howe proof is adopted here. |
| `R.rationalCuspidalEigenvalue : R.RationalCuspidalEigenvalueStatement` | Proof `29a2b3a7-87bd-4b7c-9822-644f7965b428`; commit `6820dc99b5972ed5761be21b4ac8afeba7584644`; Reviewer 10098 | Exact full simple-root-cardinality sign, including empty roots, at independent `u/v` scope. The actual standard, topological, root, compact-limit and separate `hiFl`/`hrFl` premises are retained. The no-classification verdict above applies to this proof route under these premises. |

## Family 3: corrected actual complex and terminal comparison

The source is Aubert 1995, pp.2186–2187, corrected by the erratum,
pp.4687–4690, and the two-sided filtration and actual-map repair in
Ban–Jantzen §4, pp.160–162. The
[complex source map](smooth-complex-construction-source-map.md) and
[support/filtration source map](support-filtration-consequences-source-map.md)
explain the source correspondence.

| Current declarations | Structure and topology retained | Representation, corrected filtration and proof status |
| --- | --- | --- |
| `rationalDegreeObject`, `rationalDifferential`, `rationalBoundary`, `rationalInitialMap`, `rationalInitialEquiv`, `rationalInitialDifferential`, `rationalTerminalProjection`, `rationalSharpObject`, `rationalSharpFunctor` | Actual standard family; order/endpoint hypotheses where required by the construction and initial comparison; canonical topology and the displayed subgroup premises | Actual quotient-induced maps, orientation signs, differential, initial identification and terminal cokernel in [RationalStandardComplex](../../Langlands/Representation/Aubert/General/RationalStandardComplex.lean). Intrinsic laws in [RationalCorrectedTheorem36](../../Langlands/Representation/Aubert/General/RationalCorrectedTheorem36.lean) include `rationalTerminalProjection_surjective` and `rationalTerminalProjection_ker`. These constructions impose no finite-length premise and do not prove corrected exactness. |
| `RationalCorrectedTheorem36Statement` | Standard cocharacter, order, endpoint and Levi-intersection statements; actual roots, point normalizer/centralizer comparisons; closed `U/M`, compact-limit `U` and canonical point topology | [Full-smooth target](../../Langlands/Representation/Aubert/General/RationalCorrectedTheorem36.lean), exact below degree `|S|-|I|` for every object of the actual support category. No finite-length or admissibility premise is added. No exact proof adopted; transitive classification use and version undetermined. |
| `RationalCorrectedGradedVanishingStatement`, `RationalCorrectedGradedTransitionStatement` | Actual finite `N/Z` Coxeter group, root-length, simple-reflection and Levi-Weyl comparisons. Vanishing omits order and compact-limit premises; transition retains them. Neither target uses endpoints. | [Graded targets](../../Langlands/Representation/Aubert/General/RationalCorrectedFiltrationTargets.lean). Two-sided support `θ^{J,I} = {x ∈ θ : W_J x W_I ⊆ θ}`; minimality from the length filtration; remaining lengths at least the removed length; consecutive modified supports; actual grade maps equal identity up to exterior signs. No exact proofs adopted. |
| `RationalJacquetCuspidalStatement`, `RationalFixedLeviComparisonStatement`, `RationalAssociatedLeviComparisonStatement` | The displayed actual standard/Levi/topology premises; separate compact-limit premises for restricted radicals. The associated comparison retains `actualAssociatedLeviConjugation` and root/Coxeter laws. | [Terminal targets](../../Langlands/Representation/Aubert/General/RationalTerminalJacquet.lean) at full smooth scope, using actual natural isomorphisms. No final comparison proof adopted; transitive classification use and version undetermined. |

The nine supporting targets in
[RationalSupportCategoryTargets](../../Langlands/Representation/Aubert/General/RationalSupportCategoryTargets.lean)
are `RationalCuspidalSeriesExistenceStatement`,
`RationalCuspidalSupportAssociationStatement`,
`RationalSupportCategoryAssociationInvarianceStatement`,
`RationalSupportCategoryIrreducibleJacquetDetectionStatement`,
`RationalSupportCategoryZeroDetectionStatement`,
`RationalSupportCategoryExactnessDetectionStatement`,
`RationalSupportCategoryInductionJacquetStatement`,
`RationalSupportCategoryJacquetVanishingStatement` and
`RationalSupportCategoryDecompositionStatement`.
They retain standard/intersection/root and closed-`U/M` premises, without
order, endpoint or compact-limit premises. All but series existence retain
the point normalizer and centralizer comparisons. Their publication does not
establish support existence, association, detection or full-smooth exactness.

The terminal cokernel `E#` survives. There is no final zero requiring its
vanishing. Proposition 3.2 remains unresolved; neither its failed proof nor
the original application establishes any row of this matrix.

## Family 4: finite length, irreducibility and actual involution

The source is Corollary 3.9, printed p.2189, with the corrected complex and
erratum p.4690. All six current targets are in
[RationalSharpConsequenceTargets](../../Langlands/Representation/Aubert/General/RationalSharpConsequenceTargets.lean).
They retain standard cocharacter, order, actual roots, closed `U` and
compact-limit `U` premises on canonical rational points.

| Exact main target | Additional visible premises and required conclusion | Proof and classification status |
| --- | --- | --- |
| `RationalSharpFiniteLengthStatement` | No Levi-intersection, closed-`M`, point normalizer/centralizer or endpoint premises in this target. Finite-length input must yield finite-length actual `E#`. | No exact proof adopted; transitive classification use and version undetermined. |
| `RationalSharpClassFormulaStatement` | Levi intersection, closed `M` and point normalizer/centralizer comparisons; quantified `hfl` and finite length of both `E` and `E#`. Prove the exact-class formula `D[E] = (-1)^|I| [E#]`. | No exact proof adopted; transitive classification use and version undetermined. |
| `RationalSharpSupportRetentionStatement` | Levi intersection, closed `M` and point normalizer/centralizer comparisons. Retain the actual support category. | No exact proof adopted; transitive classification use and version undetermined. |
| `RationalSharpIrreducibleStatement` | Levi intersection and closed `M`; no point normalizer/centralizer or endpoint premise. Prove actual irreducibility, including nonzero, of the terminal module. | No exact proof adopted; transitive classification use and version undetermined. |
| `RationalSharpCuspidalSeriesStatement` | Levi intersection, closed `M` and point normalizer/centralizer comparisons. Retain the actual cuspidal series. | No exact proof adopted; transitive classification use and version undetermined. |
| `RationalSharpInvolutionStatement` | Levi intersection and closed `M`; no point normalizer/centralizer or endpoint premise. Obtain an actual isomorphism `(E#)# ≅ E` for irreducibles. | No exact proof adopted; transitive classification use and version undetermined. |

Corrected exactness, termwise exactness, length/Euler arguments, support and
nonvanishing must be supplied where used. Equality of arbitrary exact-K0
classes does not imply isomorphism of modules.

## Family 5: actual GL specialization and the whole graded ring

The source is Aubert 1995, Definition 2.1, Remark 2.2 and Theorem 2.3,
printed pp.2184–2185. The
[GL target map](gl-specialization-source-map.md),
[general-specialization addendum](gl-general-specialization.md) and
[point-topology comparison](gl-algebraic-point-specialization.md) give the
separate model and dependency boundaries.

| Current declarations | Model, representation and formal ingredients retained | Proof and classification status |
| --- | --- | --- |
| `Langlands.GeneralLinear.BlockShape.generalInductionIso`, `generalJacquetIso`; `Langlands.Parabolic.generalInductionK0_eq`, `generalJacquetK0_eq`, `generalInductionJacquetK0_eq`; `A.generalAlternatingOperator_eq` | Actual upper-parabolic/right-translation models and quotient Levi; positive induction and inverse Jacquet half-moduli. `GeneralModulusCompatibility` / `GeneralLinearModulusCompatibility` compare the full parabolic modulus, not only its Levi restriction. | Conditional actual functor, K0 and operator comparisons in [GeneralLinearSpecialization](../../Langlands/Representation/Aubert/GeneralLinearSpecialization.lean). Current exact-K0 preservation is for `PadicField`; the more general topological-ring functor comparisons do not prove preservation for arbitrary local fields. D07 and the actual rational-point specialization remain closure obligations. Transitive classification use of the completed specialization is undetermined. |
| `A.gradedAdjustedOperator`, `gradedAdjustedOperator_unit` | Actual homogeneous support-sign adjustment and degree-zero unit | Constructed operator and intrinsic unit law in [ZelevinskyComparison](../../Langlands/Representation/Aubert/ZelevinskyComparison.lean), not a whole-ring comparison proof. |
| `A.AdjustedHomogeneousMultiplicativityStatement`, `AdjustedMultiplicativityStatement`, `AdjustedSegmentExchangeStatement`, `AdjustedInvolutivityStatement` | Actual graded induction product, binary exactness and ring laws; support-sign compatibility and actual segment constituents | Same [target file](../../Langlands/Representation/Aubert/ZelevinskyComparison.lean). No final exact proofs adopted; transitive classification use and versions undetermined. |
| `A.SegmentPolynomialComparisonStatement`, `SegmentMonomialSpanningStatement`, `SegmentMonomialBasisStatement`, `ZelevinskyInvolutivityStatement` | Actual polynomial/segment comparison and monomial spanning or basis for the entire graded exact Grothendieck ring | [ZelevinskyPolynomial](../../Langlands/Representation/Aubert/ZelevinskyPolynomial.lean). Conditional constructors do not discharge these targets. No final exact proofs adopted; classification declarations and versions must be recorded in their actual proofs. |
| `A.AubertZelevinskyComparisonStatement`, `AubertZelevinskyRingComparisonStatement`, `AubertZelevinskyInvolutionComparisonStatement`, `AubertTheorem23Statement` | Whole graded additive/ring agreement, actual multiplication and involution, polynomial/monomial comparison, and the support-sign adjustment | [Final targets](../../Langlands/Representation/Aubert/ZelevinskyComparison.lean). No final exact proofs adopted; transitive classification use and versions undetermined. A segment-generator calculation does not establish these conclusions. |

The existing `A.segmentSocleHead` theorem gives the supplied-constituent
segment formula with the unadjusted sign `(-1)^(n-k)`. Its hypotheses and
scope must be retained. Known GL helper roots include
`normalizedInductionFiniteLength`, `cuspidalEmbedding` and
`cuspidalInductionLength`; a declaration audit must identify the exact
versions actually reached by a final proof, rather than infer a classification
verdict from their module locations. The algebraic
`Langlands.Group.GL.AlgebraicPointTopology` bridge is separate from
`GeneralLinearSpecialization` and is not automatically combined with it.
The degree-zero GL convention and unit remain part of the whole-ring claim.

## Classification accounting and remaining assembly

This program permits Langlands and Zelevinsky classification. An upstream
consumer decides separately whether a published proof satisfies its own route
constraints. A final audit must traverse both declaration types and proof
values, identify any classification theorem by its exact Lean name and
version, and retain every premise still used. Importing a module with
“Classification” in its name does not by itself demonstrate use of its
classification theorem; omitting that word from a target demonstrates
no independence.

The bounded no-classification verdict recorded here is the reviewed
`R.rationalCuspidalEigenvalue` route under its visible premises. For the other
main results the final transitive verdict is undetermined in this matrix:
there is no adopted complete proof and premise-discharge chain from which to
give an exact classification version. Partial GL import and declaration
inventories are not a completed semantic verdict.

All five families remain open overall. The remaining assembly must discharge
the representation premises, map only actually consumed external structural
inputs to S01–S23, prove the retained D rows, establish the actual corrected
grade maps and terminal comparisons, and complete the general-to-GL and
whole-ring comparisons. Exact proof successors remain with their existing
owners; supporting helper publications do not silently close their parent
targets.

Worker 76 assembled this matrix. It reuses Worker 164's structural boundary,
Worker 320's correction guidance, Workers 165/1186's rational formal-target
map, Workers 194/379's corrected-complex and support accounts, and
Workers 585/34's GL construction and dependency accounts. These attributions
do not enlarge any original-source reading record or supply proof acceptance.
