# Renard V.3 and VII.1–VII.2: actual roots, exponents and normalization

This focused map, updated on 5 November 2026 with the published proof
explanation, supplements the
[whole-book ledger](coverage.md) and the
[Chapter V structural-input ledger](chapter-v-structural-inputs.md).
It records twenty-one pairs of the Library and the further steps to the
all-parabolic temperedness criterion and its VII.1–VII.2 consequences. It is not a complete inventory of
V.3, VII.1 or VII.2, and supplies no new Lean proof.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
PDF page numbers below are one-based and equal printed page numbers plus six.
The source passages and the current Lean/Markdown pairs were read for the
claims below. All thirty-two selected mathematical files match the files
of the commits where they first appeared and the files at Library
`a9f12d1e4a0823c676b8a7b9292f17ea7c1d08ee`. The five later pairs listed last
in the table below were checked at Library
`b21e71ce008bc85afd0463fb58fb171b22a6e62a`. Eight of their files equal the
files as first checked. The Levi-points pair was edited when it entered the
Library: its
two local closed-subgroup helpers were replaced by the imported
`GroupScheme.IsClosedSubgroup.comp` and
`GroupScheme.IsClosedSubgroup.isRepresentedBy_range`, so its Library files
(`667bf851…`, `49505cdf…`), already so at Library commit
`1831431f93603e52c73600a2a900dd42d7f18deb`, differ from the files first
checked (`c51e1703…`, `cb40990e…`).

## Selected source assertions and exact interfaces

| Passage, printed / PDF page | Published interface and retained obligation |
| --- | --- |
| V.3.4, 110 / 116: nonzero ambient Lie roots, radical roots and reduction by divisibility within the actual root set | `Langlands.GroupScheme.RenardRootConventionStatement` compares actual dynamic-radical Lie weights with positive relative roots and their indivisible parts. This is a published **statement**, proved as `renardRootConvention` (`Langlands/GroupScheme/Rational/RenardRootConventionProof.lean`). Divisibility is not primitivity in the entire character lattice. |
| V.3.12, 112 / 118: the simple system of the reduced positive roots of a minimal parabolic | The same statement compares indecomposables in the reduced positive set with `simpleRelativeRoots`, whose definition uses all positive relative roots. It does not identify all indivisible positive roots with simple roots. Bases, fundamental weights, coroots and central decompositions retain separate obligations. |
| V.3.14, 113 / 119: choose a contained minimal parabolic whose maximal split torus contains the specified Levi split component; restrict the simple roots outside the Levi index | `ParabolicRootPresentationData.IsCompatible` and `ParabolicRootPresentation p l a` record actual choices for specified maps. `pres.restrictedRoots` is the existing restricted-simple-root set. This construction does not prove existence or independence of those choices. |
| First two V.3.15 displays, 113 / 119: positive and nonnegative sums over the restricted roots | `pres.positiveCone` and `pres.nonnegCone` instantiate the existing finite-sum constructions in the full real character space. Membership, empty-index and elementary cone laws are implemented. The subsequent coroot-inequality chambers are different sets and are not substituted here. |
| V.3.19–V.3.20, 115–116 / 121–122, combined with VII.2.1, 227 / 233: real parameters and the exponent-cone test | The published theorem `normalizedTemperedLogarithmicComparison` proves the corrected all-point formula with factor `-log q`, the equivalent negative-raw cone test, and the complete predicate comparison. It preserves every compatible-presentation quantifier and does not prove presentation existence. |
| V.3.20, 116 / 122: complex exponential, periods, lifts and unitary image | The published theorem `Langlands.Plancherel.rationalComplexParameter` proves the eight algebraic actual-image and canonical-point assertions: surjectivity, period kernel and difference criterion, normalized real part of every lift, unitarity and imaginary image, and the two canonical-point transfers. The separately published `rationalComplexParameterQuotient` proves the two complex open quotient maps and their prescribed-value quotient homeomorphisms. |
| V.3.20, 116 / 122: period lattice and compact imaginary quotient | The published theorem `Langlands.Plancherel.rationalImaginaryParameterQuotient` proves discreteness and closedness of the original and restricted periods, compactness of the imaginary quotient, and the two imaginary open quotient maps and prescribed-value quotient homeomorphisms on the actual image and canonical rational points. The source's tensor, algebraic-torus and real-submanifold identifications remain separate. |
| V.3.20, 116 / 122: rational-character tensors and the pure-tensor absolute-value formula | The published construction `Langlands.Plancherel.rationalCharacterTensorParameter` extends actual integer evaluation to a complex-linear map. For affine groups locally of finite type, its composition with the existing canonical exponential satisfies `rationalCanonicalCharacterTensorExponential_tmul_val`, the formula \(e^{s\otimes\chi}(g)=\lvert\chi(g)\rvert_F^s\) on every actual rational point. The split-center comparison remains separate. |
| V.3.19–V.3.20, 115–116 / 121–122: the equal-rank lattices and \(\mathfrak a^*_{\mathbb C}=\operatorname{Hom}_{\mathbb Z}(\Lambda(M),\mathbb C)\), written \(X^*(M)\otimes_{\mathbb Z}\mathbb C\) on printed p.116 | The published `Langlands.Plancherel.RationalCharacterTensorParameterStatement` asserts bijectivity of `rationalCharacterTensorParameter G` for every actual connected reductive `G` over every nonarchimedean local field, taking the Levi to be the group itself. This is a published **statement**, proved as `rationalCharacterTensorParameterBijective` (`Langlands/Representation/Plancherel/RationalCharacterTensorParameterProof.lean`). |
| VI.1.2, 135–136 / 141–142: normalized Jacquet quotient and the inverse modular-function convention | `Langlands.Aubert.General.RepresentedParabolic.jacquetFunctor` uses the actual coinvariant quotient and inverse-half Haar twist on literal point images. Its split-component action formula makes the factor explicit. This focused construction does not establish the section's exactness, adjunction or preservation assertions. |
| VII.1.1, 220 / 226: compact-open characteristic spaces, normalized exponents and their set | `normalizedJacquetWeightSpace`, `IsNormalizedJacquetExponent` and `normalizedJacquetExponents` apply the published weight-space machinery to the actual quotient. Membership uses one power uniform over all torus points. Definitions and intrinsic laws extend to smooth inputs; the direct-sum, admissibility and finite-length conclusions are separate. |
| VII.1.1, 220–221 / 226–227: (VII.1.1.1), finiteness of exponents in finite length, the case `P = G`, and Lemma (i)–(ii) comparing exponents of `W`, `i_P^G W`, `V` and `r_P^G V` | The published `ArbitraryParabolicInduction` proves the point-image semidirect decomposition and defines `inductionFunctor`, `leviWeightSpace`, `IsLeviExponent`, `groupWeightSpace`, `IsGroupExponent` and `groupExponents`. The published **statement** `ArbitraryParabolicExponentStatement` asserts the direct sum for admissible `π`, finiteness in finite length, the `P = G` decomposition, and (i)–(ii) for every point homomorphism `A_G(F) → A_M(F)` compatible with the two inclusions. The Library proves it, as `arbitraryParabolicExponent` (`Langlands/Representation/Exponents/ArbitraryParabolicExponentProof.lean`). |
| VII.1.2, 221–224 / 227–230: Casselman's criterion | The published **statement** `ArbitraryParabolicCasselmanCriterionStatement` asserts, for admissible `π` with a unitary central character and every Haar measure on `G(F) ⧸ Z(G(F))`, square-integrability modulo the center if and only if every normalized exponent at every actual parabolic has `q^(-s)` real part in `pres.positiveCone` for every compatible presentation. Its Markdown explains why the strictly positive root cone of the proof replaces the printed coroot chamber, and why Renard's `δ_P` is the inverse of the Library's modulus. The Library does not prove it. |
| VII.2.1, Remark 2, 227 / 233: square-integrable modulo the center implies tempered | The published **statement** `SquareIntegrableNormalizedTemperedStatement` concludes `IsNormalizedExponentTempered` from the published square-integrability predicate. Irreducibility is omitted because it serves only to supply admissibility, which that predicate contains. The Library proves it, as `squareIntegrableNormalizedTempered` (`Langlands/Representation/Exponents/SquareIntegrableNormalizedTemperedProof.lean`). |
| VI.1.2 and VII.2.2–VII.2.6, 135–136 / 141–142 and 227–231 / 233–237: induction and restriction between representations of `M` and `G` | The published `ArbitraryParabolicLeviPoints` constructs `leviPointsEquiv : M(F) ≃ₜ* pointImage (l ≫ p)` for the canonical topology on `M(F)`, derives local compactness and the nonarchimedean property of `M(F)`, and defines `leviInductionFunctor` and `leviJacquetFunctor` on representations of `M(F)`. It makes the published temperedness predicate for `M` applicable to Levi representations. It proves no representation-theoretic assertion. |
| VII.2.1, 227 / 233: admissibility and the nonnegative root-cone condition for every exponent at every parabolic | The published derived `IsNormalizedExponentTempered` combines admissibility with the actual all-parabolic, all-presentation condition. Its explicitly normalized parameter retains the corrected-source comparison described below; this construction does not complete original source-definition coverage. |
| VII.2.1, Remark 1, first assertion, 227 / 233: full-group exponents are unitary, equivalently have zero real part | The published theorem `normalizedTemperedFullGroupExponent` proves `NormalizedTemperedFullGroupExponentStatement` for the identity parabolic and identity Levi. Centrality of the supplied split component makes the actual root-combination cone `{0}`, giving zero normalized real part and norm one at every split-component point. The full-center consequence is separate. |
| VII.2.1, Remark 1, second assertion, 227 / 233: a scalar central character is unitary | The published corrected derived `NormalizedTemperedCentralCharacterStatement` concludes norm one on the full point-group center for every prescribed scalar central character of a nonzero normalized-exponent tempered representation. Nonzeroness repairs the source's zero-representation obstruction; the Library proves it, as `normalizedTemperedCentralCharacter` (`Langlands/Representation/Exponents/NormalizedTemperedCentralCharacterProof.lean`). |
| VII.2.1, Remark 3, 227 / 233: reduction to standard parabolics | The published `NormalizedTemperedStandardReductionStatement` fixes one actual maximal split torus and generic cocharacter defining a minimal dynamic parabolic. It states an equivalence with admissibility and the exponent-cone tests on the corresponding actual standard family. The Library proves it, as `normalizedTemperedStandardReduction` (`Langlands/Representation/Exponents/NormalizedTemperedStandardReductionProof.lean`). |

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
universe. Finite-dimensional carriers are not required. The all-parabolic
predicate, full-group exponent statement and standard-reduction statement
require no scalar central character. The central-character consequence
additionally quantifies a prescribed scalar character and requires a nonzero
representation.

## In the Library

The twenty-one pairs are six definitions, ten statements and five exact
proofs. A definition covers its construction and intrinsic laws; a statement
does not prove its proposition. For each statement the last column gives the
proof the Library has now.

| Pair and exact declaration | Kind | First appeared at Library commit | Proof in the Library |
| --- | --- | --- | --- |
| [ArbitraryParabolic](../../Langlands/Representation/Exponents/ArbitraryParabolic.md), `Langlands.Aubert.General.RepresentedParabolic.IsNormalizedJacquetExponent` | definition | `7596502b4fe9738072198e7f23076fa02293f254` | — |
| [ParabolicRootPresentation](../../Langlands/GroupScheme/Rational/ParabolicRootPresentation.md), `Langlands.GroupScheme.ParabolicRootPresentation.nonnegCone` | definition | `6d810cf8b71c5da9cf2722e850d66305665461f5` | — |
| [RenardRootConventionStatement](../../Langlands/GroupScheme/Rational/RenardRootConventionStatement.md), `Langlands.GroupScheme.RenardRootConventionStatement` | statement | `6d810cf8b71c5da9cf2722e850d66305665461f5` | `renardRootConvention` (`Langlands/GroupScheme/Rational/RenardRootConventionProof.lean`) |
| [ParabolicRootPresentationStatement](../../Langlands/GroupScheme/Rational/ParabolicRootPresentationStatement.md), `Langlands.GroupScheme.ParabolicRootPresentationStatement` | statement | `fd5d309e44e7f2f66516fa1781a0112c4e3a56ac` | `parabolicRootPresentation` (`Langlands/GroupScheme/Rational/ParabolicRootPresentationProof.lean`) |
| [ArbitraryParabolicTempered](../../Langlands/Representation/Exponents/ArbitraryParabolicTempered.md), `Langlands.Aubert.General.RepresentedParabolic.IsNormalizedExponentTempered` | definition | `fd5d309e44e7f2f66516fa1781a0112c4e3a56ac` | — |
| [NormalizedTemperedFullGroupStatement](../../Langlands/Representation/Exponents/NormalizedTemperedFullGroupStatement.md), `Langlands.Aubert.General.RepresentedParabolic.NormalizedTemperedFullGroupExponentStatement` | statement | `cf220a229d7dcb607b8e9ff31488860fb7037d7c` | `normalizedTemperedFullGroupExponent` (`Langlands/Representation/Exponents/NormalizedTemperedFullGroupProof.lean`) |
| [NormalizedTemperedStandardReductionStatement](../../Langlands/Representation/Exponents/NormalizedTemperedStandardReductionStatement.md), `Langlands.Aubert.General.RepresentedParabolic.NormalizedTemperedStandardReductionStatement` | statement | `cf220a229d7dcb607b8e9ff31488860fb7037d7c` | `normalizedTemperedStandardReduction` (`Langlands/Representation/Exponents/NormalizedTemperedStandardReductionProof.lean`) |
| [NormalizedTemperedCentralCharacterStatement](../../Langlands/Representation/Exponents/NormalizedTemperedCentralCharacterStatement.md), `Langlands.Aubert.General.RepresentedParabolic.NormalizedTemperedCentralCharacterStatement` | statement | `c41b568e7835014dced08e75cc4af6f669955f5d` | `normalizedTemperedCentralCharacter` (`Langlands/Representation/Exponents/NormalizedTemperedCentralCharacterProof.lean`) |
| [NormalizedTemperedLogarithmicComparisonStatement](../../Langlands/Representation/Exponents/NormalizedTemperedLogarithmicComparisonStatement.md), `Langlands.Aubert.General.RepresentedParabolic.NormalizedTemperedLogarithmicComparisonStatement` | statement | `687ec597518e5ed344da1618d8a37af0df359b54` | `normalizedTemperedLogarithmicComparison` (`Langlands/Representation/Exponents/NormalizedTemperedLogarithmicComparison.lean`) |
| [NormalizedTemperedFullGroupProof](../../Langlands/Representation/Exponents/NormalizedTemperedFullGroupProof.md), `Langlands.Aubert.General.RepresentedParabolic.normalizedTemperedFullGroupExponent` | proof | `50c05a5877c13ea23a52ea298c0ec2bd6fdb0817` | — |
| [NormalizedTemperedLogarithmicComparison](../../Langlands/Representation/Exponents/NormalizedTemperedLogarithmicComparison.md), `Langlands.Aubert.General.RepresentedParabolic.normalizedTemperedLogarithmicComparison` | proof | `50c05a5877c13ea23a52ea298c0ec2bd6fdb0817` | — |
| [RationalComplexParameter](../../Langlands/Representation/Plancherel/RationalComplexParameter.md), `Langlands.Plancherel.rationalComplexParameter` | proof | `50c05a5877c13ea23a52ea298c0ec2bd6fdb0817` | — |
| [RationalComplexParameterQuotient](../../Langlands/Representation/Plancherel/RationalComplexParameterQuotient.md), `Langlands.Plancherel.rationalComplexParameterQuotient` | proof | `4dd5f7c45ce9b800a0caffa94e2e790953bf7c96` | — |
| [RationalCharacterTensorParameter](../../Langlands/Representation/Plancherel/RationalCharacterTensorParameter.md), `Langlands.Plancherel.rationalCharacterTensorParameter` | definition | `a4a5fb7b2643f2b9b9a6ac9c41bde7cc387d4a1a` | — |
| [RationalImaginaryParameterQuotient](../../Langlands/Representation/Plancherel/RationalImaginaryParameterQuotient.md), `Langlands.Plancherel.rationalImaginaryParameterQuotient` | proof | `476a152fd90d846bcb20b9897f53829a768b822c` | — |
| [RationalCharacterTensorParameterStatement](../../Langlands/Representation/Plancherel/RationalCharacterTensorParameterStatement.md), `Langlands.Plancherel.RationalCharacterTensorParameterStatement` | statement | `409542525904dd50036abafdafb8ad1459eadade` | `rationalCharacterTensorParameterBijective` (`Langlands/Representation/Plancherel/RationalCharacterTensorParameterProof.lean`) |
| [ArbitraryParabolicInduction](../../Langlands/Representation/Exponents/ArbitraryParabolicInduction.md), `Langlands.Aubert.General.RepresentedParabolic.inductionFunctor` | definition | `0bd5bf67c3464359bc8da3b3100163d6ee3da352` | — |
| [ArbitraryParabolicExponentStatement](../../Langlands/Representation/Exponents/ArbitraryParabolicExponentStatement.md), `Langlands.Aubert.General.RepresentedParabolic.ArbitraryParabolicExponentStatement` | statement | `910675f18ad6c3d8b09c12c678a0243795a673b9` | `arbitraryParabolicExponent` (`Langlands/Representation/Exponents/ArbitraryParabolicExponentProof.lean`) |
| [ArbitraryParabolicCasselmanStatement](../../Langlands/Representation/Exponents/ArbitraryParabolicCasselmanStatement.md), `Langlands.Aubert.General.RepresentedParabolic.ArbitraryParabolicCasselmanCriterionStatement` | statement | `1831431f93603e52c73600a2a900dd42d7f18deb` | not proved |
| [SquareIntegrableNormalizedTemperedStatement](../../Langlands/Representation/Exponents/SquareIntegrableNormalizedTemperedStatement.md), `Langlands.Aubert.General.RepresentedParabolic.SquareIntegrableNormalizedTemperedStatement` | statement | `1831431f93603e52c73600a2a900dd42d7f18deb` | `squareIntegrableNormalizedTempered` (`Langlands/Representation/Exponents/SquareIntegrableNormalizedTemperedProof.lean`) |
| [ArbitraryParabolicLeviPoints](../../Langlands/Representation/Exponents/ArbitraryParabolicLeviPoints.md), `Langlands.Aubert.General.RepresentedParabolic.leviPointsEquiv` | definition | `1831431f93603e52c73600a2a900dd42d7f18deb` | — |

The logarithmic, algebraic complex-parameter, complex-quotient and
imaginary-quotient proofs were each checked by a Lake build against the
exact target, with the statement and its inputs unchanged. The
imaginary-quotient companion explanation is reused below.

The arbitrary-parabolic wrapper imports the existing generic and
standard-family weight machinery unchanged. For the full-group proof, the
argument below follows its published Lean implementation and companion
Markdown.

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
by the published derived definition; they do not identify membership of the two
parameters in the same nonnegative root cone.

The published
`Langlands.Aubert.General.RepresentedParabolic.NormalizedTemperedLogarithmicComparisonStatement`
now states the corresponding corrected-source comparison. For every actual
normalized exponent and compatible presentation, normalized cone membership
is equivalent to existence of a parameter in that same cone satisfying
`log norm = (-log q) * pair` at every actual split-torus point. It is also
equivalent to membership of the **negative** raw parameter in that cone,
since negative raw is the positive scalar `log q` times normalized.
The complete predicate equivalence preserves admissibility, every actual
parabolic/Levi/split-component triple, nonempty compatible presentations,
and every presentation, matching represented radical/decomposition and
exponent. It does not establish the required presentation existence.

The Library proves this comparison, as
`normalizedTemperedLogarithmicComparison` in the table above.
The proof uses the exponent's open kernel, the all-point raw pairing formula,
valuation-image uniqueness after cancellation of nonzero `-log q`,
and cone scaling by `log q` and its inverse. It then transfers the local
equivalence under all unchanged predicate quantifiers, retaining admissibility
and the nonempty-presentation conjuncts.

The separate published `rationalComplexParameter` proves the algebraic
exponential assertions on the actual rational valuation image
`Lambda = Additive (rationalDiscreteValuationImage G)`, and transfers
surjectivity and equality modulo periods to canonical rational points.
For `L = log q` and `c = 2*pi*i/L`, the scalar kernel calculation uses
`Complex.exp_eq_one_iff`; injectivity of `n ↦ c*n` assembles the pointwise
integers into an additive map `Lambda →+ ℤ`. This identifies the kernel
with the actual range of `rationalImagePeriodEmbedding`, and the division
law gives equality of exponentials precisely when their difference lies
in that period subgroup. Surjectivity uses the published basis-value lift.
The normalized real-part law holds for every lift, and pointwise imaginary
parts reconstruct a lift of every unitary character. The canonical continuous
character equivalence supplies the two actual-point transfers.

The published `rationalComplexParameterQuotient` proves the four-clause
`RationalComplexParameterQuotientStatement`. It makes the actual exponential
an open quotient map, both on the valuation image and on canonical rational
points, and identifies `V/P` with each existing character space. Here
`V = Hom_Z(Lambda,C)` has its pointwise topology and
`P = (2*pi*i/log q) Hom_Z(Lambda,Z)` is the original period subgroup.
The quotient has its standard group quotient topology; both character spaces
retain their existing compact-open topologies. Each homeomorphism sends every
projected parameter to its prescribed exponential value.

The implemented proof first proves openness and surjectivity of
`z ↦ exp(-z*log q)` into complex units. Finite coordinates evaluating the
same actual integer basis on parameters and characters identify the actual
exponential with a product of these scalar maps. The imported algebraic
period-difference criterion makes the quotient descent well-defined and
bijective. Quotient continuity and openness give the prescribed
homeomorphism. The existing canonical image-to-unramified character
homeomorphism transfers the two conclusions to rational points.
These explicit topological assertions are derived formulations of V.3.20.

The published `rationalImaginaryParameterQuotient` proves all nine clauses
of `RationalImaginaryParameterQuotientStatement`. Write
`I` for the actual zero-real-part subgroup of `V`, and `P_I` for the
inverse image of the original periods `P` under `I → V`. The conclusions
are discreteness and closedness of `P`, discreteness and closedness of
`P_I`, compactness of `I/P_I`, and an open quotient map and a
prescribed-value quotient homeomorphism for each of the actual-image
unitary characters and the canonical-point unitary unramified characters.
Both homeomorphisms send every projected parameter to its actual exponential.
The parameter topology remains pointwise, the subgroup topologies are
inherited, the quotient topology is the standard additive-group quotient
topology, and the character topologies remain compact-open.

The implemented proof maps a finite integer tuple to the complex parameter
whose values on the actual image basis are its period-scaled entries.
Integer inclusion in the complex numbers is a closed embedding;
multiplication by the nonzero period and the existing finite-coordinate
homeomorphism preserve that property. Extension and restriction on the
same integer basis identify its range with the original period subgroup.
The range is therefore closed and discrete. The inclusion of the restricted
periods into the original periods is an embedding for their inherited
subgroup topologies, so it transfers discreteness; continuous preimage
transfers closedness.

The proved unitary-preimage criterion identifies `I` with the preimage of
the unitary-character subgroup under the complex exponential.
`IsOpenQuotientMap.restrictPreimage` then restricts the published complex
open quotient map to the actual imaginary exponential. The exact complex
period-fiber criterion descends to the restricted periods and makes the
quotient lift bijective. Quotient continuity and openness give the
homeomorphism with its prescribed value on every representative.
Compactness transfers from the existing compact unitary character group.
The canonical image-to-unramified character homeomorphism transports the
open quotient map and quotient homeomorphism to rational points.
Closedness, the open quotient maps and these commuting homeomorphisms are
explicit derived topological conclusions of V.3.20.

All three parameter theorems retain arbitrary connected reductive groups
and general nonarchimedean local fields, without an added finite-rank,
split or characteristic-zero premise. The character/split-center tensor
comparisons, algebraic-torus and real-submanifold structures, and the
remaining original source-definition coverage are separate obligations.

The separately published tensor construction uses the shared
`GroupScheme.rationalCharacters G` and actual integer valuation image. It
evaluates a character at an image element and includes that integer in
complex numbers, then uses `AlgebraTensorModule.lift` to obtain
`rationalCharacterTensorParameter`. Thus
\((s\otimes\chi)(a)=s\,a(\chi)\). Composing with the existing exponential
gives \(\exp(-s\,a(\chi)\log q)\).

On canonical rational points,
`rationalCanonicalCharacterTensorExponential_tmul_val` proves the source's
pure-tensor absolute-value formula. The proof writes the positive
residue-normalized absolute value as \(q^{-v_F(\chi(g))}\), takes its real
logarithm, identifies the complex logarithm of that positive real number
and rewrites complex power. The construction works for any actual group
scheme over the given local field; its canonical-point formula adds only
affineness and local finite type. It assumes no reductivity, splitting,
characteristic-zero or rank condition. Mathlib's scalar-first tensor
convention is related to the source's character-first notation by tensor
commutation.

The construction and its intrinsic laws do not prove that the canonical
linear map is bijective. Finite freeness of the actual valuation image
alone supplies no rank comparison with the rational-character group.

The separately published `RationalCharacterTensorParameterStatement`
states that identification. It quantifies over every field universe,
every nonarchimedean local field with its field, valuation and topology
instances, and every actual connected reductive group scheme over it. Its
conclusion is bijectivity of the existing `rationalCharacterTensorParameter G`
from `ℂ ⊗[ℤ] GroupScheme.rationalCharacters G` to the existing
`rationalImageComplexFunctionals G`, the additive complex functionals on
the actual `rationalDiscreteValuationImage G`. It chooses no replacement
lattice, pairing or map, and adds no splitting, rank-equality,
character-restriction, supplied-bijectivity or characteristic-zero premise.
The Markdown paired with the statement relates it to V.3.19's equal-rank
lattices and V.3.20's two descriptions of \(\mathfrak a^*_{\mathbb C}\), taking the
group itself as the Levi.

The Library proves this proposition, as
`rationalCharacterTensorParameterBijective` (`Langlands/Representation/Plancherel/RationalCharacterTensorParameterProof.lean`).
The split-center comparison,
algebraic-torus representability and manifold structure are separate
results; this note records no proof of them.
The coroot-pairing positivity used for the Langlands-classification parameters
of VII.4 also retains its own construction and comparison obligations.

## Published normalized formulation and remaining proof gates

The published aggregate
`Langlands.GroupScheme.ParabolicRootPresentationStatement`
asserts existence for every specified actual `p,l,a`, independence of
restricted roots and both cones across arbitrary compatible presentations,
and both-direction pullback transport under compatible component isomorphisms.
All presentation fields may vary in its comparisons. The Library proves
this proposition, as `parabolicRootPresentation` (`Langlands/GroupScheme/Rational/ParabolicRootPresentationProof.lean`).

The published
`Langlands.Aubert.General.RepresentedParabolic.IsNormalizedExponentTempered`
requires admissibility and the normalized exponent condition for every
specified actual parabolic, rational Levi and split component. For each
triple it requires a nonempty compatible-presentation type and tests
**every** presentation, matching represented radical and exponent.
The rational-Levi predicate already supplies existence of a matching
radical. Missing presentations cannot make this condition true.
The construction includes six direct extraction laws, not a structural,
analytic or representation-theoretic criterion.

The full-group exponent statement uses both identity maps, with every
actual represented radical and matching multiplication-isomorphism witness.
It tests every actual normalized exponent and concludes both zero
`normalizedRealPart` in the full real character space and pointwise norm one.
The exponent predicate already includes an open character kernel and nonzero
generalized weight space, so no extra character-smoothness premise is added.
A proof needs the
full-group cone degeneration and both conclusions from these actual inputs;
`normalizedTemperedFullGroupExponent` proves that target.

Its helper `ParabolicRootPresentation.restrictedRoot_eq_zero_identity`
simplifies the compatible presentation's factorization through the ambient
torus to the supplied central split-component map. The published
`root_restrict_eq_zero_of_isCentral` then makes every actual restricted
simple-root vector zero. `ParabolicRootPresentation.nonnegCone_identity`
expands the finite root-combination sums, proves each summand zero and uses
the existing zero-membership law for the reverse inclusion. Thus the
nonnegative cone is `{0}` in the full real character space, including
central directions. No empty-root-set or cone-degeneration premise is added.

The main theorem extracts a compatible presentation from the actual
temperedness premise and applies its universal cone condition to the same
represented radical, multiplication isomorphism and exponent. Cone
membership gives zero normalized real part. The exponent's existing open
kernel then permits the published all-point
`Plancherel.SplitTorus.normalizedRealPart_eq_zero_iff` to give norm one.
All original topology hypotheses are retained, with arbitrary characteristic,
possibly nonsplit ambient groups and independent field/group and carrier
universes.
No scalar central character, irreducibility or finite-dimensional carrier
is required. This argument supplies no general presentation-existence
theorem and makes no comparison between the two real-part conventions.

The standard-reduction statement fixes its actual torus, embedding and
generic cocharacter before the equivalence. Its standard tests quantify
over `J,ζ` with `IsStandardCocharacter i ν J ζ`, then all actual
`p,l,a` and their structural witnesses. Four all-test equalities require
the parabolic image to equal both `standardParabolic i ν J` and the
dynamic parabolic of `ζ`, and the composite Levi image to equal both
`standardLevi i ν J` and the dynamic centralizer of that same `ζ`.
The right side retains admissibility and the full all-presentation cone
condition. A single `ζ` must realize both images; an empty
standard-cocharacter family cannot provide that witness. Conjugacy and
exponent transport remain obligations for the proof.
A proof must establish the completeness and transport needed for the
converse. The Library proves the standard-reduction statement, as
`normalizedTemperedStandardReduction` (`Langlands/Representation/Exponents/NormalizedTemperedStandardReductionProof.lean`).

The central-character statement reuses `SmoothRep.HasCentralCharacter`,
the scalar-action equation for a homomorphism on the full point-group center.
It asserts pointwise norm one for that prescribed character, without assuming
irreducibility, finite dimension, character smoothness or a comparison between
the split component and the full center. It retains `[Nontrivial π]`.
III.1.1, printed p.58/PDF p.64, permits the zero representation, and III.1.10,
printed p.63/PDF p.69, defines scalar central action without excluding it.
Every character acts scalarly on zero, while VII.1.1's nonzero weight-space
condition gives it no exponents. The nonunitary smooth absolute-value
character of the multiplicative group therefore obstructs the unqualified
printed consequence. This is a source argument documented in the paired
Markdown, not a kernel-checked counterexample or a claim that zero meets the
derived predicate's presentation-existence conditions.

The Library proves the corrected central-character proposition, as
`normalizedTemperedCentralCharacter` (`Langlands/Representation/Exponents/NormalizedTemperedCentralCharacterProof.lean`).
A proof must establish the actual full-center
structure, restriction, character-smoothness and identity-Jacquet comparisons
used by its argument, or reach the same conclusion by another checked route.
The neighboring full-group exponent proposition is not a premise.
The full-group proof above concerns exponents on the split
component and does not supply the full-center conclusion.

The dependency order requires the following; the status in the Library is
given for each.

1. Proof of the published `RenardRootConventionStatement`. The Library
   proves it, as `renardRootConvention` (`Langlands/GroupScheme/Rational/RenardRootConventionProof.lean`).
2. Proof of the published presentation existence, full
   independence and transport targets. Fixed-presentation pullback laws
   do not replace these targets. The Library proves them, as
   `parabolicRootPresentation` (`Langlands/GroupScheme/Rational/ParabolicRootPresentationProof.lean`).
3. Proof of the published tensor-identification statement, the
   split-center comparison, algebraic-torus and real-submanifold
   structures, and exact proofs of the published standard-reduction and
   corrected central-character statements. The
   corrected logarithmic comparison, eight algebraic complex-parameter
   clauses, four complex-quotient clauses and nine imaginary-quotient clauses
   above are proved. The Library also proves the tensor-identification,
   standard-reduction and corrected central-character statements (see the
   table above); this note records no proof of the split-center comparison
   or of the algebraic-torus and real-submanifold structures.
   Actual topology, subgroup-image, conjugacy and exponent-transport
   comparisons remain explicit.
4. The source's separate representation-theoretic assertions. The VII.1.1
   direct-sum and finite-exponent results, Casselman's criterion and
   VII.2.1 Remark 2 are published statements. The Library proves the first
   and the third, as `arbitraryParabolicExponent` (`Langlands/Representation/Exponents/ArbitraryParabolicExponentProof.lean`) and `squareIntegrableNormalizedTempered` (`Langlands/Representation/Exponents/SquareIntegrableNormalizedTemperedProof.lean`); it does not prove Casselman's criterion,
   `ArbitraryParabolicCasselmanCriterionStatement`. The published support of
   the VII.1.1 statement reduces its finiteness clause to actual Jacquet
   spanning and compactness of the literal parabolic quotient.
   Represented-parabolic Jacquet admissibility, the input for spanning, and
   quotient compactness are stated as
   `ArbitraryParabolicJacquetAdmissibilityStatement` and
   `ArbitraryParabolicQuotientCompactStatement`, and proved as
   `arbitraryParabolicJacquetAdmissibility` and
   `arbitraryParabolicQuotientCompact` (files
   `ArbitraryParabolicJacquetAdmissibilityProof.lean` and
   `ArbitraryParabolicQuotientCompactProof.lean` of
   `Langlands/Representation/Exponents/`). The VII.1.3, VII.2.2–VII.2.4 and
   VII.2.6 statements are published in the
   [parabolic-functor and tempered map](parabolic-functors-tempered-progress.md).
   This note records no statement of VII.2.5 or of the classification
   results. A scalar central
   character is a premise only of its separate corrected consequence; it is not
   a premise of the all-parabolic definition, full-group exponent statement or
   standard-reduction statement.
