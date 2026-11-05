# Renard V.3 and VII.1–VII.2: actual roots, exponents and normalization

Worker 6, updated 4 November 2026. This focused map supplements the
[whole-book ledger](coverage.md) and the
[Chapter V structural-input ledger](chapter-v-structural-inputs.md).
It records fourteen verified publications and the remaining gates to the
all-parabolic temperedness criterion. It is not a complete inventory of
V.3, VII.1 or VII.2, and supplies no new Lean proof.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
PDF page numbers below are one-based and equal printed page numbers plus six.
The source passages and the current Lean/Markdown pairs were read for the
claims below. The publication receipts were checked separately from
compilation, and all twenty-eight selected mathematical files match their
frozen accepted hashes and the files at Library
`b01e426d540ff0d2edcc0480f6f0d03dd2f71e78`.

## Selected source assertions and exact interfaces

| Passage, printed / PDF page | Published interface and retained obligation |
| --- | --- |
| V.3.4, 110 / 116: nonzero ambient Lie roots, radical roots and reduction by divisibility within the actual root set | `Langlands.GroupScheme.RenardRootConventionStatement` compares actual dynamic-radical Lie weights with positive relative roots and their indivisible parts. This is a published **statement**, with its proof still open. Divisibility is not primitivity in the entire character lattice. |
| V.3.12, 112 / 118: the simple system of the reduced positive roots of a minimal parabolic | The same statement compares indecomposables in the reduced positive set with `simpleRelativeRoots`, whose definition uses all positive relative roots. It does not identify all indivisible positive roots with simple roots. Bases, fundamental weights, coroots and central decompositions retain separate obligations. |
| V.3.14, 113 / 119: choose a contained minimal parabolic whose maximal split torus contains the specified Levi split component; restrict the simple roots outside the Levi index | `ParabolicRootPresentationData.IsCompatible` and `ParabolicRootPresentation p l a` record actual choices for specified maps. `pres.restrictedRoots` is the existing restricted-simple-root set. This construction does not prove existence or independence of those choices. |
| First two V.3.15 displays, 113 / 119: positive and nonnegative sums over the restricted roots | `pres.positiveCone` and `pres.nonnegCone` instantiate the existing finite-sum constructions in the full real character space. Membership, empty-index and elementary cone laws are implemented. The subsequent coroot-inequality chambers are different sets and are not substituted here. |
| V.3.19–V.3.20, 115–116 / 121–122, combined with VII.2.1, 227 / 233: real parameters and the exponent-cone test | The published theorem `normalizedTemperedLogarithmicComparison` proves the corrected all-point formula with factor `-log q`, the equivalent negative-raw cone test, and the complete predicate comparison. It preserves every compatible-presentation quantifier and does not prove presentation existence. |
| V.3.20, 116 / 122: complex exponential, periods, lifts and unitary image | The published theorem `Langlands.Plancherel.rationalComplexParameter` proves the eight algebraic actual-image and canonical-point assertions: surjectivity, period kernel and difference criterion, normalized real part of every lift, unitarity and imaginary image, and the two canonical-point transfers. The separately published `rationalComplexParameterQuotient` proves the two complex open quotient maps and their prescribed-value quotient homeomorphisms. Period discreteness, imaginary compactness and the source's tensor and algebraic-torus identifications remain separate. |
| V.3.20, 116 / 122: rational-character tensors and the pure-tensor absolute-value formula | The published construction `Langlands.Plancherel.rationalCharacterTensorParameter` extends actual integer evaluation to a complex-linear map. For affine groups locally of finite type, its composition with the existing canonical exponential satisfies `rationalCanonicalCharacterTensorExponential_tmul_val`, the formula \(e^{s\otimes\chi}(g)=\lvert\chi(g)\rvert_F^s\) on every actual rational point. Bijectivity of the tensor map and the split-center comparison remain separate. |
| VI.1.2, 135–136 / 141–142: normalized Jacquet quotient and the inverse modular-function convention | `Langlands.Aubert.General.RepresentedParabolic.jacquetFunctor` uses the actual coinvariant quotient and inverse-half Haar twist on literal point images. Its split-component action formula makes the factor explicit. This focused construction does not establish the section's exactness, adjunction or preservation assertions. |
| VII.1.1, 220 / 226: compact-open characteristic spaces, normalized exponents and their set | `normalizedJacquetWeightSpace`, `IsNormalizedJacquetExponent` and `normalizedJacquetExponents` apply the published weight-space machinery to the actual quotient. Membership uses one power uniform over all torus points. Definitions and intrinsic laws extend to smooth inputs; the direct-sum, admissibility and finite-length conclusions are separate. |
| VII.2.1, 227 / 233: admissibility and the nonnegative root-cone condition for every exponent at every parabolic | The published derived `IsNormalizedExponentTempered` combines admissibility with the actual all-parabolic, all-presentation condition. Its explicitly normalized parameter retains the corrected-source comparison described below; this construction does not complete original source-definition coverage. |
| VII.2.1, Remark 1, first assertion, 227 / 233: full-group exponents are unitary, equivalently have zero real part | The published theorem `normalizedTemperedFullGroupExponent` proves `NormalizedTemperedFullGroupExponentStatement` for the identity parabolic and identity Levi. Centrality of the supplied split component makes the actual root-combination cone `{0}`, giving zero normalized real part and norm one at every split-component point. The full-center consequence is separate. |
| VII.2.1, Remark 1, second assertion, 227 / 233: a scalar central character is unitary | The published corrected derived `NormalizedTemperedCentralCharacterStatement` concludes norm one on the full point-group center for every prescribed scalar central character of a nonzero normalized-exponent tempered representation. Nonzeroness repairs the source's zero-representation obstruction; the full-center proof remains open. |
| VII.2.1, Remark 3, 227 / 233: reduction to standard parabolics | The published `NormalizedTemperedStandardReductionStatement` fixes one actual maximal split torus and generic cocharacter defining a minimal dynamic parabolic. It states an equivalence with admissibility and the exponent-cone tests on the corresponding actual standard family. Its structural completeness and transport proof remain open. |

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

## Verified publications

Each receipt below has `accepted = true`, `public = true`, an unqualified
independent semantic approval and a published integration. The fourteen units
are four definitions, six statements and four exact proofs. A definition
receipt covers its construction and intrinsic laws; a statement receipt
does not prove its proposition.

| Pair and exact declaration | Candidate, independent review and publication |
| --- | --- |
| [ArbitraryParabolic](../../Langlands/Representation/Exponents/ArbitraryParabolic.md), `Langlands.Aubert.General.RepresentedParabolic.IsNormalizedJacquetExponent` | Definition `678ceb15-602f-4aaf-b1c2-3bc9c4ee24c0`; Reviewer 12310, review `f305b203-8d2e-4735-ad66-1e76371db9d7`; integration `d757143185e04f3c8a8456056ecf2a12`, commit `7596502b4fe9738072198e7f23076fa02293f254`. |
| [ParabolicRootPresentation](../../Langlands/GroupScheme/Rational/ParabolicRootPresentation.md), `Langlands.GroupScheme.ParabolicRootPresentation.nonnegCone` | Definition `e204b3f2-bd58-49e9-95dc-f9e1888f50bf`; Reviewer 12327, review `c0ce4017-c01f-4c43-86ba-9d04327e46a5`; integration `38571d24640344bfb006ae105b655720`, commit `6d810cf8b71c5da9cf2722e850d66305665461f5`. |
| [RenardRootConventionStatement](../../Langlands/GroupScheme/Rational/RenardRootConventionStatement.md), `Langlands.GroupScheme.RenardRootConventionStatement` | Statement `3204db6d-d854-4955-bed8-74b6e65a3cf9`; Reviewer 12337, review `c7efa60d-01f4-458c-ae8b-a5953c24a3dd`; integration `1d435d5d66a8493488125f8b84ec2210`, commit `6d810cf8b71c5da9cf2722e850d66305665461f5`. |
| [ParabolicRootPresentationStatement](../../Langlands/GroupScheme/Rational/ParabolicRootPresentationStatement.md), `Langlands.GroupScheme.ParabolicRootPresentationStatement` | Statement `5fe091ee-4eaf-4aa5-ab1a-0c994c44ec86`; Reviewer 12375, review `b4a378ef-5647-434d-b7e8-6cd9a0392f75`; integration `00244bce2e1044ad98de2f0712b7f0fe`, commit `fd5d309e44e7f2f66516fa1781a0112c4e3a56ac`. |
| [ArbitraryParabolicTempered](../../Langlands/Representation/Exponents/ArbitraryParabolicTempered.md), `Langlands.Aubert.General.RepresentedParabolic.IsNormalizedExponentTempered` | Definition `9571e30c-ad43-4382-ab43-19ed1aad72c0`; Reviewer 12384, review `a9f9c9b2-dc1e-4579-b239-9620c4d194ed`; integration `aea05d32927b424195375673ace0ccd6`, commit `fd5d309e44e7f2f66516fa1781a0112c4e3a56ac`. |
| [NormalizedTemperedFullGroupStatement](../../Langlands/Representation/Exponents/NormalizedTemperedFullGroupStatement.md), `Langlands.Aubert.General.RepresentedParabolic.NormalizedTemperedFullGroupExponentStatement` | Statement `ad80b6ba-e43a-4378-bc92-883b7065e2fc`; Reviewer 12429, review `4881e2c5-63bb-444c-84a0-2bb3193b8849`; integration `edfdf00e1cfc4255be95f35950ea1636`, commit `cf220a229d7dcb607b8e9ff31488860fb7037d7c`. |
| [NormalizedTemperedStandardReductionStatement](../../Langlands/Representation/Exponents/NormalizedTemperedStandardReductionStatement.md), `Langlands.Aubert.General.RepresentedParabolic.NormalizedTemperedStandardReductionStatement` | Statement `daf38b57-1ae2-4d22-b3ad-e51c016d6895`; Reviewer 12432, review `8c6d12b3-2131-4dc1-ae79-fd257531624e`; integration `906617bac7344acda598e2e32a381a5c`, commit `cf220a229d7dcb607b8e9ff31488860fb7037d7c`. |
| [NormalizedTemperedCentralCharacterStatement](../../Langlands/Representation/Exponents/NormalizedTemperedCentralCharacterStatement.md), `Langlands.Aubert.General.RepresentedParabolic.NormalizedTemperedCentralCharacterStatement` | Statement `1e7616e3-25b5-4d17-bada-55460e7c2119`; Reviewer 12504, review `ad9ef60a-557b-4b6a-9309-88b04b004e5b`; integration `ccd2ecc3e1f14209b51339bda20ea5df`, commit `c41b568e7835014dced08e75cc4af6f669955f5d`. |
| [NormalizedTemperedLogarithmicComparisonStatement](../../Langlands/Representation/Exponents/NormalizedTemperedLogarithmicComparisonStatement.md), `Langlands.Aubert.General.RepresentedParabolic.NormalizedTemperedLogarithmicComparisonStatement` | Statement `57bf045c-784d-4771-b46a-49291d74a287`; Reviewer 12567, review `421c12e0-655d-4435-b6cc-0ff939301bbd`; integration `0f51d21dae3a4661ac334de0f3beedd4`, commit `687ec597518e5ed344da1618d8a37af0df359b54`. |
| [NormalizedTemperedFullGroupProof](../../Langlands/Representation/Exponents/NormalizedTemperedFullGroupProof.md), `Langlands.Aubert.General.RepresentedParabolic.normalizedTemperedFullGroupExponent` | Proof `f23de670-bc8a-4e8f-8c5f-ac059aed8bda`; Reviewer 13143, review `eb61c208-2cd9-4270-8ecf-7a2856f2ea3c`; machine `25782988-958a-4747-8d8f-914c0d15332b` accepted under `lean.proof@1` with build and exact-target checks; integration `bded81b0119248ce995aa959e331ad6d`, commit `50c05a5877c13ea23a52ea298c0ec2bd6fdb0817`. |
| [NormalizedTemperedLogarithmicComparison](../../Langlands/Representation/Exponents/NormalizedTemperedLogarithmicComparison.md), `Langlands.Aubert.General.RepresentedParabolic.normalizedTemperedLogarithmicComparison` | Proof `a9190a54-90e8-40f0-8b72-607383ca08bb`; Reviewer 13198, review `20105ad0-bbb4-4e17-bf5e-725e4973a61d`; machine `d3ac77ed-f0b6-4bff-9adc-f96cf6d2657a`; integration `65312fa4ce6f4b40a0e52b06c2ae1e33`, commit `50c05a5877c13ea23a52ea298c0ec2bd6fdb0817`. |
| [RationalComplexParameter](../../Langlands/Representation/Plancherel/RationalComplexParameter.md), `Langlands.Plancherel.rationalComplexParameter` | Proof `6bf086b3-88ba-479f-8542-cb693b8d2e9d`; Reviewer 13227, review `e5d8bead-cf4d-4740-9aab-c4a67cd1d699`; machine `81cdfcbd-cc3d-4f8c-99bc-13f871a56942`; integration `89a8b9bf8974479a98ca24b2116820bb`, commit `50c05a5877c13ea23a52ea298c0ec2bd6fdb0817`. |
| [RationalComplexParameterQuotient](../../Langlands/Representation/Plancherel/RationalComplexParameterQuotient.md), `Langlands.Plancherel.rationalComplexParameterQuotient` | Proof `a58e2446-72fb-4062-bcac-b87da5b45f60`; Reviewer 13393, review `ee719a12-f6dc-42e7-87a6-283296241bab`; machine `16a2d280-f771-43e9-b4df-b244157d1347`; integration `1af3227263864292abdd7c8aab4006c5`, commit `4dd5f7c45ce9b800a0caffa94e2e790953bf7c96`. |
| [RationalCharacterTensorParameter](../../Langlands/Representation/Plancherel/RationalCharacterTensorParameter.md), `Langlands.Plancherel.rationalCharacterTensorParameter` | Definition `26067a47-60dc-42c6-b970-0b48d6dd0418`; Reviewer 13447, review `82e0e7f1-8ba4-4c75-855e-6d84cc7a8e42`; machine `820db56f-6140-40be-842a-e10723cc6549`; integration `21dce902fd0a4fd986346142cee3f988`, commit `a4a5fb7b2643f2b9b9a6ac9c41bde7cc387d4a1a`. |

The logarithmic, algebraic complex-parameter and complex-quotient machine receipts each accept
`lake-build`, `exact-target`, `unchanged-statement` and `frozen-inputs`
under `lean.proof@1`; their independent semantic approvals have no
qualifications. The logarithmic proof was supplied by Worker 6 and verified
and submitted by Worker 1593. Worker 6 supplied the complex-parameter proof,
with verification and submission by Worker 1444. The same authors supplied,
verified and submitted the complex-quotient proof.

The arbitrary-parabolic wrapper imports Worker 1507's existing generic and
standard-family weight machinery unchanged. This map credits that reuse
without assigning any of the remaining proof obligations to its author.
Worker 1590 authored the full-group proof; the argument below follows its
published Lean implementation and companion Markdown.

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

Exact proof successor `5e93d170-2e08-4a46-8fed-b33ee6f928c0` revision 1
is discharged by the independently accepted and published
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

Both complex-parameter theorems retain arbitrary connected reductive groups
and general nonarchimedean local fields, without an added finite-rank,
split or characteristic-zero premise. They do not establish discrete periods
or the compact imaginary quotient, the character/split-center tensor
comparisons or an algebraic-torus structure. Exact
proof task `8560dddc-2f5b-4f5f-b631-a9cbe9fe5489` targets the separately
published `RationalImaginaryParameterQuotientStatement`, including
discrete and closed periods and the compact imaginary quotient. That task
and its shared proof draft supply no accepted proof.
These distinct V.3.20 obligations and original source-definition coverage
remain open.

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
That identification, the split-center comparison, algebraic-torus
representability and manifold structure retain separate proof obligations.
The coroot-pairing positivity used for the Langlands-classification parameters
of VII.4 also retains its own construction and comparison obligations.

## Published normalized formulation and remaining proof gates

The published aggregate
`Langlands.GroupScheme.ParabolicRootPresentationStatement`
asserts existence for every specified actual `p,l,a`, independence of
restricted roots and both cones across arbitrary compatible presentations,
and both-direction pullback transport under compatible component isomorphisms.
All presentation fields may vary in its comparisons. The focused statement
task is `324d4a6a-1bb2-4eb5-8cc7-0e8e01fa19ee`; the proof successor is
`c6c736b5-f1c4-4203-bb23-f7981c4fc3af`. Publication of this proposition
supplies no proof of existence, independence or transport.

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
Exact proof task `e8d2e2ad-434b-412e-abc2-d466a08724f1` requires the
full-group cone degeneration and both conclusions from these actual inputs;
the accepted/public `normalizedTemperedFullGroupExponent` proves that target.

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
Exact proof task `c9759a7b-aa16-42d4-8f0f-64cdc265e173` must establish
the completeness and transport needed for the converse.

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

Exact proof task `deba47f5-308e-431c-bfc1-13ef8390feb7` targets the corrected
central-character proposition. Its proof must establish the actual full-center
structure, restriction, character-smoothness and identity-Jacquet comparisons
used by its argument, or another checked route to the same conclusion.
The neighboring full-group exponent proposition is not a premise.
The standard-reduction and central-character task identifiers locate the
remaining separate proof obligations; publication of those tasks supplies
no theorem. The full-group proof above concerns exponents on the split
component and does not supply the full-center conclusion.

The dependency order still requires:

1. Proof of the published `RenardRootConventionStatement`, with focused
   successor task `90eeb314-6b62-4150-bf19-095a45c0ff33`.
2. Proof of the published presentation existence, full
   independence and transport targets. Fixed-presentation pullback laws
   do not replace these targets.
3. The remaining imaginary quotient topology, discrete periods,
   compactness of the imaginary quotient, tensor and algebraic-torus comparisons,
   and exact proofs of the published standard-reduction and corrected
   central-character statements. The corrected logarithmic comparison and
   eight algebraic complex-parameter clauses and four complex-quotient clauses
   above are already proved and public.
   Actual topology, subgroup-image, conjugacy and exponent-transport
   comparisons remain explicit.
4. The source's separate representation-theoretic assertions: the VII.1.1
   direct-sum and finite-exponent results, Casselman's criterion, the
   VII.2.1 Remark 2's Casselman implication, induction and restriction behavior,
   and the later tempered-support and classification results. A scalar central
   character is a premise only of its separate corrected consequence; it is not
   a premise of the all-parabolic definition, full-group exponent statement or
   standard-reduction statement.

The listed task identifiers locate work. They are not proof receipts,
ownership changes or authority to resume held tasks. General reductive scope,
positive-characteristic local fields, existing owners and user run controls
remain unchanged.
