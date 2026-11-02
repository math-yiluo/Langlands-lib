# GL Aubert specialization: actual models, full comparison targets and dependencies

Workers 585 and 34 constructed the GL adapters and graded targets described
below. This note maps original source assertions to those exact declarations,
records the body/type dependency inventory including private helper constants,
and preserves the remaining general-specialization and proof obligations.
It supplies no proof of the full Aubert or Zelevinsky theorem. A staged target
is not public mathematics until independent acceptance and integration.

The scope and target inventory was checked against Library
`0ebc0efd383ff160084af3b33ab2b7806f7a1dde` and the explicitly identified staged
pairs. Status descriptions below refer to that audit snapshot. Later users
should locate results by Lean name in the current Library.

## Scope and conventions

The constructions use actual smooth complex representations of the existing
`PadicField` GL models, independent field/carrier universes and carriers in
`Type (max uF uV)`. Exact K0 is the existing quotient by all actual short
exact sequences. The direct sum contains every natural rank, including zero;
its unit is the actual one-dimensional trivial representation of GL_0.
Upper parabolics, right translation, positive induction half-modulus and
inverse Jacquet half-modulus are unchanged. No arbitrary-local-field bridge
or general reductive structure is supplied by this graded branch.

## Actual GL models and support adjustment

The following declarations reuse the existing upper block parabolics, actual
radical kernels, block projections and diagonal sections. Their ordinary
matrix-group definitions include every natural rank, with the empty block
shape at rank zero. All abbreviated Lean names in this section are under
`Langlands`.

| Construction | Exact declarations and meaning |
| --- | --- |
| Actual parabolic quotient | `GeneralLinear.BlockShape.parabolicQuotientLevi`, `unipotentAmbientEquiv`, `parabolic_eq_levi_mul_unipotent`, `leviSubgroup_inf_unipotentSubgroup` and their ambient-conjugation formulas compare actual groups, not abstract labels. `parabolicQuotientLeviContinuous` adds the quotient/product topology comparison. |
| Smooth and exact-K0 Levi models | `Parabolic.productToEmbeddedLevi`, `productToQuotientLevi`, `embeddedToQuotientLevi`; `embeddedLeviK0Equiv`, `quotientLeviK0Equiv`, `embeddedToQuotientLeviK0Equiv` and the commuting triangle. These retain original vector spaces and linear maps and use the existing exact quotient by all short-exact relations. |
| Genuine quotient Jacquet action | `GeneralLinear.BlockShape.normalizedQuotientJacquetOf` uses Mathlib's actual `quotientToCoinvariants`, normalized by the inverse positive half. `_eq` proves equality with pullback of the existing product-Levi action. `normalizedQuotientJacquetIsoOf` is natural and the identity on coinvariant vectors. `Parabolic.normalizedQuotientJacquetK0_eq` is equality on the entire exact K0, using the existing explicit p-adic block character. |
| Actual quotient induction | `GeneralLinear.BlockShape.quotientInducingRepresentation` inflates through `QuotientGroup.mk'`; `_eq` identifies its parabolic action with the existing product-Levi inducing action. `quotientInducedEquiv_eval` preserves every smooth covariant function pointwise. `normalizedQuotientInductionFunctorOf_map_eval` retains actual postcomposition by each original intertwiner. `Parabolic.normalizedQuotientInductionK0_eq` uses inverse actual Levi transport. |
| Existing unadjusted composite/operator | `Parabolic.normalizedQuotientInductionJacquetK0_eq` cancels the inverse model transports on all exact classes. `Aubert.alternatingOperator_eq_quotientLevi_sum` and `alternatingOperator_eq_rootSubset_sum` reexpress the unchanged existing GL operator. The latter uses `BlockShape.leviRootSubsetEquiv`; its root-subset cardinality is `n-B.length`. These are GL identities, not the pending general-datum specialization. |
| Actual support sign | `Aubert.supportSign` is the unique sign making the actual unadjusted irreducible Aubert image effective. Existence uses the actual quasicuspidal embedding and signed effectivity; uniqueness uses actual involutivity/nonzeroness and integer positivity. `supportSign_of_support` gives `(-1)^(n-B.length)` for every actual quasicuspidal support presentation, matching Aubert Definition 2.1. |
| Rankwise exact adjustment | `Aubert.adjustedOperator` extends those actual values through the proved Jordan–Holder factor-count/realization maps. `adjustedOperator_irreducible` is its exact-class formula; `adjustedOperator_rankZero` is identity on the whole actual degree-zero K0. The graded extension below preserves its actual unit. |

SupportSign, ParabolicQuotient and RootSubsetExpansion were verified public at
the snapshot. LeviModelTransport had machine validation and independent approval
but awaited integration (`3ffc4cf3-9252-40f6-816b-93b2d24d31ac`). The quotient
Jacquet (`d55f4230-35bb-45dd-b63e-196fe462fafe`) and induction/composite
(`82b8e447-9f67-4b22-945f-58106eb3ada3`) pairs were staged. Their normal module
paths are `Langlands/Representation/Parabolic/QuotientJacquetComparison` and
`QuotientInductionComparison`, with paired Lean and Markdown. The latter imports
the former, which imports LeviModelTransport. These focused units must integrate
in that order before their names are public downstream proof targets.

The group-model construction works over commutative topological rings, with a
Hausdorff condition only where actual subgroup closedness requires it. The
generic quotient induction/Jacquet comparisons keep independent field and
representation universes; smooth induction has carrier universe `max uF uV`.
Generic Jacquet finite-length/exactness premises remain explicit. Their p-adic
specializations use existing preservation and exactness proofs at the established
saturated carrier universe. No arbitrary-local-field theorem or Haar modulus
identity follows from using the explicit block character.

## General-specialization bridges still required

The shared general adapter task `593ef603-6672-4424-976c-14e11e920d9c` had no
public artifact or shared draft at this snapshot. Its exact accepted general
datum, normalized induction/Jacquet and operator declarations must be specialized
when available. The current GL model comparisons above supply concrete target
sides; they do not instantiate a hypothetical general datum or construct a
competing general operator.

| Bridge | Exact available starting point and retained obligation |
| --- | --- |
| Algebraic GL, parabolic, Levi and radical | Use the existing `GroupScheme.GeneralLinear.groupScheme`, its algebraic point equivalences and the actual `Group.GL.Blocks` models. The algebraic-owner route is Worker 1107; actual scheme-subgroup/block identification is a separate construction/proof requirement. |
| Rational-point topology | `GroupScheme.GeneralLinear.pointsEquiv`, `affinePointsEquiv` and `homEquiv` are algebraic maps. The scheme-point/matrix multiplicative homeomorphism with commuting subgroup embeddings/projections, transported closedness, local compactness and nonarchimedeanness was not verified public. Worker 118 routed this to Conrad task `886bf565-95e9-4dc6-8a9d-73284a523668` (Workers 105/208). The ring/test-algebra scheme API currently shares one universe; independent-universe and rank-zero comparison must be checked explicitly. |
| Matrix topology | Existing `PadicField.TopologicalData.generalLinearTopology`, `generalLinearTopologicalGroup`, `generalLinearLocallyCompactSpace` and the PadicBlocks parabolic/radical/Levi topology, compactness, embeddings, projection and `blockDecomposition` are actual matrix-side tools. Their names do not supply a scheme-point comparison. |
| Actual roots/Weyl/standard subsets | `GroupScheme.GeneralLinear.diagonalTorus`, `characterCoordEquiv`, `cocharacterCoordEquiv`, `rootDatum`, `permutationAction` and reflection formulas give the full central lattice coordinates and a standard split datum. Identifying it with actual adjoint roots, maximality and rational-point Weyl image remains the `GeneralLinearRootDatumStatement` proof obligation. Relative-root owners 1220/176 and algebraic owner 1107 coordinate the actual standard-block and empty-root-set bridge. |
| Published relative-root scope | `GroupScheme.Rational.RelativeRoots` constructs `relativeRoots`, `relativeWeylGroup`, `relativeRootSpan`, `relativeWeylAction` and `IsGenericCocharacter`. `Rational.Statement` gives `RelativeRootSystemStatement`, `RationalBruhatStatement` and `GenericCentralizerStatement` as propositions, not proofs. A larger shared draft is not additional public coverage. |
| Block characters/weights | Actual block-Levi determinant scheme characters, compatibility with `Group.GL.BlockModulus`, and block-radical root-weight multiplicities remain bridges beyond the published standard split root datum. Worker 339 routed these through owners 1107/207 and 1220/176. The weight-decomposition candidate had machine validation and independent approval at the snapshot, with integration pending. |
| Generic induction design | The unreviewed closed-semidirect task `82bfcc29-81a6-4092-9b9c-f089d2abfb76`, revision 2, records actual closed M/U/P, normalizer containment, disjointness and product, then actual covariance and full smooth right translation. A private GL test proves its projection equals the actual diagonal projection, its trivial-radical covariance equals the existing GL inducing action, and its induced-function comparison is natural and pointwise identity. This is development evidence against an unreviewed interface, not an accepted shared adapter. The paused owner's hold is retained. |
| Actual Haar normalization | `HaarModulus.restrictCharacter` and closed-subgroup wrappers construct actual normalizer moduli and positive/inverse halves. Identifying them with the explicit GL block character and root-product formula is retained Chapter V obligation D07, including orientation. It is not an additional external structural input. |

The finite external boundary is the separately reviewed
[Renard Chapter V ledger](../renard/chapter-v-structural-inputs.md), rows S01–S23.
Its D01–D08 deductions, intrinsic construction laws and all representation-theoretic
premises remain obligations. The rational Weyl quotients have centralizer
denominators, and the empty root set is retained. General and GL comparisons
must not silently narrow positive-characteristic, nonsplit or nonquasisplit
scope. The present concrete GL representation development has explicit
`PadicField` scope; its extension to arbitrary nonarchimedean local fields is a
separate bridge.

## Original-source to declaration map

| Original source | Constructed declarations / precise proof targets |
| --- | --- |
| Ze80 §1.7, pp.172–173 | `GradedGrothendieckGroup`, `gradedInclusion`, `binaryProductK0`, `gradedMultiplication`, `gradedUnit`; separate `BinaryProductExactnessStatement` and `GradedInductionRingLawsStatement`; conditional `gradedInductionRing`. |
| Aubert p.2184 product paragraph, corrected to product Levi; Ze80 §1.7 | `binaryProductLeviTensorFunctor`, actual functor factorization, `productLeviTensorMap`, separate `ProductLeviTensorPrerequisitesStatement` and `ProductLeviTensorBijectiveStatement`, conditional tensor equivalence; `productLeviInductionTensorMap_eq` proves equality only after induction into the larger GL K0. |
| Ze80 §§3.1,9.1, pp.180–181,197 | `segmentSocleObject`, `segmentSpecialObject`, actual isomorphism and exact-class transport theorems; `gradedSegmentSocle` and `gradedSegmentSpecial`. |
| Aubert Remark2.2/Theorem2.3, pp.2184–2185 | `alternatingOperator_segmentSocleClass` reuses the published unadjusted segment identity with sign `(-1)^(degree-length)`, on identified actual objects. |
| Ze80 Corollary7.5, p.193 | `segmentPolynomialEvaluation`; `SegmentPolynomialComparisonStatement` is its actual bijectivity; `SegmentMonomialSpanningStatement` and `SegmentMonomialBasisStatement` concern all induction monomials. The conditional polynomial equivalence and actual monomial basis are constructed. |
| Ze80 §9.12, p.201, with9.13–9.14, pp.201–202 | `zelevinskyEndomorphism` is actual segment-to-special-quotient substitution via the polynomial comparison; `ZelevinskyInvolutivityStatement` is separate; `zelevinskyRingInvolution` is constructed from it. |
| Aubert Theorem2.3 proof, p.2185, with monomial correction | `GradedOperatorComparison` extends homogeneous multiplicativity, constructs a ring endomorphism from explicit product/unit conditions, compares linear maps on spanning monomials, and proves the polynomial whole-ring comparison from explicit conditions. |
| Aubert Definition2.1 and Theorem2.3, pp.2184–2185 | `gradedAdjustedOperator` extends the actual published `adjustedOperator` over all natural ranks. `gradedAdjustedOperator_homogeneous` identifies its homogeneous values; `gradedAdjustedOperator_unit` proves preservation of the actual degree-zero unit using `adjustedOperator_rankZero`. |
| Aubert Theorem2.3, pp.2184–2185, with Ze80 Corollary7.5 and §9.12 | `AubertTheorem23Statement` conjoins multiplicativity of the actual adjusted operator, involutivity of the constructed Zelevinsky endomorphism and equality on the whole actual graded exact K0. All lower exactness, ring-law and polynomial-comparison parameters are explicit. |

The Aubert source is registered as `aubert-1995-duality`, SHA256
`57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693`.
Ze80 is `zelevinsky-1980-induced-ii`, SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
The original passages above were read from the retained PDFs. Aubert's
p.2184 tensor identification is corrected to the product Levi and its
induction citation to Theorem1.7(2), as in the published corrected-source
note. The defective Proposition3.2 and original Theorem3.6 argument do
not supply an extra proof input here.

The polynomial bijectivity target depends mathematically on the
classification basis of Ze80§6.5 and the triangular unipotent multiplicity
matrix of7.1. Defining a polynomial evaluation does not establish those
facts. The involutivity target corresponds to the expansion9.13 and
alternating segment-subdivision argument9.14. Exactness, ring laws,
tensor bijectivity, the polynomial comparison and actual adjusted
multiplicativity remain representation-theoretic proof obligations;
none is an allowed external Chapter V structural input merely because it
is written as a parameter of a construction.

## Exact final targets and proof succession

All names in this section are in `Langlands.Aubert`. The main final module is
`Langlands/Representation/Aubert/ZelevinskyComparison.lean`. Its frozen
candidate is `a666a2cb-65ab-4b7a-960d-02f523fb0a93`. Its helper candidates are
`924a6b4b-ff72-4b80-919a-8f2e6b5412d7` (`ZelevinskyPolynomial`) and
`0af82854-592c-40de-bc4d-80dfef858c6a` (`GradedOperatorComparison`).
These three candidates were still unpublished when the final-target extraction was
made; the final candidate has accepted machine validation and is undergoing
semantic review, and the helpers have approving semantic reports. The final
bundle includes byte-identical copies of the two helper pairs. Integrate
`ZelevinskyPolynomial`, then `GradedOperatorComparison`, then
`ZelevinskyComparison`, retaining one copy of each shared path. Fresh seven-module
restoration check `fb70a667-8349-4166-8870-eb9f218339ab` has no errors or warnings.

The final eight Prop-valued targets were individually inspected in the approved
environment. These are targets for subsequent proofs, not eight proved theorems.

| Exact target | Scope and explicit parameters | Successful Prop inspection |
| --- | --- | --- |
| `AdjustedHomogeneousMultiplicativityStatement` | The actual adjusted rankwise operator preserves the actual binary induction product on arbitrary two homogeneous exact-K0 classes; parameter `hx`. | `506007ab-94dd-4c27-a6bc-2f55539c0126` |
| `AdjustedMultiplicativityStatement` | Multiplicativity on every pair of graded classes; parameter `hx`. | `a8e6a97b-b849-4da8-8b2f-ea49025304b3` |
| `AdjustedSegmentExchangeStatement` | Unsigned equality on the identified actual segment-socle and special-quotient classes; no `hx`, `hl` or `hp` parameter. | `dcfaf529-2dcb-4e5a-9009-43beafea3b49` |
| `AdjustedInvolutivityStatement` | Applying the actual graded adjusted additive operator twice is the identity on every graded class; no `hx`, `hl` or `hp` parameter. | `b575aa2a-8046-4729-873a-7f0e77e126ff` |
| `AubertZelevinskyComparisonStatement` | Equality of integer-linear maps on the entire graded exact K0; parameters `hx`, `hl`, `hp`. | `cdba7951-16c9-4aa0-80de-67c901c34a6b` |
| `AubertZelevinskyRingComparisonStatement` | Equality of ring endomorphisms with the actual adjusted additive map as the first underlying function; parameters `hx`, `hl`, `hp`, `hm`. | `183b19bc-bf7d-4fea-8784-bdc95e0186b6` |
| `AubertZelevinskyInvolutionComparisonStatement` | Equality of the actual adjusted integer-linear map with the additive map underlying the constructed Zelevinsky ring involution; parameters `hx`, `hl`, `hp`, `hi`. | `09378f47-e5b7-497f-b7f9-555042545933` |
| `AubertTheorem23Statement` | Conjunction of actual adjusted multiplicativity, constructed Zelevinsky involutivity and whole additive comparison; parameters `hx`, `hl`, `hp`. | `cb1a2883-a81f-451d-afc9-6946ba82a305` |

Here `hx` proves `BinaryProductExactnessStatement`, `hl` proves
`GradedInductionRingLawsStatement F T hx`, `hp` proves
`SegmentPolynomialComparisonStatement F T hx hl`, `hm` proves
`AdjustedMultiplicativityStatement F T hx`, and `hi` proves
`ZelevinskyInvolutivityStatement F T hx hl hp`. Coefficients remain complex
for representations and integral for exact K0; every comparison retains the
existing `PadicField` model, supplied topology, independent field and carrier
universes and the actual degree-zero group.

The parent can create focused proof successors from these exact names once
each defining pair is published, in the following dependency order. This is a map of remaining mathematical
obligations, not a declaration that these proofs already exist.

| Stage | Exact target or existing construction | Needed mathematical content and consumer |
| --- | --- | --- |
| Binary exactness | `BinaryProductExactnessStatement` in `GradedGrothendieck` | Preserve every actual mapped finite-length short exact sequence in both inputs of the all-ranks binary product. Finite-length preservation is already proved by `binaryProduct_preservesFiniteLength`. Worker 76 has published focused proof task `9e926f35-f515-46d5-bf8c-80ea29b66f4b` r1 for this public target; publication of a task does not supply its proof. |
| Ring laws | `GradedInductionRingLawsStatement` after `hx` | Associativity, commutativity and both unit laws for the constructed actual induction multiplication. Bilinearity already supplies the additive/distributive laws. Its proof supplies `hl` for the conditional `gradedInductionRing`. |
| Product-Levi tensor | `ProductLeviTensorPrerequisitesStatement`, then `ProductLeviTensorBijectiveStatement` in `ProductLeviGrothendieck` | Actual finite length and two-variable exactness for the product-Levi tensor functor, then bijectivity of its exact-K0 tensor map. The tensor target is the product Levi. The existing `productLeviInductionTensorMap_eq` only identifies the composite after induction into the larger GL group. |
| Polynomial comparison | `SegmentPolynomialComparisonStatement` after `hx`, `hl`; related `SegmentMonomialSpanningStatement` and `SegmentMonomialBasisStatement` | Actual polynomial evaluation must be bijective. The full family of induction monomials, including the empty one, supplies the additive basis. The implemented `segmentPolynomialEquiv`, `segmentMonomialBasis` and `segmentMonomialBasis_apply` consume `hp`; defining them does not prove `hp`. |
| Zelevinsky involutivity | `ZelevinskyInvolutivityStatement` after `hx`, `hl`, `hp` | The constructed socle-to-special-quotient substitution squares to the identity on all classes; Ze80 §§9.13–9.14 give the representation-theoretic route. `zelevinskyRingInvolution` consumes this separate proof. |
| Actual adjusted product compatibility | `AdjustedHomogeneousMultiplicativityStatement`, then `AdjustedMultiplicativityStatement` | The actual support adjustment must respect induction. The implemented `gradedOperator_multiplicative_of_homogeneous` extends a proved homogeneous identity to every graded class. `gradedAdjustedOperator_unit` already supplies the unit condition. |
| Actual adjusted segment identity | `AdjustedSegmentExchangeStatement` | Combine the existing signed unadjusted exchange on identified actual constituents with the actual support-sign formula. The unsigned target is separate from both a representation isomorphism and the unadjusted `(-1)^(degree-length)` identity. |
| Whole comparison and assembly | `AubertZelevinskyComparisonStatement`, `AubertZelevinskyRingComparisonStatement`, `AubertZelevinskyInvolutionComparisonStatement`, `AdjustedInvolutivityStatement`, `AubertTheorem23Statement` | `gradedOperatorRingHom_eq_zelevinsky` implements the algebraic implication from `hp`, product, unit and segment conditions; `gradedLinearMap_ext_monomials` supplies the additive route using all monomials. Actual involutivity and the involution comparison additionally use `hi`. Assemble the full primary target only after the named lower obligations are proved. |

None of these representation-theoretic premises is discharged by the parent's allowed external Renard Chapter V structural boundary.

## Exact transitive declaration inventory

The audit recursively visits each checked declaration's type and the body of
every definition, theorem and opaque constant, including private proof helpers,
and visits inductive constructors. It records actual defining modules and prunes
nonproject modules: the pinned Lean/Mathlib dependencies cannot import project
constants. Thus an imported but unused module is not counted as a body dependency.
The complete Classification-origin constant membership is listed below for all
27 selected construction, formula and final-target roots. This is a constant-use
inventory, not a semantic certificate that a theorem is independent of
classification. Classification modules also contain basic definitions and
algebraic transport proofs. Proof-route descriptions retain their actual meaning.

The original six graded roots were extracted in diagnostic
`a6b45808-de31-4db0-a8a5-a07a8d24514c`, the eight final roots in
`7652f402-cfed-4e39-89b2-b685ff421289`, and the thirteen specialization roots in
`5756ea3a-a5b1-4531-8be6-66389fcd5cad`, in approved environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`. They touch 842 distinct
project modules, each with nonempty same-stem Markdown. Every publicly present
source pair byte-matched Library `0ebc0efd383ff160084af3b33ab2b7806f7a1dde`.
The only additional pairs were the staged modules listed below. The normalized
sorted module/pair-fingerprint inventory has SHA-256 `73da5046930a337c3be0b158a9b3ef82e97bc5e783e7b6c79df977b795f49474`.
The full Classification-origin pairs have their individual fingerprints below.

Additional pairs at the audit snapshot:

- `Langlands.Group.GL.ParabolicQuotientTopology`
- `Langlands.Representation.Aubert.GradedOperatorComparison`
- `Langlands.Representation.Aubert.ZelevinskyComparison`
- `Langlands.Representation.Aubert.ZelevinskyPolynomial`
- `Langlands.Representation.Parabolic.LeviModelTransport`
- `Langlands.Representation.Parabolic.QuotientInductionComparison`
- `Langlands.Representation.Parabolic.QuotientJacquetComparison`

| Key | Actual root | Project declarations | Project modules | Classification-origin constants |
| --- | --- | ---: | ---: | ---: |
| B | `Langlands.Aubert.binaryProduct_preservesFiniteLength` | 5438 | 442 | 47 |
| L | `Langlands.Aubert.productLeviInductionTensorMap` | 5441 | 456 | 67 |
| Z | `Langlands.Aubert.segmentSocleObject` | 5406 | 482 | 219 |
| S | `Langlands.Aubert.segmentSpecialObject` | 5404 | 482 | 221 |
| A | `Langlands.Aubert.alternatingOperator_segmentSocleClass` | 8596 | 756 | 417 |
| P | `Langlands.Aubert.zelevinskyEndomorphism` | 6967 | 594 | 268 |
| G | `Langlands.Aubert.gradedAdjustedOperator` | 8324 | 674 | 131 |
| U | `Langlands.Aubert.gradedAdjustedOperator_unit` | 8503 | 690 | 137 |
| R | `Langlands.Aubert.adjustedRingEndomorphism` | 8643 | 694 | 140 |
| T | `Langlands.Aubert.AubertTheorem23Statement` | 9503 | 786 | 353 |
| I | `Langlands.Aubert.AubertZelevinskyInvolutionComparisonStatement` | 9502 | 785 | 353 |
| H | `Langlands.Aubert.gradedOperator_multiplicative_of_homogeneous` | 5497 | 445 | 47 |
| C | `Langlands.Aubert.gradedOperatorRingHom_eq_zelevinsky` | 6976 | 595 | 268 |
| M | `Langlands.Aubert.gradedLinearMap_ext_monomials` | 6941 | 594 | 249 |
| D1 | `Langlands.Aubert.adjustedOperator` | 8321 | 671 | 131 |
| D2 | `Langlands.Aubert.supportSign_of_support` | 8484 | 684 | 137 |
| D3 | `Langlands.Aubert.adjustedOperator_rankZero` | 8491 | 685 | 137 |
| D4 | `Langlands.Aubert.alternatingOperator_eq_rootSubset_sum` | 5463 | 455 | 67 |
| D5 | `Langlands.GeneralLinear.BlockShape.parabolicQuotientLeviContinuous` | 70 | 4 | 0 |
| D6 | `Langlands.Parabolic.quotientLeviK0Equiv` | 152 | 15 | 2 |
| D7 | `Langlands.GeneralLinear.BlockShape.normalizedQuotientJacquetIsoOf` | 183 | 19 | 0 |
| D8 | `Langlands.Parabolic.normalizedQuotientJacquetK0` | 5434 | 456 | 67 |
| D9 | `Langlands.Parabolic.normalizedQuotientJacquetK0_eq` | 5467 | 457 | 67 |
| D10 | `Langlands.GeneralLinear.BlockShape.quotientInducedEquiv` | 114 | 10 | 0 |
| D11 | `Langlands.Parabolic.normalizedQuotientInductionK0` | 5424 | 456 | 67 |
| D12 | `Langlands.Parabolic.normalizedQuotientInductionJacquetK0_eq` | 5482 | 458 | 67 |
| D13 | `Langlands.Aubert.alternatingOperator_eq_quotientLevi_sum` | 5486 | 458 | 67 |

The union is 420 Classification-origin constants. The thirteen specialization
roots contribute 137, all already present in the graded union. D5 (actual quotient
topology), D7 (actual Jacquet natural isomorphism) and D10 (actual inducing
function equivalence) contain no such reference. D6 (generic exact-K0 model
transport) reaches only `FiniteLengthAssembly.length_comp_surjective` and
`finiteLength_comp_surjective_iff`, whose proof is invariance through the actual
subrepresentation order isomorphism.

D8–D9 and D11–D13 reach the existing p-adic normalized induction/Jacquet
finite-length and exactness chains. Their 67 Classification-origin constants
include refined-Jacquet length induction, normalized induction length,
admissible product-Levi factorization, irreducible product embeddings and finite
length, supercuspidal product support, cuspidal tensor/induction length and ordered
regrouping. These are reused proved representation-theoretic inputs, not new
external structural assumptions. D1–D3 additionally reach actual quasicuspidal
embedding, signed effectivity, induction commutation/involutivity and genuine
Jordan–Holder transport. The absence of a classification parameter from a root's
statement does not remove any of these transitive dependencies.

For B, the all-ranks finite-length helper uses rank-zero finite-dimensional inert
tensor products and rank transports, or the positive-rank admissible finite-length
product theorem and finite-length admissibility. Its body uses no derivative
theorem despite its containing module's larger import closure. Z/S use actual
constituent-existence chains; A uses the existing Aubert segment exchange,
irreducible-image and signed-effectivity routes. P is a polynomial substitution
constructed from actual segment objects and explicit `hx`, `hl`, `hp` premises.
G/U/R record the actual support adjustment and unit/ring constructor; T/I include
full comparison types and constructions. H/C/M implement the algebraic passage
from homogeneous laws, polynomial bijectivity or monomial spanning to whole-class
identities. Their explicit premises are still representation-theoretic obligations.

The underlying original GL proof route and its corrected source limitations are
recorded in [Aubert duality: corrected sources and independence](../henniart/aubert-duality-route.md).
In particular, the unresolved Proposition 3.2 and defective original Theorem 3.6
argument are not extra accepted proof inputs. The polynomial-basis and
involutivity statements below retain the Zelevinsky classification/triangularity
and segment-subdivision obligations even though their targets are conditional.

### Complete Classification-origin constant memberships

#### Langlands.Representation.Classification.CanonicalConstituents

| Declaration | Roots |
| --- | --- |
| `Langlands.Classification.HasIrreducibleHead` | Z, S, A, P, T, I, C, M |
| `Langlands.Classification.HasIrreducibleSocle` | Z, S, A, P, T, I, C, M |
| `Langlands.Classification.IsIrreducibleHead.headKernel_eq` | Z, S, A, P, T, I, C, M |
| `Langlands.Classification.IsIrreducibleHead.nonempty_headEquiv` | A |
| `Langlands.Classification.IsIrreducibleSocle.nonempty_socleEquiv` | A |
| `Langlands.Classification.IsIrreducibleSocle.socle_eq` | Z, S, A, P, T, I, C, M |
| `Langlands.Classification.head` | A |
| `Langlands.Classification.headEquivOfSurjective` | A |
| `Langlands.Classification.headEquivOfSurjective._proof_1` | A |
| `Langlands.Classification.headEquivOfSurjective._proof_2` | A |
| `Langlands.Classification.headEquivOfSurjective._proof_3` | A |
| `Langlands.Classification.headEquivOfSurjective._proof_4` | A |
| `Langlands.Classification.headEquivOfSurjective._proof_5` | A |
| `Langlands.Classification.headKernel` | Z, S, A, P, T, I, C, M |
| `Langlands.Classification.headKernel._proof_1` | Z, S, A, P, T, I, C, M |
| `Langlands.Classification.headKernel._proof_2` | Z, S, A, P, T, I, C, M |
| `Langlands.Classification.headKernel._proof_3` | Z, S, A, P, T, I, C, M |
| `Langlands.Classification.headKernel._proof_4` | Z, S, A, P, T, I, C, M |
| `Langlands.Classification.headKernel_le_ker` | Z, S, A, P, T, I, C, M |
| `Langlands.Classification.headKernel_stable` | A |
| `Langlands.Classification.irreducibleImages` | Z, S, A, P, T, I, C, M |
| `Langlands.Classification.ofSocle._proof_1` | A |
| `Langlands.Classification.range_le_socle` | Z, S, A, P, T, I, C, M |
| `Langlands.Classification.socle` | Z, S, A, P, T, I, C, M |
| `Langlands.Classification.socle._proof_1` | Z, S, A, P, T, I, C, M |
| `Langlands.Classification.socleEquivOfInjective` | A |
| `Langlands.Classification.socleEquivOfInjective._proof_1` | A |
| `Langlands.Classification.socleEquivOfInjective._proof_2` | A |
| `Langlands.Classification.socleEquivOfInjective._proof_3` | A |
| `Langlands.Classification.socleRepresentation` | A |
| `Langlands.Classification.toHead._proof_1` | A |

#### Langlands.Representation.Classification.CommonImageMultiplicityOneProof

| Declaration | Roots |
| --- | --- |
| `Langlands.Classification.commonImageMultiplicityOne` | Z, S, A, P, T, I, C, M |
| `Langlands.Classification.commonImageMultiplicityOne._proof_1_1` | Z, S, A, P, T, I, C, M |
| `_private.Langlands.Representation.Classification.CommonImageMultiplicityOneProof.0.Langlands.Classification.irreducible_carrier_nontrivial` | Z, S, A, P, T, I, C, M |
| `_private.Langlands.Representation.Classification.CommonImageMultiplicityOneProof.0.Langlands.Classification.positive_zero_composite_impossible` | Z, S, A, P, T, I, C, M |
| `_private.Langlands.Representation.Classification.CommonImageMultiplicityOneProof.0.Langlands.Classification.positive_zero_composite_impossible._proof_1_1` | Z, S, A, P, T, I, C, M |

#### Langlands.Representation.Classification.CommonImageMultiplicityOneStatement

| Declaration | Roots |
| --- | --- |
| `Langlands.Classification.CommonImageMultiplicityOneStatement` | Z, S, A, P, T, I, C, M |

#### Langlands.Representation.Classification.ConstituentRelations

| Declaration | Roots |
| --- | --- |
| `Langlands.Classification.HasScalarCharacter` | A |
| `Langlands.Classification.IsIrreducibleHead` | Z, S, A, P, T, I, C, M |
| `Langlands.Classification.IsIrreducibleSocle` | Z, S, A, P, T, I, C, M |
| `Langlands.Classification.IsIrreducibleSubrepresentation` | A |

#### Langlands.Representation.Classification.Cosocle

| Declaration | Roots |
| --- | --- |
| `Langlands.Classification.isIrreducible_iff_isCoatom_ker` | Z, S, A, P, T, I, C, M |

#### Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof

| Declaration | Roots |
| --- | --- |
| `Langlands.Classification.IntegralTwistFreeness.character_eq_one_on_center` | Z, S, A, P, T, I, C, M |
| `Langlands.Classification.IntegralTwistFreeness.exponent_eq_zero_of_equiv` | Z, S, A, P, T, I, C, M |
| `Langlands.Classification.IntegralTwistFreeness.scalar_uniformizer_value` | Z, S, A, P, T, I, C, M |
| `Langlands.Classification.cuspidalIntegralTwistFreeness` | Z, S, A, P, T, I, C, M |

#### Langlands.Representation.Classification.CuspidalIntegralTwistFreenessStatement

| Declaration | Roots |
| --- | --- |
| `Langlands.Classification.CuspidalIntegralTwistFreeness` | Z, S, A, P, T, I, C, M |

#### Langlands.Representation.Classification.CuspidalJacquetFunctorExactnessProof

| Declaration | Roots |
| --- | --- |
| `Langlands.CuspidalJacquetMultiplicity.oppositeFunctor_additive` | S, A, P, T, I, C |
| `Langlands.CuspidalJacquetMultiplicity.oppositeFunctor_preservesEpimorphisms` | S, A, P, T, I, C |
| `Langlands.CuspidalJacquetMultiplicity.oppositeFunctor_preservesMonomorphisms` | S, A, P, T, I, C |
| `Langlands.CuspidalJacquetMultiplicity.oppositeUnipotent_finite_containment` | S, A, P, T, I, C |
| `Langlands.CuspidalJacquetMultiplicity.upperFunctor_additive` | Z, A, P, T, I, C, M |
| `Langlands.CuspidalJacquetMultiplicity.upperFunctor_preservesEpimorphisms` | Z, A, P, T, I, C, M |
| `Langlands.CuspidalJacquetMultiplicity.upperFunctor_preservesMonomorphisms` | Z, A, P, T, I, C, M |

#### Langlands.Representation.Classification.CuspidalJacquetFunctors

| Declaration | Roots |
| --- | --- |
| `Langlands.CuspidalJacquetMultiplicity.oppositeFunctor` | S, A, P, T, I, C |
| `Langlands.CuspidalJacquetMultiplicity.oppositeFunctor._proof_1` | S, A, P, T, I, C |
| `Langlands.CuspidalJacquetMultiplicity.oppositeFunctor._proof_2` | S, A, P, T, I, C |
| `Langlands.CuspidalJacquetMultiplicity.oppositeMap` | Z, S, A, P, T, I, C, M |
| `Langlands.CuspidalJacquetMultiplicity.oppositeMap._proof_1` | Z, S, A, P, T, I, C, M |
| `Langlands.CuspidalJacquetMultiplicity.oppositeMap._proof_2` | Z, S, A, P, T, I, C, M |
| `Langlands.CuspidalJacquetMultiplicity.oppositeMap._proof_3` | Z, S, A, P, T, I, C, M |
| `Langlands.CuspidalJacquetMultiplicity.oppositeMap._proof_4` | Z, S, A, P, T, I, C, M |
| `Langlands.CuspidalJacquetMultiplicity.oppositeMap._proof_5` | Z, S, A, P, T, I, C, M |
| `Langlands.CuspidalJacquetMultiplicity.upperFunctor` | Z, A, P, T, I, C, M |
| `Langlands.CuspidalJacquetMultiplicity.upperFunctor._proof_1` | Z, A, P, T, I, C, M |
| `Langlands.CuspidalJacquetMultiplicity.upperFunctor._proof_2` | Z, A, P, T, I, C, M |

#### Langlands.Representation.Classification.CuspidalJacquetMultiplicityProof

| Declaration | Roots |
| --- | --- |
| `Langlands.glCuspidalJacquetMultiplicityPrerequisites` | Z, S, A, P, T, I, C, M |

#### Langlands.Representation.Classification.CuspidalJacquetMultiplicityStatement

| Declaration | Roots |
| --- | --- |
| `Langlands.CuspidalJacquetMultiplicity.induced` | Z, S, A, P, T, I, C, M |
| `Langlands.CuspidalJacquetMultiplicity.induced._proof_1` | Z, S, A, P, T, I, C, M |
| `Langlands.CuspidalJacquetMultiplicity.oppositeJacquet` | Z, S, A, P, T, I, C, M |
| `Langlands.CuspidalJacquetMultiplicity.oppositeJacquet._proof_1` | Z, S, A, P, T, I, C, M |
| `Langlands.CuspidalJacquetMultiplicity.oppositeJacquet._proof_2` | Z, S, A, P, T, I, C, M |
| `Langlands.CuspidalJacquetMultiplicity.upperJacquet` | Z, S, A, P, T, I, C, M |
| `Langlands.CuspidalJacquetMultiplicity.upperJacquet._proof_1` | Z, S, A, P, T, I, C, M |
| `Langlands.GLCuspidalJacquetMultiplicityPrerequisitesStatement` | Z, S, A, P, T, I, C, M |
| `Langlands.GLCuspidalJacquetMultiplicityStatement` | Z, S, A, P, T, I, C, M |

#### Langlands.Representation.Classification.FiniteLengthProof

| Declaration | Roots |
| --- | --- |
| `Langlands.FiniteLengthAssembly.complementaryProjection` | L, A, G, U, R, T, I, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.FiniteLengthAssembly.complementaryProjection._proof_1` | L, A, G, U, R, T, I, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.FiniteLengthAssembly.complementaryProjection._proof_2` | L, A, G, U, R, T, I, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.FiniteLengthAssembly.complementaryProjection_surjective` | L, A, G, U, R, T, I, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.FiniteLengthAssembly.finiteLength_comp_surjective_iff` | L, A, G, U, R, T, I, D1, D2, D3, D4, D6, D8, D9, D11, D12, D13 |
| `Langlands.FiniteLengthAssembly.finiteLength_normalizedJacquet_of_refinements` | L, A, G, U, R, T, I, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.FiniteLengthAssembly.finiteLength_of_complement` | L, A, G, U, R, T, I, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.FiniteLengthAssembly.finiteLength_of_complement._simp_1_2` | L, A, G, U, R, T, I, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.FiniteLengthAssembly.finiteLength_of_complement._simp_1_3` | L, A, G, U, R, T, I, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.FiniteLengthAssembly.finiteLength_of_injective` | L, A, G, U, R, T, I, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.FiniteLengthAssembly.finiteLength_of_refinedJacquet` | L, A, G, U, R, T, I, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.FiniteLengthAssembly.finiteLength_of_surjective` | L, A, G, U, R, T, I, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.FiniteLengthAssembly.finite_of_surjective` | L, A, G, U, R, T, I, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.FiniteLengthAssembly.finite_summand` | L, A, G, U, R, T, I, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.FiniteLengthAssembly.isAdmissible_levi_subrepresentation` | L, A, G, U, R, T, I, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.FiniteLengthAssembly.isAdmissible_normalizedJacquet` | L, A, G, U, R, T, I, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.FiniteLengthAssembly.length_comp_surjective` | L, A, G, U, R, T, I, D1, D2, D3, D4, D6, D8, D9, D11, D12, D13 |
| `Langlands.FiniteLengthAssembly.length_eq_add_of_complement` | L, A, G, U, R, T, I, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.FiniteLengthAssembly.normalizedJacquet_eq_twist` | L, A, G, U, R, T, I, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.FiniteLengthAssembly.refinedJacquetMap_surjective` | L, A, G, U, R, T, I, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.FiniteLengthAssembly.refinement_measure_lt` | L, A, G, U, R, T, I, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.FiniteLengthAssembly.refinement_measure_lt._proof_1_1` | L, A, G, U, R, T, I, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.Parabolic.normalizedJacquetFiniteLength` | L, A, G, U, R, T, I, D1, D2, D3, D4, D8, D9, D11, D12, D13 |

#### Langlands.Representation.Classification.HeadQuotientCriterionProof

| Declaration | Roots |
| --- | --- |
| `Langlands.Classification.unequalIrreducibleQuotientKernels` | Z, S, A, P, T, I, C, M |
| `Langlands.Classification.unequalIrreducibleQuotientKernels._abel_1_1` | Z, S, A, P, T, I, C, M |

#### Langlands.Representation.Classification.HeadQuotientCriterionStatement

| Declaration | Roots |
| --- | --- |
| `Langlands.Classification.UnequalIrreducibleQuotientKernelsStatement` | Z, S, A, P, T, I, C, M |

#### Langlands.Representation.Classification.IrreducibleProductEmbedding

| Declaration | Roots |
| --- | --- |
| `Langlands.Classification.irreducibleProductEmbedding` | B, L, A, P, G, U, R, T, I, H, C, M, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.Classification.irreducibleProduct_embedding` | B, L, A, P, G, U, R, T, I, H, C, M, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.Classification.irreducible_supercuspidalProduct_embedding` | B, L, A, P, G, U, R, T, I, H, C, M, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.Classification.normalizedProduct_embedding_of_factor_embeddings` | B, L, A, P, G, U, R, T, I, H, C, M, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.FiniteTensor.externalMap_injective` | B, L, A, P, G, U, R, T, I, H, C, M, D1, D2, D3, D4, D8, D9, D11, D12, D13 |

#### Langlands.Representation.Classification.IrreducibleProductEmbeddingStatement

| Declaration | Roots |
| --- | --- |
| `Langlands.Classification.IrreducibleProductEmbeddingTheorem` | B, L, A, P, G, U, R, T, I, H, C, M, D1, D2, D3, D4, D8, D9, D11, D12, D13 |

#### Langlands.Representation.Classification.IrreducibleProductFiniteLengthProof

| Declaration | Roots |
| --- | --- |
| `Langlands.Classification.irreducibleProductFiniteLength` | B, L, A, P, G, U, R, T, I, H, C, M, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `_private.Langlands.Representation.Classification.IrreducibleProductFiniteLengthProof.0.Langlands.Classification.flattenSupercuspidalFactors` | B, L, A, P, G, U, R, T, I, H, C, M, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `_private.Langlands.Representation.Classification.IrreducibleProductFiniteLengthProof.0.Langlands.Classification.flattenSupercuspidalFactors_obj` | B, L, A, P, G, U, R, T, I, H, C, M, D1, D2, D3, D4, D8, D9, D11, D12, D13 |

#### Langlands.Representation.Classification.MultiplicityOneConstituentProof

| Declaration | Roots |
| --- | --- |
| `Langlands.Classification.mappedProductSplitting` | Z, S, A, P, T, I, C, M |
| `Langlands.Classification.multiplicityOneHeadCore` | Z, S, A, P, T, I, C, M |
| `Langlands.Classification.multiplicityOneHeadCore._proof_1_1` | Z, S, A, P, T, I, C, M |
| `Langlands.Classification.multiplicityOneSocleCore` | Z, S, A, P, T, I, C, M |
| `Langlands.Classification.multiplicityOneSocleCore._proof_1_1` | Z, S, A, P, T, I, C, M |
| `Langlands.Classification.smoothProduct` | Z, S, A, P, T, I, C, M |
| `Langlands.Classification.smoothProduct._proof_1` | Z, S, A, P, T, I, C, M |
| `_private.Langlands.Representation.Classification.MultiplicityOneConstituentProof.0.Langlands.Classification.isAtom_embedding_range` | Z, S, A, P, T, I, C, M |

#### Langlands.Representation.Classification.NormalizedProductFiniteLengthProof

| Declaration | Roots |
| --- | --- |
| `Langlands.Classification.ProductLengthProof.finiteLength_of_injective` | B, L, A, P, G, U, R, T, I, H, C, M, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.Classification.ProductLengthProof.finiteLength_of_range_eq_ker` | B, L, A, P, G, U, R, T, I, H, C, M, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.Classification.ProductLengthProof.finiteLength_of_surjective` | B, L, A, P, G, U, R, T, I, H, C, M, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.Classification.ProductLengthProof.irreducibleLevi` | B, L, A, P, G, U, R, T, I, H, C, M, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.Classification.ProductLengthProof.leviPreservation` | B, L, A, P, G, U, R, T, I, H, C, M, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.Classification.ProductLengthProof.selfMatching_of_finiteLength` | B, P, R, T, I, H, C, M |
| `Langlands.Classification.ProductLengthProof.step` | B, L, A, P, G, U, R, T, I, H, C, M, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.Classification.admissibleFiniteLengthProductPreservation` | B, P, R, T, I, H, C, M |
| `Langlands.Classification.normalizedInductionFiniteLength` | B, L, A, P, G, U, R, T, I, H, C, M, D1, D2, D3, D4, D8, D9, D11, D12, D13 |

#### Langlands.Representation.Classification.NormalizedProductFiniteLengthStatement

| Declaration | Roots |
| --- | --- |
| `Langlands.Classification.AdmissibleFiniteLengthProductPreservation` | B, P, R, T, I, H, C, M |
| `Langlands.Classification.IrreducibleProductFiniteLength` | B, L, A, P, G, U, R, T, I, H, C, M, D1, D2, D3, D4, D8, D9, D11, D12, D13 |

#### Langlands.Representation.Classification.OppositeCuspidalJacquetFiltrationProof

| Declaration | Roots |
| --- | --- |
| `Langlands.OppositeCuspidalJacquetFiltration.conjugatesLevi_reverse` | Z, S, A, P, T, I, C, M |
| `Langlands.OppositeCuspidalJacquetFiltration.isMinimalRepresentative_reverse_inv_mul` | Z, S, A, P, T, I, C, M |
| `Langlands.OppositeCuspidalJacquetFiltration.isMinimalRepresentative_reverse_mul` | Z, S, A, P, T, I, C, M |
| `Langlands.OppositeCuspidalJacquetFiltration.leviConjugation_symm_leviReverseEquiv` | Z, S, A, P, T, I, C, M |
| `Langlands.OppositeCuspidalJacquetFiltration.leviConjugation_symm_leviReverseEquiv._simp_1_1` | Z, S, A, P, T, I, C, M |
| `Langlands.OppositeCuspidalJacquetFiltration.leviConjugation_symm_leviReverseEquiv._simp_1_4` | Z, S, A, P, T, I, C, M |
| `Langlands.OppositeCuspidalJacquetFiltration.minimalReverseEquiv` | Z, S, A, P, T, I, C, M |
| `Langlands.OppositeCuspidalJacquetFiltration.minimalReverseEquiv._proof_1` | Z, S, A, P, T, I, C, M |
| `Langlands.OppositeCuspidalJacquetFiltration.minimalReverseEquiv._proof_10` | Z, S, A, P, T, I, C, M |
| `Langlands.OppositeCuspidalJacquetFiltration.minimalReverseEquiv._proof_2` | Z, S, A, P, T, I, C, M |
| `Langlands.OppositeCuspidalJacquetFiltration.minimalReverseEquiv._proof_3` | Z, S, A, P, T, I, C, M |
| `Langlands.OppositeCuspidalJacquetFiltration.minimalReverseEquiv._proof_4` | Z, S, A, P, T, I, C, M |
| `Langlands.OppositeCuspidalJacquetFiltration.minimalReverseEquiv._proof_5` | Z, S, A, P, T, I, C, M |
| `Langlands.OppositeCuspidalJacquetFiltration.minimalReverseEquiv._proof_6` | Z, S, A, P, T, I, C, M |
| `Langlands.OppositeCuspidalJacquetFiltration.minimalReverseEquiv._proof_7` | Z, S, A, P, T, I, C, M |
| `Langlands.OppositeCuspidalJacquetFiltration.minimalReverseEquiv._proof_8` | Z, S, A, P, T, I, C, M |
| `Langlands.OppositeCuspidalJacquetFiltration.minimalReverseEquiv._proof_9` | Z, S, A, P, T, I, C, M |
| `Langlands.OppositeCuspidalJacquetFiltration.oppositeJacquetReverseEquiv` | Z, S, A, P, T, I, C, M |
| `Langlands.OppositeCuspidalJacquetFiltration.oppositeJacquetReverseEquiv._proof_1` | Z, S, A, P, T, I, C, M |
| `Langlands.OppositeCuspidalJacquetFiltration.oppositeJacquetReverseEquiv._proof_2` | Z, S, A, P, T, I, C, M |
| `Langlands.OppositeCuspidalJacquetFiltration.reverseCoinvariantsEquiv` | Z, S, A, P, T, I, C, M |
| `Langlands.OppositeCuspidalJacquetFiltration.reverseCoinvariantsEquiv._proof_1` | Z, S, A, P, T, I, C, M |
| `Langlands.OppositeCuspidalJacquetFiltration.reverseCoinvariantsEquiv._proof_2` | Z, S, A, P, T, I, C, M |
| `Langlands.OppositeCuspidalJacquetFiltration.reverseCoinvariantsEquiv._proof_3` | Z, S, A, P, T, I, C, M |
| `Langlands.OppositeCuspidalJacquetFiltration.reverseCoinvariantsEquiv._proof_4` | Z, S, A, P, T, I, C, M |
| `Langlands.OppositeCuspidalJacquetFiltration.reverseCoinvariantsEquiv._proof_5` | Z, S, A, P, T, I, C, M |
| `Langlands.OppositeCuspidalJacquetFiltration.reverseCoinvariantsEquiv._proof_6` | Z, S, A, P, T, I, C, M |
| `Langlands.OppositeCuspidalJacquetFiltration.reverseJacquetEquiv` | Z, S, A, P, T, I, C, M |
| `Langlands.OppositeCuspidalJacquetFiltration.reverseJacquetEquiv._proof_1` | Z, S, A, P, T, I, C, M |
| `Langlands.OppositeCuspidalJacquetFiltration.reverseJacquetEquiv_mk` | Z, S, A, P, T, I, C, M |
| `Langlands.OppositeCuspidalJacquetFiltration.reversePermutation_lt_of_blockIndex_eq` | Z, S, A, P, T, I, C, M |
| `Langlands.OppositeCuspidalJacquetFiltration.reversePermutation_symm_index_strictMono` | Z, S, A, P, T, I, C, M |
| `Langlands.OppositeCuspidalJacquetFiltration.transportReverseEquiv` | Z, S, A, P, T, I, C, M |
| `Langlands.OppositeCuspidalJacquetFiltration.transportReverseEquiv._proof_1` | Z, S, A, P, T, I, C, M |
| `Langlands.OppositeCuspidalJacquetFiltration.transportReverseEquiv._proof_2` | Z, S, A, P, T, I, C, M |
| `Langlands.glOppositeCuspidalJacquetFiltrationFromUpper` | Z, S, A, P, T, I, C, M |

#### Langlands.Representation.Classification.OppositeCuspidalJacquetFiltrationStatement

| Declaration | Roots |
| --- | --- |
| `Langlands.GLOppositeCuspidalJacquetFiltrationFromUpperStatement` | Z, S, A, P, T, I, C, M |
| `Langlands.GLOppositeCuspidalJacquetFiltrationFromUpperStatement._proof_1` | Z, S, A, P, T, I, C, M |

#### Langlands.Representation.Classification.OppositeJacquetQuotientDetectionProof

| Declaration | Roots |
| --- | --- |
| `Langlands.oppositeJacquetQuotientDetection` | Z, S, A, P, T, I, C, M |

#### Langlands.Representation.Classification.OppositeJacquetQuotientDetectionStatement

| Declaration | Roots |
| --- | --- |
| `Langlands.OppositeJacquetQuotientDetectionStatement` | Z, S, A, P, T, I, C, M |

#### Langlands.Representation.Classification.ProductLeviMinimalIndex

| Declaration | Roots |
| --- | --- |
| `Langlands.ProductLeviMinimalIndex.blockIndex_eq_flatten` | A, U, R, D2, D3 |
| `Langlands.ProductLeviMinimalIndex.blockIndex_flatten_index` | A, U, R, D2, D3 |
| `Langlands.ProductLeviMinimalIndex.blockIndex_flatten_index_eq_iff` | A, U, R, D2, D3 |
| `Langlands.ProductLeviMinimalIndex.blockIndex_flatten_index_ne` | A, U, R, D2, D3 |
| `Langlands.ProductLeviMinimalIndex.blockIndex_flatten_index_ne._simp_1_1` | A, U, R, D2, D3 |
| `Langlands.ProductLeviMinimalIndex.blockWeyl_flatten_le` | A, U, R, D2, D3 |

#### Langlands.Representation.Classification.SegmentConstituentCentralCharacterProof

| Declaration | Roots |
| --- | --- |
| `Langlands.Classification.hasScalarCharacter_twist` | A |
| `Langlands.PadicField.TopologicalData.coe_determinantPowerCharacter_scalar` | A |
| `Langlands.PadicField.TopologicalData.hasScalarCharacter_segmentFactor` | A |

#### Langlands.Representation.Classification.SegmentConstituentStatement

| Declaration | Roots |
| --- | --- |
| `Langlands.Classification.SegmentSpecialConstituentExistence` | S, A, P, T, I, C |
| `Langlands.Classification.SegmentZelevinskyConstituentExistence` | Z, A, P, T, I, C, M |

#### Langlands.Representation.Classification.SegmentFullJacquetAdjunction

| Declaration | Roots |
| --- | --- |
| `Langlands.SegmentFullJacquet.exists_jacquet_to_tensor_ne_zero` | A |

#### Langlands.Representation.Classification.SegmentFullJacquetCentral

| Declaration | Roots |
| --- | --- |
| `Langlands.SegmentFullJacquet.blockTensor_blockScalarLevi` | A |
| `Langlands.SegmentFullJacquet.digits_sum_injective` | A |
| `Langlands.SegmentFullJacquet.digits_sum_injective._f` | A |
| `Langlands.SegmentFullJacquet.digits_sum_injective.match_1_1` | A |
| `Langlands.SegmentFullJacquet.leviConjugation_symm_blockScalarLevi` | A |
| `Langlands.SegmentFullJacquet.perm_eq_of_weightedSum_eq` | A |
| `Langlands.SegmentFullJacquet.segmentScalar` | A |
| `Langlands.SegmentFullJacquet.segmentScalar_eq` | A |
| `Langlands.SegmentFullJacquet.segmentScalar_injective` | A |
| `Langlands.SegmentFullJacquet.separatingEntries` | A |
| `Langlands.SegmentFullJacquet.transport_blockTensor_blockScalarLevi` | A |
| `Langlands.SegmentFullJacquet.uniformizerAbs` | A |
| `Langlands.SegmentFullJacquet.uniformizerAbs_lt_one` | A |
| `Langlands.SegmentFullJacquet.uniformizerAbs_pos` | A |

#### Langlands.Representation.Classification.SegmentFullJacquetSplitting

| Declaration | Roots |
| --- | --- |
| `Langlands.SegmentFullJacquet.blockPerm` | A |
| `Langlands.SegmentFullJacquet.blockPerm._proof_1` | A |
| `Langlands.SegmentFullJacquet.blockPerm_injective` | A |
| `Langlands.SegmentFullJacquet.exists_segmentJacquetFiltration` | A |
| `Langlands.SegmentFullJacquet.separatingScalar` | A |
| `Langlands.SegmentFullJacquet.separatingScalar_comm` | A |
| `Langlands.SegmentFullJacquet.transport_segment_separatingScalar` | A |

#### Langlands.Representation.Classification.SegmentHeadDecreasingSocle

| Declaration | Roots |
| --- | --- |
| `Langlands.Classification.IsIrreducibleSocle.nonempty_equiv_of_subrepresentation` | A |
| `Langlands.Classification.IsIrreducibleSocle.of_targetEquiv` | A |
| `Langlands.PadicField.TopologicalData.IsSegmentHead.isIrreducibleSocle_down` | A |
| `Langlands.PadicField.TopologicalData.IsSegmentHead.nonempty_equiv_of_down_jacquet_hom` | A |
| `Langlands.PadicField.TopologicalData.IsSegmentHead.nonempty_equiv_of_down_subrepresentation` | A |

#### Langlands.Representation.Classification.SegmentInductionAdmissibilityProof

| Declaration | Roots |
| --- | --- |
| `Langlands.Classification.segmentInductionAdmissibility` | Z, S, A, P, T, I, C, M |

#### Langlands.Representation.Classification.SegmentInductionAdmissibilityStatement

| Declaration | Roots |
| --- | --- |
| `Langlands.Classification.SegmentInductionAdmissibilityStatement` | Z, S, A, P, T, I, C, M |

#### Langlands.Representation.Classification.SegmentJacquetMultiplicityProof

| Declaration | Roots |
| --- | --- |
| `Langlands.Classification.segmentJacquetMultiplicityReduction` | Z, S, A, P, T, I, C, M |

#### Langlands.Representation.Classification.SegmentJacquetMultiplicityStatement

| Declaration | Roots |
| --- | --- |
| `Langlands.Classification.SegmentJacquetMultiplicityReductionStatement` | Z, S, A, P, T, I, C, M |
| `Langlands.Classification.SegmentJacquetMultiplicityReductionStatement._proof_1` | Z, S, A, P, T, I, C, M |

#### Langlands.Representation.Classification.SegmentJacquetReversal

| Declaration | Roots |
| --- | --- |
| `Langlands.Classification.segmentTensorDownReverseEquiv` | S, A, P, T, I, C |
| `Langlands.Classification.segmentTensorDownReverseEquiv._proof_1` | S, A, P, T, I, C |
| `Langlands.Classification.segmentTensorDownReverseEquiv._proof_2` | S, A, P, T, I, C |
| `Langlands.Classification.segmentTensorDownReverseEquiv._proof_3` | S, A, P, T, I, C |
| `Langlands.Classification.segmentTensorReverseEquiv` | Z, A, P, T, I, C, M |
| `Langlands.Classification.segmentTensorReverseEquiv._proof_1` | Z, A, P, T, I, C, M |
| `Langlands.Classification.segmentTensorReverseEquiv._proof_2` | Z, S, A, P, T, I, C, M |
| `Langlands.Classification.segmentTensorReverseEquiv._proof_3` | Z, S, A, P, T, I, C, M |
| `Langlands.Classification.segmentTensorReverseEquiv._proof_4` | Z, S, A, P, T, I, C, M |
| `Langlands.Classification.segmentTensorReverseEquiv._proof_5` | Z, A, P, T, I, C, M |
| `Langlands.Classification.segmentTensorReverseEquiv._proof_6` | Z, A, P, T, I, C, M |
| `Langlands.Classification.segment_opposite_upper_multiplicity_iff` | S, A, P, T, I, C |
| `Langlands.Classification.segment_upper_opposite_multiplicity_iff` | Z, A, P, T, I, C, M |

#### Langlands.Representation.Classification.SegmentJacquetSubobject

| Declaration | Roots |
| --- | --- |
| `Langlands.SegmentFullJacquet.exists_subrepresentationJacquetSeries` | A |
| `Langlands.SegmentFullJacquet.subrepresentationJacquet_isLeviQuasicuspidal` | A |
| `_private.Langlands.Representation.Classification.SegmentJacquetSubobject.0.Langlands.SegmentFullJacquet.subobjectJacquet_injective` | A |
| `_private.Langlands.Representation.Classification.SegmentJacquetSubobject.0.Langlands.SegmentFullJacquet.supercuspidalScalarCharacter` | A |

#### Langlands.Representation.Classification.SegmentSpecialConstituentExistenceProof

| Declaration | Roots |
| --- | --- |
| `Langlands.Classification.segmentSpecialConstituentExistence` | S, A, P, T, I, C |
| `_private.Langlands.Representation.Classification.SegmentSpecialConstituentExistenceProof.0.Langlands.Classification.segmentSpecialConstituentExistence_of_pointwise` | S, A, P, T, I, C |
| `_private.Langlands.Representation.Classification.SegmentSpecialConstituentExistenceProof.0.Langlands.Classification.specialSegmentQuotient_admissible` | S, A, P, T, I, C |

#### Langlands.Representation.Classification.SegmentTensorReversalProof

| Declaration | Roots |
| --- | --- |
| `Langlands.Classification.segmentFactors_associated_segmentFactorsDown` | Z, S, A, P, T, I, C, M |
| `Langlands.Classification.segmentFactors_associated_segmentFactorsDown._proof_1_1` | Z, S, A, P, T, I, C, M |
| `_private.Langlands.Representation.Classification.SegmentTensorReversalProof.0.Langlands.Classification.blockPermutationTensorEquiv` | Z, S, A, P, T, I, C, M |
| `_private.Langlands.Representation.Classification.SegmentTensorReversalProof.0.Langlands.Classification.blockPermutationTensorEquiv._proof_1` | Z, S, A, P, T, I, C, M |
| `_private.Langlands.Representation.Classification.SegmentTensorReversalProof.0.Langlands.Classification.blockPermutationTensorEquiv._proof_2` | Z, S, A, P, T, I, C, M |
| `_private.Langlands.Representation.Classification.SegmentTensorReversalProof.0.Langlands.Classification.blockPermutationTensorEquiv._proof_3` | Z, S, A, P, T, I, C, M |

#### Langlands.Representation.Classification.SegmentTensorStabilizerProof

| Declaration | Roots |
| --- | --- |
| `Langlands.Classification.cuspidalDatum_integralTwist_injective` | Z, S, A, P, T, I, C, M |
| `Langlands.Classification.segmentFactorsDown_isIrreducible_isLeviCuspidal` | Z, S, A, P, T, I, C, M |
| `Langlands.Classification.segmentFactorsDown_tensorStabilizer_count` | Z, S, A, P, T, I, C, M |
| `Langlands.Classification.segmentFactorsDown_tensorStabilizer_count._proof_1_1` | Z, S, A, P, T, I, C, M |
| `Langlands.Classification.segmentFactors_isIrreducible_isLeviCuspidal` | Z, S, A, P, T, I, C, M |
| `Langlands.Classification.segmentFactors_tensorStabilizer_count` | Z, S, A, P, T, I, C, M |
| `Langlands.Classification.segmentSupercuspidalFactor` | Z, S, A, P, T, I, C, M |
| `Langlands.Classification.segmentSupercuspidalFactor_datum_injective_nat` | Z, S, A, P, T, I, C, M |

#### Langlands.Representation.Classification.SegmentZelevinskyConstituentExistenceProof

| Declaration | Roots |
| --- | --- |
| `Langlands.Classification.segmentZelevinskyConstituentExistence` | Z, A, P, T, I, C, M |
| `_private.Langlands.Representation.Classification.SegmentZelevinskyConstituentExistenceProof.0.Langlands.Classification.segmentQuotient_admissible` | Z, A, P, T, I, C, M |
| `_private.Langlands.Representation.Classification.SegmentZelevinskyConstituentExistenceProof.0.Langlands.Classification.segmentZelevinskyConstituentExistence_of_pointwise` | Z, A, P, T, I, C, M |

#### Langlands.Representation.Classification.Segments

| Declaration | Roots |
| --- | --- |
| `Langlands.Classification.IsIrreducibleHead.of_equiv` | Z, A, P, T, I, C, M |
| `Langlands.Classification.IsIrreducibleSocle.of_equiv` | S, A, P, T, I, C |
| `Langlands.Classification.IsIrreducibleSocle.of_equiv._simp_1_1` | S, A, P, T, I, C |
| `Langlands.Classification.IsIrreducibleSubrepresentation.of_equiv` | A |
| `Langlands.GeneralLinear.BlockShape.uniform` | Z, S, A, P, T, I, C, M |
| `Langlands.GeneralLinear.BlockShape.uniform._proof_1` | Z, S, A, P, T, I, C, M |
| `Langlands.GeneralLinear.SupercuspidalClass.twist_congr` | Z, S, A, P, T, I, C, M |
| `Langlands.PadicField.TopologicalData.CuspidalDatum` | Z, S, A, P, T, I, C, M |
| `Langlands.PadicField.TopologicalData.CuspidalDatum.IsRepresentedBy` | Z, S, A, P, T, I, C, M |
| `Langlands.PadicField.TopologicalData.CuspidalDatum.casesOn` | Z, S, A, P, T, I, C, M |
| `Langlands.PadicField.TopologicalData.CuspidalDatum.cls` | Z, S, A, P, T, I, C, M |
| `Langlands.PadicField.TopologicalData.CuspidalDatum.mk` | Z, S, A, P, T, I, C, M |
| `Langlands.PadicField.TopologicalData.CuspidalDatum.mk.inj` | Z, S, A, P, T, I, C, M |
| `Langlands.PadicField.TopologicalData.CuspidalDatum.mk.injEq` | Z, S, A, P, T, I, C, M |
| `Langlands.PadicField.TopologicalData.CuspidalDatum.mk.noConfusion` | Z, S, A, P, T, I, C, M |
| `Langlands.PadicField.TopologicalData.CuspidalDatum.noConfusion` | Z, S, A, P, T, I, C, M |
| `Langlands.PadicField.TopologicalData.CuspidalDatum.noConfusionType` | Z, S, A, P, T, I, C, M |
| `Langlands.PadicField.TopologicalData.CuspidalDatum.rank` | Z, S, A, P, T, I, C, M |
| `Langlands.PadicField.TopologicalData.CuspidalDatum.rank_pos` | Z, S, A, P, T, I, C, M |
| `Langlands.PadicField.TopologicalData.CuspidalDatum.rec` | Z, S, A, P, T, I, C, M |
| `Langlands.PadicField.TopologicalData.CuspidalDatum.twist` | Z, S, A, P, T, I, C, M |
| `Langlands.PadicField.TopologicalData.CuspidalDatum.twist_twist` | Z, S, A, P, T, I, C, M |
| `Langlands.PadicField.TopologicalData.CuspidalDatum.twist_zero` | Z, S, A, P, T, I, C, M |
| `Langlands.PadicField.TopologicalData.IsSegmentHead` | S, A, P, T, I, C |
| `Langlands.PadicField.TopologicalData.IsSegmentSocle` | Z, A, P, T, I, C, M |
| `Langlands.PadicField.TopologicalData.IsSegmentSocle.isSegmentSubrepresentation` | A |
| `Langlands.PadicField.TopologicalData.IsSegmentSubrepresentation` | A |
| `Langlands.PadicField.TopologicalData.Segment` | Z, S, A, P, T, I, C, M |
| `Langlands.PadicField.TopologicalData.Segment.base` | Z, S, A, P, T, I, C, M |
| `Langlands.PadicField.TopologicalData.Segment.degree` | Z, S, A, P, T, I, C, M |
| `Langlands.PadicField.TopologicalData.Segment.length` | Z, S, A, P, T, I, C, M |
| `Langlands.PadicField.TopologicalData.Segment.length_pos` | Z, S, A, P, T, I, C, M |
| `Langlands.PadicField.TopologicalData.Segment.mk` | Z, S, A, P, T, I, C, M |
| `Langlands.PadicField.TopologicalData.Segment.rank` | Z, S, A, P, T, I, C, M |
| `Langlands.PadicField.TopologicalData.Segment.rank_pos` | Z, S, A, P, T, I, C, M |
| `Langlands.PadicField.TopologicalData.isSegmentHead_iff` | A |
| `Langlands.PadicField.TopologicalData.isSegmentSubrepresentation_iff` | A |
| `Langlands.PadicField.TopologicalData.segmentFactor` | Z, S, A, P, T, I, C, M |
| `Langlands.PadicField.TopologicalData.segmentFactors` | Z, S, A, P, T, I, C, M |
| `Langlands.PadicField.TopologicalData.segmentFactorsDown` | Z, S, A, P, T, I, C, M |
| `Langlands.PadicField.TopologicalData.segmentInduced` | Z, S, A, P, T, I, C, M |
| `Langlands.PadicField.TopologicalData.segmentInducedDown` | Z, S, A, P, T, I, C, M |
| `Langlands.PadicField.TopologicalData.segmentInducedDownIso` | Z, S, A, P, T, I, C, M |
| `Langlands.PadicField.TopologicalData.segmentInducedDownIso._proof_1` | Z, S, A, P, T, I, C, M |
| `Langlands.PadicField.TopologicalData.segmentInducedDownIsoOfRepresented` | Z, S, A, P, T, I, C, M |
| `Langlands.PadicField.TopologicalData.segmentInducedIso` | A |
| `Langlands.PadicField.TopologicalData.segmentInducedIso._proof_1` | A |
| `Langlands.PadicField.TopologicalData.segmentInducedIsoOfRepresented` | A |
| `Langlands.PadicField.TopologicalData.segmentInducedIsoOfRepresented._proof_1` | Z, S, A, P, T, I, C, M |
| `Langlands.PadicField.TopologicalData.supercuspidalClassRealPowerTwist_add` | Z, S, A, P, T, I, C, M |
| `Langlands.PadicField.TopologicalData.supercuspidalClassRealPowerTwist_zero` | Z, S, A, P, T, I, C, M |

#### Langlands.Representation.Classification.Supercuspidal

| Declaration | Roots |
| --- | --- |
| `Langlands.GeneralLinear.BlockShape.conjugateUnipotent` | B, L, Z, S, A, P, G, U, R, T, I, H, C, M, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.GeneralLinear.IsSupercuspidal` | B, L, Z, S, A, P, G, U, R, T, I, H, C, M, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.GeneralLinear.SupercuspidalClass` | Z, S, A, P, T, I, C, M |
| `Langlands.GeneralLinear.SupercuspidalRep` | B, L, Z, S, A, P, G, U, R, T, I, H, C, M, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.GeneralLinear.SupercuspidalRep.isoClass` | Z, S, A, P, T, I, C, M |
| `Langlands.GeneralLinear.SupercuspidalRep.isoClass_eq_iff` | Z, S, A, P, T, I, C, M |
| `Langlands.GeneralLinear.isSupercuspidal_of_equiv` | B, L, A, P, G, U, R, T, I, H, C, M, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.GeneralLinear.supercuspidalProperty` | B, L, Z, S, A, P, G, U, R, T, I, H, C, M, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.Jacquet.coinvariantsEquiv` | B, L, Z, S, A, P, G, U, R, T, I, H, C, M, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.Jacquet.coinvariantsEquiv._proof_1` | B, L, Z, S, A, P, G, U, R, T, I, H, C, M, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.Jacquet.coinvariantsEquiv._proof_2` | B, L, Z, S, A, P, G, U, R, T, I, H, C, M, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.Jacquet.coinvariantsEquiv._proof_3` | B, L, Z, S, A, P, G, U, R, T, I, H, C, M, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.Jacquet.coinvariantsEquiv._proof_4` | B, L, Z, S, A, P, G, U, R, T, I, H, C, M, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.Jacquet.coinvariants_subsingleton_iff` | B, L, Z, S, A, P, G, U, R, T, I, H, C, M, D1, D2, D3, D4, D8, D9, D11, D12, D13 |

#### Langlands.Representation.Classification.SupercuspidalContragredientAux

| Declaration | Roots |
| --- | --- |
| `Langlands.GeneralLinear.isSupercuspidal_iff_standard` | B, L, A, P, G, U, R, T, I, H, C, M, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.Jacquet.coinvariantsConjEquiv` | B, L, A, P, G, U, R, T, I, H, C, M, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.Jacquet.coinvariantsConjEquiv._proof_1` | B, L, A, P, G, U, R, T, I, H, C, M, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.Jacquet.coinvariantsConjEquiv._proof_2` | B, L, A, P, G, U, R, T, I, H, C, M, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.Jacquet.coinvariantsConjEquiv._proof_3` | B, L, A, P, G, U, R, T, I, H, C, M, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.Jacquet.coinvariantsConjEquiv._proof_4` | B, L, A, P, G, U, R, T, I, H, C, M, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.Jacquet.coinvariantsConjEquiv._proof_5` | B, L, A, P, G, U, R, T, I, H, C, M, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.Jacquet.coinvariantsConjEquiv._proof_6` | B, L, A, P, G, U, R, T, I, H, C, M, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.Jacquet.coinvariants_conj_subsingleton_iff` | B, L, A, P, G, U, R, T, I, H, C, M, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.eq_zero_of_smoothDual_annihilates` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.isIrreducible_iff_of_equiv` | B, L, Z, S, A, P, G, U, R, T, I, H, C, M, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.isIrreducible_of_smoothContragredient` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.isIrreducible_smoothContragredient_iff_of_bidual` | A, G, U, R, T, I, D1, D2, D3 |

#### Langlands.Representation.Classification.SupercuspidalSupport

| Declaration | Roots |
| --- | --- |
| `Langlands.SmoothRep.IsQuotient.isSubquotient` | Z, S, A, P, G, U, R, T, I, C, M, D1, D2, D3 |
| `Langlands.SmoothRep.IsSubquotient.of_iso_right` | B, L, Z, S, A, P, G, U, R, T, I, H, C, M, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.SmoothRep.IsSubrepresentation.isSubquotient` | Z, S, A, P, G, U, R, T, I, C, M, D1, D2, D3 |
| `Langlands.SmoothRep.hom_hom_injective` | B, L, Z, S, A, P, G, U, R, T, I, H, C, M, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.SmoothRep.hom_hom_surjective` | B, L, Z, S, A, P, G, U, R, T, I, H, C, M, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.SmoothRep.isSubquotient_iff_exists` | B, L, Z, S, A, P, G, U, R, T, I, H, C, M, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.SmoothRep.isSubquotient_iff_exists.match_1_1` | B, L, Z, S, A, P, G, U, R, T, I, H, C, M, D1, D2, D3, D4, D8, D9, D11, D12, D13 |

#### Langlands.Representation.Classification.SupercuspidalTwist

| Declaration | Roots |
| --- | --- |
| `Langlands.GeneralLinear.BlockShape.conjugateUnipotent_le_ker_determinant` | Z, S, A, P, T, I, C, M |
| `Langlands.GeneralLinear.BlockShape.determinant_eq_one_of_mem_unipotentSubgroup` | B, L, Z, S, A, P, G, U, R, T, I, H, C, M, D1, D2, D3, D4, D8, D9, D11, D12, D13 |
| `Langlands.GeneralLinear.SupercuspidalClass.twist` | Z, S, A, P, T, I, C, M |
| `Langlands.GeneralLinear.SupercuspidalClass.twist._proof_1` | Z, S, A, P, T, I, C, M |
| `Langlands.GeneralLinear.SupercuspidalClass.twist.match_1` | Z, S, A, P, T, I, C, M |
| `Langlands.GeneralLinear.SupercuspidalClass.twist_one` | Z, S, A, P, T, I, C, M |
| `Langlands.GeneralLinear.SupercuspidalClass.twist_twist` | Z, S, A, P, T, I, C, M |
| `Langlands.GeneralLinear.SupercuspidalRep.isoMk` | Z, S, A, P, T, I, C, M |
| `Langlands.GeneralLinear.SupercuspidalRep.twist` | Z, S, A, P, T, I, C, M |
| `Langlands.GeneralLinear.SupercuspidalRep.twist._proof_1` | Z, S, A, P, T, I, C, M |
| `Langlands.GeneralLinear.SupercuspidalRep.twistFunctor` | Z, S, A, P, T, I, C, M |
| `Langlands.GeneralLinear.SupercuspidalRep.twistFunctor._proof_1` | Z, S, A, P, T, I, C, M |
| `Langlands.GeneralLinear.isSupercuspidal_twist_iff` | Z, S, A, P, T, I, C, M |
| `Langlands.GeneralLinear.isSupercuspidal_twist_iff_of_le_ker` | Z, S, A, P, T, I, C, M |
| `Langlands.GeneralLinear.ker_determinant_le_ker_comp` | Z, S, A, P, T, I, C, M |
| `Langlands.GeneralLinear.ker_determinant_le_ker_mul` | Z, S, A, P, T, I, C, M |
| `Langlands.GeneralLinear.ker_determinant_le_ker_one` | Z, S, A, P, T, I, C, M |
| `Langlands.Jacquet.subsingleton_coinvariants_twist_iff` | Z, S, A, P, T, I, C, M |
| `Langlands.PadicField.TopologicalData.determinantPowerCharacter` | Z, S, A, P, T, I, C, M |
| `Langlands.PadicField.TopologicalData.isOpen_ker_determinantPowerCharacter` | Z, S, A, P, T, I, C, M |
| `Langlands.PadicField.TopologicalData.ker_determinant_le_ker_determinantPowerCharacter` | Z, S, A, P, T, I, C, M |
| `Langlands.PadicField.TopologicalData.supercuspidalClassRealPowerTwist` | Z, S, A, P, T, I, C, M |

#### Langlands.Representation.Classification.TwoFactorProductConstituentCommutativityProof

| Declaration | Roots |
| --- | --- |
| `Langlands.Classification.TwoFactorCommutativity.annihilator` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.annihilator._proof_1` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.annihilator._proof_2` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.annihilator._proof_3` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.annihilator._proof_4` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.annihilatorQuotientEquiv` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.annihilatorRestrict` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.annihilatorRestrict._proof_1` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.annihilatorRestrict._proof_10` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.annihilatorRestrict._proof_11` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.annihilatorRestrict._proof_2` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.annihilatorRestrict._proof_3` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.annihilatorRestrict._proof_4` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.annihilatorRestrict._proof_5` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.annihilatorRestrict._proof_6` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.annihilatorRestrict._proof_7` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.annihilatorRestrict._proof_8` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.annihilatorRestrict._proof_9` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.annihilatorRestrict_eq_zero_iff` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.annihilatorRestrict_surjective` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.annihilator_antitone` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.annihilator_bot` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.annihilator_top` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.canonicalTopology` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.dualSeries` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.dualSeries._proof_1` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.dualSeries._proof_2` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.dualSeries._proof_3` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.dualSeries._proof_4` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.dualSeries_graded` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.gelfandKazhdan_inverseTranspose` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.gelfandKazhdan_inverseTranspose._proof_1_1` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.haveSameJordanHolderFactors_dual_comp` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.haveSameJordanHolderFactors_of_comp` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.isAdmissible_of_isIrreducible` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.isSmooth_quotientRep` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.isSmooth_toRepresentation` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.productSmoothDual` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.quotientProjection` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.quotientProjection._proof_1` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.quotientRepEquiv` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.quotientRepEquiv._proof_1` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.quotientRepEquiv._proof_2` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.quotientRepEquiv._proof_3` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.quotientRepEquiv._proof_4` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.quotientRepEquiv._proof_5` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.subrepInclusion` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.subrepInclusion._proof_1` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorCommutativity.subrepInclusion._proof_2` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.adjacentSwap_zero_eq_revPerm` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.adjacentSwap_zero_eq_revPerm._proof_1` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.adjacentSwap_zero_eq_revPerm._proof_1_1` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.twoFactorProductConstituentCommutativity` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.twoFactorProductConstituentCommutativity_of_finiteLength` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.twoFactorProductConstituentCommutativity_of_finiteLength._proof_1_1` | A, G, U, R, T, I, D1, D2, D3 |
| `_private.Langlands.Representation.Classification.TwoFactorProductConstituentCommutativityProof.0.Langlands.Classification.TwoFactorCommutativity.gelfandKazhdanOfTopology` | A, G, U, R, T, I, D1, D2, D3 |

#### Langlands.Representation.Classification.TwoFactorProductConstituentCommutativityStatement

| Declaration | Roots |
| --- | --- |
| `Langlands.Classification.TwoFactorProductConstituentCommutativity` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorProductConstituentCommutativity._proof_1` | A, G, U, R, T, I, D1, D2, D3 |
| `Langlands.Classification.TwoFactorProductConstituentCommutativity._proof_2` | A, G, U, R, T, I, D1, D2, D3 |

#### Langlands.Representation.Classification.UpperCuspidalJacquetMultiplicityProof

| Declaration | Roots |
| --- | --- |
| `Langlands.glUpperCuspidalJacquetMultiplicityFromFiltration` | Z, S, A, P, T, I, C, M |

#### Langlands.Representation.Classification.UpperCuspidalJacquetMultiplicityStatement

| Declaration | Roots |
| --- | --- |
| `Langlands.GLUpperCuspidalJacquetMultiplicityFromFiltrationStatement` | Z, S, A, P, T, I, C, M |

#### Langlands.Representation.Classification.UpperJacquetSubrepresentationDetectionProof

| Declaration | Roots |
| --- | --- |
| `Langlands.upperJacquetSubrepresentationDetection` | Z, S, A, P, T, I, C, M |

#### Langlands.Representation.Classification.UpperJacquetSubrepresentationDetectionStatement

| Declaration | Roots |
| --- | --- |
| `Langlands.UpperJacquetSubrepresentationDetectionStatement` | Z, S, A, P, T, I, C, M |

### Classification-origin source fingerprints

Each row gives SHA-256 for the actual defining module and its paired Markdown
at the audit snapshot; hashes are not publication or proof receipts.

| Module | Lean SHA-256 | Markdown SHA-256 |
| --- | --- | --- |
| `Langlands.Representation.Classification.CanonicalConstituents` | `3d928c04a8b8f9a8dea9eb52f4b202d303a8f474372e8fe1b4b7de0ced9e1d97` | `7c2c55ccb0c35c34405d4c61bedb253d8a9f088da308585eade4ecdd096e616e` |
| `Langlands.Representation.Classification.CommonImageMultiplicityOneProof` | `c19e8c64cb3c8d6228761b2aed69ebaa50fe285844b8ffb3ad02e1fbcb395edd` | `22d5cf398213638f61a0d4b194c569eba5d85b7b77c1b3aada8a21f07a16325a` |
| `Langlands.Representation.Classification.CommonImageMultiplicityOneStatement` | `d00f9b03aa344e2f5ee39b54e86df05a5d4ccf18597bb6ade809bc18178c80fd` | `e85404d911a0c5caa930cddb92844d3d00ceeb84c5276e739080508fbbf8132b` |
| `Langlands.Representation.Classification.ConstituentRelations` | `deb56924ecebd5c12a875ecf69f4b4960801e3ed6df5d8fe013c9a303cd58721` | `47047bc2be3ee74e4be6e5077319f06c463d7e446b586f7b3d4b58e016d8641d` |
| `Langlands.Representation.Classification.Cosocle` | `8b7168578343ff57b4b156b368cb6766bc72c7846d38e0b7a024e6c170269e2d` | `f5449414ae2bcd42f75b05e3a6b4be70ef88f3eaecf7a7d3488ad89fd271ed4c` |
| `Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof` | `91598de302fedc32f669d5e32036bb2993e70063c2db308b93398e38bd14aff5` | `59e14ef1fd2d7fa36f55558ea272239aff9a2b065bc2e3497074c64335c85aa0` |
| `Langlands.Representation.Classification.CuspidalIntegralTwistFreenessStatement` | `e1203547aab90cb91ae335176fbcf4f57b6fc19759c4ae12b04f85df64f9d0f9` | `96af8f0c54cfaafd99d4987f50ad41201e171bbd67e4124ac305eaa694acfb5e` |
| `Langlands.Representation.Classification.CuspidalJacquetFunctorExactnessProof` | `51acc4c02231a68ecefa28809c73b0ee34584dc46cd7d90c38dc83ed5856e1b4` | `66fd1ba3b50e7825a5d6ae61d77372e8129d66617fd922150f3cbc8019ddb493` |
| `Langlands.Representation.Classification.CuspidalJacquetFunctors` | `59bc704c7b39caa770aecfd1d65703c9e36593c0d0ba2cca1a9f670bdc2315f3` | `938f245d6f2f2f3374158f9025bf26cc3abd98fbe53d9333867d84ff63520916` |
| `Langlands.Representation.Classification.CuspidalJacquetMultiplicityProof` | `e0d80552aa3eb3dbd82452be0f55ecd7c3be3d0704cd0f8d4c9da43a47fb7397` | `b69555e4568163c20a97bb96eee35137038a4552b42a49168b7d4c8bb9a1233d` |
| `Langlands.Representation.Classification.CuspidalJacquetMultiplicityStatement` | `0adb72d788d2ac848e510f8a6e016f2a888cdf95e65f023d60f67c248421ff1e` | `b5395e1f4a3143c89fb8ab794b7c2ae12a0832aa28b98074edb6fb1f00a4f6d0` |
| `Langlands.Representation.Classification.FiniteLengthProof` | `a43bc7e1a097f6441ad180310c1301e5a22166eacc18c325a47d2baf129baaa8` | `2f084b7d91939088137a46eac5d6cfef1ee00473d754bd54bab7bc3030179641` |
| `Langlands.Representation.Classification.HeadQuotientCriterionProof` | `13a22ea328fdbf7e4f6ee6f4a8f5a62299744f8127da09614103428b4f74bcb7` | `57480d86304c63944d9529098e9c6ad70868712c86a186b8d5d6856fdd6d49cc` |
| `Langlands.Representation.Classification.HeadQuotientCriterionStatement` | `3d3dea109a39cc4d38739f8d188c6949dd5ec3c94b28f916ee23978769705b67` | `1d9f840e11b727dbbf6a2bdc56a9ca33a91f8b0af6dfb6dba22c6948e2594f5d` |
| `Langlands.Representation.Classification.IrreducibleProductEmbedding` | `0a999855052b3dbbaceaed17741d151b354627faf3004049c9ce58232ef00f4e` | `2c581f724e233c558b874480ef5d4c40199dc81a763f8ddd12590787c7330f0a` |
| `Langlands.Representation.Classification.IrreducibleProductEmbeddingStatement` | `15aae2c06f59c603bdbb162faad33d14fadaf462bb14429dd374b21492a052d5` | `a6a9843c1f66aa4d2e83595ec35a40315c3a84d8c30d7d0b03924e578831b709` |
| `Langlands.Representation.Classification.IrreducibleProductFiniteLengthProof` | `a33e3cec646613d2850af65b070ce61e1bac5f15cb2f27e5a20bf7939286e4c1` | `2dab0bc3ddb209af152cf88ec9a77551618eff1bcb77f6fee8df23e26fc3c0f1` |
| `Langlands.Representation.Classification.MultiplicityOneConstituentProof` | `17e938dded92d7d335b7ff15e4ebbc8db723d8b5712d2b40d629a91c9ae8d1c3` | `b80ad7ca453bebf8c20a10a5d719482df81eab0b7080bdf035820bec7520c40c` |
| `Langlands.Representation.Classification.NormalizedProductFiniteLengthProof` | `6dbdffc815e2d8c4020e68d71e25f1a79d0251edf9512201dc027af1d717072a` | `9609c9d7b5ad6e66247a1727ae2f4edb3f34f76bcd4e14120379fa2bd4db7c60` |
| `Langlands.Representation.Classification.NormalizedProductFiniteLengthStatement` | `ad77de724ec74c75a6fd349b61119f6fa106adef2bf204f28d26c87c70ccf6b5` | `e428d95b452fadae47625d55cdd3b3ce89fc44292547de8f57c3631e982830d5` |
| `Langlands.Representation.Classification.OppositeCuspidalJacquetFiltrationProof` | `7b8fd819e58731644234bf647893a399142238a61e40b0e01363744488450e9d` | `da3543bdaff230cc49f8001d1445d0d5729310be08e0eb3f8f0bdfabe9fe9f59` |
| `Langlands.Representation.Classification.OppositeCuspidalJacquetFiltrationStatement` | `5f94c4af13a640d09c7386afdfd849091e5bcee7739cec5107b82c524f5b9ad9` | `ec158e2534775abf8ad13d1a853db30589c59db9075df568f394717924b5440b` |
| `Langlands.Representation.Classification.OppositeJacquetQuotientDetectionProof` | `ea19caf22aca2400667311132f0bfe0fdf8d721dd9b1d70237e6c64dbfe0d055` | `5d5e2e80e0f3ac1d60e3ae2da3a6822d04a2eeef2a9d57a098b328683659a7c6` |
| `Langlands.Representation.Classification.OppositeJacquetQuotientDetectionStatement` | `143d5cf5534d4b4d0bf8d48821a1347615da4b48d354e5423a508ece1fc43558` | `d87c5f0e0f0fe18fa0b09ae3be6d7a5786f4583683209d1ced3463b989d2d61c` |
| `Langlands.Representation.Classification.ProductLeviMinimalIndex` | `fdb04db09d41da5db0b936d8e314e78c2f6ce90926079eb4dbd1b1010de9547d` | `b5fc01b29963c53615445f0411d50ee5e77c0619f4a6c85a9105857d0149a20a` |
| `Langlands.Representation.Classification.SegmentConstituentCentralCharacterProof` | `beff1d4b955f46f2344edad55ffd47e39e8dfc5fc7c13871289647baeebc9f38` | `e318d93a52d2915a2318fe4142e5d0ba2167c37aa557b49ae2fbe25e75dbc769` |
| `Langlands.Representation.Classification.SegmentConstituentStatement` | `7639f8816b3e05d00203be1a25093811a5b7d6b0b02026ade3484aa2b08c4ff3` | `cfed4fcab0337dc2870c97272b78fb18ab80759fe8efc71a83ec3bc5c2400aa3` |
| `Langlands.Representation.Classification.SegmentFullJacquetAdjunction` | `f64361996c065f48a5c818f48d12fb76c6fb8eb42286cd1e4253e38323145a3b` | `bbc8c6b6fffe9ba1a4d1baa4f160caad6a75f2e532f68ef72f9155a6bdce85cf` |
| `Langlands.Representation.Classification.SegmentFullJacquetCentral` | `e3eebfc47b743204c7942c28bf6fada12d888b744985b5429e4060757ee0b77a` | `01ee0c72ac4125faa9c45248886d63978112ec42c3b69a07ef468c4a42c7bffc` |
| `Langlands.Representation.Classification.SegmentFullJacquetSplitting` | `db6fbd8c8496d561cc9cc4b5f6a4867764d4f8b2eb3026b086c12dbb4671fdff` | `0c7050e5a1c2f12b43121b16cd326f3b71c621ff21845c912cb0080d7a5b5c35` |
| `Langlands.Representation.Classification.SegmentHeadDecreasingSocle` | `5a144a5a5bbaf5e3464c6c8fa264f560c8ccca2e233534b57cf879c7f881ca3d` | `b3e773614f10caeb0ed72cf6b189cb4fdf24a0b476075b52652b1f845b128354` |
| `Langlands.Representation.Classification.SegmentInductionAdmissibilityProof` | `7fe3133e14ecc702fa2d1b26d05f1dc888ac8f645ac99a01740a7b434c2388bd` | `3d7c2f74c8e2cec8e837c210abacf6ebe853ff92b01da2731fb0edea0a64ae89` |
| `Langlands.Representation.Classification.SegmentInductionAdmissibilityStatement` | `82cf43a5f958647f4cbaf777ebb1cf38ee70199cf8e84daf61adb06fb04d51ad` | `30f433bb37fad406fc7422a2c9e830f5a86c4c7e1749f7259e54db9b764ac07b` |
| `Langlands.Representation.Classification.SegmentJacquetMultiplicityProof` | `ae261452804dfd04d3fdd31635162c01f9c3032ca365e24ae3bb159962f2b3ff` | `fe30119b9b78ac01f1dae0687a64e1f0d763ee9f1facee0d911a1082ce851797` |
| `Langlands.Representation.Classification.SegmentJacquetMultiplicityStatement` | `43dea26db7a0de03a5c49bc4bfcecdf67c7af0beebf3b8646880fc744c972868` | `dd1d12b483499f31228ca6aecd26543958b358e6fe9a494f4fbcb168a485f405` |
| `Langlands.Representation.Classification.SegmentJacquetReversal` | `20c69d78ba4b390dfc2c6d1e48ddccc5253d0193c2bfd2ba68f197032186cb15` | `34ded6da688d90fda3533c72d12b888652ca46ca5f953b035cec9686f59a81be` |
| `Langlands.Representation.Classification.SegmentJacquetSubobject` | `fd7c405f64e2743f1768e15029f5342b22a713c7c692e49295b7b7af69a1b20c` | `15606ab3f5ca51f8e5938cf1902d7fe0c94e1f5e09700ea10203a9bbbded185a` |
| `Langlands.Representation.Classification.SegmentSpecialConstituentExistenceProof` | `7e3e0f5bf561338acb3a63a46b254dd69eb3bd1dc4ab2e668d1ac09831bc5271` | `84bb2cffd76a823dc2a2ff2d4670b36e8852feb1ac8a2b001952c6959a781738` |
| `Langlands.Representation.Classification.SegmentTensorReversalProof` | `8763c7766b2e1df50f3614d1b3bf1888e5d47d36ab146f6a4723821343fe31be` | `a6ac8fd23324c240f56e5f3a7f63c8a431587dc533c675f352e23f74b84c4e96` |
| `Langlands.Representation.Classification.SegmentTensorStabilizerProof` | `85f13c35cac5b5f1247d8ff9282ade2b2fc6607cf317a15c56d86f72d4efc108` | `53ccf2663d85ba3e8476d40a45606d67bcff79c77fc6bef14ed59cba198bae48` |
| `Langlands.Representation.Classification.SegmentZelevinskyConstituentExistenceProof` | `e4ac2f9b66c118ddb660a7e13517e57e919e0381f4ab00eb9d55f2b13ef7194d` | `9963bc36b2161698864488a6ad3389562bd66561d469ced1227d307dbae72e88` |
| `Langlands.Representation.Classification.Segments` | `b09e9fdc1445e6fabe2a923a896c5f0f5675fe31fd0f8adc7fe351e98346edda` | `ba5682b3f3e143817d63133383fc3b05469cc48f05ed20c9aaee5344b272189f` |
| `Langlands.Representation.Classification.Supercuspidal` | `c13ba8ffad11de2c3b2861c4afc385be2663b3e76963d5e89807ba92c753f9f1` | `b46be626d8b287d7011f47c8ee66cc8e22620efb6a94c0086486d75ee212f09d` |
| `Langlands.Representation.Classification.SupercuspidalContragredientAux` | `b073fcfb57858c9a80029ebb148aabf16597a953d75c04dfd8967652908e3713` | `4a75bb9194c2ae7d0bbb31a1cc2b1e1668b9ea28ea953faa683d361bc979ae29` |
| `Langlands.Representation.Classification.SupercuspidalSupport` | `4680302c6b5ad320893b38e1787f11739aca615cc8f44b38021824423089990a` | `7f8064dc6500a598053a8dcbf6dfba8fdc1a6413b49ccb4cabc3267eae4e6e1f` |
| `Langlands.Representation.Classification.SupercuspidalTwist` | `057738fc8e7b1aeaee62186dec29b412049a22f15ac7f71ff7759eaea1bf2b58` | `f3ed69bf8418af1014b430c58193a8bce4797cd18e72673207d7f0164d695fa6` |
| `Langlands.Representation.Classification.TwoFactorProductConstituentCommutativityProof` | `a83cefa584ef099bf5b2dde1a7e52a3f0d121edb93d930a946baea5581812e25` | `35a05fd54cdfb1a3ef1d330a28c00684a2484c9d325679cc3d2756f81b931d5f` |
| `Langlands.Representation.Classification.TwoFactorProductConstituentCommutativityStatement` | `fe8eaf801109f6e00a6c7a68bc359fb8f55860904c4c715e8ba5a4a9f2ead79e` | `3bf79e3f4f181013854ab422f856b4b3442a22672482674f2c9a9391d915329e` |
| `Langlands.Representation.Classification.UpperCuspidalJacquetMultiplicityProof` | `cbbd967e71957e75e14d6747a18f66ee183e21617bf6aa320eddd9f12ab66072` | `0744ae52ae8cef5ddbb588f84717b3597a21ce9ceb57d94a42006defd7cf49bf` |
| `Langlands.Representation.Classification.UpperCuspidalJacquetMultiplicityStatement` | `f76d23a3e7ee4709bb0c64fb185b9591691508651406212229ac61a4e38c87da` | `a57bd3eaf46a2ec32b6329974d8b75a0675d49aa778a4d39fd4c13d76bb4206a` |
| `Langlands.Representation.Classification.UpperJacquetSubrepresentationDetectionProof` | `eeb8997bfcd15e464f63276e23df7526901bb6c2bd1d49c8d54a750f144faebe` | `edd3d0a16c21109ca201fc3916d4c6d1312d596ae415082650ef04ab0231ac4f` |
| `Langlands.Representation.Classification.UpperJacquetSubrepresentationDetectionStatement` | `9c3ad79e11c4c0658d2ca1e492de1bf13c4bf0d0ad573e20106e6be86449eb82` | `595be7b36e77fd008b701d88e144a123021152d7e64d900e41a0c45327989739` |
