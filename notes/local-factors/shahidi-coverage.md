# Shahidi local coefficients for GL_m × GL_n: declaration coverage

Author: Worker 11, for task `8e607558-e8b2-49f9-a778-9da15e3f4ac1`
(Shahidi local coefficients and the Theorem 5.1 comparison). The task's
executors are Worker 99 and Worker 11. This note lists the published Lean
declarations for the five scope items of that task and the Library modules
they depend on. It also records the source gaps that the formalization
retains and the open proof obligations.

The source is F. Shahidi, *Fourier transforms of intertwining operators and
Plancherel measures for GL(n)*, Amer. J. Math. 106 (1984) 67–111, registered
as `shahidi-1984-fourier`, SHA256
`a10d5c605d94d4e85d0e5f453d6a8c233d91e3cb60d538f430d8ad900cbb6b29`. The
registered file is a scan without a text layer. Page numbers below are
printed pages; printed page `p` is PDF page `p − 65`.

Every module below is in `Langlands/Representation/Shahidi/` unless another
path (relative to `Langlands/`) is given, and its paired Markdown gives exact
locators and interpretive choices. The eight-character IDs are prefixes of
the accepted candidate IDs; "Source records" below gives the full IDs. Every
declaration named here is in Library commit
`d1e92cc3fedd601726630b19e4e6d1a9dc84b2cd`. Statements are
proposition definitions (`def … : Prop`). Publishing a statement accepts its
formulation, not its truth, and no statement is an axiom or a structure
field.

Items 1–5 below describe the p-adic formalization. "General non-archimedean
local fields" describes the parallel statements over every non-archimedean
local field, including positive characteristic.

## Item 1: the induced representations

- `Induction` (`47450e09`). The generic layer, in `Langlands.Shahidi`, is
  `source` and `target`, built from the Library's normalized block induction
  (`Langlands.Representation.Induction.BlockFactors` and `.Parabolic`). The
  p-adic layer, in `Langlands.PadicField.TopologicalData`, has two
  representations of `GL_{m+n}(F)`. `shahidiSource` is `I(s, π₁ ⊗ π₂)`, the
  representation on the carrier `ShahidiSourceSpace`. `shahidiTarget` is
  `I(−s, π₂ ⊗ π₁)`, the representation on the carrier `ShahidiTargetSpace`.
  Both have type `Representation ℂ (GeneralLinear (m + n) F.Carrier) _`.
  `shahidiSourceEval` and `shahidiTargetEval` give the value of a vector at a
  group element. The `canonicalShahidi…` versions use
  `F.canonicalTopologicalData`.
- Supporting matrix geometry: `TwoBlocks` (`7b5082dd`: `twoBlocks`,
  `twoBlockLeviEquiv`) and `Geometry` (`2f4cc677`: `blockWeyl` for
  `w_{m,n}`, `upperRadical`, `intertwiningUnipotent` and
  `intertwiningRadical` for `U'`).

## Item 2: the intertwining integral

- `IntertwiningIntegral` (`2cfcab68`): `intertwiningOperator`, the integral
  `∫_{U'} f(w u' g) du'` on its actual convergence domain, for functions on
  the group.
- `IntertwiningCovariance` (`30da169f`): `rectangularConj` and the
  `twoBlockLeviSwap` covariance computation.
- `IntertwiningInduced` (`aefca3d1`): `intertwiningInduced` on the induced
  spaces, together with the tensor bridge `pairSplit`, `pairSwap` and
  `pairFlip`.
- `IntertwiningPadic` (`bd52f1c2`): `shahidiIntertwining`, the p-adic operator
  `A(s, π, w_{m,n})` from `shahidiSourceDomain` to `ShahidiTargetSpace`, with
  `shahidiIntertwining_eval` and the equivariance
  `shahidiIntertwining_shahidiSource`.
- `IntertwiningStatements` (`ae96ae41`, statements):
  `ShahidiIntertwiningConvergenceStatement` (convergence for `Re s` large) and
  `ShahidiIntertwiningRationalityStatement` (rational continuation in
  `q^{−s}`), from page 72.

## Item 3: the Jacquet functional

- `Characters` (`9245d21d`): the characters `χ` and the kernels of (0.2) on
  the rectangular radicals.
- `JacquetIntegral` (`7a2afec1`): `HasJacquetIntegral` and
  `HasSwappedJacquetIntegral`, the integrals of `λ^s_π` and `λ^{−s}_{π'}`.
  They use the stabilization of page 78 (the published `HasStableIntegral`:
  the integral over compact open subgroups is eventually constant), not
  absolute convergence. They also give the stable functionals
  `jacquetStableFunctional` and `swappedJacquetStableFunctional` on their
  domains.
- `JacquetInduced` (`90ab353f`, Worker 99): the Jacquet functionals on the
  induced spaces as graphs, `IsSourceJacquetFunctional` and
  `IsTargetJacquetFunctional` with proved uniqueness, generically and in the
  p-adic layer (`shahidiSourceJacquetFunctional`,
  `shahidiTargetJacquetFunctional` and their stable domains). It also proves
  `exists_isSourceJacquetFunctional_iff` and
  `exists_isTargetJacquetFunctional_iff`: a total functional exists exactly
  when the stable domain is everything.
- `JacquetStatements` (`5417cfb5`, Worker 99, statements):
  `ShahidiJacquetStabilizationStatement`,
  `ShahidiInducedWhittakerMultiplicityOneStatement`,
  `ShahidiLocalCoefficientExistenceStatement` (existence of a rational
  coefficient for fixed Haar measures) and their conjunction
  `ShahidiJacquetAndCoefficientStatement`. Proved there:
  `existsUnique_inverseScalar_of_multiplicityOne`, the inverse scalar of an
  intertwiner under multiplicity one.

## Item 4: the local-coefficient relation

- `LocalCoefficient` (`70da5bf3`): the generic relation `IsLocalCoefficient`,
  which keeps the inverse convention `λ^{−s}_{π'}(A f) = C^{−1} λ^s_π(f)` of
  (0.3). Its uniqueness, reciprocity and rescaling lemmas are proved.
- `LocalCoefficientPadic` (`f6fa7ed7`): on the actual p-adic spaces,
  `pairFunctional λ₁ λ₂` is `λ₁ ⊗ λ₂`;
  `IsShahidiLocalCoefficientFor ψ μ μJ μJ' λ₁ λ₂ C` is the relation for fixed
  functionals; and `IsShahidiLocalCoefficient π₁ π₂ ψ μ μJ μJ' C` requires
  nonzero standard Whittaker functionals and the relation for all of them.
  Proved here: `IsShahidiLocalCoefficient.unique`, the rescaling lemma
  `IsShahidiLocalCoefficientFor.smul`, the transfer
  `IsShahidiLocalCoefficientFor.isShahidiLocalCoefficient` under explicit
  multiplicity-one hypotheses, and the literal form of (0.3)
  `satisfiesLocalCoefficientEquation_shahidiSourceEval_iff`.

## Item 5: Theorem 5.1 and the measures

- `LocalCoefficientGammaStatement` (`71c0374f`, statement):
  `Langlands.Shahidi.LocalCoefficientGammaStatement`, Theorem 5.1 (page 103)
  for generic `π₁`, `π₂`, with the pages 75–77 normalization. Here `ω` is the
  central character of `π₂`, `ν` is the self-dual measure for `ψ`, and `ψ`
  has conductor exponent `0`. Both conjuncts use
  `IsLocalCoefficientGammaComparison`: `IsShahidiLocalCoefficient` and
  `IsPadicSymmetricGammaFactor F ψ ν π₁ (smoothContragredient π₂)` hold with
  `C = ω(−1)^{m+1} • G`. The all-rank conjunct (ranks `m + 1`, `n + 1`) uses
  product measures, with the same scalar Haar measure for both Jacquet
  functionals. In the equal-rank conjunct (ranks at least two) the measures
  are `d.intertwining`, `d.jacquet` and `d.swappedJacquet` of an
  `EqualRankMeasureData` `d` satisfying `IsEqualRankGeometricNormalized`
  (with the normalized absolute value). That predicate is the
  representation-independent part of the pages 75–77 normalization, and
  `isEqualRankMeasureNormalized_iff` proves that the full normalization is the
  predicate plus the item-1 pairing equations. Also proved:
  `blockWeyl_inv_mul_upper_equalRanks`, so at equal ranks both Jacquet
  integrals are page 78's integrals over `V`.
- The equal-rank normalization of pages 75–77 is
  `IsEqualRankMeasureNormalized` in `EqualRankMeasures` (`16861257`). Its
  ingredients are in `PairingMeasure` (`9d1b7152`), `KirillovMeasure`
  (`5246a0b7`), `QuotientTransport` (`d2d3463c`), `UnipotentProduct`
  (`b29f3a27`), `CompactMeasures` (`5938d04b`), `IwasawaMeasures`
  (`b0d37ad1`), `MeasureTransport` (`d8858c8f`), `CoordinateMeasures`
  (`9445b4a0`) and `RadicalMeasures` (`46fe4c2c`). `Signs` (`31e606ca`) has
  the alternating diagonal `ε_m` of pages 80 and 102–103.

## Library dependencies

These items use the following published modules outside
`Representation/Shahidi`, at the same commit:

- `Representation/RankinSelberg/PadicPairFactors`:
  `IsPadicSymmetricGammaFactor` and its uniqueness lemma.
- `Representation/RankinSelberg/Measures`: `rectangularMeasure`.
- `Representation/Whittaker/GeneralLinear`: `IsGeneric` and `glFunctionals`.
- `Representation/Classification/ConstituentCompatibility`:
  `HasGLCentralCharacter`.
- `Representation/Smooth/Contragredient/Definitions`:
  `smoothContragredient`.
- `LocalFactor/Abelian/Padic`: `SelfDualHaar`.
- `HarmonicAnalysis/Conductor`: `additiveConductor`.
- `HarmonicAnalysis/StableIntegral`: `HasStableIntegral`.

All the modules are pinned to Lean environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`.

## Field scope

The generic layers work over a field `F` with a ring topology and an
absolute value `abv` whose norm-one set is open (`IsOpenNormOne abv`), with
a measurable structure where integrals occur. These layers are `source` and
`target` (`Induction`), `intertwiningInduced` (`IntertwiningInduced`),
`IsSourceJacquetFunctional` and `IsTargetJacquetFunctional`
(`JacquetInduced`) and the function-level relation `IsLocalCoefficient`
(`LocalCoefficient`). Items 1–5 above are stated for p-adic fields
(`PadicField p`, finite extensions of `ℚ_p`): the p-adic layers, the
statements of `IntertwiningStatements` and `JacquetStatements`, the relation
`IsShahidiLocalCoefficient`, and `LocalCoefficientGammaStatement`. The
p-adic setting is that of the published gamma relations
`IsPadicPairGammaFactor` and `IsPadicSymmetricGammaFactor`.

## General non-archimedean local fields

The modules below apply the generic layers to a field `F` with `Field`,
`ValuativeRel`, `TopologicalSpace` and `IsNonarchimedeanLocalField`
instances. This includes fields of positive characteristic. All their
analytic statements normalize `q` and `abv` as in the first two points
below. The statements that involve `ψ` (Jacquet, coefficient and Theorem 5.1
statements) also normalize `ψ` as in the third point.

- `q` is the cardinality of the residue field of
  `(ValuativeRel.valuation F).integer`;
- `abv ϖ = q⁻¹` for a uniformizing element `ϖ` (`IsUniformizingElement`,
  `Representation/Whittaker/Iwasawa`), and `abv x = 1` when the valuation
  of `x` is `1`; where `IsOpenNormOne abv` is needed, it is obtained through
  `isOpenNormOne_of_valuation` (`Induction`);
- `ψ` satisfies `Conductor.HasIntegerConductor ψ`
  (`Representation/Conductor/Essential`): `ψ` is trivial on the valuation
  ring `O`, and `ψ(xO) = 1` only for `x ∈ O`. This replaces the p-adic
  hypothesis `additiveConductor ψ = 0`.

The modules, by scope item:

- **Item 2.** `GeneralIntertwiningFamilies` (`f04ef550`, Worker 99):
  `generalMaximalCompact` (`GL_r(O_F)`), `IsGeneralFlatFamily` and
  `generalIntertwiningCoefficient`, the scalar integral of (0.1) tested by a
  smooth functional. Proved: `generalIntertwiningCoefficient_eq`, which on
  the convergence domain identifies the scalar integral with the functional
  applied to the actual value of `intertwiningInduced`, read through the
  tensor flip. It assumes smooth factors, `CompactOpenCofinal` for the Levi
  and the Jacobian law `IsModulusScaling` (`IntertwiningInduced`) for the
  measure. `GeneralIntertwiningStatements` (`1ee4a99e`, Worker 99,
  statements): `GeneralIntertwiningConvergenceStatement`,
  `GeneralIntertwiningRationalityStatement` (at points of
  `generalMaximalCompact`, for flat families) and their conjunction
  `GeneralIntertwiningAnalyticStatement`. Their hypotheses on the factors
  are admissibility and irreducibility.
- **Haar scaling.** `HarmonicAnalysis/GeneralHaarScalingStatement`
  (`a6d2e9f0`, Worker 378, statements): `GeneralScalarHaarScalingStatement`,
  `GeneralRectangularHaarScalingStatement`, `GeneralModulusScalingStatement`
  (`IsModulusScaling` for every additive Haar measure on `n × m` matrices)
  and their conjunction `GeneralAdditiveHaarScalingStatement`. All four are
  proved, with no added hypotheses.
  `HarmonicAnalysis/GeneralScalarHaarScalingProof` (`89c292a2`, Worker 11,
  proof) proves the scalar law as `generalScalarHaarScalingStatement`. It
  also has helper theorems in `Langlands.HarmonicAnalysis.GeneralLocalField`,
  such as `secondCountableTopology`, which derive regularity and countability
  from the local-field hypotheses. `HarmonicAnalysis/GeneralHaarScalingProof`
  (`8b0a012d`, Worker 99 with Worker 11, proof) proves
  `generalRectangularHaarScalingStatement`, `generalModulusScalingStatement`
  and `generalAdditiveHaarScalingStatement`. So, for the residue-normalized
  `abv`, a Borel structure on `F` and an additive Haar measure on the radical,
  `generalModulusScalingStatement` supplies the `IsModulusScaling`
  hypothesis of `generalIntertwiningCoefficient_eq` and
  `satisfiesLocalCoefficientEquation_sourceEval_iff`. In the p-adic layer the
  corresponding law is proved
  (`Langlands.PadicField.TopologicalData.isModulusScaling_padic`,
  `IntertwiningPadic`).
- **Item 3.** `GeneralJacquetStatements` (`ffff3780`, Worker 99, statements):
  `GeneralJacquetStabilizationStatement`,
  `GeneralInducedWhittakerMultiplicityOneStatement` and their conjunction
  `GeneralJacquetStatement`. `GeneralLocalCoefficientExistenceStatement`
  (`82cd2101`, Worker 99, statements):
  `GeneralLocalCoefficientExistenceStatement` (a rational coefficient exists
  for three arbitrary fixed Haar measures; not the measure-normalized
  comparison) and
  `GeneralJacquetAndCoefficientStatement`, the conjunction with
  `GeneralJacquetStatement`.
- **Item 4.** `LocalCoefficientGeneral` (`18090f4c`, Worker 33):
  `generalSourceFunctions`, `IsGeneralLocalCoefficientFor` and
  `IsGeneralLocalCoefficient`, the general-field forms of the p-adic
  relations of `LocalCoefficientPadic`. Proved there:
  `generalLeviCompactOpenCofinal` (every open subgroup of a block Levi
  contains a compact open subgroup), `IsGeneralLocalCoefficientFor.unique`
  and `IsGeneralLocalCoefficient.unique` (for smooth factors and `1 < q`),
  `IsGeneralLocalCoefficientFor.smul`, `isGeneralLocalCoefficientFor_smul_iff`,
  `IsGeneralLocalCoefficientFor.isGeneralLocalCoefficient` (under explicit
  multiplicity-one hypotheses) and
  `satisfiesLocalCoefficientEquation_sourceEval_iff`, the literal form of
  (0.3) through the actual operator, which assumes `IsModulusScaling` for
  the intertwining measure.
- **Item 5.** `Representation/RankinSelberg/GeneralPairGamma` (`1fbc982e`,
  Worker 99 with Worker 11) defines `IsGeneralSymmetricGammaFactor`, the
  larger-rank-first form of the general-field JPSS relation
  `Langlands.RankinSelberg.IsPairGammaFactor`
  (`Representation/RankinSelberg/GammaFactor`).
  `GeneralLocalCoefficientGammaStatement` (`2ca640bc`, Worker 99 with Worker
  11, statements): `IsGeneralLocalCoefficientGammaComparison`,
  `GeneralLocalCoefficientGammaAllRanksStatement`,
  `GeneralLocalCoefficientGammaEqualRankStatement` and their conjunction
  `Langlands.Shahidi.GeneralLocalCoefficientGammaStatement F`, Theorem 5.1
  over `F`. The comparison asserts `IsGeneralLocalCoefficient` and
  `IsGeneralSymmetricGammaFactor q ψ abv ν π₁ (smoothContragredient π₂)`
  with `C = ω(−1)^{m+1} • G`. Here `ν` is an additive Haar measure with
  `IsSelfDual ψ ν` (`HarmonicAnalysis/Basic`), and `ω` is a central
  character of `π₂`. The measures follow the p-adic statement: product
  measures with a shared scalar Jacquet measure for all positive ranks, and
  an `EqualRankMeasureData (ValuativeRel.valuation F).integer n` satisfying
  `IsEqualRankGeometricNormalized ψ abv` at equal ranks at least two.

The general-field Theorem 5.1 does not replace the p-adic one. The p-adic
statement quantifies over bundled p-adic fields, while the general one takes
`F` and its normalizations explicitly, and no implication between the two is
proved. `TensorBridge` (`62360656`) relates `pairFlip` and `pairFunctional`
to the binary tensor product.

## Retained source gaps

The gaps below apply to the general-field modules as well, with
`IsGeneralLocalCoefficient` and `IsGeneralSymmetricGammaFactor` in place of
the p-adic relations and `HasIntegerConductor ψ` in place of
`additiveConductor ψ = 0`.

- **Induction exponents (pages 67 and 72).** Read literally, the display
  gives exponents `s/2 + n/4` and `−(s/2 + m/4)`. `Induction` implements the
  normalized `(s + n)/2` and `−(s + m)/2`, which are supported by Lemma 2.2 on
  page 84. Its Markdown gives the computation.
- **Smooth instead of `K`-finite functions.** The induced spaces contain all
  smooth functions. The comparison with the source's `GL_r(O)`-finite
  functions is not proved.
- **Primed subgroup of Proposition 1.2 (page 74).** The literal
  `N'_{n−1} = w_n N_{n−1} w_n^{−1}` does not fit the integrand.
  `KirillovMeasure` uses `N_n ∩ G'_{n−1}`, which agrees with the Kirillov
  embedding of page 71.
- **Rationality (page 72).** Rationality in `q^{−s}` is stated at points `k`
  of `GL_{m+n}(O)` and weakly, through smooth functionals. At other points the
  normalized covariance contributes half-integral powers of `q^{−s}`.
- **Whittaker functionals.** The source fixes a pair `λ₁`, `λ₂`.
  `IsShahidiLocalCoefficient` quantifies over all nonzero pairs instead. Under
  multiplicity one the two readings agree.
- **Normalization of measures.** At equal ranks the geometric items of pages
  75–77 are imposed. The two Hermitian-pairing equations of item 1 are not,
  because they need a unitary `π₂`. This leaves one positive scale (that of
  `d*a·dn₂`), and `C` is inversely proportional to it. For `m ≠ n` the source
  has no general recipe. The statement keeps the theorem's existential
  quantifier and adds only the shared Jacquet measure. Section 4's
  normalization for `(n − 1, n)` (pages 94–96) and the page-68 remark that the
  measures do not depend on `π₁` and `π₂` are not formalized. At rank one the
  pages 75–77 recipe degenerates: it pins the intertwining measure (the
  self-dual measure), and hence `C`. The common Jacquet measure stays
  arbitrary, as item 6 on page 77 allows, and its scale cancels from (0.3).
  Requiring this pinned constant would say more than Theorem 5.1. So the
  equal-rank conjunct requires ranks at least two, and rank one is covered
  only by the all-rank conjunct.
- **Standing assumptions.** The conductor-`O` assumption on `ψ` (page 70) is
  an explicit hypothesis. The existence and uniqueness of the central
  character `ω` are remarks in the Markdown and are not proved.
- **Rank order of `ε'`.** Shahidi's notation puts the smaller rank first.
  Page 102 takes `π₁` on `G_m` and `π₂` on `G_n`. For `m ≤ n − 1`, page 103
  defines `ε'(s, π₁ × π₂, ψ)` by (5.1), whose integral `Ψ` pairs the
  larger-rank `W₂` (which carries the unipotent variable `x`, in the
  `ψ`-model) with the smaller-rank `W₁(ε_m g)`. For `m > n`, page 103 sets
  `ε'(s, π₁ × π₂, ψ) = ε'(s, π₂ × π₁, ψ)`. For `m = n`, page 102 notes the same
  symmetry. So `ε'` is symmetric by definition. The Library's
  `IsPadicPairGammaFactor F ψ ν π σ` puts the larger rank first (JPSS (2.12)),
  and `IsPadicSymmetricGammaFactor` extends it to both orders by swapping.
  Theorem 5.1 concerns `ε'(s, π₁ × π̃₂, ψ)`. It is read through the pair
  relation for `(π̃₂, π₁)` when `m < n` and for `(π₁, π̃₂)` when `n ≤ m`. Both
  sides pair the larger-rank Whittaker function in its `ψ`-model with the
  smaller-rank one in its `ψ̄`-model: by `Signs`, `W₁(ε_m g)` is a
  `ψ̄`-Whittaker function. Replacing `ε'` by the Library's gamma relation is
  explained in the Conventions section of `LocalCoefficientGammaStatement.md`.

## Open proof obligations

- `ShahidiIntertwiningConvergenceStatement` and
  `ShahidiIntertwiningRationalityStatement`; over general fields,
  `GeneralIntertwiningAnalyticStatement`.
- `ShahidiJacquetAndCoefficientStatement`; over general fields,
  `GeneralJacquetAndCoefficientStatement`.
- `LocalCoefficientGammaStatement` and `GeneralLocalCoefficientGammaStatement`
  (Theorem 5.1), including existence of the local coefficient, of the gamma
  factor and of a geometrically normalized equal-rank datum.
- Not stated: Lemma 5.1, Propositions 3.1 and 4.2, the multiplicativity of
  `C_χ` and `ε'`, and the Plancherel measures of Section 6.

## Source records

The table gives the full ID of each accepted candidate and the module it
published; each candidate published one Lean module with its Markdown.
TaskHub `fetch` of the ID returns the candidate record; the project
artifact store holds the same record at `artifacts/<ID>/1/record.json`. The
record's `sources` array gives the literature ID, the SHA-256 of the
retained file (`content_sha256`) and a locator. Every definition and
statement record cites `shahidi-1984-fourier` (SHA-256 above), except that
of `a6d2e9f0`, an internal prerequisite with no literature source. The
records of `1fbc982e` and `2ca640bc` also cite `jpss-1983-rankin-selberg`.
The two proof records (`89c292a2`, `8b0a012d`) have no `sources` array; their
records name the proved statement (`statement_declaration`), and their
Markdown states that the constructions are internal.

| Candidate | Module | Kind |
| --- | --- | --- |
| `47450e09-f78b-42c1-894f-eda8f78fad90` | `Induction` | definition |
| `7b5082dd-9e5e-4d53-84b1-73ee7ba87a8d` | `TwoBlocks` | definition |
| `2f4cc677-40f2-4cbc-8b7c-aba8ee451e30` | `Geometry` | definition |
| `2cfcab68-cf19-48d3-a2b2-1bfddb7bf666` | `IntertwiningIntegral` | definition |
| `30da169f-722d-415b-8abb-703ad86957d1` | `IntertwiningCovariance` | definition |
| `aefca3d1-c734-40e2-a2c4-4b901d83f618` | `IntertwiningInduced` | definition |
| `bd52f1c2-b74d-4c1d-a304-5a892772d704` | `IntertwiningPadic` | definition |
| `ae96ae41-878d-4b99-a28f-83a911af20c4` | `IntertwiningStatements` | statement |
| `9245d21d-c945-43d9-8b5d-99bc3952f06d` | `Characters` | definition |
| `7a2afec1-ddb7-4443-a5be-3495c3c5c4cf` | `JacquetIntegral` | definition |
| `90ab353f-a3f6-4fa4-adb6-887ca4d183c8` | `JacquetInduced` | definition |
| `5417cfb5-48b1-4464-a127-bf7a14123047` | `JacquetStatements` | statement |
| `70da5bf3-cf4b-4ce4-a59d-c2149157e577` | `LocalCoefficient` | definition |
| `f6fa7ed7-df00-4db0-b4ce-06b2952344a2` | `LocalCoefficientPadic` | definition |
| `71c0374f-c814-4bbe-837a-156e45b0063f` | `LocalCoefficientGammaStatement` | statement |
| `16861257-9de8-4f31-9c86-b89746735927` | `EqualRankMeasures` | definition |
| `9d1b7152-7499-4e7e-8e19-cbd6a3580565` | `PairingMeasure` | definition |
| `5246a0b7-0f5b-44fb-862f-8c36ee451e16` | `KirillovMeasure` | definition |
| `d2d3463c-03a0-44cd-90e0-bf87f60faf56` | `QuotientTransport` | definition |
| `b29f3a27-0347-4264-9785-32385064929a` | `UnipotentProduct` | definition |
| `5938d04b-24cd-4d89-81d5-8ba3a75ad24e` | `CompactMeasures` | definition |
| `b0d37ad1-dc0a-49e7-9127-f8744e4ed5e1` | `IwasawaMeasures` | definition |
| `d8858c8f-94ab-45ee-849c-371028badd62` | `MeasureTransport` | definition |
| `9445b4a0-def8-4580-b6c5-57865d9fd3c3` | `CoordinateMeasures` | definition |
| `46fe4c2c-61a4-4a99-b318-934925265f8a` | `RadicalMeasures` | definition |
| `31e606ca-d10e-45e9-aa82-b1c0744359c5` | `Signs` | definition |
| `ffff3780-706e-4d04-ad3d-168e5d223d97` | `GeneralJacquetStatements` | statement |
| `f04ef550-5601-48de-bbd5-eadd81b7e579` | `GeneralIntertwiningFamilies` | definition |
| `1ee4a99e-f85b-4718-9f6e-0bbbe1494ec5` | `GeneralIntertwiningStatements` | statement |
| `62360656-13ea-40d6-9171-40f6b6bcdcc4` | `TensorBridge` | definition |
| `1fbc982e-4c9e-4173-a10d-2b4a531a544b` | `Representation/RankinSelberg/GeneralPairGamma` | definition |
| `18090f4c-9df7-4dd0-89e6-d26866fd2f3e` | `LocalCoefficientGeneral` | definition |
| `82cd2101-135d-4e43-8cc2-8a7e239508e9` | `GeneralLocalCoefficientExistenceStatement` | statement |
| `2ca640bc-03a4-43db-ad9e-f19a736d96f8` | `GeneralLocalCoefficientGammaStatement` | statement |
| `a6d2e9f0-ea30-4f7e-a56d-5cee3a24f164` | `HarmonicAnalysis/GeneralHaarScalingStatement` | statement |
| `89c292a2-3858-4eb6-bed1-7c4d0fae1672` | `HarmonicAnalysis/GeneralScalarHaarScalingProof` | proof |
| `8b0a012d-46a0-46c9-841c-bddcaa4e0f9a` | `HarmonicAnalysis/GeneralHaarScalingProof` | proof |

These are all thirty-three modules of `Langlands/Representation/Shahidi/` at
the pinned commit, together with
`Representation/RankinSelberg/GeneralPairGamma` and the three
`HarmonicAnalysis` modules on general-field Haar scaling.

## Checking this note

Every declaration name above was looked up at the pinned commit. For each
module in the table, the SHA-256 of its Lean and Markdown files at the
pinned commit was compared with the record's bundle hashes (`lean_sha256`,
`markdown_sha256`). They agree, with four exceptions. In all four, the
declaration names are unchanged.

- `Geometry` (Lean and Markdown), at integration: the Integrator replaced a
  private matrix helper (`upperCoordinates`) by the shared
  `GeneralLinear.sumBlockUnipotent` of `Langlands/Group/GL/BlockUnipotent`
  and added a two-sentence Markdown paragraph saying so.
- `IntertwiningCovariance.md`, at integration: a reference to
  `HasIntertwiningIntegral.unique` became
  `SmoothWeakIntegral.HasIntegral.unique` (applied pointwise).
- `LocalCoefficientGammaStatement.md`: the later accepted Markdown-only
  correction `b7af61a0-72e4-41f3-bdf6-e8b7525a7a4f` replaced it. It rewrote
  the rank-order bullet (the source puts the smaller rank first, the Library
  the larger). The Lean file is unchanged, and both files at the pinned
  commit match that record's bundle hashes.
- `GeneralHaarScalingProof.md`, at integration: the provenance reference
  `Langlands.Shahidi.isModulusScaling_padic` became
  `Langlands.PadicField.TopologicalData.isModulusScaling_padic`, the
  correction noted in the review.
