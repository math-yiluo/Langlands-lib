# Shahidi local coefficients for GL_m × GL_n: declaration coverage

This note lists the Lean declarations for the five scope items of the
formalization of Shahidi's local coefficients and the Theorem 5.1
comparison, and the Library modules they depend on. It also records the
source gaps that the formalization
retains and the open proof obligations.

The source is F. Shahidi, *Fourier transforms of intertwining operators and
Plancherel measures for GL(n)*, Amer. J. Math. 106 (1984) 67–111, registered
as `shahidi-1984-fourier`, SHA256
`a10d5c605d94d4e85d0e5f453d6a8c233d91e3cb60d538f430d8ad900cbb6b29`. The
registered file is a scan without a text layer. Page numbers below are
printed pages; printed page `p` is PDF page `p − 65`.

Every module below is in `Langlands/Representation/Shahidi/` unless another
path (relative to `Langlands/`) is given, and its paired Markdown gives exact
locators and interpretive choices. This note was checked against Library
commit `d1e92cc3fedd601726630b19e4e6d1a9dc84b2cd` (the pinned commit below),
which has every declaration named here. Statements are
proposition definitions (`def … : Prop`). Stating it in the Library fixes a
statement's formulation, not its truth, and no statement is an axiom or a structure
field.

Items 1–5 below describe the p-adic formalization. "General non-archimedean
local fields" describes the parallel statements over every non-archimedean
local field, including positive characteristic.

## Item 1: the induced representations

- `Induction`. The generic layer, in `Langlands.Shahidi`, is
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
- Supporting matrix geometry: `TwoBlocks` (`twoBlocks`,
  `twoBlockLeviEquiv`) and `Geometry` (`blockWeyl` for
  `w_{m,n}`, `upperRadical`, `intertwiningUnipotent` and
  `intertwiningRadical` for `U'`).

## Item 2: the intertwining integral

- `IntertwiningIntegral`: `intertwiningOperator`, the integral
  `∫_{U'} f(w u' g) du'` on its actual convergence domain, for functions on
  the group.
- `IntertwiningCovariance`: `rectangularConj` and the
  `twoBlockLeviSwap` covariance computation.
- `IntertwiningInduced`: `intertwiningInduced` on the induced
  spaces, together with the tensor bridge `pairSplit`, `pairSwap` and
  `pairFlip`.
- `IntertwiningPadic`: `shahidiIntertwining`, the p-adic operator
  `A(s, π, w_{m,n})` from `shahidiSourceDomain` to `ShahidiTargetSpace`, with
  `shahidiIntertwining_eval` and the equivariance
  `shahidiIntertwining_shahidiSource`.
- `IntertwiningStatements` (statements):
  `ShahidiIntertwiningConvergenceStatement` (convergence for `Re s` large) and
  `ShahidiIntertwiningRationalityStatement` (rational continuation in
  `q^{−s}`), from page 72.

## Item 3: the Jacquet functional

- `Characters`: the characters `χ` and the kernels of (0.2) on
  the rectangular radicals.
- `JacquetIntegral`: `HasJacquetIntegral` and
  `HasSwappedJacquetIntegral`, the integrals of `λ^s_π` and `λ^{−s}_{π'}`.
  They use the stabilization of page 78 (the published `HasStableIntegral`:
  the integral over compact open subgroups is eventually constant), not
  absolute convergence. They also give the stable functionals
  `jacquetStableFunctional` and `swappedJacquetStableFunctional` on their
  domains.
- `JacquetInduced`: the Jacquet functionals on the
  induced spaces as graphs, `IsSourceJacquetFunctional` and
  `IsTargetJacquetFunctional` with proved uniqueness, generically and in the
  p-adic layer (`shahidiSourceJacquetFunctional`,
  `shahidiTargetJacquetFunctional` and their stable domains). It also proves
  `exists_isSourceJacquetFunctional_iff` and
  `exists_isTargetJacquetFunctional_iff`: a total functional exists exactly
  when the stable domain is everything.
- `JacquetStatements` (statements):
  `ShahidiJacquetStabilizationStatement`,
  `ShahidiInducedWhittakerMultiplicityOneStatement`,
  `ShahidiLocalCoefficientExistenceStatement` (existence of a rational
  coefficient for fixed Haar measures) and their conjunction
  `ShahidiJacquetAndCoefficientStatement`. Proved there:
  `existsUnique_inverseScalar_of_multiplicityOne`, the inverse scalar of an
  intertwiner under multiplicity one.

## Item 4: the local-coefficient relation

- `LocalCoefficient`: the generic relation `IsLocalCoefficient`,
  which keeps the inverse convention `λ^{−s}_{π'}(A f) = C^{−1} λ^s_π(f)` of
  (0.3). Its uniqueness, reciprocity and rescaling lemmas are proved.
- `LocalCoefficientPadic`: on the actual p-adic spaces,
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

- `LocalCoefficientGammaStatement` (statement):
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
  `IsEqualRankMeasureNormalized` in `EqualRankMeasures`. Its
  ingredients are in `PairingMeasure`, `KirillovMeasure`,
  `QuotientTransport`, `UnipotentProduct`,
  `CompactMeasures`, `IwasawaMeasures`,
  `MeasureTransport`, `CoordinateMeasures`
  and `RadicalMeasures`. `Signs` has
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

- **Item 2.** `GeneralIntertwiningFamilies`:
  `generalMaximalCompact` (`GL_r(O_F)`), `IsGeneralFlatFamily` and
  `generalIntertwiningCoefficient`, the scalar integral of (0.1) tested by a
  smooth functional. Proved: `generalIntertwiningCoefficient_eq`, which on
  the convergence domain identifies the scalar integral with the functional
  applied to the actual value of `intertwiningInduced`, read through the
  tensor flip. It assumes smooth factors, `CompactOpenCofinal` for the Levi
  and the Jacobian law `IsModulusScaling` (`IntertwiningInduced`) for the
  measure. `GeneralIntertwiningStatements` (statements): `GeneralIntertwiningConvergenceStatement`,
  `GeneralIntertwiningRationalityStatement` (at points of
  `generalMaximalCompact`, for flat families) and their conjunction
  `GeneralIntertwiningAnalyticStatement`. Their hypotheses on the factors
  are admissibility and irreducibility.
- **Haar scaling.** `HarmonicAnalysis/GeneralHaarScalingStatement`
  (statements): `GeneralScalarHaarScalingStatement`,
  `GeneralRectangularHaarScalingStatement`, `GeneralModulusScalingStatement`
  (`IsModulusScaling` for every additive Haar measure on `n × m` matrices)
  and their conjunction `GeneralAdditiveHaarScalingStatement`. All four are
  proved, with no added hypotheses.
  `HarmonicAnalysis/GeneralScalarHaarScalingProof` (proof) proves the scalar law as `generalScalarHaarScalingStatement`. It
  also has helper theorems in `Langlands.HarmonicAnalysis.GeneralLocalField`,
  such as `secondCountableTopology`, which derive regularity and countability
  from the local-field hypotheses. `HarmonicAnalysis/GeneralHaarScalingProof`
  (proof) proves
  `generalRectangularHaarScalingStatement`, `generalModulusScalingStatement`
  and `generalAdditiveHaarScalingStatement`. So, for the residue-normalized
  `abv`, a Borel structure on `F` and an additive Haar measure on the radical,
  `generalModulusScalingStatement` supplies the `IsModulusScaling`
  hypothesis of `generalIntertwiningCoefficient_eq` and
  `satisfiesLocalCoefficientEquation_sourceEval_iff`. In the p-adic layer the
  corresponding law is proved
  (`Langlands.PadicField.TopologicalData.isModulusScaling_padic`,
  `IntertwiningPadic`).
- **Item 3.** `GeneralJacquetStatements` (statements):
  `GeneralJacquetStabilizationStatement`,
  `GeneralInducedWhittakerMultiplicityOneStatement` and their conjunction
  `GeneralJacquetStatement`. `GeneralLocalCoefficientExistenceStatement`
  (statements):
  `GeneralLocalCoefficientExistenceStatement` (a rational coefficient exists
  for three arbitrary fixed Haar measures; not the measure-normalized
  comparison) and
  `GeneralJacquetAndCoefficientStatement`, the conjunction with
  `GeneralJacquetStatement`.
- **Item 4.** `LocalCoefficientGeneral`:
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
- **Item 5.** `Representation/RankinSelberg/GeneralPairGamma` defines `IsGeneralSymmetricGammaFactor`, the
  larger-rank-first form of the general-field JPSS relation
  `Langlands.RankinSelberg.IsPairGammaFactor`
  (`Representation/RankinSelberg/GammaFactor`).
  `GeneralLocalCoefficientGammaStatement` (statements): `IsGeneralLocalCoefficientGammaComparison`,
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
proved. `TensorBridge` relates `pairFlip` and `pairFunctional`
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

The table lists the modules, each one Lean module with its Markdown, and
their kind. Every definition and statement module has
`shahidi-1984-fourier` (SHA-256 above) as its source, except
`HarmonicAnalysis/GeneralHaarScalingStatement`, an internal prerequisite with
no literature source. `Representation/RankinSelberg/GeneralPairGamma` and
`GeneralLocalCoefficientGammaStatement` also cite `jpss-1983-rankin-selberg`.
The two proof modules have no literature source; their Markdown states that
the constructions are internal.

| Module | Kind |
| --- | --- |
| `Induction` | definition |
| `TwoBlocks` | definition |
| `Geometry` | definition |
| `IntertwiningIntegral` | definition |
| `IntertwiningCovariance` | definition |
| `IntertwiningInduced` | definition |
| `IntertwiningPadic` | definition |
| `IntertwiningStatements` | statement |
| `Characters` | definition |
| `JacquetIntegral` | definition |
| `JacquetInduced` | definition |
| `JacquetStatements` | statement |
| `LocalCoefficient` | definition |
| `LocalCoefficientPadic` | definition |
| `LocalCoefficientGammaStatement` | statement |
| `EqualRankMeasures` | definition |
| `PairingMeasure` | definition |
| `KirillovMeasure` | definition |
| `QuotientTransport` | definition |
| `UnipotentProduct` | definition |
| `CompactMeasures` | definition |
| `IwasawaMeasures` | definition |
| `MeasureTransport` | definition |
| `CoordinateMeasures` | definition |
| `RadicalMeasures` | definition |
| `Signs` | definition |
| `GeneralJacquetStatements` | statement |
| `GeneralIntertwiningFamilies` | definition |
| `GeneralIntertwiningStatements` | statement |
| `TensorBridge` | definition |
| `Representation/RankinSelberg/GeneralPairGamma` | definition |
| `LocalCoefficientGeneral` | definition |
| `GeneralLocalCoefficientExistenceStatement` | statement |
| `GeneralLocalCoefficientGammaStatement` | statement |
| `HarmonicAnalysis/GeneralHaarScalingStatement` | statement |
| `HarmonicAnalysis/GeneralScalarHaarScalingProof` | proof |
| `HarmonicAnalysis/GeneralHaarScalingProof` | proof |

These are all thirty-three modules of `Langlands/Representation/Shahidi/` at
the pinned commit (the directory now has thirty-seven), together with
`Representation/RankinSelberg/GeneralPairGamma` and the three
`HarmonicAnalysis` modules on general-field Haar scaling.

## Checking this note

Every declaration name above was looked up at the pinned commit. For each
module in the table, the SHA-256 of its Lean and Markdown files at the
pinned commit was compared with the hashes of the files as first submitted.
They agree, with four exceptions. In all four, the declaration names are
unchanged.

- `Geometry` (Lean and Markdown), when it entered the Library: a
  private matrix helper (`upperCoordinates`) was replaced by the shared
  `GeneralLinear.sumBlockUnipotent` of `Langlands/Group/GL/BlockUnipotent`
  and a two-sentence Markdown paragraph saying so was added.
- `IntertwiningCovariance.md`, when it entered the Library: a reference to
  `HasIntertwiningIntegral.unique` became
  `SmoothWeakIntegral.HasIntegral.unique` (applied pointwise).
- `LocalCoefficientGammaStatement.md`: a later Markdown-only correction
  replaced it. It rewrote the rank-order bullet (the source puts the smaller
  rank first, the Library the larger). The Lean file is unchanged, and both
  files at the pinned commit match the corrected version.
- `GeneralHaarScalingProof.md`, when it entered the Library: the provenance
  reference `Langlands.Shahidi.isModulusScaling_padic` became
  `Langlands.PadicField.TopologicalData.isModulusScaling_padic`.
