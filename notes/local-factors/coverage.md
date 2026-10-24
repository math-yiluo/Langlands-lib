# Rankin-Selberg local factors of pairs: statement coverage

Author: Worker 11, for task `80b8ac90-940b-487d-acdf-1f228d63f8d6`
(representation-side local-factor statements). This note maps that task's
sources to the published Lean declarations that state them. It lists the
supporting definitions they use, the retained source gaps, the delegated
responsibilities and the open proof obligations.

Every declaration named below is in Library commit
`67dfb8a24d65657a6bf35da262b1009383d873d5`. Every statement is a
proposition definition (`def … : Prop`). Its publication accepts the
formulation and the source correspondence; it does not prove the
proposition. No statement is an axiom: a proved result that needs an
unproved statement takes it as an explicit hypothesis. Look up a result by
its module and declaration name in the current Library.

Sources are recorded in two places. Each module's paired Markdown names its
original sources with section and page locators, and explains the
quantifiers and the interpretive choices. The exact registered source
identities are in the accepted candidate records (see "Source records"
below). Each record has a `sources` array giving the literature ID, the
SHA-256 of the retained file and the locator. Some module Markdown files
repeat the literature IDs and SHA-256 values, but many of this task's do
not. The record is the authoritative location.

## Shared conventions

- **Field.** The field scope depends on the statement family.
  - The base relations take the residue cardinality `q` and the absolute
    value `abv : AbsoluteValue F ℝ` as explicit parameters.
    `IsPairEpsilonFactor` and `IsPairGammaFactor` are defined over any field
    with `[ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]`
    and the measurable structures they use. `IsPairLPolynomial` is defined
    over any field with `[TopologicalSpace F] [MeasurableSpace F]`.
  - The essential-vector and conductor statements of
    `Conductor/EssentialStatement` quantify over every field `F` with
    `[Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]`, including fields of positive
    characteristic. There `q`, `abv`, the uniformizer `ϖ` and `ψ` are tied
    to `F` by explicit normalization hypotheses (see "Essential vectors and
    conductors" below).
  - Every other statement family is over `F : PadicField p`, a finite
    extension of `ℚ_p`, for every prime `p`. The source theorems hold for
    every non-Archimedean local field. The Library's local-field data
    (`PadicField.TopologicalData`, `F.canonicalTopologicalData`) and the
    p-adic forms `IsPadicPair…` of the relations exist only for
    `PadicField`, so these families are restricted to p-adic fields. They
    differ in how the topology of `F` is given.
    - **Supplied topological data.** The statements of
      `RankinSelberg/AnalyticStatement` and
      `RankinSelberg/FunctionalEquationStatement` take a supplied
      `T : F.TopologicalData`, as does `Conductor/NewvectorStatement`. Such
      a `T` is a local-field structure on `F` whose topology is the module
      topology over `ℚ_p` and whose valuation extends that of `ℚ_p`. `QuotientHaarExistenceStatement`,
      `EqualRankAnalyticStatement`, `UnequalRankAnalyticStatement`,
      `UnequalRankCommonGeneratorStatement`,
      `EqualRankFunctionalEquationStatement` and
      `UnequalRankFunctionalEquationStatement` take `F` and `T` as
      arguments. `Theorem27Statement` and `NewvectorStatement` quantify over
      every `T`. Here `q` is `T.residueCardinality` and `|·|` is
      `normalizedAbsoluteValue T`. No equality with
      `F.canonicalTopologicalData` is imposed; the canonical data are one
      admissible `T`.
    - **Spectral-norm topology.** `Whittaker/PrerequisitesStatement` and
      `Whittaker/GenericDualStatement` use the topology of the spectral norm
      (`F.canonicalNormedField`).
    - **Canonical data.** All other statements fix
      `F.canonicalTopologicalData`. So do the p-adic relations
      `IsPadicPair…` (including `IsPadicPairLPolynomial`),
      `IsPadicSymmetric…` and `IsLanglandsPairLPolynomial`. Wherever `q` and
      `|·|` occur, directly or inside these relations, `q` is the residue
      cardinality of the canonical data and `|·|` its normalized absolute
      value (`|ϖ| = q⁻¹`).
- **Groups and representations.** The groups are `Langlands.GeneralLinear
  (n + 1) F` (on `F.Carrier` for a `PadicField`), written with rank `n + 1`
  so that every positive rank is covered. `Langlands.GeneralLinear n R` is
  an abbreviation of Mathlib's `Matrix.GeneralLinearGroup (Fin n) R`.
  `Whittaker/PrerequisitesStatement`, `Whittaker/GenericDualStatement` and
  `Conductor/NewvectorStatement` write the Mathlib name directly.
  Representations are Mathlib `Representation ℂ G V` on carriers with
  independent universes.
  Irreducibility, admissibility, genericity and unitarity are explicit
  hypotheses where the source uses them. No statement assumes that every
  irreducible representation is generic.
- **Whittaker models.** The first member of a pair uses standard Whittaker
  functionals for `ψ` (`glFunctionals ψ`), the second for `ψ⁻¹`
  (`glInverseFunctionals ψ`), as in JPSS. There `ψ` is a nontrivial
  continuous unitary additive character (`UnitaryAdditiveCharacter`). The
  `Whittaker/…Statement` modules and `Conductor/NewvectorStatement` instead
  take `ψ : AddChar F ℂ` wherever a character occurs, with continuity,
  `ψ ≠ 1` and `|ψ| = 1` as hypotheses. They write out the equivariance of
  the Whittaker functionals explicitly.
- **Factors are relations, not chosen functions.** The base relations
  below take `π` on `GL_(r+1)` and `σ` on `GL_(n+1)`. Each is false when
  `r < n`. Their quantifier structures differ.
  - `IsPairEpsilonFactor … e`, `e = (c, m) : ℂˣ × ℤ`, says
    `ε(s, π × σ, ψ) = c q^(-ms)`. `IsPairGammaFactor … G` says
    `γ(s, π × σ, ψ) = G(q^(-s))`. Each requires a compatible quotient
    measure, a nonzero `ψ`-Whittaker functional on `π` and a nonzero
    `ψ⁻¹`-Whittaker functional on `σ` to exist, so it is never vacuous. It
    then asserts the functional equation for every compatible quotient
    measure and every pair of nonzero functionals. Uniqueness for `1 < q`
    (`IsPairEpsilonFactor.unique`, `IsPairGammaFactor.unique`) and
    invariance under equivalences (`.congr_equiv`) are proved.
  - `IsPairLPolynomial q ψ abv μ ν π σ P` (in `RankinSelberg/PairLFactor`)
    says `L(s, π × σ) = 1 / P(q^(-s))` for the quotient measure `μ`, which
    is a fixed argument. It has no existence clause and quantifies over no
    measures or functionals. It says that `P` is the normalized generator
    of the zeta values (`IsNormalizedGenerator`: `P(0) = 1` and `1 / P`
    spans the same Laurent-polynomial module as the zeta values). The zeta
    values come from all Whittaker functions of `π` and `σ`: the unions
    `whittakerSet` and `inverseWhittakerSet` of the coefficient models of
    all their standard functionals. For `r = n` this is
    `IsEqualRankLPolynomial`. For `n < r` the condition is imposed for
    every block `r = n + (j + k + 1)`, using the product measure
    `rectangularMeasure ν j (n + 1)`. Uniqueness
    (`IsPairLPolynomial.unique`) and invariance under equivalences
    (`isPairLPolynomial_congr_equiv`) are proved.
  - The p-adic forms `IsPadicPairEpsilonFactor` and `IsPadicPairGammaFactor`
    insert the canonical data (`q` the residue cardinality, the normalized
    absolute value) into the base relations. `IsPadicPairLPolynomial`
    inserts the same data. It also requires a compatible quotient measure
    to exist and asserts `IsPairLPolynomial` for every compatible quotient
    measure. It has no functional-existence clause. The symmetric forms
    `IsPadicSymmetric…` read the pair with the larger rank first (JPSS
    (2.12)).
- **Measures.** The additive Haar measure `ν` enters the unequal-rank blocks
  and the Fourier transform. The relations do not require `ν` to be
  self-dual; statements that need the standard normalization assume
  `ν : SelfDualHaar … ψ`. The Fourier transform is the row transform of
  `Langlands/HarmonicAnalysis/RowFourier` with the plus-sign pairing `∑ xᵢ yᵢ`.
- **Signs.** JPSS Theorem 2.7(iii) (printed p. 391) has the sign
  `ω_(π')(-1)^(N-1)`, where `N` is the larger rank of the pair and `π'` is
  the second member. The functional equations keep this sign. They replace
  `ω_σ(-1)` by the scalar `ζ` by which `-1` acts on the model of the second
  member `σ` (`HasModelMinusOneScalar σ ℓ' ζ`); for irreducible `σ`,
  `ζ = ω_σ(-1)`. With `π` on `GL_(r+1)` and `σ` on `GL_(n+1)` as above,
  `N = r + 1`, so the sign is `ζ^r`, which is `ζ^n` in equal rank `r = n`
  (`RankinSelberg/EpsilonFactor`;
  `RankinSelberg/FunctionalEquationStatement.md`, "The central sign").

## Coverage by topic

Candidate IDs are those of this task; module paths are under
`Langlands/Representation/` unless stated.

### Whittaker models, uniqueness and genericity

- `Whittaker/PrerequisitesStatement`: `WhittakerPrerequisitesStatement`
  (multiplicity one, inverse-character genericity, injectivity of the
  coefficient model). JPSS 1983 §2.1, pp. 385-386. Published before this
  task (candidate `5b814476`).
- `Whittaker/GenericDualStatement`: `GenericContragredientStatement` (the
  smooth contragredient of a generic representation is generic for `ψ⁻¹`,
  through the inverse transpose). JPSS 1983 §0.3 and §2.1. Published before
  this task (candidate `6d8f1fc3`).
- `Whittaker/KirillovStatement` (`2d10d368`): `WhittakerTypeKirillovStatement`,
  `SupercuspidalKirillovStatement`, family `KirillovPrerequisitesStatement`.
  JPSS 1983 §2 (p. 386), Bernstein-Zelevinsky 1976.
- `Whittaker/InducedStatement` (`f9df70fd`): `InducedFiniteTypeStatement`,
  `InducedWhittakerTypeStatement`, family `InducedWhittakerPrerequisitesStatement`.
  JPSS 1983 §2, pp. 385-387.
- `Whittaker/AsymptoticStatement` (`313f5c28`): `WhittakerGaugeStatement`,
  `WhittakerTypeAsymptoticStatement`, `GenericWhittakerAsymptoticStatement`,
  family `WhittakerAsymptoticPrerequisitesStatement`. JPSS 1983 §2.5,
  pp. 388-389; JPS 1979 §2.

### Convergence, rationality and normalized generators

- `RankinSelberg/AnalyticStatement` (published with `05a25aa0`):
  `QuotientHaarExistenceStatement`, `EqualRankAnalyticStatement`,
  `UnequalRankAnalyticStatement`, `UnequalRankCommonGeneratorStatement`.
  JPSS 1983 Theorem 2.7(i)-(ii), pp. 390-391: convergence in a right half
  plane, rational continuation, the fractional ideal and its normalized
  generator `1/P`, the same for every unequal-rank block.
- `RankinSelberg/RationalContinuation` (published before this task,
  candidate `ae8d8dfa`): definitions `spectralPoint`,
  `HasRationalContinuation`, with proved uniqueness of rational
  continuations.
- `RankinSelberg/RationalZeta`, `RankinSelberg/LocalFactor` and
  `RankinSelberg/PairLFactor` are definition modules that were not produced
  by this task. They define the Laurent span `zetaSpan`,
  `IsNormalizedGenerator`, the Whittaker sets `whittakerSet` and
  `inverseWhittakerSet`, the zeta-value sets `equalRankZetaValues` and
  `unequalRankZetaValues`, the L relations `IsEqualRankLPolynomial`,
  `IsUnequalRankLPolynomial` and `IsPairLPolynomial` (described under
  "Shared conventions"), and the existence proposition
  `PairLPolynomialExists`. `pairLFactor` is defined only from a proof of
  `PairLPolynomialExists`. Two proved theorems derive
  `PairLPolynomialExists` from the unproved p-adic analytic statements.
  The conclusion covers pairs of Whittaker type, with every compatible
  quotient measure. `EqualRankAnalyticStatement.pairLPolynomialExists`
  treats equal ranks.
  `UnequalRankCommonGeneratorStatement.pairLPolynomialExists` treats
  `n < r` and also assumes `UnequalRankAnalyticStatement` for every block.
- `RankinSelberg/EqualRankEulerStatement` (`87c1dfdc`):
  `UnitaryEqualRankConvergenceStatement`, `UnitaryEqualRankNonvanishingStatement`
  (Jacquet-Shalika, Euler products I, Prop. (1.5)(i)-(ii)).

### Functional equations, epsilon and gamma factors

- `RankinSelberg/FunctionalEquationStatement` (`05a25aa0`):
  `EqualRankFunctionalEquationStatement`, `UnequalRankFunctionalEquationStatement`,
  family `Theorem27Statement`. JPSS 1983 Theorem 2.7(iii), p. 391, with the
  dual models (`firstDualFunction`, `secondDualFunction`), the Weyl elements
  (`blockWeylAt`), the sign (`HasModelMinusOneScalar`) and
  `NormalizedFunctionalEquation`.
- `RankinSelberg/EpsilonFactor` (`8bfa0c63`, definitions with proved
  lemmas): `EqualRankEpsilonEquation`, `UnequalRankEpsilonEquation`,
  `IsEqualRankEpsilonFactor`, `IsUnequalRankEpsilonFactor`,
  `IsPairEpsilonFactor`, `IsClassEpsilonFactor`.
- `RankinSelberg/GammaFactor` (published with `25d647da`): `IsPairGammaFactor`,
  `IsPadicPairGammaFactor`, `IsClassGammaFactor` and the equations.
- `RankinSelberg/PadicPairFactors` (published with `0ea8e52f`, definitions
  with proved lemmas): `IsPadicPairLPolynomial`, `IsPadicSymmetricGammaFactor`,
  `IsPadicSymmetricEpsilonFactor`, `IsPadicSymmetricLPolynomial`.
- `RankinSelberg/LocalConverseStatement` (`80449948`): defines
  `IsPadicPairEpsilonFactor`.
- `Langlands/HarmonicAnalysis/RowFourier` (`9c9709ae`, definitions): the row Fourier
  transform and self-duality used by the equal-rank equation.
- `RankinSelberg/PairEpsilonNormalizationStatement` (`716f07d6`):
  `ContragredientEpsilonCentralValueStatement` (Bushnell-Henniart 1999,
  Théorème 2, stated there for `π` on `GL_n` as
  `ε(1/2, π × π̌, ψ) = ω_π(-1)^(n-1)`; the Lean takes generic `π` on
  `GL_(r+1)`, so the sign is `ω_π(-1)^r`),
  `PairEpsilonExponentStatement` (Bushnell-Henniart-Kutzko 1998, p. 703:
  the exponent is `n₁n₂ n(ψ) + f(π₁ × π₂)` with `f` independent of `ψ`).

Constructions of the factors from the analytic inputs are published by the
definition owners and bridge to these relations: `EqualRankGammaFactor`
(`pairGammaFactor_isPairGammaFactor_equalRank`), `UnequalRankGammaFactor`,
`PadicGammaFactor`, `ClassGammaFactor`, `PairEpsilonFactor`, `DualModels`
(see each module's Markdown).

### Multiplicativity

- `RankinSelberg/MultiplicativityStatement` (`ebc3ee58`):
  `GammaMultiplicativityStatement`, `LFactorMultiplicativityStatement`, family
  `MultiplicativityStatement`. JPSS 1983 Theorem (3.1): the gamma factor is
  multiplicative under parabolic induction of the second member, for
  representations of Whittaker type as in the source; for L only the
  divisibility of the source is stated, not constituent-wise L
  multiplicativity.

### Special, tempered and Langlands-data formulas

- `RankinSelberg/SegmentFactorStatement` (`6ddc16eb`):
  `SegmentHeadLFactorStatement`, `SegmentHeadContragredientLFactorStatement`,
  `SegmentHeadGammaFactorStatement`, family `SegmentHeadFactorStatement`.
  Henniart 2002 §2.6 (factors of `St_n(ρ) × St_n'(ρ')`).
- `RankinSelberg/TemperedLFactorStatement` (`66547e0f`):
  `SupercuspidalUnequalRankLFactorStatement`, `SupercuspidalEqualRankLFactorStatement`,
  `SquareIntegrableLFactorStatement`, `SquareIntegrablePoleFreeStatement`,
  `TemperedLFactorStatement`, family `TemperedLFactorFormulasStatement`.
  JPSS 1983 Proposition 8.1, Theorem 8.2 and §8.4.
- `RankinSelberg/LanglandsQuotientLFactorStatement` (`bb2f6617`):
  `LanglandsTypeLFactorStatement`, `GenericLanglandsQuotientLFactorStatement`,
  `LanglandsPairLFactorExistenceStatement`, `SquareIntegrableDataLFactorStatement`,
  family `LanglandsQuotientLFactorStatement`, with the L relation
  `IsLanglandsPairLPolynomial` for arbitrary (also nongeneric) irreducible
  admissible pairs. JPSS 1983 §9.4-9.5.
- `RankinSelberg/PairLFactorCharacterizationStatement` (`c0f82b7d`):
  `SupercuspidalLFactorCharacterizationStatement`,
  `SquareIntegrablePoleOrderCharacterizationStatement`, family
  `PairLFactorCharacterizationStatement`. Henniart 2002 Théorèmes 1.6(b) and
  1.7(b).

### Unramified computations

- `RankinSelberg/UnramifiedPairStatement` (`97ec752b`):
  `UnramifiedSphericalVectorStatement`, `UnramifiedPairIntegralStatement`,
  `UnramifiedUnitaryPoleFreeStatement`, family `UnramifiedPairStatement`.
  Jacquet-Shalika, Euler products II, §1.3-1.5.
- `RankinSelberg/UnramifiedFactorStatement` (`e38e2eff`):
  `UnramifiedEqualRankIntegralStatement`, `UnramifiedPairLFactorStatement`,
  `UnramifiedPairEpsilonStatement`, `UnramifiedUnitaryParameterBoundStatement`,
  family `UnramifiedFactorStatement`. Cogdell, *Analytic theory of
  L-functions for GL_n* (2004), Theorem 3.3, and the Fields lectures (2003).
- `RankinSelberg/EqualRankEulerStatement` (`87c1dfdc`):
  `UnramifiedGenericEqualRankIntegralStatement` (Euler products I,
  Proposition (2.3), without unitarity), family `EqualRankEulerStatement`.

### Twisting and change of additive character

- `RankinSelberg/UnramifiedTwistStatement` (`8653663a`):
  `UnramifiedTwistLFactorStatement`, `UnramifiedTwistEpsilonStatement`, family
  `UnramifiedTwistStatement`. Henniart 1993 §4.4 (twist by `|·|^u`), JPSS
  1983 (2.4) and (2.7)(iii).
- `RankinSelberg/PairFactorCharacterChangeStatement` (`f3848a3b`):
  `UnequalRankLPolynomialCharacterChangeStatement`,
  `UnequalRankEpsilonCharacterChangeStatement`, family
  `PairFactorCharacterChangeStatement`. Cogdell-Piatetski-Shapiro 1994,
  Lemma 2.1 and its proof, for unequal ranks, converted to self-dual
  measures. This module writes `π` on `GL_(r+1)` and `σ` on `GL_(t+1)`
  with `r ≠ t`, and states
  `ε(s, π × σ, ψ^a) = ω_π(a)^(t+1) ω_σ(a)^(r+1) |a|^((r+1)(t+1)(s-1/2)) ε(s, π × σ, ψ)`
  for the symmetric p-adic epsilon relation.
- `PairEpsilonExponentStatement` above gives the dependence of the exponent
  on the conductor of `ψ`.
- The transport of the integrals and L-ideals under `ψ ↦ ψ^a` with explicit
  measure laws is published separately: `Whittaker/CharacterChange`,
  `RankinSelberg/{CharacterChange, CharacterChangeBlocks,
  EqualRankCharacterChange, UnequalRankCharacterChange,
  UnequalRankCharacterIntegrals, UnequalRankCharacterTransport,
  CharacterChangeMeasureStatement, RectangularCharacterChangeMeasureStatement,
  UnipotentCharacterChangeModulusStatement}` (by other workers; see their
  Markdown).

### Highly ramified twists

- `RankinSelberg/HighlyRamifiedStatement` (`0ea8e52f`):
  `HighlyRamifiedGammaStabilityStatement`, `HighlyRamifiedEpsilonStabilityStatement`,
  `HighlyRamifiedLVanishingStatement`, family
  `HighlyRamifiedStabilityStatement`, with `SameGLCentralCharacter`.
  Jacquet-Shalika 1985, §§1 and 4.

### Essential vectors and conductors

- `Conductor/NewvectorStatement` (published before this task, candidate
  `38986482`): `NewvectorStatement` (least level with nonzero fixed
  vectors, one-dimensional there). It quantifies over every prime `p`,
  every `F : PadicField p` and every supplied `T : F.TopologicalData`, and
  takes the topology of `T`. The level-`a` group consists of the matrices
  with entries and inverse entries in `T.Integers` whose last row is
  congruent to `(0, …, 0, 1)` modulo the `a`-th power of the maximal ideal
  of `T.Integers`.
- `Conductor/EssentialStatement` (`9905996f`): `EssentialVectorStatement`,
  `ConductorExponentStatement`, `EssentialVectorLevelStatement`, family
  `EssentialConductorStatement`. JPSS 1981 Théorème (5.1), p. 211, with
  Jacquet's corrected existence theorem (2012, Theorem 1, p. 517); the
  flawed 1981 existence proof is not stated as established. Unlike the
  p-adic families, these four statements quantify over an arbitrary
  non-Archimedean local field (`IsNonarchimedeanLocalField`), including
  positive characteristic, as both papers do. `EssentialVectorStatement`
  and `EssentialVectorLevelStatement` assume
  `h : IsJacquetNormalization q ψ abv ϖ μ`: `q` is the residue cardinality,
  `ϖ` a uniformizer, `abv` the normalized absolute value (`abv ϖ = q⁻¹`,
  trivial on units), `ψ` has conductor `𝔒`, and `μ` is the quotient measure
  compatible with the Haar measures giving `GL_(n+1)(𝔒)` and `N_(n+1)(𝔒)`
  mass one. `ConductorExponentStatement` assumes the same conditions on `q`,
  `ϖ`, `abv` and `ψ` directly, and a Haar measure `ν` self-dual for `ψ`.
  The two essential-vector statements cover ranks at least two;
  `ConductorExponentStatement` covers every rank. The spherical test
  integrals are in `Conductor/SphericalTests`.
  The originals use the Godement-Jacquet standard factors of `π`. JPSS 1981
  defines the conductor exponent from `ε(s, π, ψ)`, and Jacquet 2012 uses
  the standard L-polynomial of `L(s, π)`. The Lean statements use the JPSS
  pair factors of `π` against the trivial character of `GL_1` instead. The
  essential vector (`IsEssentialVector` in `Conductor/Essential`) uses
  `IsCharacterLPolynomial` for `L(s, π × 1)`, and the conductor targets use
  `IsPairEpsilonFactor … π (rankOneCharacter 1)` for `ε(s, π × 1, ψ)`. That
  the two kinds of factor agree is not proved; see "Retained source gaps".

### Local converse theorem

- `RankinSelberg/LocalConverseStatement` (`80449948`):
  `SupercuspidalLocalConverseStatement` (Henniart 1993, Corollary, p. 340:
  epsilon factors against supercuspidals of ranks `1, …, n - 1`), with
  `SameClassEpsilonFactors` and `SameSupercuspidalEpsilonFactors`.
- `RankinSelberg/GenericLocalConverseStatement` (`25d647da`):
  `GenericLocalConverseStatement`, `GenericSupercuspidalLocalConverseStatement`,
  family `GammaLocalConverseStatement`. Henniart 1993 Theorem 1.1 and the
  referee's remark, p. 340, with the exact test ranks of the source.

### Finite-place comparison with Shahidi's local coefficients

Delegated to task `8e607558-e8b2-49f9-a778-9da15e3f4ac1` (published by this
task). At the commit pinned above the Library had no intertwining operators,
Jacquet integrals or local coefficients. That task has since published them,
together with Shahidi 1984 Theorem 5.1 as the statement
`Langlands.Shahidi.LocalCoefficientGammaStatement`
(`Representation/Shahidi/LocalCoefficientGammaStatement`, Library commit
`40a7d025f604f74140054607638d2af422b581ce`). The statement compares the
local coefficient with `IsPadicSymmetricGammaFactor`, keeping the
contragredient of the second member and the sign `ω_(π₂)(-1)^m` (Shahidi's
`π₁` is on `GL_m` and `π₂` on `GL_n`; in Lean the ranks are `m + 1` and
`n + 1`, so the exponent is `m + 1`). The raw coefficient is not identified
with an epsilon factor. The declarations, their field scope, gaps and open
obligations are listed in
[Shahidi local coefficients for GL_m × GL_n: declaration coverage](shahidi-coverage.md).
The global task `91266440` (Workers 35 and 44) was told of the delegation
and of the final declaration names.

## Retained source gaps

- **Nongeneric epsilon factors.** JPSS §9.4 and Henniart 2002 §2.8 define
  the factors of arbitrary irreducible pairs through Langlands data. This
  task states the L relation (`IsLanglandsPairLPolynomial` and the §9.4-9.5
  statements). The epsilon factor of §2.8 is Worker 31's published
  definition `IsLanglandsPairEpsilonFactor` (`RankinSelberg/LanglandsFactors`),
  the product over pairs of square-integrable blocks; its block existence and
  independence of the presenting data are explicit inputs there, not proved.
  Worker 31's `langlandsPairEpsilonFactorOfClassification`
  (`RankinSelberg/LanglandsFactorDescent`) constructs the factor of a pair
  of irreducible representations over a p-adic field. It takes the
  published square-integrable exhaustion and classification propositions
  and block-factor existence as hypotheses. It derives the independence of
  the presenting data from the classification proposition
  (`langlandsPairEpsilonDataIndependence_of_classification`).
  Bushnell-Henniart 1999 Théorème 2 and the exponent statement of
  Bushnell-Henniart-Kutzko are stated with the JPSS relation, so for generic
  pairs only.
- **Godement-Jacquet versus JPSS factors in the conductor statements.**
  JPSS 1981 (§1.1, printed p. 199, and Théorème (5.1), p. 211) defines the
  conductor exponent from the Godement-Jacquet epsilon factor `ε(s, π, ψ)`.
  Jacquet 2012 (printed p. 517, before Theorem 1) states the essential-vector
  identity with the Godement-Jacquet L-polynomial of `L(s, π)`. The
  statements of `Conductor/EssentialStatement` use the JPSS 1983 factors of
  `π` against the trivial character of `GL_1` instead: `L(s, π × 1)` through
  `IsCharacterLPolynomial` in `IsEssentialVector`, and `ε(s, π × 1, ψ)`
  through `IsPairEpsilonFactor … π (rankOneCharacter 1)`. Two comparisons
  are retained as open: `L(s, π × 1) = L(s, π)` and
  `ε(s, π × 1, ψ) = ε(s, π, ψ)`. Bushnell-Henniart-Kutzko 1998 (Ann. Sci.
  ENS, §1.3, printed p. 538) state `L(χ × π) = L(χπ)` and
  `ε(χ × π, ψ) = ε(χπ, ψ)` for a quasicharacter `χ`, without proof; `χ = 1`
  gives both comparisons. Neither is proved in a source read for this task
  or in the Library, and the Library has no Godement-Jacquet factor
  definition. `Conductor/EssentialStatement.md` ("Interpretation and gaps")
  gives the exact retained scope, and `RankinSelberg/LocalFactor.md` also
  says that agreement with the Godement-Jacquet standard L-factor is not
  asserted. Given both comparisons, the Lean statements are the theorems of
  JPSS 1981 and Jacquet 2012. Without them, the Lean statements make the
  same assertions with the JPSS factors in place of the Godement-Jacquet
  ones. This entry documents a dependency; it does not prove the
  comparisons.
- **Equal-rank change of additive character for ε.** Cogdell-Piatetski-
  Shapiro 1994 treat `m < n`. No original source for `m = n` was found in the
  project literature.
- **Unramified L and ε without unitarity.** Cogdell's Theorem 3.3 assumes
  unitary generic representations; Euler products I computes the integral
  without unitarity (Proposition (2.3), stated) but defers the identification
  with the gcd to a later paper. The unitary scope is kept in
  `UnramifiedFactorStatement`.
- **Archimedean places.** All statements are at finite places. The
  Archimedean theory (Jacquet-Shalika, *Archimedean theory*) belongs to the
  global branch.
- **Henniart 1986 §4.** The pole-region statement used by the global branch
  is Worker 35's `Langlands/Global/Factors/GLPoleRegionStatement` (the `GL_n` half of
  Proposition 4.5(ii)), stated with the JPSS L-polynomial relations
  `IsEqualRankLPolynomial` and `IsUnequalRankLPolynomial`.

## Proof obligations

One statement is proved: `QuotientHaarExistenceStatement` is the theorem
`quotientHaarExistence` of `RankinSelberg/QuotientHaarExistence`. It holds
for every prime `p`, every `F : PadicField p`, every
`T : F.TopologicalData` and every `n`. For the topology of `T` and the
Borel measurable structures, it gives the right invariance of the Haar
measure of the upper unipotent group of `GL_(n+1)` and the existence of a
compatible quotient measure on `N_(n+1)\GL_(n+1)`.

- With `T = F.canonicalTopologicalData` this is exactly the measure
  conjunct of `IsPadicPairEpsilonFactor`, `IsPadicPairGammaFactor` and
  `IsPadicPairLPolynomial`, where `n + 1` is the rank of the second member.
- The base relations `IsPairEpsilonFactor` and `IsPairGammaFactor` are over
  any non-Archimedean local field. In the cases `r = n` and `n < r`, where
  they are not `False`, they contain the same pair of propositions for the
  topology and measurable structures in context. `quotientHaarExistence`
  supplies it only for p-adic fields.
- The base relation `IsPairLPolynomial` has no such conjunct, since it
  takes its measure as an argument.

No other statement family above is proved. The other proved results in the
modules of this task are intrinsic properties of the definitions:
uniqueness of the factors, invariance under equivalences, rank-order
unfolding, uniqueness of rational continuations and the row Fourier
measure properties. Proved results elsewhere that use these statements, such
as the two `pairLPolynomialExists` theorems above, take them as hypotheses.
Each statement is a separate proof obligation for proof tasks that bind the
published declaration by name.

The character-change measure laws listed under "Twisting and change of
additive character" are other workers' statements, not this task's. Of
these, `CharacterChangeRectangularMeasureStatement` (Worker 99) is proved
by Worker 90's theorem `characterChangeRectangularMeasureStatement` in
`RankinSelberg/RectangularCharacterChangeMeasureProof`. No proof of
`CharacterChangeCompatibleMeasureStatement` or
`UnipotentCharacterChangeModulusStatement` is in the pinned commit.

## Source records

The table gives the full ID of each accepted candidate of this task and
the modules it published, with the entry module first. TaskHub `fetch` of
the ID returns the candidate record as its `data` part; the project
artifact store holds the same record at `artifacts/<ID>/1/record.json`.
The record's `sources` array lists each original source with its
literature ID, the SHA-256 of the retained file (`content_sha256`) and a
locator. The last column repeats the literature IDs.

| Candidate | Modules | Literature IDs in `sources` |
| --- | --- | --- |
| `9c9709ae-2bec-4ec7-94fc-0dc062983e42` | `Langlands/HarmonicAnalysis/RowFourier` | `jpss-1983-rankin-selberg` |
| `2d10d368-431c-4f0f-8c12-ed2b0e4455dc` | `Whittaker/KirillovStatement` | `bernstein-zelevinsky-1976-representations-gln`, `jpss-1983-rankin-selberg` |
| `f9df70fd-3b83-4acd-a90e-3b6bfbd6383e` | `Whittaker/InducedStatement` | `jpss-1983-rankin-selberg` |
| `313f5c28-0970-49ea-8a4c-3a36f04fdd97` | `Whittaker/AsymptoticStatement` | `jps-1979-gl3-i`, `jpss-1983-rankin-selberg` |
| `05a25aa0-2fc6-4562-b3d0-d1d0c866cecd` | `RankinSelberg/FunctionalEquationStatement`, `RankinSelberg/AnalyticStatement` | `jpss-1983-rankin-selberg` |
| `8bfa0c63-845f-42de-b6ca-8cdf776d77cf` | `RankinSelberg/EpsilonFactor` | `henniart-1993-epsilon-pairs`, `jpss-1983-rankin-selberg` |
| `80449948-4006-4cd7-a2cc-05a6b3c79518` | `RankinSelberg/LocalConverseStatement` | `henniart-1993-epsilon-pairs`, `jpss-1983-rankin-selberg` |
| `25d647da-a3fd-4bb0-9370-5ca221d8cec8` | `RankinSelberg/GenericLocalConverseStatement`, `RankinSelberg/GammaFactor` | `henniart-1993-epsilon-pairs`, `jpss-1983-rankin-selberg` |
| `0ea8e52f-37f9-4dad-b4a8-da2d75fc67b8` | `RankinSelberg/HighlyRamifiedStatement`, `RankinSelberg/PadicPairFactors` | `jacquet-shalika-1985-ramified-factors`, `jpss-1983-rankin-selberg` |
| `9905996f-a6cd-4591-9aa4-0e1c58407ca1` | `Conductor/EssentialStatement` | `bhk-1998-conducteurs-paires`, `jacquet-2012-conductor-correction`, `jpss-1981-conductor`, `jpss-1983-rankin-selberg` |
| `ebc3ee58-b10a-4773-939f-5dda55ee7e94` | `RankinSelberg/MultiplicativityStatement` | `jpss-1983-rankin-selberg` |
| `bb2f6617-d42a-409a-a4b7-ee6968df5dd6` | `RankinSelberg/LanglandsQuotientLFactorStatement` | `henniart-2002-characterization`, `jpss-1983-rankin-selberg` |
| `66547e0f-6376-4124-8b6c-b5c82e1aea1d` | `RankinSelberg/TemperedLFactorStatement` | `henniart-2002-characterization`, `jpss-1983-rankin-selberg` |
| `8653663a-65d8-4b6e-85fa-f2d0c8ea1294` | `RankinSelberg/UnramifiedTwistStatement` | `henniart-1993-epsilon-pairs`, `jpss-1983-rankin-selberg` |
| `c0f82b7d-7c11-4f88-9d9d-d9d71cd627a6` | `RankinSelberg/PairLFactorCharacterizationStatement` | `henniart-2002-characterization` |
| `716f07d6-1ad0-4e6a-96d5-626bd744b9bf` | `RankinSelberg/PairEpsilonNormalizationStatement` | `bhk-1998-explicit-conductor`, `bushnell-henniart-1999-epsilon-pairs` |
| `6ddc16eb-8047-4567-a0d1-752c2bdc1f59` | `RankinSelberg/SegmentFactorStatement` | `henniart-2002-characterization` |
| `97ec752b-392b-4d90-adba-0e64b8bcf43c` | `RankinSelberg/UnramifiedPairStatement` | `jacquet-shalika-1981-euler-products-ii` |
| `e38e2eff-cadf-43ee-861d-177e2e807af9` | `RankinSelberg/UnramifiedFactorStatement` | `cogdell-2003-fields-lectures-www`, `cogdell-2004-analytic-theory-gln` |
| `87c1dfdc-b0ac-434c-bf19-5386d2628342` | `RankinSelberg/EqualRankEulerStatement` | `provided-6d5abbbab517cf7269b6ab243e0d7a101940980b658f88cb722e13748f802ad4` (Jacquet-Shalika, Euler products I) |
| `f3848a3b-e182-41df-bcfe-803a45cef627` | `RankinSelberg/PairFactorCharacterChangeStatement` | `cogdell-piatetski-shapiro-1994-converse` |

The four modules published before this task (`Whittaker/PrerequisitesStatement`,
`Whittaker/GenericDualStatement`, `RankinSelberg/RationalContinuation` and
`Conductor/NewvectorStatement`; candidates `5b814476`, `6d8f1fc3`,
`ae8d8dfa`, `38986482`) have no record in the project's artifact store.
Their Markdown gives the literature ID and the SHA-256 of each retained
source file.

## Checking this map

For each module in the "Source records" table, the SHA-256 of its Lean and
Markdown files at the pinned commit was compared with the file hashes in
the candidate's accepted manifest (`artifacts/<ID>/1/manifest.json`). For
the entry module these equal the bundle hashes in the record. The four
modules published before this task (`5b814476`, `6d8f1fc3`, `ae8d8dfa`,
`38986482`) have no record in the project's artifact store; they were only
checked to be present at the pinned commit. The hashes agree, with two
integration-time exceptions:

- `RankinSelberg/LocalConverseStatement`: a duplicate proved lemma
  (`isClassEpsilonFactor_mk_iff`) was removed in favour of the existing
  `isClassEpsilonFactor_mk` of `EpsilonFactor`; the Markdown says so. The
  statement is unchanged.
- `RankinSelberg/UnramifiedFactorStatement.md`: the Integrator added a
  citation of Jacquet-Shalika, Euler products I.
