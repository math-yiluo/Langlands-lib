# Local Langlands correspondence for GL_n: specification and statement coverage

Author: Worker 7 (task 1fecded2). Construction addendum: Worker 31, with
Worker 7's interface and scope contributions. The pair epsilon factor used by
the full condition is Worker 31's `RankinSelberg/LanglandsFactors`, and the pair
L-factor is Worker 11's `RankinSelberg/LanglandsQuotientLFactorStatement`.

This note maps the statement layer of the local Langlands correspondence for
`GL_n(F)`, all `n ≥ 1` and every p-adic field `F`, at Library commit
`bd3d155f1f3eb32c90b044cd3bf1e992e726beb7`. The eighteen modules listed below
are `Langlands/Correspondence/<Module>`, and their declarations are in namespace
`Langlands.Correspondence`. Other modules in that directory belong to other
tasks and are outside this original inventory; the construction addendum below is
separately pinned. Use the current Library by module and
declaration name; the commit fixes the versions described. Every statement is a
`Prop`-valued `def`. **None is proved.** Publication accepts the formulation and
its source correspondence, not the proposition. Four interface modules
(AutomorphicRelations, SupercuspidalRelations, Domains, OperationCompatibility)
also prove small structural lemmas, such as `fullMap_ext` and
`supercuspidalToAutomorphic_injective`; these are not correspondence statements.
The paired Markdown of each module gives exact sources, quantifiers and design
notes.

## Conventions

- `F : PadicField p` is an actual finite extension of `ℚ_p`, with its canonical
  topology. The groups are `GeneralLinear n F.Carrier`.
- Representation side: `AutomorphicClass F n`, the isomorphism classes of
  irreducible admissible complex representations, with the carrier universe as a
  parameter and nongeneric ones included. `SupercuspidalAutomorphicClass` is the
  supercuspidal part.
- Parameter side: `WeilDeligneClass F n`, the Frobenius-semisimple
  Weil–Deligne classes with arbitrary monodromy, and `IrreducibleWeilClass F n`.
- `FullMap F` and `SupercuspidalMap F` are rank-indexed maps from parameter
  classes to representation classes. That is Henniart's direction; Harris–Taylor's
  `rec` goes the other way.
- Reciprocity enters through a `ReciprocityCandidate F` with
  `IsGeometricReciprocity` (uniformizers go to geometric Frobenius). It is
  existential in the correspondence predicates and universal in the derived
  statements. The two forms agree once such a candidate is unique, which is the
  uniqueness half of the published, unproved statement
  `LocalClassField.WeilReciprocityExistenceUniqueness`.
- Factors: the L-factor is `P(q^(-s))⁻¹` for a polynomial `P ∈ ℂ[X]`. The epsilon
  factor is `c q^(-ms)`, recorded as `e = (c, m) : ℂˣ × ℤ`. Both are compared at
  every measure self-dual for `ψ`, and a self-dual measure must exist. On the
  parameter side, epsilon comes from a local-constant system
  (`NonabelianSystem.IsSystem`) whose base component is the reciprocity
  candidate (`IsBaseReciprocity`).
- Gamma is never an extra condition. It is derived as
  `γ = ε · L(1 - s, π^∨ × π'^∨) / L(s, π × π')` (Henniart 2002 §1.2).

## Modules

| Module | Main declarations | Content |
| --- | --- | --- |
| LocalConventions | `QuasiCharacter`, `NontrivialAdditiveCharacter`, `LocalAdditiveHaarMeasure`, `IsSelfDualMeasure` | Characters and measures; none is chosen |
| AutomorphicRelations | `AutomorphicClass`, `IsCharacterTwist`, `IsSmoothDual`, `IsRankOneCharacter` | Representation classes and their relations |
| SupercuspidalRelations | `SupercuspidalAutomorphicClass`, `supercuspidalToAutomorphic` | Supercuspidal classes |
| Domains | `WeilDeligneClass`, `IrreducibleWeilClass`, `parameterForget`, `FullMap`, `SupercuspidalMap`, `RankwiseBijective`, `ExtendsSupercuspidal` | Domains and maps |
| OperationCompatibility | `IsGeometricReciprocity`, `RankOne/Determinant/Twist/DualCompatibility` and supercuspidal versions | Rank one, determinant, twist and contragredient conditions |
| ArithmeticFactors | `arithmeticPairLFactor`, `IsBaseReciprocity`, `IsArithmeticPairEpsilonFactor` | Weil–Deligne pair L and epsilon factors |
| SupercuspidalFactorCompatibility | `SupercuspidalFactorCompatibility` | Pair L/epsilon condition on supercuspidals, every `ψ` |
| SupercuspidalGammaCompatibility | `IsArithmeticPairGammaFactor`, `SupercuspidalGammaFromFactorsStatement` | Derived gamma, supercuspidal family |
| SupercuspidalSpecification | `IsSupercuspidalCorrespondence`, `SupercuspidalCorrespondenceStatement` | Supercuspidal correspondence, existence and uniqueness |
| UnramifiedNormalization | `IsSphericalClass`, `principalSeries`, `UnramifiedCompatibility` | Unramified normalization (Borel 1979 §10.4) |
| AssemblyRelation | `IsAssembledFrom`, `IsAssemblyOf`, `AssemblyWellDefined/Bijective/Extends/OperationStatement` | Assembly of a supercuspidal map through blocks, segments and Langlands quotients |
| FullLFactorCompatibility | `IsAutomorphicPairLPolynomial`, `IsPairLCompatibleAt`, `FullPairLCompatibility(At)` | Full-family pair L condition |
| AssemblyLFactorStatement | `IsIndecomposableParameterClass`, `AssemblyLInheritanceStatement`, `AssemblyLCharacterizationStatement` | L inheritance; Henniart 2002 Thm 1.8 |
| FullFactorCompatibility | `IsAutomorphicPairEpsilonFactor`, `IsPairEpsilonCompatibleAt`, `FullEpsilonCompatibility`, `FullFactorCompatibility(At)` | Full-family pair epsilon condition, conjoined with L |
| FullGammaCompatibility | `IsAutomorphicPairGammaFactor`, `FullGammaCompatibility`, `FullGammaFromFactorsStatement` | Derived gamma, full family |
| FullSpecification | `IsFullCorrespondence`, `FullCorrespondenceExistence/Uniqueness/ExistsUnique`, `FullCorrespondenceStatement`, `FullCorrespondenceRestrictionStatement`, `FullCorrespondenceUnramifiedStatement` | The full correspondence |
| FullCharacterizationStatement | `FullCharacterizationExtendsStatement`, `FullCharacterizationStatement` | Henniart 2002 Cor 1.6 and Cor 1.8 |
| AssemblyTheorems | `AssemblyEpsilonInheritanceStatement`, `ConditionalAssemblyStatement` | Epsilon inheritance; the assembly is a full correspondence |

`IsFullCorrespondence F c` holds when `c` is bijective in every rank and compatible
with contragredients, and some geometric reciprocity candidate `e` makes it
compatible with rank one, determinants, twists and all pair L- and
epsilon-factors for every nontrivial `ψ`.

## Top-level statements

- `SupercuspidalCorrespondenceStatement`: for every `p` and `F`, exactly one
  supercuspidal correspondence exists (Henniart 2000; Henniart 2002 §§1.3–1.4).
- `FullCorrespondenceStatement`: for every `p` and `F`, exactly one full
  correspondence exists (Harris–Taylor 2001 Theorem A and Henniart's
  uniqueness). This is the unconditional final statement; it takes no
  correspondence as input.
- `ConditionalAssemblyStatement F`: every supercuspidal correspondence has an
  assembly, and every assembly is a full correspondence (Henniart 2002 Thm 1.5,
  §2.9).
- `FullCharacterizationStatement F` (Cor 1.8): a full map that is compatible
  with rank one and with all pair L- and epsilon-factors at one `ψ` is the
  assembly of every supercuspidal correspondence `c0`, and every assembly of `c0`
  equals it.

None of these statements assumes another. One intended route to
`FullCorrespondenceStatement` combines them: existence from the supercuspidal
statement and `ConditionalAssemblyStatement`; uniqueness from
`FullCorrespondenceRestrictionStatement`, `FullCharacterizationStatement` and the
existence of a nontrivial additive character of `F`.
No proof of this route is in the Library.

## Source-to-declaration map

| Source | Declarations |
| --- | --- |
| Henniart 2000 §1.1 p.439 | `SupercuspidalAutomorphicClass`, `IrreducibleWeilClass`, `SupercuspidalMap` |
| Henniart 2000 §1.2 p.440, §1.3 pp.440–441 | supercuspidal operation and factor conditions; gamma remark → `*GammaFromFactorsStatement` |
| Henniart 2002 §1.1 p.588 | `WeilDeligneClass`, `AutomorphicClass`, `FullMap` |
| Henniart 2002 §1.2 pp.588–589 | `ArithmeticFactors`, `FullLFactorCompatibility`, `FullFactorCompatibility`, `FullGammaCompatibility` |
| Henniart 2002 §§1.3–1.4 p.589 | `IsSupercuspidalCorrespondence`, `SupercuspidalCorrespondence*` |
| Henniart 2002 §1.5 p.590, Thm (i)–(iii) | `ExtendsSupercuspidal`, `AssemblyLInheritanceStatement`, `AssemblyEpsilonInheritanceStatement`, `ConditionalAssemblyStatement` |
| Henniart 2002 Cor 1.6 p.591 | `FullCharacterizationExtendsStatement` |
| Henniart 2002 §1.7 and Thm 1.8 p.591; proof §4.5 p.600 | `IsIndecomposableParameterClass`, `AssemblyLCharacterizationStatement` |
| Henniart 2002 Cor 1.8 p.592 | `FullCharacterizationStatement` |
| Henniart 2002 §§2.2–2.9 pp.593–596 | `AssemblyRelation`, `AssemblyTheorems`; the §2.8 epsilon product is Worker 31's `IsLanglandsPairEpsilonFactor` |
| Harris–Taylor 2001 Intro pp.1–2 | `IsFullCorrespondence`, `FullCorrespondenceStatement` |
| Tate 1979 (3.6.4), (4.1.6) | self-dual measure convention; `arithmeticPairLFactor` |
| Borel 1979 §7.2 p.39, §10.4 pp.44–45 | `UnramifiedNormalization`, `FullCorrespondenceUnramifiedStatement` |

## Design decisions

- **Every `ψ`.** The correspondence predicates require the factor identities
  for every nontrivial `ψ`; Henniart and Harris–Taylor fix one. With the
  central-character property the two forms agree (Henniart 2000 §1.3,
  remark), which the Library does not prove. The characterization statements
  use one `ψ` as hypothesis, which makes them stronger.
- **Monodromy and nongeneric classes.** The full domain allows nonzero
  monodromy and nongeneric representations. Irreducible Weil parameters and
  supercuspidals stay a separate family.
- **Derived conditions.** Gamma compatibility and the unramified normalization
  are derived statements (`FullGammaFromFactorsStatement`,
  `FullCorrespondenceUnramifiedStatement`), not parts of `IsFullCorrespondence`.
- **Local instances.** Several modules install the canonical topologies as
  local instances. They carry explicit module-specific names (for example
  `unramifiedFieldTopology`, `assemblyFieldTopology`): auto-generated names
  collided and prevented joint imports.

## Dependencies

The eighteen modules import the thirty modules below from other tasks. Their
other imports are each other and two Mathlib modules. Each dependency is an accepted and
published Library module. The versions used are those at commit `bd3d155f`. The
last column gives the first 12 hex digits of the SHA-256 of the `.lean` file in
that commit's `manifest.json`. Paths are relative to `Langlands/`.

| Module | Imported by | Declarations used | `.lean` SHA-256 |
| --- | --- | --- | --- |
| ClassFieldTheory/Local/WeilReciprocityStatement | OperationCompatibility | `GeometricWeilReciprocityRelation` | `b8e6143debd6` |
| Group/GL/Padic | AutomorphicRelations | `canonicalGeneralLinearTopology`, `canonicalGeneralLinearTopologicalGroup` | `803a2561ddc8` |
| Group/GL/UnramifiedCharacter | UnramifiedNormalization | `IsUnramifiedCharacter` | `69df6a7fd220` |
| HarmonicAnalysis/Basic | LocalConventions | `Quasicharacter`, `UnitaryAdditiveCharacter`, `AdditiveHaarMeasure`, `SchwartzBruhat`, `fourierTransform`, `IsSelfDual` | `2198cecae146` |
| LocalFactor/CommonClosureGamma | ArithmeticFactors | `conditionalPairEpsilonValue` | `a1288fb0cf32` |
| LocalFactor/RankOne | OperationCompatibility | `ReciprocityCandidate`, `reciprocityUnits`, `weilCharacter` | `94d67d384e29` |
| LocalField/Canonical | LocalConventions | `canonicalTopologicalData` | `e702bb7808fc` |
| Representation/Category/Basic | AutomorphicRelations | `SmoothRep`, `IrreducibleAdmissibleRep`, `SmoothDualClass` | `6a4781890b64` |
| Representation/Category/Twist | AutomorphicRelations | `IrreducibleAdmissibleRep.twist`, `SmoothDualClass.twist` | `9fb1bca986f0` |
| Representation/Classification/LanglandsData | AssemblyRelation | `Multisegment.IsLanglandsHead` | `3678fb721704` |
| Representation/Classification/Supercuspidal | SupercuspidalRelations | `SupercuspidalClass`, `SupercuspidalClass.toSmoothDualClass` | `c13ba8ffad11` |
| Representation/Classification/SupercuspidalTwist | SupercuspidalRelations | `toSmoothDualClass_twist` | `ee34d058655f` |
| Representation/Conductor/Congruence | UnramifiedNormalization | `integralSubgroup` | `c21658d4ae14` |
| Representation/Induction/BlockFactors | UnramifiedNormalization | `normalizedProductInduced` | `734929d120a1` |
| Representation/RankinSelberg/FunctionalEquationStatement | ArithmeticFactors | `epsilonMonomial` | `d2abd6d09f1c` |
| Representation/RankinSelberg/LanglandsFactors | FullFactorCompatibility | `IsLanglandsPairEpsilonFactor` | `1a3252c080fd` |
| Representation/RankinSelberg/LanglandsQuotientLFactorStatement | FullLFactorCompatibility | `IsLanglandsPairLPolynomial` | `5096be373e6c` |
| Representation/RankinSelberg/PadicPairFactors | SupercuspidalFactorCompatibility | `IsPadicSymmetricLPolynomial`, `IsPadicSymmetricEpsilonFactor` and their `congr_equiv` lemmas | `182e30861f1d` |
| Representation/RankinSelberg/PairFactors | SupercuspidalGammaCompatibility | `rationalGammaExpression` (used by FullGammaCompatibility) | `1a160d63a4f9` |
| Representation/Smooth/Contragredient/Definitions | AutomorphicRelations | `smoothContragredient` | `878b6130d7c5` |
| Representation/Twist/Definitions | AutomorphicRelations | `characterRepresentation`, `twist` | `9e193a22784c` |
| Weil/Local/Parameters | Domains | `LocalFrobeniusSemisimpleParameterClassesOfRank`, `LocalContinuousIrreducibleWeilClasses`, `LocalWeilRepresentation` | `411478f2fd50` |
| Weil/Representation/Determinant | OperationCompatibility | `determinantCharacter`, `determinantCharacterClass` | `9a327d3755e3` |
| Weil/Representation/DualClasses | OperationCompatibility | `continuousIrreducibleDualEquiv` | `126e2e2b73cf` |
| Weil/Representation/TwistClasses | OperationCompatibility | `continuousIrreducibleTwistEquiv` | `210fff747f1e` |
| WeilDeligne/BlockStatements | AssemblyLFactorStatement | `IsIndecomposable` | `2f4ab8469721` |
| WeilDeligne/DirectSum | AssemblyRelation, UnramifiedNormalization | `directSum` | `a8ec6276d9ed` |
| WeilDeligne/ParameterRelations | Domains | `forget` | `29d82698b084` |
| WeilDeligne/Restriction | ArithmeticFactors | `restrict` | `ef8109768e49` |
| WeilDeligne/SpecialBlocks | AssemblyRelation | `block` | `1280fb510bf4` |

The statements also name declarations that reach them only through these
imports:

| Module | Declarations used | `.lean` SHA-256 |
| --- | --- | --- |
| LocalFactor/CommonClosure | `ReciprocityFamily` | `b9031e072d4a` |
| LocalFactor/NonabelianSystem | `Assignment`, `IsSystem` | `2c1af8c3021a` |
| LocalFactor/WeilDelignePair | `pairLFactorClass`, `rationalLRatioClass` | `64acceef509c` |
| Representation/RankinSelberg/PairEpsilonFactor | `rationalEpsilonMonomial` | `7f3f9b3f491a` |

The two Mathlib imports are `Mathlib.RepresentationTheory.Intertwining`
(UnramifiedNormalization) and `Mathlib.Topology.MetricSpace.Ultra.TotallySeparated`
(LocalConventions). Their version is fixed by the Library's
`lean-environment.lock.json`, which belongs to environment artifact
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`.

## Delegated and coordinated responsibilities

No covered statement takes any of the inputs below as a hypothesis. A proof
would need them, and each belongs to its owner's task. The last item lists the
proofs themselves.

- **Nongeneric pair epsilon factor.** Worker 31 owns this factor (task
  `6f0365a3`). It was published as `RankinSelberg/LanglandsFactors`; Worker 7 is
  a coauthor of that candidate. `IsLanglandsPairEpsilonFactor` is a relation.
  To get a factor for a given pair you need the two propositions
  `LanglandsPairEpsilonBlockExistence` and
  `LanglandsPairEpsilonDataIndependence` in the same module. Both are stated and
  neither is proved.
- **Nongeneric pair L-factor.** Worker 11 owns `IsLanglandsPairLPolynomial`. Its
  existence for every irreducible admissible pair is
  `LanglandsPairLFactorExistenceStatement` (JPSS 1983 (9.4)), which is part of
  `LanglandsQuotientLFactorStatement` and is not proved.
- **Langlands classification.** Workers 34 and 126 wrote
  `Representation/Classification/MultisegmentClassificationStatement` (task
  `f72fff19`, `.lean` SHA-256 `639faca64a0e` at `bd3d155f`). This module is not
  imported here. Its `MultisegmentHeadExistence`, `MultisegmentHeadExhaustion`,
  `MultisegmentHeadClassification` and the `SquareIntegrableLanglands*`
  statements are classification inputs for proofs of
  `AssemblyWellDefinedStatement`, `AssemblyBijectiveStatement` and
  `ConditionalAssemblyStatement`.
- **Weil–Deligne blocks.** `WeilDeligne/BlockStatements` (imported for
  `IsIndecomposable`) also states `DecompositionExistence` and
  `DecompositionUniqueness`, neither of them proved. These are the block
  decomposition inputs of the same assembly proofs.
- **Local class field theory and local constants.** Worker 10's
  `LocalClassField.WeilReciprocityExistenceUniqueness` is not proved, and
  neither are `NonabelianSystem.Exists` and `NonabelianSystem.Unique` (Deligne's
  local constants). Proofs of the existence statements, and the agreement of
  existential and universal reciprocity, depend on them.
- **Proofs.** Every correspondence statement in this inventory is a separate
  proof obligation. The
  shared proof DAG records them as `proof.full-factor-compatibilities`,
  `proof.conditional-classification-assembly`, `proof.full-llc-characterization`
  and `proof.local-langlands-all-ranks`. A task search on 2026-10-22 found no
  published proof task for them.

## Remaining obligations

- Every statement above still needs a proof. The Library proves none of them.
- Source facts used only in design notes and not proved in the Library: Deligne's
  existence and uniqueness of local constants, the JPSS functional equation,
  `ψ`-independence (Henniart 2000 §1.3), and the identification of
  inverse-transpose pullbacks with contragredients.
- Source misprints recorded in published Markdown. Henniart 2002 §4.5
  restates Thm 1.8(ii) with `τ ∈ G(r)` and prints "⊗" for "×". The proof uses
  only `G_2(r)`, and `AssemblyLCharacterizationStatement` follows the proof
  (see `AssemblyLFactorStatement.md`). The text of §2.6 omits `ρ^∨` in the
  dual of `St_n(ρ)`; the correct form is `St_n(ρ)^∨ ≅ St_n(ν^(1-n) ρ^∨)`
  (Zelevinsky 1980 Props 3.3 and 9.4). Worker 11 records this in
  `Langlands/Representation/RankinSelberg/SegmentFactorStatement.md`. No
  module covered here states that identity.
- Superseded remark. `FullLFactorCompatibility.md` was published before the
  nongeneric epsilon factor. It still says that this factor "is not yet in the
  Library" and that the full L and epsilon condition will be a separate module.
  At `bd3d155f` the factor is `RankinSelberg/LanglandsFactors`, and that
  module is `FullFactorCompatibility`.
- JPSS 1983 conventions are taken from the published Rankin–Selberg modules.
  Worker 7 did not re-read the scan, which has no text layer.

## Published construction addendum: certified class pair factors

At Library commit `9ff0d4f8edaf10dd32d87468c3045da6ec3ee5c6`,
[`Langlands.Correspondence.AutomorphicPairFactors`](../../Langlands/Correspondence/AutomorphicPairFactors.md)
adds proved transport and uniqueness lemmas and conditional constructions.
It preserves the class predicates in `FullLFactorCompatibility` and
`FullFactorCompatibility`. It proves no correspondence statement from the
eighteen-module inventory above.

| Declaration | Published result |
| --- | --- |
| `Classification.IsIrreducibleQuotient.of_target_equiv` | Transports an actual surjective quotient intertwiner and irreducibility across a target equivalence |
| `RankinSelberg.IsLanglandsPairEpsilonFactor.congr_equiv`, `RankinSelberg.IsLanglandsPairLPolynomial.congr_equiv` | Preserve both existential presenting data and all universal factor certificates under representation equivalence |
| `isAutomorphicPairEpsilonFactor_iff`, `isAutomorphicPairLPolynomial_iff` | Identify the class relation with its representation relation on supplied equivalent representatives |
| `IsAutomorphicPairEpsilonFactor.unique`, `IsAutomorphicPairLPolynomial.unique` | Prove uniqueness for each fixed class pair, additive character and Haar measure |
| `IsAutomorphicPairLPolynomial.coeff_zero`, `.ne_zero` | Prove the certified polynomial has constant coefficient one and is nonzero |
| `automorphicPairLFactor`, `coe_automorphicPairLFactor`, `automorphicPairLFactor_eq` | Construct the rational unit `1/P(X)` from a certified class polynomial and prove independence from that certified input |
| `automorphicPairEpsilonFactor` | Package the existing representation epsilon constructor with its class certificate |

All names start with `Langlands`. Entries without `Classification` or
`RankinSelberg` prefixes are in `Langlands.Correspondence`. In the class adapters,
representatives have carrier universe `uA`, equivalent targets have universe
`max uF uA`, and block
carriers remain in `uA`. The additive character and Haar measure are fixed.

The L constructor requires a certified class polynomial. The epsilon constructor
requires supplied representatives and equivalences, square-integrable quotient
data existence for both targets, block-factor existence and datum independence.
The L certificates use tempered standard data; these are not identified with
the square-integrable epsilon data. Neither constructor establishes totality.
Classification, analytic existence, character/measure independence, smooth-dual
comparison and descent of block carriers to a smaller universe remain separate
obligations. In particular, the classification epsilon constructor with block
universe `max uF uA` cannot silently supply this adapter's block universe `uA`.

The paired Markdown explains the implemented algebraic proofs and their
derived provenance, with the original-source locations Henniart 2002 §§1.2,
2.8 and JPSS 1983 §9.4. This addendum records the published Lean API; it adds
no new source interpretation or analytic theorem.
