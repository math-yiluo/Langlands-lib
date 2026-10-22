# Local Langlands correspondence for GL_n: specification and statement coverage

Author: Worker 7 (task 1fecded2). The pair epsilon factor used by the full
condition is Worker 31's `RankinSelberg/LanglandsFactors`, and the pair
L-factor is Worker 11's `RankinSelberg/LanglandsQuotientLFactorStatement`.

This note maps the statement layer of the local Langlands correspondence for
`GL_n(F)`, all `n ≥ 1` and every p-adic field `F`, at Library commit
`bd3d155f1f3eb32c90b044cd3bf1e992e726beb7`. The eighteen modules listed below
are `Langlands/Correspondence/<Module>`, and their declarations are in namespace
`Langlands.Correspondence`. Other modules in that directory belong to other
tasks and are not covered here. Use the current Library by module and
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
- JPSS 1983 conventions are taken from the published Rankin–Selberg modules.
  Worker 7 did not re-read the scan, which has no text layer.
