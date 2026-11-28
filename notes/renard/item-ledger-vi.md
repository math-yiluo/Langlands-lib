# Renard 2026, Chapter VI: item-by-item coverage ledger

This note is the Chapter VI part of the item ledger of the whole book
([coverage.md](coverage.md)). It lists every headed
item of Chapter VI and the unheaded assertions found so far. For each row it gives
the printed and PDF pages, the Lean declarations, and the implementation status
with its evidence. It declares no section or chapter complete. A published
statement is not a proof; every row keeps the proof status explicit.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Printed page
numbers are given first and PDF page numbers second; PDF = printed + 6. Library
facts refer to commit `16c60abdc019c1181a2734d3052305ec3d6e7b85` unless stated
otherwise.

The VI.9.1 compression localization row, the VI.9.7 equivariance and
all-Iwahori-index row, and the VI.10.4 first-Lemma freeness proof refer to
Library `19fb2c25ab3dc0b2e83bebdca35724e7a62d864a`. The historical audits
below concern the rows as they stood at their own dated Library snapshots.

The F3 update of 14 November 2026 checks the VI.6.1 Proposition, VI.6.3 Corollary
and VI.9.4 rows against Library `757a67934ac7327ca3de64f9c869f76ea240ec44`.
The [`StandardIwahoriDecompositionStatements`](../../Langlands/Representation/Jacquet/StandardIwahoriDecompositionStatements.lean)
and its [paired Markdown](../../Langlands/Representation/Jacquet/StandardIwahoriDecompositionStatements.md)
first appeared in the Library at
`410c79471b79f65a02fb0f6070da7f2800793ff3`. Both files at the checked Library commit
match the hashes recorded when they were checked. At that commit the three statements
had no proofs; their comparison implications are proved. Other rows retain their earlier dated status.

The gap update of 14 November 2026 records the statement modules below. With
the other published statements named in the rows, they state the gaps of the earlier audit,
the framework comparisons F2 and F4, and VI.10.6 Proposition (i). The update
checks them against Library `c0debd6f4dd02fdd68d70811cf610906b945a962`. For each
module, both files at that commit have the SHA256 recorded when the module was checked. The module
`Jacquet/StandardIwahoriFixedVectorCategoryStatements` entered the Library later; it is checked at Library
`c40a01345b2f4172fa41e07ff31644b40e695003`, its first Library commit. The
rows VI.1.1 Remark, VI.2.1 Remark 1, VI.6.1, VI.6.3 Corollary, VI.9.1, VI.9.4, VI.10.6 and
VI.10.7 Variant, the framework comparisons and the gap list use this update. Other rows
retain their earlier dated status. At that commit none of the statements below had a proof.

| Module (under `Langlands/Representation/`) | First Library commit |
| --- | --- |
| [`Exponents/RepresentedIwahoriDecompositionStatements`](../../Langlands/Representation/Exponents/RepresentedIwahoriDecompositionStatements.md) | `db8d6b3d466f2fd453a4df4624ce6c90db8eed46` |
| [`Exponents/RepresentedCanonicalSectionStatements`](../../Langlands/Representation/Exponents/RepresentedCanonicalSectionStatements.md) | `e5365902d74534dbf1622c06e695dffdc128d723` |
| [`Exponents/RepresentedParabolicRemarksStatements`](../../Langlands/Representation/Exponents/RepresentedParabolicRemarksStatements.md) | `e5365902d74534dbf1622c06e695dffdc128d723` |
| [`CuspidalSupport/StandardLeviFixedVectorSupportStatements`](../../Langlands/Representation/CuspidalSupport/StandardLeviFixedVectorSupportStatements.md) | `4f6abf4c7e19610e4d89edc9bf64b34ba1db9ff2` |
| [`Families/RenardFamilyFiniteTypeStatements`](../../Langlands/Representation/Families/RenardFamilyFiniteTypeStatements.md) | `4f6abf4c7e19610e4d89edc9bf64b34ba1db9ff2` |
| [`Jacquet/StandardIwahoriCornerInductionStatement`](../../Langlands/Representation/Jacquet/StandardIwahoriCornerInductionStatement.md) | `e5365902d74534dbf1622c06e695dffdc128d723` |
| [`Jacquet/StandardIwahoriFixedVectorCategoryStatements`](../../Langlands/Representation/Jacquet/StandardIwahoriFixedVectorCategoryStatements.md) | `c40a01345b2f4172fa41e07ff31644b40e695003` |

The `Langlands.Hecke.LevelHeckeCornerComparisonStatement` (VI.9.4 Proposition row) is
proved by the exact proof below.

The Hecke comparison update of 17 November 2026 checks the
normalized comparison in the VI.9.4 Proposition row and gap 6 against Library
`b369a8f280229cf081a17f96b81c7a8c1ff1f539`. The theorem
[`Langlands.Hecke.levelHeckeCornerComparison`](../../Langlands/Representation/Hecke/LevelHeckeCornerComparisonProof.lean)
has exactly the type
`Langlands.Hecke.LevelHeckeCornerComparisonStatement.{u, v}`, with independent
group and representation-space universes. Its
[proof Markdown](../../Langlands/Representation/Hecke/LevelHeckeCornerComparisonProof.md)
describes the normalized coset expansion and its use for multiplication and
actions. The proof was checked by a Lake build against the exact target, with
the statement and its inputs unchanged, and first appeared in the Library at
`f24f97443f21ff7e59b1cf3b509602157dae54c2`. At the checked Library commit, the
proof and `Hecke/LevelHeckeCornerLinear` Lean–Markdown pairs have exactly the
hashes recorded when it was checked; the target pair is unchanged from the proof's base.

This derived bridge supplies the complex linear equivalence from the
measure-free `LevelHeckeAlgebra ℂ K` to `HeckeAlgebra.Corner μ K hK`, its
pointwise formula `e(a)(x) = μ(K)⁻¹ a(xK)`, product preservation and compatibility
with the two actions on `V^K`. It applies to every compact open subgroup of a
Hausdorff nonarchimedean locally compact group with a Borel measurable structure
and a left Haar measure, and every smooth complex representation. It needs no
normality, Iwahori decomposition or unimodularity assumption. The normalization
comes from Renard II.3.11–II.3.12 (printed pp.51–53 / PDF pp.57–59) and
III.1.3–III.1.5 (printed pp.59–60 / PDF pp.65–66); the comparison is an
derived implementation bridge for the use of `H(G,K)` in VI.9.4. Only this
comparison changes from S to P. The
categorical equivalence and inverse functor remain separate obligations with
the dated statuses below; every other row retains its earlier dated status.

The proof-status update of 17 November 2026 checks the rows of the
eight statements in the table below against Library
`ab9053b1751d6b6557d044c38c04e4c8a67dfffc`. For each statement the Library has a
theorem whose type is exactly that statement.
Each proof passed the proof checks. All eight first appeared
in the Library at `2613dbbf784309977c42d9252b78c1e1cd40be63`. At the checked commit the Lean
and Markdown files of each proof module have the SHA256 recorded when the proof was
checked and are byte-identical to `2613dbbf`; they contain no `sorry`, `admit`
or `axiom`. Only these eight statements change from S to P. The rows
VI.1.1 Remark, VI.2.1 Remark 1, VI.6.1 Theorem, VI.6.1 Proposition and VI.10.6
Corollary, the framework comparisons F2–F4 and the gap list use this update; every
other row retains its earlier dated status. Proof modules are under
`Langlands/Representation/`.

| Row | Statement | Theorem | Proof module |
| --- | --- | --- | --- |
| VI.1.1 Remark, first sentence | `RP.LeviUnnormalizedInductionRightAdjointStatement` | `leviUnnormalizedInductionRightAdjoint` | [Exponents/LeviUnnormalizedInductionRightAdjointProof](../../Langlands/Representation/Exponents/LeviUnnormalizedInductionRightAdjointProof.md) |
| VI.2.1 Remark 1 | `RP.SupercuspidalStandardParabolicCriterionStatement` | `supercuspidalStandardParabolicCriterion` | [Exponents/SupercuspidalStandardParabolicCriterionProof](../../Langlands/Representation/Exponents/SupercuspidalStandardParabolicCriterionProof.md) |
| VI.6.1 Theorem | `RP.RepresentedIwahoriContractionStatement` | `representedIwahoriContraction` | [Exponents/RepresentedIwahoriContractionProof](../../Langlands/Representation/Exponents/RepresentedIwahoriContractionProof.md) |
| VI.6.1 Theorem | `RP.RepresentedJacquetLemmaStatement` | `representedJacquetLemma` | [Exponents/RepresentedJacquetLemmaProof](../../Langlands/Representation/Exponents/RepresentedJacquetLemmaProof.md) |
| VI.6.1 Proposition | `RP.RepresentedChamberIwahoriContractionStatement` | `representedChamberIwahoriContraction` | [Exponents/RepresentedChamberIwahoriContractionProof](../../Langlands/Representation/Exponents/RepresentedChamberIwahoriContractionProof.md) |
| VI.6.1 Proposition | `RP.RepresentedCanonicalSectionStatement` | `representedCanonicalSection` | [Exponents/RepresentedCanonicalSectionProof](../../Langlands/Representation/Exponents/RepresentedCanonicalSectionProof.md) |
| VI.6.1 Proposition, standard parabolics | `J.StandardIwahoriCanonicalSectionStatement` | `standardIwahoriCanonicalSection` | [Jacquet/StandardIwahoriCanonicalSectionProof](../../Langlands/Representation/Jacquet/StandardIwahoriCanonicalSectionProof.md) |
| VI.10.6 Corollary | `CS.StandardLeviCompactInheritanceStatement` | `standardLeviCompactInheritance` | [CuspidalSupport/StandardLeviCompactInheritanceProof](../../Langlands/Representation/CuspidalSupport/StandardLeviCompactInheritanceProof.md) |

The proof-status update of 19 November 2026 checked the rows then marked S
against Library `24390f9f6d7a3b7df9e5b9dd4d6e79e178c8ac85`. As in the
update of 14 November 2026, each statement named in those rows at that time was compared with
the Library theorems whose type is exactly that statement. Only one statement
changes from S to P: `CS.StandardRepresentativeFixedVectorCriterionStatement`, the
first claim of the VI.10.6 Corollary (printed p.215 / PDF p.221). For a standard
cuspidal datum `(M_I, σ)` it says that some smooth representation with inertial
support `[M_I, σ]_G` has a nonzero `K`-fixed vector if and only if `σ` has a
nonzero vector fixed by `K ∩ M_I(F)`. The theorem
[`Langlands.CuspidalSupport.standardRepresentativeFixedVectorCriterion`](../../Langlands/Representation/CuspidalSupport/StandardRepresentativeFixedVectorCriterionProof.lean)
has exactly the type
`CS.StandardRepresentativeFixedVectorCriterionStatement.{uF, uV}`. The proof was
checked by a Lake build and first appeared in the Library at
`5f5d3a914cd43b9dc1cd32c07887a973f561df96`. At the checked commit the proof's Lean
and Markdown files have the SHA256 recorded when it was checked (`1a146c4b…` and
`eaa358cd…`). The statement pair `CuspidalSupport/StandardLeviFixedVectorSupportStatements`
has the SHA256 recorded when it was checked (`93e52b68…` and `6d4fedfe…`).
A separate check at the checked
commit compiles the proof module with no errors or warnings. The theorem depends
only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

The [proof Markdown](../../Langlands/Representation/CuspidalSupport/StandardRepresentativeFixedVectorCriterionProof.md)
follows the source's argument for (⇒). It writes a conjugating point as `pk`, with
`p` in a standard parabolic and `k ∈ K₀`. Normality of `K` under `K₀` and the
Iwahori projection then move fixed vectors along the Levi part of `p`. The published
normal-level Mackey criterion `Jacquet.nontrivial_standardInduction_fixedVectors_iff`
replaces the source's Jacquet modules. A representative of the inertial class may
lie on another standard Levi. The proof handles this case by transport along an
actual Levi conjugacy and an unramified twist, without the VI.5.4 Lemma or
inertial-support invariance. The direction (⇐) is the published
`exists_bernsteinInertialSupport_fixedVectors_of_literalLevi`
(`CuspidalSupport/StandardRepresentativeFixedVectorHelpers`). Three hypotheses of
the statement are unused: the standard-cocharacter hypothesis, compactness of `K₀`
and `K ≤ K₀`.

At the 19 November check, the Library had a supporting result but no proof of
`CS.StandardLeviFixedVectorSupportStatement`. The theorem
`nontrivial_standardLeviInduction_fixedVectors_iff`
([`CuspidalSupport/StandardLeviInductionFixedVectors`](../../Langlands/Representation/CuspidalSupport/StandardLeviInductionFixedVectors.md))
proves the separate proposition `CS.StandardLeviInductionFixedVectorsStatement`.
For standard indices `leviIndex J I ⊆ J`, normalized induction inside `M_J` has a
nonzero `K ∩ M_J(F)`-fixed vector if and only if its coefficient has a nonzero
vector fixed by `K ∩ M_{leviIndex J I}(F)`. It first appeared in the Library at
`b86269dd36757fdbea2e51976499d645ca61a625`, and at the checked commit both files
have the SHA256 recorded when it was checked. This is a step of the target's proof, not the
exact proof. See the 20 November follow-up for the exact proof. Only the
VI.10.6 Corollary row and gap 4 use this update.

The proof-status follow-up of 20 November 2026 checks Library
`d6b462beebdb629f6b6746bdf0698a800d84104f`. The Library has the exact proof
[`Langlands.CuspidalSupport.standardLeviFixedVectorSupport`](../../Langlands/Representation/CuspidalSupport/StandardLeviFixedVectorSupportProof.lean),
of type `CS.StandardLeviFixedVectorSupportStatement.{uF, uV}`. It was checked
by a Lake build against the exact target, with the statement and its inputs
unchanged, and first appeared in the Library at `6e9e589baa721ce995563f73f648b6f4e45718a1`.
At both Library commits the proof pair has the SHA256 recorded when it was checked
(`afa67699…` and `781b42bf…`); the statement pair still matches the proof's base.
A separate check compiles the proof
module at the checked commit with no errors or warnings.

For a standard Levi `M = M_J` and a nested standard cuspidal datum `b`, the
result proves `[b]_M ∈ B(M)_{K ∩ M}` iff `[b]_G ∈ B(G)_K`. It keeps the
published hypotheses, including the minimal Iwasawa factorization, compact
open `K` normal in `K₀`, and the standard Iwahori decompositions. The
[proof Markdown](../../Langlands/Representation/CuspidalSupport/StandardLeviFixedVectorSupportProof.md)
explains the use of induction in stages instead of repeating the representative
criterion inside `M` as on printed p.215 / PDF p.221. In the forward direction,
compact-open fixed-vector exactness lifts nontriviality from an irreducible
subquotient to the normalized induction inside `M` of its datum `b'`. The
inside-Levi criterion then detects a fixed vector of the coefficient at
`K ∩ M_{b'.roots}(F)`, and the ambient representative criterion gives an
irreducible representation with nonzero `K`-fixed vectors. The `M`-inertia
relation also gives equality of the two ambient inertial classes, implementing
`i_{MG}` on representatives (VI.7.3, printed p.185 / PDF p.191). In the reverse
direction, the two criteria give a nonzero fixed vector in the induction inside
`M` of `b` itself, and `SmoothRep.hasFixedVectorConstituent_of_nontrivial`
produces an irreducible subquotient retaining one. The proof does not construct
`B(M)` as a type or `i_{MG}` as a function. Only the final support statement
changes from S to P in this follow-up (VI.10.6 Corollary row and gap 4).

The conditional reduction update of 17 November 2026 checks the VI.6.3 Corollary and VI.9.4 Corollary rows against Library
`371b9c350ae74d42665a9e7e0ec32e4c66f56619`. The module
[`Jacquet/StandardIwahoriSubquotientGenerationReduction`](../../Langlands/Representation/Jacquet/StandardIwahoriSubquotientGenerationReduction.lean),
with its [paired Markdown](../../Langlands/Representation/Jacquet/StandardIwahoriSubquotientGenerationReduction.md),
proves the theorem
`J.standardIwahoriFixedVectorSubquotientGeneration_of_specialVertexInputs`. Its
only premise is the unproved `CS.RationalSpecialVertexCompactInputsStatement.{uF}`.
Its conclusion is the unchanged
`J.StandardIwahoriFixedVectorSubquotientGenerationStatement.{uF, uV}`. The variants
`J.standardIwahoriFixedVectorSubquotientGeneration_of_jointBasis`, `_of_availability`
and `_of_groupAxiomsExistence` instead take one of these premises:
`Langlands.BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement`,
`Langlands.Geometry.Building.BruhatTitsAvailabilityStatement`
or `Langlands.Geometry.Building.GroupAxiomsExistenceStatement`. All three are unproved
at the checked commit. The source obtains the corollary by rerunning the proof of
Corollary VI.6.3 with the generalized Jacquet lemma (printed p.200 / PDF p.206). The
Lean proof uses instead a weak Jacquet lemma that holds for every smooth
representation. Its contracting element is a power of the standard cocharacter, so the
proof uses no hypothesis on `K` beyond those of the target statement. The module's
entry, checked as a definition, is
the proposition-valued definition
`J.standardIwahoriFixedVectorSubquotientGenerationOfSpecialVertexInputs`, whose type is
this implication. It first appeared in the Library at the checked
commit, where both files have exactly the SHA256 recorded when it was checked. This is
a conditional implication, not a proof of the target. Both rows keep their status. Every other row retains its earlier dated status.

The proof-status update of 14 November 2026 checked the rows then marked S
against Library `a163f87c7a46874f408deed853c10c83207e9f69`. Each statement
named in those rows at that time was compared with the Library theorems whose type is exactly that
statement, with no hypotheses. A statement is marked proved (P) only when such a
theorem exists. For each one the theorem line was read; its file has no `sorry` or
`admit`. The table gives, for each proof, the Library commit where it first appeared.
Its Lean and Markdown files at the checked commit have the SHA256 recorded when the
proof was checked. Proof modules
named by bare paths in the rows are under `Langlands/Representation/`. For the
statements of the other S rows, no such theorem exists at that commit.

| Row | Theorem | Proof module | First Library commit |
| --- | --- | --- | --- |
| VI.3.1 Lemma | `rationalNormKernelConjugationLemma` | [RationalNormKernelConjugationLemmaProof](../../Langlands/Representation/CuspidalSupport/RationalNormKernelConjugationLemmaProof.md) | `cfedefb6` |
| VI.3.3 Remarks 1–2, VI.4.4 Remark | `rationalTwistStabilizerKernel` | [RationalTwistStabilizerKernelProof](../../Langlands/Representation/CuspidalSupport/RationalTwistStabilizerKernelProof.md) | `cfedefb6` |
| VI.3.3 Remarks 1–2, VI.7.1 Example | `rationalInertiaOrbitTorus` | [RationalInertiaOrbitTorusProof](../../Langlands/Representation/CuspidalSupport/RationalInertiaOrbitTorusProof.md) | present in `ed924aef`, the oldest available snapshot |
| VI.4.2 Proposition, right modules | `rationalNormKernelHeckeModule` | [RationalNormKernelHeckeModuleProof](../../Langlands/Representation/CuspidalSupport/RationalNormKernelHeckeModuleProof.md) | `cfedefb6` |
| VI.4.3 structure | `rationalNormKernelHecke_structure` | [RationalNormKernelHeckeStructureProof](../../Langlands/Representation/CuspidalSupport/RationalNormKernelHeckeStructureProof.md) | `cfedefb6` |
| VI.4.4 Lemma | `rationalSummandStabilizerLemma` | [RationalSummandStabilizerLemmaProof](../../Langlands/Representation/CuspidalSupport/RationalSummandStabilizerLemmaProof.md) | `cfedefb6` |
| VI.4.4 Proposition, variety | `rationalSummandCenterVariety` | [RationalSummandCenterVarietyProof](../../Langlands/Representation/CuspidalSupport/RationalSummandCenterVarietyProof.md) | `b128d289` |
| VI.4.5 Corollary | `rationalInertiaBlockIndecomposable` | [RationalInertiaBlockIndecomposableProof](../../Langlands/Representation/CuspidalSupport/RationalInertiaBlockIndecomposableProof.md) | `cfedefb6` |
| VI.5.4 Lemma | `standardWeylElementaryChain` | [StandardWeylElementaryChainProof](../../Langlands/GroupScheme/Rational/StandardWeylElementaryChainProof.md) | `cc5aa77f` |
| VI.7.1 Theorem, component variety | `bernsteinComponentVariety` | [BernsteinComponentVarietyProof](../../Langlands/Representation/CuspidalSupport/BernsteinComponentVarietyProof.md) | `cc5aa77f` |
| VI.9.6, equivalence of the two Theorems | `leviSecondAdjointnessContragredientEquivalence` | [LeviSecondAdjointnessContragredientEquivalenceProof](../../Langlands/Representation/Exponents/LeviSecondAdjointnessContragredientEquivalenceProof.md) | `cfedefb6` |
| VI.10.4 second Lemma | `inducedProgeneratorCenterInclusion` | [InducedProgeneratorCenterInclusionProof](../../Langlands/Representation/CuspidalSupport/InducedProgeneratorCenterInclusionProof.md) | `51e4d897` |
| VI.10.4 third Lemma | `renardBimoduleFiltrationCentralizer` | [RenardBimoduleFiltrationCentralizerProof](../../Langlands/Algebra/RenardBimoduleFiltrationCentralizerProof.md) | `cfedefb6` |

The VI.7.2 Theorem, VI.7.2 first Lemma and VI.10.4 Corollary rows concern
`CS.BernsteinDecompositionStatements`, the conjunction of
`CS.BernsteinDecompositionStatement`, `CS.BernsteinSplitSubrepresentationStatement`
and `CS.BernsteinBlockAbelianStatement`, and `CS.BernsteinBlockCenterStatements`, the
conjunction of `CS.BernsteinBlockCenterNoetherianStatement` and
`CS.BernsteinBlockIndecomposableStatement`. At Library
`58ad0f796899b4aa457077d0146815c24758f739` the Library had only conditional
reductions for these targets: `bernsteinDecompositionStatements_of_inputs` and
`bernsteinBlockCenterStatements_of_centerFunctions`, the latter from the open
`CS.BernsteinBlockCenterFunctionsStatement`. No status letter changes.

## How the rows were checked

Each headed item was matched with the declarations whose docstring or
Markdown cites that section, and the source passage was read where the match was not
obvious. An earlier tool matched items by Markdown mentions alone. It over-reported
coverage: VI.2.2 Corollary, VI.2.3–VI.2.4 and VI.3.1 had no statement. These items
were stated afterwards (rows below). Proof status comes from a scan of the Library
for theorems whose type is exactly the statement (`proved by`).

Many Chapter VI statements are **derived formulations**: they use the
represented-parabolic interface (all actual rational parabolics) or the standard-family
interface (`BernsteinStandardFamily`, `BernsteinCuspidalDatum`), and each statement's
Markdown documents its departures from the printed text. A row marks a departure when it
restricts the scope of the source assertion; the comparisons it needs are collected under
"Framework comparisons" below.

Namespace abbreviations: `CS` = `Langlands.CuspidalSupport`,
`RP` = `Langlands.Aubert.General.RepresentedParabolic`,
`RPF` = `Langlands.Aubert.General.RationalPointFamily`,
`AG` = `Langlands.Aubert.General`, `J` = `Langlands.Jacquet`,
`AF` = `Langlands.Renard.AlgebraicFamily`, `PN` = `Langlands.Plancherel.RationalNormalized`.

Status codes:

- **P**: proved; the named theorem has exactly the statement's type.
- **S**: statement published; its proof is open. (All statements with status S were
  checked again against the present Library: none has an unconditional proof.)
- **D**: definition or construction.
- **C**: covered by a published statement that is stronger or equivalent, or
  derived from published statements; the row says which.
- **Restricted scope**: the published statement covers the item only under extra
  hypotheses, which the row names; the full source scope is a gap.
- **St**: a step of the proof of a stated result, covered by that result or by a
  proved construction.
- **X**: expository, convention or attribution.
- **G**: genuine gap, with its blocker.

## VI.1 Parabolic induction and restriction

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| VI.1.1 Theorem | 135 / 141 | `RP.LeviUnnormalizedFrobeniusReciprocityStatement`, `RP.LeviUnnormalizedFunctorsExactStatement` | P: `leviUnnormalizedFrobeniusReciprocity`, `leviUnnormalizedFunctorsExact` |
| VI.1.1 Corollary | 135 / 141 | `RP.LeviUnnormalizedFunctorsPreserveLimitsStatement` | P: `leviUnnormalizedFunctorsPreserveLimits` |
| VI.1.1 Remark, conclusion (`Ind_P^G` preserves colimits) | 135 / 141 | `RP.LeviUnnormalizedFunctorsPreserveLimitsStatement`, `RP.LeviUnnormalizedParabolicStatements` | P: `leviUnnormalizedFunctorsPreserveLimits` |
| VI.1.1 Remark, first sentence (`Ind_P^G` has a right adjoint) | 135 / 141 | `RP.LeviUnnormalizedInductionRightAdjointStatement` (`Exponents/RepresentedParabolicRemarksStatements`): for every actual rational parabolic, `Ind_P^G` (pullback along the Levi-point equivalence, inflation, then smooth induction from `P(F)`, with no normalizing character) satisfies `IsLeftAdjoint` | P: `leviUnnormalizedInductionRightAdjoint` (`Exponents/LeviUnnormalizedInductionRightAdjointProof`; proof-status update of 17 November 2026). The statement asserts existence of a right adjoint; it does not name the source's construction from `I_M^P`, the pseudo-forgetful functor and a twist |
| VI.1.2 normalizations (VI.1.2.1)–(VI.1.2.2) | 135 / 141 | normalized functors of the represented-parabolic interface (`Langlands/Representation/Aubert/General/Parabolic`) | D |
| VI.1.2 Remark (convention for `δ_P`) | 136 / 142 | modulus conventions recorded in `Aubert/General/Parabolic.md` | X |
| VI.1.2 Proposition | 136 / 142 | `RP.LeviFrobeniusReciprocityStatement`, `RP.LeviParabolicFunctorsExactStatement` | P: `leviFrobeniusReciprocity`, `leviParabolicFunctorsExact` |
| VI.1.2 Corollary | 136 / 142 | `RP.LeviParabolicFunctorsPreserveLimitsStatement` | P: `leviParabolicFunctorsPreserveLimits` |
| VI.1.2 Remarks (`δ_P` trivial on compact subgroups and on `N`; (VI.1.2.3)) | 136 / 142 | `isUnimodularModulus_of_isLimitOfCompactSubgroups`, `closedHalfCharacter_unipotent`, `normalizedInductionFunctor_covariant` (`Aubert/General/Parabolic`) | P (proved lemmas) |
| VI.1.3 Proposition | 136 / 142 | `RP.LeviJacquetFiniteTypeStatement` | P: `leviJacquetFiniteType` |
| VI.1.4 Lemma | 137 / 143 | `RP.LeviParabolicTransitivityStatement`; dynamic form `AG.DynamicNestedParabolicTransitivityStatement` | P: `leviParabolicTransitivity` |

## VI.2 Supercuspidal representations

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| VI.2.1 Definition | 137 / 143 | `RP.IsSupercuspidal` (`Exponents/LeviSupercuspidalInductionSupport`) | D |
| VI.2.1 Remark 1, first block (standard parabolics suffice) | 137 / 143 | `RP.SupercuspidalStandardParabolicCriterionStatement` (`Exponents/RepresentedParabolicRemarksStatements`): for a maximal split torus `i` and a generic cocharacter `ν`, `RP.IsSupercuspidal A` holds iff the normalized Jacquet module of `A` vanishes along every proper actual rational parabolic whose parabolic and Levi subgroup functors are `standardParabolic i ν J` and `standardLevi i ν J` for some `J ⊆ Δ` | P: `supercuspidalStandardParabolicCriterion` (`Exponents/SupercuspidalStandardParabolicCriterionProof`; proof-status update of 17 November 2026) |
| VI.2.1 Remark 2, first block (subquotients) | 137 / 143 | `RP.IsSupercuspidal.of_isSubquotient`; conjunct of `RP.SupercuspidalRemarksStatements` | P (theorem); S for the conjunction |
| VI.2.1 Theorem, (a) ⇔ (c) | 137 / 143 | `RPF.RationalCuspidalCompactRestrictionStatement`, `RPF.RationalCompactRestrictionCuspidalStatement` (standard-family cuspidality, `rationalPointTopology`) | P: `rationalCuspidalCompactRestriction`, `rationalCompactRestrictionCuspidal` |
| VI.2.1 Theorem, (a) ⇔ (b) | 137 / 143 | `RP.SupercuspidalCoefficientCriterionStatement`; unitary irreducible case `RP.SupercuspidalUnitaryCoefficientCompactSupportStatement` | S |
| VI.2.1 Remarks, second block (compact centre; `f_{K,v}` criterion) | 139 / 145 | `RP.SupercuspidalRemarksStatements` | S |
| VI.2.1 Corollary | 139 / 145 | `RPF.RationalCuspidalEmbeddingStatement`, `RP.LeviCuspidalEmbeddingStatement`, `RPF.RationalCuspidalSeriesExistenceStatement` | P: `rationalCuspidalEmbedding`, `leviCuspidalEmbedding`, `rationalCuspidalSeriesExistence` |
| VI.2.2 Theorem | 140 / 146 | `AG.RationalPointsIrreducibleAdmissibleStatement` | S |
| VI.2.2 Corollary | 140 / 146 | `CS.ContragredientIrreducibilityStatement` | S |
| VI.2.3 Theorem and Remark | 140–141 / 146–147 | `CS.RationalPointsUniformAdmissibilityStatement`, `CS.RationalNormKernelUniformAdmissibilityStatement` (in `CS.UniformAdmissibilityStatements`) | S |
| VI.2.4 Proposition | 141 / 147 | `CS.SupercuspidalUniformCoefficientSupportStatement` (in `CS.UniformAdmissibilityStatements`) | S |

## VI.3 The cuspidal part of the category

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| VI.3.1 Lemma | 142–143 / 148–149 | `CS.RationalNormKernelConjugationLemmaStatement` | P: `rationalNormKernelConjugationLemma` (`CuspidalSupport/RationalNormKernelConjugationLemmaProof`) |
| VI.3.2 Proposition (i)–(iii) | 143 / 149 | `CS.RationalNormKernelOrbitStatement`, `CS.RationalNormKernelFiniteRestrictionStatement`, `CS.RationalNormKernelTwistEquivalenceStatement` | P: `rationalNormKernelOrbit`, `rationalNormKernelFiniteRestriction`, `rationalNormKernelTwistEquivalence` |
| VI.3.3 Proposition (`W'` is `G`-invariant; `π(g) ∘ π(e_{σ_i}) = π(e_{σ_i^g}) ∘ π(g)`) | 145 / 151 | VI.3.1 (ii) above, `CompactIsotypicComplementStatement` (IV.1.5), and the covariance lemma `pointwiseFiniteSum_isotypic_covariant` (`CompactCoefficient/AmbientProjector`) | C: derived from these |
| (VI.3.3.1) decomposition | 145 / 151 | `CS.RationalCuspidalInertiaDecompositionStatement`; compact-restriction form `CS.RationalCompactRestrictionInertiaDecompositionStatement` | S; compact-restriction form P |
| VI.3.3 Remarks 1–2 | 145 / 151 | `CS.RationalInertiaOrbitTorusStatement`, `CS.RationalTwistStabilizerKernelStatement`; Remark 2 from VI.3.2 (i), (iii) and VI.2.1 | P: `rationalInertiaOrbitTorus` (`CuspidalSupport/RationalInertiaOrbitTorusProof`) and `rationalTwistStabilizerKernel` (`CuspidalSupport/RationalTwistStabilizerKernelProof`); Remark 2 C |
| VI.3.4 Theorem | 146 / 152 | `CS.RationalNormKernelCategoryDecompositionStatement` (with `CS.RationalNormKernelUniformSupportStatement`, `CS.RationalNormKernelFixedLevelFinitenessStatement`) | S |
| VI.3.4 Remark | 146 / 152 | `CS.RationalCuspidalInertiaFinitenessStatement` | S |
| VI.3.5 Theorem | 146 / 152 | `CS.RationalWholeCuspidalCategoryDecompositionStatement`, `CS.RationalCuspidalInertiaProductDecompositionStatement`, `RP.RepresentedCuspidalRemainderSplittingStatement` | S |
| VI.3.6 Lemma | 147 / 153 | `RP.RepresentedSupercuspidalSubquotientRealizationStatement` | S |
| VI.3.6 Proposition | 148 / 154 | `RP.RepresentedSupercuspidalCentralProjectivityStatement` | S |

## VI.4 The category `M(G)[π]` and its centre

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| VI.4.1 Proposition | 149 / 155 | `CS.RationalSummandSmallProgeneratorStatement` | S |
| VI.4.1 Remark | 149–150 / 155–156 | `CS.RationalUniversalSmallProgeneratorStatement`; comparison `CS.RationalUniversalProgeneratorComparisonStatement` | S; comparison P |
| VI.4.1 Theorem | 150 / 156 | `CS.RationalSummandHomEquivalenceStatement`; quasi-inverse `CS.RationalSummandTensorQuasiInverseStatement` | S |
| VI.4.2 Proposition | 152 / 158 | `CS.RationalNormKernelHeckeStatement`; right-module paragraphs `CS.RationalNormKernelHeckeModuleStatement` | P: `rationalNormKernelHecke_equiv`; modules P: `rationalNormKernelHeckeModule` (`CuspidalSupport/RationalNormKernelHeckeModuleProof`) |
| VI.4.3 structure (VI.4.3.1)–(VI.4.3.3) | 154–155 / 160–161 | `CS.RationalNormKernelHeckeStructureStatement` | P: `rationalNormKernelHecke_structure` (`CuspidalSupport/RationalNormKernelHeckeStructureProof`) |
| VI.4.3 Lemma | 154 / 160 | `CS.RationalNormKernelEndSeparationStatement` | P: `rationalNormKernelEnd_separation` |
| VI.4.3 Corollary (i)–(ii) | 155 / 161 | `CS.RationalNormKernelEndDomainStatement`, `CS.RationalSummandEndCommutativeStatement` | P: `rationalNormKernelEnd_isDomain`, `rationalSummandEnd_commutative` |
| VI.4.4 Remark (the group `T`) | 157 / 163 | `CS.RationalTwistStabilizerKernelStatement` | P: `rationalTwistStabilizerKernel` (`CuspidalSupport/RationalTwistStabilizerKernelProof`) |
| VI.4.4 Lemma | 157 / 163 | `CS.RationalSummandStabilizerLemmaStatement` | P: `rationalSummandStabilizerLemma` (`CuspidalSupport/RationalSummandStabilizerLemmaProof`) |
| VI.4.4 Theorem | 158 / 164 | `CS.RationalSummandEndCenterStatement` | P: `rationalSummandEndCenter` |
| VI.4.4 Corollary | 159 / 165 | `CS.RationalSummandEndNoetherianStatement`; remark on modules `CS.RationalInertiaBlockNoetherianModulesStatement` | P: `rationalSummandEndNoetherian`; remark S |
| VI.4.4 Proposition | 159 / 165 | `CS.RationalSummandCenterGroupAlgebraStatement`, `CS.RationalSummandCenterVarietyStatement` | P: `rationalSummandCenterGroupAlgebra`; variety P: `rationalSummandCenterVariety` (`CuspidalSupport/RationalSummandCenterVarietyProof`) |
| VI.4.5 Proposition | 160 / 166 | `CS.RationalInertiaBlockCenterEvaluationStatement`, `CS.RationalSummandBlockCenterStatement` | S |
| VI.4.5 Corollary | 160 / 166 | `CS.RationalInertiaBlockIndecomposableStatement` | P: `rationalInertiaBlockIndecomposable` (`CuspidalSupport/RationalInertiaBlockIndecomposableProof`) |

## VI.5 The geometric lemma and composition series of induced supercuspidals

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| VI.5.1 Theorem and its reformulation | 161–162 / 167–168 | `RP.RepresentedGeometricLemmaStatement`, `RP.RepresentedGeometricLemmaGeometryStatement` | P: `representedGeometricLemma`, `representedGeometricLemmaGeometry` |
| VI.5.1 Remarks (representatives `W_{Q,P}`; notation for the conjugation functor) | 161 / 167 | `RP.RepresentedGeometricLemmaGeometryStatement`; conjugation functors in `Aubert/General/ConjugationComposition` | P / D |
| VI.5.1 Proposition (support filtration lattice) | 162 / 168 | support filtration construction `Aubert/General/ParabolicSupportFiltration` | St: step of the proved VI.5.1 Theorem |
| (VI.5.1.3) injectivity (proof replaced in the 2026 edition) | 167 / 173 | step of the proved VI.5.1 Theorem | St |
| VI.5.2 Definition (cuspidal datum) | 172 / 178 | `BernsteinCuspidalDatum` (standard family, `CuspidalSupport/BernsteinData`); represented cuspidal-support predicates (`Exponents/LeviSupercuspidalInductionSupport`) | D |
| VI.5.2 Lemma | 173 / 179 | `RP.LeviInductionNoSupercuspidalSubquotientStatement` | S |
| VI.5.3 Proposition (i) | 173 / 179 | `RP.LeviJacquetInductionVanishingStatement` | P: `leviJacquetInductionVanishing` |
| VI.5.3 Proposition (ii) | 173 / 179 | `RP.LeviJacquetInductionNoSupercuspidalStatement` | S |
| VI.5.3 Proposition (iii) | 173 / 179 | `RP.LeviJacquetInductionSupercuspidalFiltrationStatement` | P: `leviJacquetInductionSupercuspidalFiltration` |
| VI.5.4 Theorem | 173–175 / 179–181 | `RP.LeviSupercuspidalInductionAssociationStatement`, `CS.BernsteinSupercuspidalInductionBoundsStatement`, `RPF.RationalSupercuspidalInductionFiniteLengthStatement`, `RPF.RationalCuspidalSupportAssociationStatement` | S |
| VI.5.4 definition of elementary elements | 175 / 181 | inline in `Langlands.GroupScheme.StandardWeylElementaryChainStatement` | D (inline, see next row) |
| VI.5.4 Lemma (Bernstein–Zelevinsky, Lemma 2.17) | 175 / 181 | `Langlands.GroupScheme.StandardWeylElementaryChainStatement` (hypothesis `L ≠ G` added: the literal lemma fails for `L = M = G`, `w ≠ 1`) | P: `standardWeylElementaryChain` (`Langlands/GroupScheme/Rational/StandardWeylElementaryChainProof`). `W(L, M)` and `l_S(M)` are written inline on the actual relative Weyl group, asked on 12 November 2026, has no named version and knows of none planned |
| VI.5.4 Corollary (i)–(iii) | 175 / 181 | `RP.LeviSupercuspidalInductionSameLeviStatement` | S |

## VI.6 Finiteness theorems

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| VI.6.1 Theorem (Jacquet lemma, admissible `V`) | 176 / 182 | Source scope: `RP.RepresentedJacquetLemmaStatement` (`Exponents/RepresentedIwahoriDecompositionStatements`): actual rational parabolics `P = MN`, `P̄ = MN̄` with the same Levi and `P(F) ∩ P̄(F) = M(F)`, every compact open `K = (K ∩ N̄(F))(K ∩ M(F))(K ∩ N(F))`, every admissible `V`; with the derived `RP.RepresentedIwahoriContractionStatement` (large powers of an element of `A^{++}` satisfy `IsIwahoriContraction`). Earlier forms: `RPF.GeneralizedJacquetLemmaStatement` (all smooth `V`, dynamic parabolics, `K` admitting an `M`-central `g` with `IsIwahoriContraction`) and `Langlands.Jacquet.fixedJacquetMap_surjective_of_iwahoriContraction` (`Jacquet/IwahoriContractionAdmissibility`, given one explicit contraction) | P for both represented statements: `representedJacquetLemma` and `representedIwahoriContraction` (`Exponents/RepresentedJacquetLemmaProof`, `Exponents/RepresentedIwahoriContractionProof`; proof-status update of 17 November 2026). The dynamic statement is S; the earlier admissible form is P under its explicit contraction hypothesis |
| VI.6.1 Corollary | 176 / 182 | `RP.ArbitraryParabolicJacquetAdmissibilityStatement` | P: `arbitraryParabolicJacquetAdmissibility` |
| VI.6.1 Proposition and (VI.6.1.2) | 177 / 183 | Arbitrary parabolics: `RP.RepresentedCanonicalSectionStatement` (`Exponents/RepresentedCanonicalSectionStatements`; the setting of the VI.6.1 Theorem row, admissible `V`, one `ε ≤ 1` and one section `s` for all `t ∈ A^+(ε)`), with the derived `RP.RepresentedChamberIwahoriContractionStatement` (every `t ∈ A^+(ε)` satisfies `IsIwahoriContraction`). Standard parabolics: `J.StandardIwahoriCanonicalSectionStatement` (every compact open `K` with the ordered Iwahori decomposition); earlier `J.StandardCanonicalSectionStatement` | P for the two represented statements: `representedCanonicalSection` and `representedChamberIwahoriContraction` (`Exponents/RepresentedCanonicalSectionProof`, `Exponents/RepresentedChamberIwahoriContractionProof`). P for the standard Iwahori-only statement: `standardIwahoriCanonicalSection` (`Jacquet/StandardIwahoriCanonicalSectionProof`). Both from the proof-status update of 17 November 2026. The earlier basis-member special case is P: `standardCanonicalSection` |
| VI.6.2 Lemma | 178 / 184 | `AG.DynamicInductionIrreducibleFiniteLengthStatement`; main assertion `RP.LeviInductionFiniteLengthStatement`, `AG.DynamicInductionFiniteLengthStatement` | S |
| VI.6.3 Theorem (Howe) | 178 / 184 | `AG.RationalPointsFiniteLengthAdmissibleStatement`, `Langlands.SmoothRep.RationalPointsFinitelyGeneratedAdmissibleFiniteLengthStatement` | S; finite length ⇒ finite type is immediate (a finite-length object is Noetherian) |
| VI.6.3 Lemma | 178 / 184 | `Langlands.Jacquet.FixedVectorsGenerationStatement` (theorem `fixedVectorsGeneration`), `NormalizedJacquetBridge.normalized_generation` | P |
| VI.6.3 Proposition | 178 / 184 | `CS.SupercuspidalSubquotientFixedVectorsStatement` (every compact open `K`) | S |
| VI.6.3 Corollary | 179 / 185 | the VI.9.4 Corollary statement `J.StandardIwahoriFixedVectorSubquotientGenerationStatement` (no admissibility; `K` normal in `K₀` with Iwahori decompositions along every standard parabolic) | C: the admissible special case of this published statement, whose proof is open. It follows from the unproved `CS.RationalSpecialVertexCompactInputsStatement` by the conditional reduction `J.standardIwahoriFixedVectorSubquotientGeneration_of_specialVertexInputs` (conditional reduction update of 17 November 2026 above). The earlier basis-member version `J.StandardFixedVectorSubquotientGenerationStatement` remains S |
| VI.6.4 (finite length of Jacquet modules) | 179 / 185 | `RP.LeviJacquetFiniteLengthStatement`, `AG.DynamicJacquetFiniteLengthStatement` | S |

## VI.7 The Bernstein decomposition

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| VI.7.1 Lemma | 180 / 186 | `RP.LeviCuspidalSupportAssociationStatement` | S |
| VI.7.1 Proposition | 180 / 186 | `RP.LeviCuspidalSupportSurjectiveStatement`; finite fibres `CS.BernsteinCuspidalSupportFiniteFibreStatement` | S |
| VI.7.1 Example | 181 / 187 | variety part is the V.2.7 Corollary `CS.RationalInertiaOrbitTorusStatement` | C; P: `rationalInertiaOrbitTorus` (`CuspidalSupport/RationalInertiaOrbitTorusProof`) |
| VI.7.1 Theorem | 181 / 187 | `CS.BernsteinCuspidalDataVarietyStatements`, `CS.BernsteinComponentVarietyStatement` | `CS.BernsteinComponentVarietyStatement` P: `bernsteinComponentVariety` (`CuspidalSupport/BernsteinComponentVarietyProof`). `CS.BernsteinCuspidalDataVarietyStatements` is its conjunction with the open `CS.BernsteinCuspidalSupportFiniteFibreStatement` (VI.7.1 Proposition row): S |
| VI.7.2 Theorem | 182 / 188 | `CS.BernsteinDecompositionStatement`; abelian blocks `CS.BernsteinBlockAbelianStatement` | S (see the paragraph on the Bernstein targets above); abelian blocks P: `bernsteinBlockAbelian` |
| VI.7.2 first Lemma | 182 / 188 | `CS.BernsteinSplitSubrepresentationStatement` | S |
| VI.7.2 second Lemma | 182–183 / 188–189 | `CS.BernsteinCuspAdjunctionStatement` | S |
| VI.7.2 Proposition | 184 / 190 | `CS.BernsteinBlockCharacterizationStatement` | S |
| VI.7.3 Proposition | 185 / 191 | `CS.BernsteinInductionRestrictionStatement`, `RPF.RationalSupportCategoryInductionJacquetStatement` | S |
| VI.7.4 idempotents and Hecke ideals | 185–186 / 191–192 | `CS.BernsteinCentralIdempotentStatements`, `CS.BernsteinHeckeIdealDecompositionStatement` | S |
| VI.7.4 Remark | 186 / 192 | none | X: false as printed in general; recorded as a source issue in `coverage-update-2026-11-11.md` |
| VI.7.5 Proposition | 186 / 192 | `RP.SmoothRepNoetherianCategoryStatement` | S |
| VI.7.5 Theorem | 187 / 193 | `RP.LeviInductionFiniteTypeStatement` | S |

## VI.8 Algebraic families

The [VI.8 assertion map](algebraic-families-progress.md) maps the
printed VI.8 assertions to their modules; this table gives the headed items.

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| VI.8.1 Definition (`(G, B)`-modules) | 187 / 193 | category `M(G, B)` of flat smooth families (definition module, commit `e21322ee`); hypotheses of the `AF` statements | D |
| VI.8.1 Proposition | 187 / 193 | `AF.AdmissibilityCriterionStatement` (with `AF.FixedTensorComparisonStatement`) | P |
| VI.8.1 Remark | 188 / 194 | `AF.FlatnessCriterionStatement` | P |
| VI.8.1 Lemma | 189 / 195 | `AF.SpecializationAdmissibilityStatement` | P |
| VI.8.1 Example | 189 / 195 | `PN.RationalUniversalTensorFinitenessStatement`, `AF.UniversalSpecializationStatement` | P |
| VI.8.2 Lemma (induction preserves admissibility) | 190 / 196 | `AF.InductionAdmissibleStatement`; flatness `AF.InductionFlatStatement` | P |
| VI.8.2 Proposition | 190 / 196 | `AF.InductionBaseChangeStatement` | P |
| VI.8.2 Corollary | 191 / 197 | special case `E = ℂ_χ` of `AF.InductionBaseChangeStatement`; universal family `PN.RationalNormalizedInducedSpecializationStatement` | C; universal family P |
| VI.8.3 Proposition | 191 / 197 | `AF.JacquetFlatStatement`, `AF.ParabolicStatements` | P |
| VI.8.4 Theorem | 191 / 197 | `AF.LocalFreeCoverStatement` | P |
| VI.8.4 Proposition | 192 / 198 | `AF.InducedIrreducibilityOpenStatement` | S |
| VI.8.5 Theorem | 193 / 199 | `AF.GenericInducedIrreducibilityStatement` | S |
| VI.8.5 Lemma | 194 / 200 | `AF.CentralCharacterSplittingStatement` | P |
| VI.8.6 Proposition | 195 / 201 | `AF.EndomorphismScalarStatement` | P |
| VI.8.6 Example | 195 / 201 | `AF.SupercuspidalFamilyEndomorphismStatement` | S |

## VI.9 The second adjointness theorem

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| VI.9.1 Theorem (generalized Jacquet lemma) | 195 / 201 | Source scope: `RP.RepresentedGeneralizedJacquetLemmaStatement` (`Exponents/RepresentedIwahoriDecompositionStatements`; the setting of the VI.6.1 Theorem row, every smooth `V`). Dynamic form: `RPF.GeneralizedJacquetLemmaStatement` (dynamic parabolics; `K` admitting an `M`-central `g` with `IsIwahoriContraction`) | S; dynamic form S |
| VI.9.1 first Lemma (`V(N) ∩ V^K = ⋃ ker A^i`) | 196 / 202 | `powerKernelSup_eq_ker_of_iwahoriContraction` (`Jacquet/IwahoriContractionAdmissibility`), `fixedJacquetMap_kernel_locally_nilpotent` (`Jacquet/CompressionLocalization`) | P |
| VI.9.1 second Lemma (localization) | 196 / 202 | `compressionJacquetLocalizationEquiv`, `localizationEquivOfKernelExhaustion` | D / P (proved construction) |
| VI.9.1 Proposition (uniform stabilization) | 197 / 203 | Arbitrary parabolics: `RP.RepresentedUniformCompressionStabilizationStatement` (`Exponents/RepresentedCanonicalSectionStatements`; every compact open `K` and every `M(F)`-central `g` with `IsIwahoriContraction`; `b` chosen after `K` and `g`, for all smooth `V`; it adds the conclusions `ker j = V_0^K` and `j` bijective on `V_*^K` drawn at the end of the proof of the Theorem). Dynamic form: `RPF.UniformCompressionStabilizationStatement` (`b` chosen after `χ`, `K` and `g`) | S; dynamic form S. C for the source's class of `K`: by `RP.RepresentedIwahoriContractionStatement`, proved by `representedIwahoriContraction` (VI.6.1 Theorem row), every `K` with an Iwahori decomposition admits such a `g`. The source's `b = b(G, K)` follows from the bound clauses of the next row together with VI.2.3 |
| VI.9.1 Proposition, localization at `A` is `(V^K_*, A)` | 197 / 203 | `J.CompressionStableImageLocalizationStatement` (`Jacquet/CompressionStableImageLocalizationStatement`): the unique equivalence for the actual compressed action intertwines the endomorphisms and identifies the localization map with projection along the power-kernel supremum | S for the specialization with a stationary compression and complementary kernel; the general stable-power localization result `Langlands.Renard.EndomorphismLocalization.stablePowerImageStatement` (C.II) is proved |
| VI.9.1 Proposition, `b ≤ c(G, K)`; Remarks 1–3 | 197–198 / 203–204 | `RPF.GeneralizedJacquetRemarksStatement` (bound, Remarks 1–2, dynamic parabolics), `RP.GeneralizedJacquetContractingRangeStatement` (Remark 3) (`Exponents/GeneralizedJacquetRemarksStatements`, published); bound and Remarks 1–2 along actual rational parabolics: `RP.RepresentedGeneralizedJacquetRemarksStatement` (`Exponents/RepresentedCanonicalSectionStatements`) | S for the two published statements and for the represented statement |
| VI.9.2 (VI.9.2.2) stability for the universal induced family | 198–199 / 204–205 | `Langlands.Plancherel.RationalSupercuspidalJacquetFamilyFiniteStatement` and the VI.9.1–VI.9.3 map (`uniform-compression-progress.md`) | St: step of the VI.9.1 Proposition; Jacquet-family finiteness P |
| VI.9.3 extension to all smooth representations | 200 / 206 | conditional helpers in the VI.9.1–VI.9.3 map | St |
| VI.9.4 Corollary | 201 / 207 | `J.StandardIwahoriFixedVectorSubquotientGenerationStatement`; earlier `J.StandardFixedVectorSubquotientGenerationStatement` | S for the Iwahori-only statement, which uses the source's conditions on `K`. Conditional reduction (update of 17 November 2026 above): `J.standardIwahoriFixedVectorSubquotientGeneration_of_specialVertexInputs` proves it from the unproved `CS.RationalSpecialVertexCompactInputsStatement`. |
| VI.9.4 Proposition | 201 / 207 | Over the measure-free algebra: `J.StandardIwahoriFixedVectorHeckeEquivalenceStatement`; earlier `J.StandardFixedVectorHeckeEquivalenceStatement` (modules over the measure-free `LevelHeckeAlgebra ℂ K`). Comparison of algebras: `Langlands.Hecke.LevelHeckeCornerComparisonStatement` (`Hecke/LevelHeckeCornerComparisonStatement`: a product-preserving linear bijection `LevelHeckeAlgebra ℂ K ≃ Corner μ K hK` with `e(a)(x) = μ(K)⁻¹ a(xK)`, compatible with the two actions on `V^K`). Over the Haar-measure `H(G, K)` with the inverse functor: `J.StandardIwahoriCornerInductionEquivalenceStatement` (`Jacquet/StandardIwahoriCornerInductionStatement`; see the VI.10.6 Proposition (ii) row) | Comparison P: `Langlands.Hecke.levelHeckeCornerComparison` (`Hecke/LevelHeckeCornerComparisonProof`; verified 17 November 2026 above). Categorical statements retain their earlier S status: the Iwahori-only statement, the earlier basis-member version and the corner-induction statement |
| VI.9.5 (`r_P^G` preserves `B`-admissibility) | 201 / 207 | `AF.JacquetAdmissibleStatement`; reduction `AF.JacquetAdmissibleReductionStatement` | S; reduction P |
| VI.9.6 first Theorem (second adjointness) | 201 / 207 | `RP.LeviSecondAdjointnessStatement` | S |
| VI.9.6 second Theorem (`r_{P̄}^G π̃ ≅ (r_P^G π)~`) and the equivalence of the two | 201–202 / 207–208 | `RP.LeviJacquetContragredientStatement`, `RP.LeviSecondAdjointnessContragredientEquivalenceStatement` | `RP.LeviJacquetContragredientStatement` S; the equivalence P: `leviSecondAdjointnessContragredientEquivalence` (`Exponents/LeviSecondAdjointnessContragredientEquivalenceProof`) |
| VI.9.6 Proposition (pairing) | 202 / 208 | `RP.LeviJacquetOppositePairingStatement` | S |
| VI.9.7 Theorem | 205 / 211 | `RP.LeviCompletionOppositeJacquetStatement` | S |
| VI.9.7, equivariance and all Iwahori component indices | 205–206 / 211–212 | `RP.LeviCompletionEquivarianceStatement` gives the unique natural Levi-equivariant unnormalized comparison from the linear theorem; `RP.LeviCompletionIwahoriFormulaStatement` extends the component formula from contraction indices to every compact open Iwahori factorization index | S for both implications |

## VI.10 The Bernstein centre

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| VI.10.1 Lemma, Proposition, Corollary, Theorem | 207–208 / 213–214 | `RP.InducedProgeneratorIndependenceStatement`, `CS.BernsteinInducedProgeneratorStatement` | S |
| VI.10.2 Theorem, `Hom_G(Π_Ω, ·)` is an equivalence | 208 / 214 | `CS.BernsteinBlockHomEquivalenceStatement` (on the published block, see F1) | S |
| VI.10.2 Theorem, the quasi-inverse is `M ↦ M ⊗_{R_Ω} Π_Ω` | 208 / 214 | `CS.BernsteinBlockTensorQuasiInverseStatement` (first published at Library `79de65ce`; the VI.4.1 analogue is `CS.RationalSummandTensorQuasiInverseStatement`) | S |
| VI.10.3 Proposition, Corollary | 209 / 215 | `CS.BernsteinBlockJacquetFaithfulStatement`, `RP.SupercuspidalInductionLengthStatement` | S |
| VI.10.4 (VI.10.4.1)–(VI.10.4.2): induction of modules corresponds to `i_P^G` | 209–210 / 215–216 | none | St: step of the VI.10.4 Theorem |
| VI.10.4 injectivity and first Lemma (`R_Ω` free of rank `|W(D)|` over `R_D`) | 209–210 / 215–216 | `RP.InducedProgeneratorEndFreeStatement` | P: `RP.inducedProgeneratorEndFree` (`CuspidalSupport/InducedProgeneratorEndFreeProof`) gives injectivity of the induction map, a right basis of rank equal to the number of twist-stabilizing double cosets, and a finite right basis over `Z(R_D)`, the centre of the Levi progenerator endomorphism ring. In both bases the right action is `x · a = x ∘ i_P^G(a)` |
| VI.10.4 second Lemma (`ℨ_Ω ⊂ ℨ_D`) | 211 / 217 | `RP.InducedProgeneratorCenterInclusionStatement` | P: `inducedProgeneratorCenterInclusion` (`CuspidalSupport/InducedProgeneratorCenterInclusionProof`) |
| VI.10.4 `ℨ_Ω ⊂ ℨ_D^{W(D)}`, `ℨ_Ω = ℨ_D^{W(D)}` | 211–212 / 217–218 | none | St: steps of the VI.10.4 Theorem |
| VI.10.4 third Lemma (centralizer for filtered bimodules) | 211–212 / 217–218 | `Langlands.Algebra.RenardBimoduleFiltrationCentralizerStatement` | P: `renardBimoduleFiltrationCentralizer` (`Langlands/Algebra/RenardBimoduleFiltrationCentralizerProof`) |
| VI.10.4 Theorem | 212 / 218 | `CS.BernsteinCenterFunctionsStatements` (with `CS.BernsteinBlockCenterFunctionsStatement`, `CS.BernsteinCentralIdempotentFunctionStatement`) | S |
| VI.10.4 Corollary, Remarks 1–3 | 212 / 218 | `CS.BernsteinBlockCenterNoetherianStatement`, `CS.BernsteinBlockIndecomposableStatement`; Remarks 1–2 in `CS.BernsteinCenterFunctionsStatements` | S for the Corollary and Remark 3 (target `CS.BernsteinBlockCenterStatements`, the conjunction of the two Corollary statements) and for Remarks 1–2 |
| VI.10.5 Proposition | 213 / 219 | `RP.HarishChandraHomomorphismStatement` | S; finiteness of `i_{MG}` as a morphism of varieties is stated only through its consequence (finite generation) |
| VI.10.6 Theorem, Proposition | 213–214 / 219–220 | `CS.CompactOpenInertialFinitenessStatement`, `J.FixedVectorCategoryStatements` | S |
| VI.10.6 Proposition (i), the decomposition `M(G)_K = ∏_{s ∈ B(G)_K} M(G)_s`, and (iii)–(iv) for the source's class of `K` | 214 / 220 | `J.StandardIwahoriFixedVectorBlockDecompositionStatement` (a smooth representation is generated by its `K`-fixed vectors iff it is a coproduct of its components in the Bernstein blocks indexed by `B(G)_K`), `J.StandardIwahoriFixedVectorCategoryStatement` ((iii)–(iv) with only the ordered Iwahori decompositions on `K`), and the proved implication `J.fixedVectorCategoryStatements_of_standardIwahori` to the earlier basis-member conclusion (`Jacquet/StandardIwahoriFixedVectorCategoryStatements`) | S for the block decomposition statement and for (iii)–(iv) |
| VI.10.6 Proposition (ii) (inverse `M ↦ H(G) ⊗_{H(G,K)} M`) | 214 / 220 | `J.StandardIwahoriCornerInductionEquivalenceStatement` (`Jacquet/StandardIwahoriCornerInductionStatement`; the Haar Hecke algebra `H(G)`, its corner `H(G, K) = e_K H(G) e_K`, the III.1.4 functor, the I.3.1 corner functor and the I.3.2 induction functor) | S |
| VI.10.6 Corollary (`B(M)_{K_M} = i_{MG}^{-1}(B(G)_K)`) | 215 / 221 | `CS.StandardLeviCompactInheritanceStatement` (the hypotheses on `K` pass to `K ∩ M`), `CS.StandardRepresentativeFixedVectorCriterionStatement`, `CS.StandardLeviFixedVectorSupportStatement` (`CuspidalSupport/StandardLeviFixedVectorSupportStatements`; standard Levi subgroups `M_J`; `B(M)` and `i_{MG}` through representatives, as in `CS.BernsteinInductionRestrictionStatement`) | P: `standardLeviCompactInheritance` (`CuspidalSupport/StandardLeviCompactInheritanceProof`; 17 November proof-status update), `standardRepresentativeFixedVectorCriterion` (`CuspidalSupport/StandardRepresentativeFixedVectorCriterionProof`; 19 November proof-status update) and `standardLeviFixedVectorSupport` (`CuspidalSupport/StandardLeviFixedVectorSupportProof`; 20 November follow-up). The last proves the support equivalence through representatives, without defining `B(M)` as a type or `i_{MG}` as a function |
| VI.10.7 Lemma, Theorem | 215 / 221 | `CS.FiniteTypeComponentCharacterizationStatement`, `RP.FiniteTypeCenterAdmissibleStatement` | S |
| VI.10.7 Corollary | 216 / 222 | `RP.HeckeAlgebraCenterFiniteStatement` | S |
| VI.10.7 Proposition | 216 / 222 | `CS.FiniteTypeComponentCharacterizationStatement` | S |
| VI.10.7 Variant (`(G, B)`-modules) | 217 / 223 | `AF.FamilyFiniteTypeCenterAdmissibleStatement`, `AF.FamilyFiniteTypeComponentCharacterizationStatement`, `AF.FamilyLeviInductionFiniteTypeStatement` (`Families/RenardFamilyFiniteTypeStatements`; `ℨ(G)` is the published categorical centre acting on the underlying smooth complex representation; components enter through irreducible subquotients) | S. The components `E_𝔰` and the algebra `B ⊗_ℂ ℨ(G)` are not constructed |
| VI.10.8 Theorem | 217 / 223 | `RP.CenterFiniteHoweStatement` | S |

## VI.11 Notes on Chapter VI

| Item | Pages | Status |
| --- | --- | --- |
| VI.11 notes | 217–218 / 223–224 | X: attributions and references (Harish-Chandra, Jacquet, Bernstein, Bernstein–Zelevinsky [5], Casselman [20], DeBacker [23], notes [38]). The notes repeat that the second adjointness theorem is equivalent to a strong form of Casselman duality without admissibility; this is the VI.9.6 equivalence stated above. |

## Framework comparisons used above

These comparisons record the scope and proof obligations of the rows above. The
gap update of 14 November 2026 states the comparisons F2 and F4 and lists the
targets of F1 and F3. The proof-status update of 17 November 2026 records the
proofs of the F2 contraction statements, of the VI.6.1 represented statements, of the
F3 canonical section and of F4; the other statements of F1–F3 have open proofs.

- **F1. Bernstein blocks.** The published blocks (`BernsteinBlock`,
  `BernsteinSaturatedBlock`) use the induction-occurrence support relation. The
  comparison targets are in `CuspidalSupport/BernsteinSupportComparison` (statements
  parametrized by the standard family). Existence of an induction presentation,
  `CS.BernsteinCuspidalSupportExistenceStatement`, is proved
  (`bernsteinCuspidalSupportExistence`). The following are proved only conditionally,
  on the represented VI.5.4 statement
  `RP.LeviSupercuspidalInductionAssociationStatement`:
  association, `CS.BernsteinCuspidalSupportAssociationStatement`
  (`bernsteinCuspidalSupportAssociation_of_represented`), and
  `CS.BernsteinAssociatedSupportInvarianceStatement`
  (`bernsteinAssociatedSupportInvariance_of_represented`). Uniqueness of the inertial
  support, `CS.BernsteinInertialSupportUniquenessStatement`, follows from association
  (`bernsteinInertialSupportUniqueness_of_association`). The comparison with Renard's
  Jacquet-defined support, `CS.BernsteinInductionJacquetSupportComparisonStatement`,
  has no proof. The Library has no unconditional proofs of association, invariance,
  uniqueness or the comparison. The rows of VI.7 and VI.10 that use the published
  blocks depend on these comparisons.
- **F2. Iwahori decompositions and contracting elements: statement gap closed.**
  The earlier VI.9.1 statements and VI.6.1 Theorem coverage use dynamic parabolics
  and a compact open `K` with an `M`-central contracting `g` (`IsIwahoriContraction`).
  The source allows every `K` with an Iwahori decomposition along an arbitrary
  parabolic. The represented statements of
  `Exponents/RepresentedIwahoriDecompositionStatements` and
  `Exponents/RepresentedCanonicalSectionStatements` (module table above) are stated along every actual rational parabolic for such `K`.
  `RP.RepresentedIwahoriContractionStatement` and
  `RP.RepresentedChamberIwahoriContractionStatement` assert that such `K` admit
  contracting elements. Both are proved: `representedIwahoriContraction`
  and `representedChamberIwahoriContraction`, with the VI.6.1 represented
  statements `representedJacquetLemma` and `representedCanonicalSection`
  (proof-status update of 17 November 2026). The represented VI.9.1 statements
  have no proofs in the Library.
- **F3. V.5.2 basis members: statement gap closed for standard parabolics.**
  The published `J.StandardIwahoriCanonicalSectionStatement`,
  `J.StandardIwahoriFixedVectorSubquotientGenerationStatement` and
  `J.StandardIwahoriFixedVectorHeckeEquivalenceStatement` assume only the ordered
  `HasIwahoriIntersectionDecomposition` on `K`, along one standard parabolic
  for VI.6.1 and every standard parabolic for VI.6.3 and VI.9.4. They retain the
  other data and conclusions of the earlier statements: the canonical section uses
  a supplied compatible split component; the VI.9.4 statements retain `K` contained
  and normal in a compact `K₀` with its Iwasawa factorization. The theorems
  `J.standardCanonicalSectionStatement_of_standardIwahori`,
  `J.standardFixedVectorSubquotientGenerationStatement_of_standardIwahori` and
  `J.standardFixedVectorHeckeEquivalenceStatement_of_standardIwahori` prove the
  implications to the earlier basis-member versions by extracting the Iwahori
  conjunct. These are conditional implications, not proofs of the three new
  statements. The first is proved, by `standardIwahoriCanonicalSection` (proof-status
  update of 17 November 2026); the other two have no unconditional proofs in the Library.
  The arbitrary-parabolic version of the VI.6.1 Proposition is stated under F2. The
  Haar-Hecke algebra and action comparison is proved (17 November 2026 update
  above). The categorical equivalence and inverse functor retain their separate
  proof obligations in the VI.9.4 Proposition row.
- **F4. Represented versus standard parabolics.** For supercuspidality, the
  comparison is `RP.SupercuspidalStandardParabolicCriterionStatement` (VI.2.1
  Remark 1 row), proved by `supercuspidalStandardParabolicCriterion`.

## Genuine gaps of Chapter VI

The earlier audit listed seven gaps. Each one is now stated. The update of
14 November 2026 records the statements below. It does not
claim that Chapter VI has no other gaps. The individual rows remain authoritative.

1. VI.1.1 Remark, first sentence (right adjoint of `Ind_P^G`):
   `RP.LeviUnnormalizedInductionRightAdjointStatement`, proved by
   `leviUnnormalizedInductionRightAdjoint`. The source's construction of
   the adjoint is not named.
2. VI.2.1, first Remark of the first block (standard parabolics suffice):
   `RP.SupercuspidalStandardParabolicCriterionStatement`, proved by
   `supercuspidalStandardParabolicCriterion`.
3. VI.10.2 Theorem: the quasi-inverse `M ↦ M ⊗_{R_Ω} Π_Ω` was not identified in the
   pinned Library. It is now stated by the published
   `BernsteinBlockTensorQuasiInverseStatement` (Library `79de65ce`), which the
   Library proves only conditionally.
4. VI.10.6 Corollary: `CS.StandardLeviCompactInheritanceStatement`,
   `CS.StandardRepresentativeFixedVectorCriterionStatement` and
   `CS.StandardLeviFixedVectorSupportStatement`, for standard Levi
   subgroups and through representatives of `B(M)`. All three are proved:
   `standardLeviCompactInheritance`,
   `standardRepresentativeFixedVectorCriterion` (19 November proof-status
   update) and `standardLeviFixedVectorSupport` (20 November follow-up).
5. VI.10.7 Variant: `AF.FamilyFiniteTypeCenterAdmissibleStatement`,
   `AF.FamilyFiniteTypeComponentCharacterizationStatement` and
   `AF.FamilyLeviInductionFiniteTypeStatement`; none has an unconditional proof in
   the Library.
6. VI.9.4 Proposition: the normalized algebra, product and action comparison
   `Langlands.Hecke.LevelHeckeCornerComparisonStatement` is now P:
   `Langlands.Hecke.levelHeckeCornerComparison` (17 November 2026
   update above). The categorical equivalence
   `J.StandardIwahoriFixedVectorHeckeEquivalenceStatement` and
   `J.StandardIwahoriCornerInductionEquivalenceStatement`, including the inverse
   functor of VI.10.6 Proposition (ii), retain their earlier S status.
7. The arbitrary-parabolic scope of VI.6.1 (Theorem and Proposition) and VI.9.1: the
   represented statements of F2. The source's class
   of `K` for standard parabolics in VI.6.1 Proposition, VI.6.3 Corollary and VI.9.4:
   the F3 targets. The block comparison F1.
   The represented VI.6.1 Theorem and Proposition statements and the F3 canonical
   section are proved (proof-status update of 17 November 2026). The represented
   VI.9.1 statements, the other two F3 targets and the F1 comparisons have no
   unconditional proofs in the Library.

The update also states VI.10.6 Proposition (i), the decomposition
`M(G)_K = ∏_{s ∈ B(G)_K} M(G)_s`, which the earlier statement
`J.FixedVectorCategoryStatements` does not contain. It is in
`Jacquet/StandardIwahoriFixedVectorCategoryStatements`; the Library proves it only
conditionally.

The VI.5.4 Lemma, unstated before this audit, is now the published
`StandardWeylElementaryChainStatement`, proved by `standardWeylElementaryChain`
(proof-status update above). The VI.9.1 bound and Remarks, the remaining
gap found by this audit, are now stated in the published module
`Exponents/GeneralizedJacquetRemarksStatements`; the Library proves them at most
conditionally.
