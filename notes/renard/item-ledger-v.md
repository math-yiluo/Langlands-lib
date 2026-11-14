# Renard 2026, Chapter V: item-by-item coverage ledger

Worker 1222, executor of the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`, revision 1. This note is the Chapter V
part of the item ledger that the task contract requires, in the format of the published
[Chapter VI](item-ledger-vi.md) and [Chapter VII](item-ledger-vii.md) ledgers. Chapter V
has few headed items: most of its assertions sit in numbered paragraphs. The rows therefore
follow the numbered paragraphs V.1–V.5.5 and the headed items inside them. The note declares
no section complete. A published statement is not a proof; every row keeps the proof status
explicit.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Printed page
numbers are given first and PDF page numbers second; PDF = printed + 6. Library facts
refer to commit `9951a27f5fd8ebbdc4bbe68eb6be65b1d0c2eb4a` unless stated otherwise.
The V.2.2 and V.3.1–V.3.24 rows have focused 13 November 2026 updates against Library
`430cc03fe803c5dbf74bc3baf91e8f7a2c26ea9c`. The V.5.3 module-form row has a
separate 13 November update against Library
`a0627c91621a99df78a1079f47cfb76995f077fa`, verified below. A further
13 November update of V.3.24 and V.4.2 uses Library
`dad81bc65e375153a3adcb2748ee7261d4444dab`: it records the published
finite-generation statement, actual nonnegative quotient construction, integral
strict faces, actual strict-image statement and closed-root-subset unit.
A focused 14 November update of V.3.24 uses Library
`c0debd6f4dd02fdd68d70811cf610906b945a962`: the nonnegative comparison,
actual strict-piece definition and actual partition statement are now public,
with exact proof Tasks 6505 and 6605 for the two new statement targets.
Other rows retain their earlier audit status. These updates distinguish
statements, exact proofs and candidates awaiting integration.

On 14 November 2026 Worker 4, the second executor of the same task, updated the
rows V.3.14–V.3.18, V.3.21–V.3.22, the V.5.5 row "proof of V.3.18" and gap 1
against Library `c0debd6f4dd02fdd68d70811cf610906b945a962`. The update cites
two Worker 4 units. Both are published in that Library, and the SHA256 digests
of their Lean and Markdown files equal those of the accepted candidates:

| Candidate | Module | Reviewer | Integration ID |
| --- | --- | --- | --- |
| `c074eb9d-450c-4886-9f71-857c5dcf0107` (statements, V.3.14–V.3.16) | [`Langlands.Representation.LanglandsClassification.ParabolicChamberStatements`](../../Langlands/Representation/LanglandsClassification/ParabolicChamberStatements.md) | Reviewer 1561 | `732c52f5cb7c40ccb5ded93fcd420948` |
| `089ffdc0-e46a-41c2-aca0-fbb8f8f05a14` (definitions, V.3.21–V.3.22) | [`Langlands.BruhatTits.Cartan.RenardLeviCones`](../../Langlands/BruhatTits/Cartan/RenardLeviCones.md) | Reviewer 1404 | `45fcf23332974867aa798316126b895d` |

The update also records two proofs present in that Library: V.3.17 by
`corootChamberUnipotentRoots` and V.3.18 by `langlandsCombinatorialDecomposition`.
Worker 4 checked that each theorem has exactly the type of the published statement,
and found no `sorry`, `admit` or `axiom` in either proof file.

A second Worker 4 pass on the same day is a full status refresh of every row outside
V.3.24 whose status was S or R, against the same Library. Every statement name in
these rows was compared with the Library theorems whose type is exactly that statement.
For each new proof Worker 4 read the theorem line and found no `sorry`, `admit` or
`axiom` in its file. The pass records these proofs:

| Row | Statement | Theorem | Proof module |
| --- | --- | --- | --- |
| V.2.3 Proposition, `⁰G` unimodular | `PL.RationalNormKernelUnimodularStatement` | `rationalNormKernelUnimodular` | [RationalNormKernelUnimodularProof](../../Langlands/Representation/Plancherel/RationalNormKernelUnimodularProof.md) |
| V.2.5 `A₁ ⊂ A₂` | `PL.RationalNormKernelRestrictionStatement` | `rationalNormKernelRestriction` | [RationalNormKernelRestrictionProof](../../Langlands/Representation/Plancherel/RationalNormKernelRestrictionProof.md) |
| V.2.6 Lemma | `RC.SplitComponentKernelStatement` | `splitComponentKernel` | [SplitComponentKernelProof](../../Langlands/Representation/Plancherel/SplitComponentKernelProof.md) |
| V.2.6 Proposition, compact centre | `PL.RationalNormKernelCompactCenterStatement` | `rationalNormKernelCompactCenter` | [RationalNormKernelCompactCenterProof](../../Langlands/Representation/Plancherel/RationalNormKernelCompactCenterProof.md) |
| V.2.7 Corollary | `Langlands.CuspidalSupport.RationalInertiaOrbitTorusStatement` | `rationalInertiaOrbitTorus` | [RationalInertiaOrbitTorusProof](../../Langlands/Representation/CuspidalSupport/RationalInertiaOrbitTorusProof.md) |
| V.3.23 representatives | `RC.FullLatticeRepresentativeStatement` | `fullLatticeRepresentative` | [FullLatticeRepresentativeProof](../../Langlands/Representation/Plancherel/FullLatticeRepresentativeProof.md) |
| V.4.3.3 | `GS.StandardLeviNormalizerQuotientStatement` | `standardLeviNormalizerQuotient` | [StandardLeviNormalizerQuotientProof](../../Langlands/GroupScheme/Rational/StandardLeviNormalizerQuotientProof.md) |
| V.4.6 Lemma | `GS.StandardWeylMinimalRepresentativesStatement` | `standardWeylMinimalRepresentatives` | [StandardWeylMinimalRepresentativesProof](../../Langlands/GroupScheme/Rational/StandardWeylMinimalRepresentativesProof.md) |
| V.4.8 | `GS.StandardMaximalLeviWeylStatement` | `standardMaximalLeviWeyl` | [StandardMaximalLeviWeylProof](../../Langlands/GroupScheme/Rational/StandardMaximalLeviWeylProof.md) |
| V.5.1 Corollary, `K_0`-conjugacy | `Langlands.BruhatTits.SpecialCompactParabolicConjugacyStatement` | `specialCompactParabolicConjugacy` | [SpecialCompactConjugacyProof](../../Langlands/BruhatTits/Parabolic/SpecialCompactConjugacyProof.md) |
| V.5.1 Theorem and V.5.2, for valid corrected KP data | `SC.AvailableSimultaneousStandardBasisStatement` | `availableSimultaneousStandardBasis` | [AvailableBasisProof](../../Langlands/BruhatTits/SpecialCompact/AvailableBasisProof.md) |

The pass also escapes the vertical bars inside table cells of the V.1, V.2.3, V.3.19,
V.3.20 and V.5.4 Lemma rows, which otherwise split those cells. It leaves unchanged
the V.3.24 rows, the V.3.24 evidence section, gap 7 and the V.3.24 sentences of the
proof-task section; Worker 1222 updates those passages separately.

A third Worker 4 pass, also on 14 November, updates the V.3.6 arbitrary-Levi row, the two
V.3.7 rows, the two V.3.12 real-form rows and the V.3.13 corrected-decomposition row against
Library `4f4af6baed8c8e029e87c8303ea44c8f1d9f2f86`. It also updates the V.3.6–V.3.13
evidence section, gap 2 and the V.3.6 and real-coroot sentences of the proof-task section.
The five proofs below were independently accepted and published at Library
`ba00e0970dd9ba6222ccc056ca2ee7f06bcc8181`. Each theorem has exactly the type of its
statement, and Worker 4 found no `sorry`, `admit` or `axiom` in its file. For the first four
proofs, the SHA256 digests of the Lean and Markdown files in the checked Library equal those
of the accepted artifact. For the fifth, see the paragraph after the table.

| Row | Statement | Theorem and proof module | Proof task | Accepted artifact, reviewer | Integration ID |
| --- | --- | --- | --- | --- | --- |
| V.3.6, arbitrary Levi | `GS.RenardLeviCentralDecompositionStatement` | `renardLeviCentralDecomposition`, [RenardLeviCentralDecompositionProof](../../Langlands/GroupScheme/Rational/RenardLeviCentralDecompositionProof.md) | Task 6224 (`423ad442`) | `50511195-1935-47e3-8fb6-7629ebb5c212`, Reviewer 3072 | `1b6b8b9b5e494d3d9c0a9bfadb547db8` |
| V.3.7, real statement and coroots | `GS.RelativeRealCorootStatement` | `relativeRealCoroot`, [RelativeRealCorootProof](../../Langlands/GroupScheme/Rational/RelativeRealCorootProof.md) | Task 6346 (`09d6ceb8`) | `0a7d7039-43d6-454b-8030-7618ea0993ad`, Reviewer 3189 | `b78546410e9a438fa64562f49304fecc` |
| V.3.12, real basis | `GS.RelativeRealSimpleRootBasisStatement` | `relativeRealSimpleRootBasis`, [RelativeRealSimpleRootBasisProof](../../Langlands/GroupScheme/Rational/RelativeRealSimpleRootBasisProof.md) | Task 6345 (`58a10059`) | `35ce58ac-7198-423d-92f8-7e28e8b46d78`, Reviewer 3063 | `dc964b16df8949b59da38e6435601bdb` |
| V.3.12, coroot basis, fundamental weights and coweights | `GS.RelativeFundamentalWeightStatement` | `relativeFundamentalWeight`, [RelativeFundamentalWeightProof](../../Langlands/GroupScheme/Rational/RelativeFundamentalWeightProof.md) | Task 6347 (`6642885b`) | `5b2c9a74-eb22-4fbb-bf2a-3edaf99bbc8a`, Reviewer 3109 | `498ec53d824e42b09a11fd42f56652b4` |
| V.3.13, corrected decompositions | `GS.StandardLeviRealDecompositionStatement` | `standardLeviRealDecomposition`, [StandardLeviRealDecompositionProof](../../Langlands/GroupScheme/Rational/StandardLeviRealDecompositionProof.md), helper [StandardLeviLinearAlgebra](../../Langlands/GroupScheme/Rational/StandardLeviLinearAlgebra.md) | Task 6348 (`ff6de4a1`) | `871a80de-5a1d-42ab-8752-57d0af31278a`, Reviewer 3129 | `5e2577b2a3264953890adb42eb7cb4b3` |

The Library files of the V.3.13 proof are not byte-identical to the accepted artifact. The
accepted proof file has SHA256 `d39a6c9b…` and its Markdown `1c8a3cb5…`; the Library copies
have `decd82eb…` and `7ac72b55…`, and the helper pair differs as well. These copies are the
same in `ba00e097` and `4f4af6ba`. The difference is the overlap that the review's
integration notes flagged as a duplicate. The helper lemma `positive_orthogonal_isCompl`
was removed from `StandardLeviLinearAlgebra`. The proof now imports
`Langlands.GroupScheme.Rational.LanglandsCharacterRestriction` and uses its published
`Langlands.LinearAlgebra.isCompl_orthogonal_of_positive`, followed by `IsCompl.symm`. The
paragraph of the helper Markdown and the sentence of the proof Markdown that described the
removed lemma were changed to match. The theorem line is unchanged, and the helper file
contains no `sorry`, `admit` or `axiom` either.

The four real-coroot statements have a conjunction, `GS.RelativeRealCorootLinearAlgebraStatement`,
which is the entry statement of Worker 4's candidate `89ad3e08-f0ca-4e7e-b9fb-5a257e4a4616`.
It has no proof in the checked Library. A Worker 4 scratch file that imports the four
Library proof modules and pairs their theorems into the conjunction compiles against this
Library (diagnostic `0e441105-9b2d-48c5-b124-8955a8dc9216`: 0 errors, 0 warnings; axioms
`propext`, `Classical.choice`, `Quot.sound` only). Worker 4 published the exact proof Task
6830 (`8a9c5345-ee7d-44ea-85d4-a16abf746ebb`) for the conjunction; no proof of it is
accepted yet.

A fourth Worker 4 pass, also on 14 November, checks against Library
`58ad0f796899b4aa457077d0146815c24758f739`. It updates the V.2.2 Remarks row and the
anisotropic-part paragraph after the V.2 table, the V.3.1 split-component row, the V.3.2 row,
gap 6 and two sentences of the proof-task section. The six proofs below were independently
accepted and first published at Library `af5d652c2f2ff5b35b4ce4dbbf7cbec8bbf3e99e`. They
are unchanged in the checked Library. Each theorem has exactly the type of its statement, and
Worker 4 found no `sorry`, `admit` or `axiom` in its file. For each proof, the SHA256 digests
of the Lean and Markdown files in the checked Library equal those of the accepted artifact.

| Row | Statement | Theorem and proof module | Proof task | Accepted artifact, reviewer | Integration ID |
| --- | --- | --- | --- | --- | --- |
| V.2.2 Remarks, maximal anisotropic subtorus and almost direct product | `GS.TorusAnisotropicPartStatement` | `torusAnisotropicPart`, [TorusAnisotropicPartProof](../../Langlands/GroupScheme/Rational/TorusAnisotropicPartProof.md) | Task 6398 (`55194693`) | `c38b65be-a024-465f-938f-25c2dffdfa54`, Reviewer 3835 | `684f66537e264cdcaa68f85188862db7` |
| V.3.1, `Z(G, A)` is a Levi factor with split component `A` | `GS.ParabolicSplitComponentLeviStatement` | `parabolicSplitComponentLevi`, [ParabolicSplitComponentLeviProof](../../Langlands/GroupScheme/Rational/ParabolicSplitComponentLeviProof.md) | Task 6452 (`d8ff4270`) | `8a5066fc-1a6f-4e01-b96d-5b2ebe084502`, Reviewer 3664 | `8f1b25ca28134ba4b7a6c5fbf14e9d62` |
| V.3.1, `A_M` is a split component of `P` | `GS.LeviSplitComponentRadicalStatement` | `leviSplitComponentRadical`, [LeviSplitComponentRadicalProof](../../Langlands/GroupScheme/Rational/LeviSplitComponentRadicalProof.md) | Task 6454 (`b2fb4859`) | `e9b76755-211a-4d22-9c7c-e1a7450a838d`, Reviewer 3646 | `cca763761ed14a55826a61a170fac91f` |
| V.3.1, `N` transitive on split components | `GS.ParabolicSplitComponentConjugacyStatement` | `parabolicSplitComponentConjugacy`, [ParabolicSplitComponentConjugacyProof](../../Langlands/GroupScheme/Rational/ParabolicSplitComponentConjugacyProof.md) | Task 6455 (`e322ff48`) | `654715c6-8ce6-486e-90bc-b288071f0518`, Reviewer 3656 | `169cadac914149928cd025fd75f158a2` |
| V.3.1, Levi subgroups as centralizers of split tori | `GS.LeviCentralizerCharacterizationStatement` | `leviCentralizerCharacterization`, [LeviCentralizerCharacterizationProof](../../Langlands/GroupScheme/Rational/LeviCentralizerCharacterizationProof.md) | Task 6456 (`da581938`) | `24f1cd16-8966-4bc9-a259-6f116a62ac34`, Reviewer 3639 | `d99c60fa8f9b448283f71d815a970656` |
| V.3.2, first sentence | `GS.MinimalParabolicSplitComponentStatement` | `minimalParabolicSplitComponent`, [MinimalParabolicSplitComponentProof](../../Langlands/GroupScheme/Rational/MinimalParabolicSplitComponentProof.md) | Task 6457 (`67bcbcad`) | `f6625a0a-8b1a-4ba5-8e9f-35c770af6c73`, Reviewer 3661 | `dad8fc30cb05442e952cab8b1209b8d4` |

The last five statements are the components of Worker 4's published unit
[ParabolicSplitComponentStatements](../../Langlands/GroupScheme/Rational/ParabolicSplitComponentStatements.md)
(candidate `409bc563-b798-41ec-84d8-0aaf06765e52`). Their conjunction,
`GS.ParabolicSplitComponentStatements`, has no proof in the checked Library. A Worker 4
scratch file that imports the five Library proof modules and pairs their theorems into the
conjunction compiles against this Library (diagnostic `a2deb435-d2ee-42cc-a88a-bd1d323df5c5`:
0 errors, 0 warnings; axioms `propext`, `Classical.choice`, `Quot.sound` only). Worker 4
published the exact proof Task 6866 (`e5eb891b-fc5e-4885-8241-647a8b70812f`) for the
conjunction; no proof of it is accepted yet. This pass leaves unchanged the V.3.24 rows, the
V.3.24 evidence section, gap 7 and the V.3.24 sentences of the proof-task section, which
Worker 1222 updates separately.

Chapter V is mostly a recall of algebraic-group and Bruhat–Tits theory with section-level
references. The published
[Chapter V structural-inputs ledger](chapter-v-structural-inputs.md) (Worker 164) classifies
those recalled assertions (rows S01–S23) and the book's own deductions (rows D01–D08). This
note gives, for each paragraph, the Library declarations that now state or prove it.

## How the rows were checked

Worker 1222 read Chapter V in the text extraction and checked the displayed formulas with
overlines in the rendered PDF. For each paragraph the Library Markdown files citing it were
listed, and their declarations were read. Proof status comes from a scan of the Library for
theorems whose type is exactly the statement (`proved by`). A `task` entry is a
`lean.proof@1` task whose contract names the statement. Task identifiers are abbreviated to
their first eight hexadecimal digits, or given by task number.

Namespace abbreviations: `GS` = `Langlands.GroupScheme`, `PL` = `Langlands.Plancherel`,
`RC` = `Langlands.Plancherel.RenardCartan`, `RP` = `Langlands.Aubert.General.RepresentedParabolic`,
`RPF` = `Langlands.Aubert.General.RationalPointFamily`, `SC` = `Langlands.BruhatTits.SpecialCompact`.

Status codes, as in the Chapter VI ledger:

- **P**: proved; the named theorem has exactly the statement's type.
- **S**: statement published; its proof remains an obligation, with the exact task given where assigned.
- **D**: definition or construction.
- **C**: covered by published statements that are stronger or equivalent, or derived from
  them; the row says which.
- **St**: a step of the proof of a stated result.
- **X**: expository, convention or attribution.
- **Rec**: an assertion recalled from the literature with a section-level reference (a row
  S.. of the structural-inputs ledger). The row says whether the Library states it.
- **A**: candidate accepted by review, waiting for integration.
- **R**: candidate staged, under review.
- **G**: genuine gap.

## V.1 Nonarchimedean local fields (103–104 / 109–110)

| Item | Lean | Status |
| --- | --- | --- |
| Normalized valuation, `𝔒_F`, `𝔓_F`, units, uniformizer decomposition, finite residue field, `\|x\|_F = q^{-v_F(x)}` | Mathlib's `IsNonarchimedeanLocalField` with `ValuativeRel`; `Langlands.FML.ord` and its laws, `LocalField.ResidueField`, `residueCardinality`, `residueNormalizedAbsoluteValue` ([ResidueNormalization](../../Langlands/LocalField/ResidueNormalization.md)); `PL.fieldNormUnits`, `PL.fieldOrderUnits` | Rec (ref. [21]); D |
| Additive Haar measure and `∫ f(ax) dx = \|a\|_F^{-1} ∫ f(x) dx` | `Langlands.HarmonicAnalysis.GeneralScalarHaarScalingStatement` | P: `generalScalarHaarScalingStatement` |
| Topology of `F`, of `GL_n(F)` and the subgroups `K_n` | Mathlib local-field topology; `rationalPointTopology` and `rationalPoint_isTopologicalGroup`, `rationalPoint_locallyCompactSpace` | Rec; D |

## V.2 Reductive p-adic groups (104–109 / 110–115)

| Item | Lean | Status |
| --- | --- | --- |
| V.2.1 radicals, reductive groups, derived group, centre, maximal tori, conjugacy of maximal split tori | `IsConnectedReductive`, derived subgroup representability, `GS.MaximalSplitTorusConjugacyStatement` | Rec (S02–S03); conjugacy P: `maximalSplitTorusConjugacy` |
| V.2.1 split component and its uniqueness | `GS.IsSplitComponent`; `GS.SplitComponentStatement` (existence, uniqueness up to isomorphism over `G`) | D; P: `splitComponentStatement` |
| V.2.1 topology independent of the embedding; `G` unimodular | `rationalPointTopology`; unimodularity is V.5.4 below | Rec (S04); D |
| V.2.2 `X^*(G)`, triviality on `𝒟G`, finite-rank lattice, duals | `GroupScheme.rationalCharacters`; `GS.RationalCharacterLatticeStatement` | D; P: `rationalCharacterLattice` |
| V.2.2 Remarks (tori): cocharacter pairing `χ(φ(t)) = t^{⟨χ,φ⟩}`, coordinate algebra `F[X^*(T)]`, anisotropic and split tori, maximal split and anisotropic subtori, almost direct product | `latticePairing`, `rationalCharacterEval_cocharacterPoints`; `IsSplitTorus` (isomorphic to `splitTorus S I`); largest split subtorus (`Rational.TorusSplitPart`); `GS.TorusAnisotropicPartStatement` ([statement](../../Langlands/GroupScheme/Rational/TorusAnisotropicPartStatement.md)) | Rec (S05). D for the listed constructions; P for the named pairing laws and largest split subtorus; P for the maximal anisotropic subtorus and finite surjective multiplication `A × T_an → T`: `torusAnisotropicPart` (Task 6398, `55194693-d01d-4220-9427-fa92990f27d6`) |
| V.2.3 (V.2.3.1) `H_G`, `⁰G`, `Λ(G)`, exact sequence; `⁰G = ⋂ ker \|χ\|_F` | `PL.rationalCharacterValuation`, `PL.rationalCommonNormKernel`, `PL.rationalCharacterValuationImage`, `PL.rationalNormKernelQuotientEquiv`; `rationalCharacterValuation_ker` | D; P |
| V.2.3 Lemma: `\|χ\|_F` smooth, kernel contains every compact subgroup | `isLocallyConstant_rationalNormCharacter`, `compactSubgroup_le_rationalCommonNormKernel`; generic `PL.CommonNormKernelTopologyStatement` | P (`commonNormKernelTopology`) |
| V.2.3 Proposition: `⁰G` open, closed, normal; compact subgroups and `𝒟G` in `⁰G` | `isOpen_rationalCommonNormKernel`, `isClosed_rationalCommonNormKernel`, instance `rationalCommonNormKernel_normal`, `derivedPoints_le_rationalCommonNormKernel` | P |
| V.2.3 Proposition: `⁰G` unimodular | `PL.RationalNormKernelUnimodularStatement` | P: `rationalNormKernelUnimodular` (Task 5711; statement candidate `51acec26`) |
| V.2.3 Definition: unramified characters | `PL.unramifiedCharacters` of the rational norm characters: continuous characters trivial on `⁰G`, which are all characters trivial on `⁰G` since `⁰G` is open | D |
| V.2.4 `X(G) ≃ Hom(Λ(G), ℂ^×)`, `Λ(G)` free of finite rank, `ℂ[Λ(G)]`, `ev_g`, `χ_un`, (V.2.4.1)–(V.2.4.2) | `PL.rationalImageCharacters`, [RationalImageLattice](../../Langlands/Representation/Plancherel/RationalImageLattice.md), [RationalUnramifiedCharacterCoordinates](../../Langlands/Representation/Plancherel/RationalUnramifiedCharacterCoordinates.md), [RationalUnramifiedCoordinateAlgebra](../../Langlands/Representation/Plancherel/RationalUnramifiedCoordinateAlgebra.md) (evaluation algebra ≅ `ℂ[Λ(G)]` ≅ Laurent polynomials), `universalUnramifiedRepresentation` | D. The complex-torus structure is given by its coordinate algebra; no complex variety is constructed |
| V.2.5 tori: `C_A`, section of `H_A`, `Λ(A) = X_*(A)` | `GS.CocharacterUniformizer.SplitTorusUniformizerSectionStatement`, `RC.uniformizerSection` | P: `splitTorusUniformizerSection` |
| V.2.5 `⁰A` is the maximal compact subgroup of a split torus `A` | `PL.TorusNormKernelCompactnessStatement` (every torus) and `compactSubgroup_le_rationalCommonNormKernel` | P: `torusNormKernelCompactness` |
| V.2.5 `A₁ ⊂ A₂` split: `⁰A₁ = A₁ ∩ ⁰A₂`, `Λ(A₁) ⊂ Λ(A₂)`, `C_{A₁} ⊂ C_{A₂}` | `PL.RationalNormKernelRestrictionStatement`; `RC.uniformizerSection_naturality` | P: `rationalNormKernelRestriction` (Task 5711); D |
| V.2.6 Lemma: `⁰A_G = ⁰G ∩ A_G` | `RC.SplitComponentKernelStatement` | P: `splitComponentKernel` (Task 5679) |
| V.2.6 Lemma: `Λ(A_G) ↪ Λ(G)` with finite index | `RC.SplitComponentLatticeStatement`; `GS.CharacterRestrictionStatement` | P: `splitComponentLattice`, `characterRestriction` |
| V.2.6 Proposition: `G/⁰G A_G` finite; `⁰G ∩ Z(G)` compact | `PL.finite_rationalCentralQuotient` with `splitComponentLattice`; `PL.isCompact_rationalCommonNormKernel_inf_center` | P |
| V.2.6 Proposition: `Z(G)` compact implies `⁰G = G` | `PL.RationalNormKernelCompactCenterStatement` | P: `rationalNormKernelCompactCenter` (Task 5711) |
| V.2.7 action of `X(G)` on `Irr(G)`, stabilizers | [RationalInertia](../../Langlands/Representation/CuspidalSupport/RationalInertia.md) | D |
| V.2.7 Lemma: `X(G)(π)` finite | `Langlands.CuspidalSupport.RationalTwistStabilizerFiniteStatement` | P: `rationalTwistStabilizerFinite` |
| V.2.7 Corollary and Notations: inertia orbits are complex tori; polynomial and rational functions on `D` | `Langlands.CuspidalSupport.RationalInertiaOrbitTorusStatement` (the Corollary and the identifications of the Notations paragraph; its Markdown explains the remaining definitions of polynomial and rational functions on `D`, which it does not restate) | P: `rationalInertiaOrbitTorus` (task `f5aebf51`) |

The anisotropic-part entry corrects the previous ledger's claim that the assertion
was unstated. At Library `430cc03fe803c5dbf74bc3baf91e8f7a2c26ea9c`, the public
`TorusAnisotropicPartStatement` pair agrees with this workspace. It quantifies over
every field and actual torus, asserts a closed anisotropic subtorus through which
every closed anisotropic subtorus factors, and asserts finite surjective
multiplication with every largest split subtorus. This expresses uniqueness up to
isomorphism over the ambient torus and the scheme-level almost direct product.
Check `4a9eab52-4b7d-4d1e-a3a7-edd2383e4719` compiled and inspected the existing
declaration as `Prop` with zero errors and warnings. No proof was found in the
public Lean files or focused task records; Task 6398 supplies its exact proof
obligation. The source was reread at V.2.2 Remark 2 and V.2.5, printed pp.105, 107 /
PDF pp.111, 113. Compilation of the statement supplies no proof evidence. At Library
`58ad0f796899b4aa457077d0146815c24758f739` the statement is proved: Task 6398's
theorem `torusAnisotropicPart` is published (fourth-pass table at the top of this note).

## V.3 Parabolic subgroups (109–117 / 115–123)

The section refers to [7] (Borel–Tits) or [42] (Springer) for its recalled assertions.

| Item | Lean | Status |
| --- | --- | --- |
| V.3 opening: parabolic subgroups, rational radicals | `IsParabolicSubgroup` | D; Rec |
| V.3.1 Levi decomposition `P = M ⋉ N`; `N` acts simply transitively on the Levi factors | `GS.ParabolicRadicalTorusLeviStatement` and `GS.ParabolicRadicalTorusCentralizerLeviStatement` (a Levi factor is the centralizer of a maximal torus of the radical of `P`), `GS.RationalLeviConjugacyStatement` (two rational Levis are conjugate by a unique rational point of the unipotent radical), `GS.ParabolicRootPresentationExistenceStatement` | P (each has its proof) |
| V.3.1 `M = Z(G, A)` for a split component `A` of `P`, `A = A_M`; Levi subgroups are the centralizers of split tori `A` with `A = A_M` | Worker 4's [ParabolicSplitComponentStatements](../../Langlands/GroupScheme/Rational/ParabolicSplitComponentStatements.md), for a split component `A` of `P` (a maximal split torus of a supplied radical of `P`, as in V.2.1): `GS.ParabolicSplitComponentLeviStatement` (`Z(G, A)` is represented by a rational Levi factor of `P` whose split component is `A`), `GS.LeviSplitComponentRadicalStatement` (the split component of a rational Levi factor is a split component of `P`), `GS.ParabolicSplitComponentConjugacyStatement` (the unipotent radical acts transitively on the split components of `P`) and `GS.LeviCentralizerCharacterizationStatement` (the rational Levi factors of parabolics are the centralizers of split subtori `A` that are their split components). `GS.LeviSplitComponentCentralizerStatement` states `Z_G(A_M) = M` as subgroup functors for every rational Levi of a rational parabolic. Related: `GS.DynamicLeviCocharacterRealizationStatement`, `GS.MinimalParabolicLeviCentralizerStatement` | Rec (S08); P for the four split-component statements: `parabolicSplitComponentLevi` (Task 6452), `leviSplitComponentRadical` (Task 6454), `parabolicSplitComponentConjugacy` (Task 6455), `leviCentralizerCharacterization` (Task 6456); their conjunction with the V.3.2 statement has exact proof Task 6866; S for the arbitrary-Levi split-component centralizer; P for the related statements; see the V.3.5 row |
| V.3.1 opposite parabolic: the unique `Q ∈ P(M)` with `P ∩ Q = M` | `GS.OppositeDynamicParabolicUniquenessStatement` | P |
| V.3.1 `P(M)` is finite | `GS.LeviParabolicFiniteStatement`, in [LeviSplitComponentRecallStatements](../../Langlands/GroupScheme/Rational/LeviSplitComponentRecallStatements.md): a uniform bound on finite families with distinct parabolic images and the same embedded rational Levi | Rec (S07); S. `GS.MaximalLeviParabolicCountStatement` covers maximal `M` (at most two) |
| V.3.2 minimal parabolics; conjugacy of maximal split tori and of minimal parabolics | `GS.MinimalParabolicSplitComponentStatement` (first sentence: a parabolic is minimal if and only if its split components are maximal split tori of `G`), `GS.MinimalParabolicLeviCentralizerStatement`, `GS.MaximalSplitTorusConjugacyStatement`, `GS.MinimalParabolicConjugacyStatement` | P (the first sentence by `minimalParabolicSplitComponent`, Task 6457) |
| V.3.3 `𝔞`, `𝔞^*` | `RealTorusSpace.Vstar` | D |
| V.3.4 `Σ'(A)`, `Σ(A)`, `Σ'(P)`, `Σ(P)` | `relativeRoots`, `RelativeRoot.indivisibleRoots`, `positiveRelativeRoots`, `reducedPositiveRelativeRoots`, `RelativeRoot.subgroupRelativeRoots`; `GS.RenardRootConventionStatement` | D; P: `renardRootConvention` |
| V.3.5 `W(A) = N_G(A)/Z_G(A) = N_G(M)/M`, acting faithfully | `relativeWeylGroup` (minimal case); `RP.LeviNormalizerWeylGroupStatements` (`N_G(M)/M` finite, faithful through the norms on the centre); `GS.LeviSplitComponentCentralizerStatement` and `GS.LeviSplitComponentNormalizerStatement` | D; P: `leviNormalizerWeylGroupStatements`; S for `Z_G(A_M) = M` as subgroup functors and `N_G(A_M) = N_G(M)` on rational points for arbitrary rational Levis. The normalizer equality is not asserted as equality of subgroup schemes; see the public pair's Weil-restriction counterexample to that stronger assertion |
| V.3.6 `𝔞^*_M = 𝔞^*_G ⊕ (𝔞^G_M)^*` and `𝔞_M = 𝔞_G ⊕ 𝔞^G_M`, for the minimal Levi `M_∅` (a maximal split torus `T`) | `GS.RelativeCentralDirectionsStatement` (conjunction of `RelativeCharacterRootComplementStatement` and `RelativeSplitCentralDirectionsStatement`): the root span and the restricted characters of `G` are complementary in `X^*(T) ⊗ ℝ`, and the split component of `G` embeds with image the common root annihilator | P (both conjuncts) |
| V.3.6 the same decompositions for an arbitrary Levi `M` | `GS.RenardLeviCentralDecompositionStatement` ([statement and scope](../../Langlands/GroupScheme/Rational/RenardLeviCentralDecompositionStatement.md)): over every field, for connected reductive `G`, `M` and actual split components with the compatible morphism diagram, both real restriction bijections, the canonical central-character inclusion, its complement with the literal restriction kernel, and the dual cocharacter complement with the pairing annihilator; both product equivalences have the specified addition formulas | P: `renardLeviCentralDecomposition` ([proof](../../Langlands/GroupScheme/Rational/RenardLeviCentralDecompositionProof.md), Task 6224 `423ad442`); statement from published candidate `92aa130e-c278-47d0-8647-615541ba61c5`. Realizing the compatible component diagram for every source Levi is separate |
| V.3.7 `Σ(A_∅)` is a root system and `W` its Weyl group | `GS.RelativeRootSystemStatement` (a Mathlib root system on the rational span of the relative roots, Weyl group = the image of `W`), `GS.RelativeWeylCoxeterStatement`, `GS.RelativeTitsSystemStatement`; `GS.RelativeRealCorootStatement` adds existence of invariant scalar products on the actual real character and cocharacter spaces and real root-system realizations | P for the rational system and Weyl identification; P for the real statement: `relativeRealCoroot` ([proof](../../Langlands/GroupScheme/Rational/RelativeRealCorootProof.md), Task 6346 `09d6ceb8`) |
| V.3.7 coroots `α̌ ∈ 𝔞_M`, the coroot system `Σ^∨(A_M)` in `𝔞_M`, and the spans `(𝔞^G_M)^*`, `𝔞^G_M` | `GS.RelativeRealCorootStatement`: the real image of each integral coroot from `RelativeRootReflectionData`, independence from those data, the formula and uniqueness for every invariant scalar product, the coroot span as the annihilator of restricted group characters, and crystallographic real root pairings for all roots and for the indivisible roots; minimal Levi only | P: `relativeRealCoroot` (Task 6346 `09d6ceb8`). For the projected generators for non-minimal standard Levis, see its V.3.13 component below |
| V.3.8 standard and semistandard parabolics; unique Levi factor containing `A_∅` | `GS.standardParabolic`, `GS.standardLevi`; `GS.StandardParabolicEndpointsStatement`, `GS.StandardLeviSplitComponentStatement` | D; P |
| V.3.9 every parabolic is conjugate to a standard one | `GS.StandardParabolicClassificationStatement` | P |
| V.3.10 semistandard intersections | `GS.DynamicSemistandardIntersectionStatement`, `GS.RepresentedParabolicLeviIntersectionStatement`, `GS.StandardLeviIntersectionStatement` | P |
| V.3.11 parabolics of `M` and parabolics of `G` contained in `P` | `GS.DynamicLeviParabolicCorrespondenceStatement`, `GS.DynamicNestedParabolicDecompositionStatement` | P |
| V.3.12 the simple roots form a basis of the root span; rank identities | `GS.RelativeRankStatement` (conjunction of `RelativeSimpleRootBasisStatement`: the simple relative roots form a basis of the rational span `relativeRootSpan` of the relative roots, and `RelativeRankIdentityStatement`: the rank identities and the rational character restriction) | P (both conjuncts) |
| V.3.12 the real form: `Δ_∅` is a basis of `(𝔞^G_∅)^*`, the kernel of restriction to `A_G` | `GS.RelativeSplitCentralDirectionsStatement` gives, for every split component `a : A_G → G`, an embedding `f : A_G → T` with `(rationalCharacterRestrictReal f).ker = relativeRootSpanReal i` (and the rational analogue). `GS.RelativeCharacterRootComplementStatement` gives the real complement. `GS.RelativeRealSimpleRootBasisStatement` states a real basis of `relativeRootSpanReal i` indexed by the actual simple roots, vector by vector `α ↦ 1 ⊗ α` | P (kernel identification and complement); P for the real basis: `relativeRealSimpleRootBasis` ([proof](../../Langlands/GroupScheme/Rational/RelativeRealSimpleRootBasisProof.md), Task 6345 `58a10059`) |
| V.3.12 `Δ_∅^∨` is a basis of `𝔞^G_∅`; fundamental weights and coweights | `GS.RelativeFundamentalWeightStatement`: the actual simple real coroot basis, bases dual to the simple coroots and simple roots, and uniqueness of each fundamental weight and coweight in its specified relative subspace | P: `relativeFundamentalWeight` ([proof](../../Langlands/GroupScheme/Rational/RelativeFundamentalWeightProof.md), Task 6347 `6642885b`) |
| V.3.13 `𝔞_G ⊂ 𝔞_L ⊂ 𝔞_M ⊂ 𝔞_∅`, with `𝔞_M` the annihilator of `Δ^M_∅` | `GS.StandardLeviCentralDirectionsStatement`: for every standard Levi, the split component embeds into `A_∅` with real cocharacter image the annihilator of the selected simple roots, with the ranks | P (`standardLeviCentralDirections`) |
| V.3.13 `𝔞^*_∅ = 𝔞^*_G ⊕ (𝔞^G_∅)^*`, with `(𝔞^G_∅)^*` the span of `Δ_∅` | the real part of `GS.RelativeCharacterRootComplementStatement` (the real root span and the restricted characters of `G` are complementary) | P |
| V.3.13 `𝔞^*_M` as the annihilator of the coroots of `M`; `𝔞_∅ = 𝔞_G ⊕ 𝔞^G_∅` with `𝔞^G_∅` the coroot span; `𝔞^*_M = 𝔞^*_L ⊕ (𝔞^L_M)^*` and its dual; orthogonality; projections `p^L_M` | `GS.StandardLeviRealDecompositionStatement`: for `J ⊆ K ⊆ Δ_∅`, root and coroot annihilator models, their perfect restricted pairing, the direct sums and projected spanning sets, and orthogonality for every invariant scalar product. The relative character space is the intersection of the coroot annihilator of `J` with the span of `K`, correcting I4; dually for cocharacters. The direct sums determine the projections | P: `standardLeviRealDecomposition` ([proof](../../Langlands/GroupScheme/Rational/StandardLeviRealDecompositionProof.md), Task 6348 `ff6de4a1`). The actual split-component character-space comparison remains separate; no named `p^L_M` map is added by this statement. The printed unprojected span remains false (I4) |
| V.3.14 `Δ(P)`, `Δ̂(P)`, `Δ^∨(P)`, `Δ̂^∨(P)`, `β̌` | [ParabolicChamberStatements](../../Langlands/Representation/LanglandsClassification/ParabolicChamberStatements.md), for a standard `P` given by its simple roots `J = Δ^M_∅`. In `𝔞^*_∅` and `𝔞_∅`: `GS.parabolicRoots`, `parabolicCoroots`, `parabolicFundamentalWeights`, `parabolicFundamentalCoweights` and the relation `IsParabolicCorootOf` (`β ↦ β̌`). On the split component `A` of `M`: `restrictedSimpleRoots` ([RestrictedSimpleRootCones](../../Langlands/GroupScheme/Rational/RestrictedSimpleRootCones.md)), `restrictedFundamentalWeights`, `restrictedParabolicCoroots`, `restrictedFundamentalCoweights` and `IsRestrictedParabolicCoroot`; also `GS.ParabolicRootPresentation`. Conjuncts 1–4 of `GS.ParabolicChamberLinearAlgebraStatement` state the uniqueness of the projections, the well-definedness of `β ↦ β̌` and the bases `Δ̂(P)` of `(𝔞^G_M)^*` and `Δ̂^∨(P)` of `𝔞^G_M`. Conjuncts 1–5 of `GS.ParabolicSplitComponentChamberStatement` compare the two settings | D; P for the module's inclusion and duality lemmas (`parabolicFundamentalWeights_subset`, `parabolicFundamentalCoweights_subset`, `pair_restrictedRootVector_of_isRealFundamentalCoweight`, `pair_restrict_of_isRealFundamentalWeight`); S for the two statements: exact proof Tasks 6450 (`f6359f4a-6550-49fd-b95f-10be692ddecf`) and 6451 (`46e6c7e2-c2c6-4505-b59b-a9903aa05ac9`), both without an executor at this update. The source remark that `Δ(P)` is in general not a set of simple roots and `β̌` not a coroot has no precise content and is not formalized. The spanning remark `(𝔞^G_M)^* = span Δ(P)` is in `GS.StandardLeviRealDecompositionStatement` |
| V.3.15 cones `⁺[𝔞^*]^G_P`, its closure, chambers `^G_P[𝔞^*]^+` and closure, the `𝔞`-versions, and the remark `χ = Σ c_α ϖ_α + μ` | On `𝔞^*_M = Vstar A`: `restrictedRootPositiveCone`, `restrictedRootNonnegCone`; `restrictedCorootChamber`, `restrictedClosedCorootChamber` ([LanglandsTriplet](../../Langlands/Representation/LanglandsClassification/LanglandsTriplet.md), defined by lifting to `𝔞^*_∅`) and the printed forms `GS.parabolicCorootChamber`, `parabolicClosedCorootChamber` (positivity against every `β̌`). In `𝔞^*_∅`: `openSimpleCorootFace`, `closedSimpleCorootFace`, `projectedRootPositiveCone`, `projectedRootNonnegCone`. The `𝔞`-versions: `projectedCorootPositiveCone`, `projectedCorootNonnegCone`, `restrictedCorootPositiveCone`, `restrictedCorootNonnegCone`, and the chambers `chamber`, `closedChamber` on `𝔞_M = V A` of [RenardLeviCones](../../Langlands/BruhatTits/Cartan/RenardLeviCones.md). The negative versions are pointwise negatives and have no names. Conjuncts 5–6 of `ParabolicChamberLinearAlgebraStatement` and 6–13 of `ParabolicSplitComponentChamberStatement` state that the printed and lifted chambers agree, the remark, the descriptions of the coroot cones and the comparison of the root cones | D; S: Tasks 6450 and 6451 |
| V.3.16 the faces `^G_P[(𝔞^G_M)^*]^+` and their closures as the positive (nonnegative) combinations of `Δ̂(P)`; chamber = face ⊕ `𝔞^*_G`; openness and closure; the two cell decompositions over `Q ⊇ P` | `openCorootFace`, `closedCorootFace` and their cone structures `openCorootFaceCone`, `closedCorootFaceCone`. Proved in [ParabolicChamberStatements](../../Langlands/Representation/LanglandsClassification/ParabolicChamberStatements.md), in the ambient model `𝔞^*_L ⊂ 𝔞^*_M ⊂ 𝔞^*_∅`: `openCorootFace_eq_inter`, `closedCorootFace_eq_inter`, `convex_openCorootFace`, `convex_closedCorootFace`, and both cell decompositions, `closedCorootFace_eq_iUnion` with `pairwiseDisjoint_openCorootFace` and `closedSimpleCorootFace_eq_iUnion` with `pairwiseDisjoint_openSimpleCorootFace`. Conjuncts 3 and 7–9 of `ParabolicChamberLinearAlgebraStatement` state the fundamental-weight descriptions, the sums with `𝔞^*_G` and the topological assertions | P for the intersection formulas, convexity and the cell decompositions; S for the rest: Task 6450 |
| V.3.17 Lemma | `GS.CorootChamberUnipotentRootsStatement` | P: `corootChamberUnipotentRoots` ([proof](../../Langlands/Representation/LanglandsClassification/CorootChamberUnipotentRoots.md), Worker 128, task `e341f206`) |
| V.3.18 Langlands' combinatorial lemma | `GS.LanglandsCombinatorialDecompositionStatement` ([statement](../../Langlands/GroupScheme/Rational/LanglandsDecompositionStatement.md), Worker 24 under Task 5474 `9abd0e5e`), for arbitrary connected reductive `G` and actual standard parabolics. The `μ⁻` condition follows the V.5.5 proof, not the literal `−p^L_M(…)` of (V.3.18.1), which does not determine `Q` (an `A_2` counterexample is in the Markdown of `LanglandsDecompositionCones`) | P: `langlandsCombinatorialDecomposition` ([proof](../../Langlands/GroupScheme/Rational/LanglandsDecompositionProof.md), Worker 5295, Task 5923 `cc6440ad`). The Euclidean projection theorem of V.5.5 is stated and proved (`Langlands.Renard.ConeProjectionStatements`) |
| V.3.19 `𝔞^* = Hom_lisse(M, ℝ)`, `ln \|χ\| ∈ 𝔞^*` | `PL.RationalSmoothRealDescentStatement` (smooth, that is open-kernel, homomorphisms) | P: `rationalSmoothRealDescent`. A step of the source argument says "tout morphisme" but uses smoothness; without it the descent fails (`M = 𝔾_m` over `ℚ_p`), as the statement's [Markdown](../../Langlands/Representation/Plancherel/RationalSmoothRealDescentStatement.md) records |
| V.3.20 `𝔞^*_ℂ = Hom(Λ(M), ℂ) → X(M)` via `q^{-s}`: surjectivity, kernel `(2iπ/ln q)ℛ`, real part `ℜ(χ)` independent of the lift, unitary characters are those with `ℜ(χ) = 0` | `PL.RationalComplexParameterStatement` (on the actual valuation image `Λ(M)`), `RationalImageComplexExponential`, `RationalImageRealPart` | P: `rationalComplexParameter` |
| V.3.20 `𝔞^*_ℂ = Hom_ℤ(Λ(M), ℂ)` identified with `X^*(M) ⊗_ℤ ℂ` | `PL.RationalCharacterTensorParameterStatement`: the canonical map `ℂ ⊗_ℤ X^*(G) → Hom_ℤ(Λ(G), ℂ)`, `s ⊗ χ ↦ (a ↦ s a(χ))`, is bijective for every connected reductive `G` over a nonarchimedean local field, so for every Levi `M` (on the actual valuation image `Λ(G)`, with Mathlib's scalar-first tensor order) | P: `rationalCharacterTensorParameterBijective` |
| V.3.20 the surjection `X^*(M) ⊗ ℂ → X(M)` is `χ ⊗ s ↦ [g ↦ \|χ(g)\|_F^s]` | `PL.rationalCanonicalCharacterTensorExponential_tmul_val` ([RationalCharacterTensorParameter](../../Langlands/Representation/Plancherel/RationalCharacterTensorParameter.md)), on actual rational points, with the normalized absolute value | P (a theorem about the published construction) |
| V.3.20 the kernel `(2iπ/ln q)ℛ` is a lattice; `Im X(M)` is the image of `i𝔞^*` and a compact torus isomorphic to `i𝔞^*/(2iπ/ln q)ℛ` | `PL.RationalImaginaryParameterQuotientStatement`: the periods are discrete and closed (in `𝔞^*_ℂ` and in `i𝔞^*`), the quotient of `i𝔞^*` by them is compact, and the imaginary exponential is an open quotient map inducing a homeomorphism, with the prescribed values, onto the unitary characters of `Λ(M)` and onto the unitary unramified characters of `M(F)` | P: `rationalImaginaryParameterQuotient` (topological formulation; its Markdown keeps the algebraic and manifold assertions separate) |
| V.3.20 "on retrouve ainsi la structure de tore algébrique de `X(M)`"; `Im X(M)` is a real submanifold of the complex torus `X(M)` | Partial. The Library gives `X(M)` its coordinate algebra `ℂ[Λ(M)]` (V.2.4 above) and basis-dependent isomorphisms of topological groups `X(M) ≃ (ℂ^×)^r` and `Im X(M) ≃ (S¹)^r`, `r` the rank of `Λ(M)` (`PL.rationalCanonicalUnramifiedCharacterCoordinates`, `PL.rationalCanonicalUnitaryUnramifiedCharacterCoordinates`, definitions, in [RationalUnramifiedCharacterCoordinates](../../Langlands/Representation/Plancherel/RationalUnramifiedCharacterCoordinates.md)). It constructs no variety or manifold structure on `X(M)` itself, and no statement compares the exponential with the algebraic structure. The two published statement files of the previous rows list these assertions as separate obligations | D (coordinates); G (small) for the algebraic and submanifold assertions. See also remark R2 |
| V.3.21 `M^+`, `M^{++}` (inverse images under `H_M` of the chambers) and the full cones `A^+_M`, `A^{++}_M` (all `a ∈ A_M` with `\|α(a)\|_F ≤ 1`, resp. `< 1`, for `α ∈ Δ(P)`) | [RenardLeviCones](../../Langlands/BruhatTits/Cartan/RenardLeviCones.md), namespace `Langlands.BruhatTits.Cartan.RenardLeviCones`: `leviPlus`, `leviStrict` (`M^+`, `M^{++}`: the points whose published positive centralizer valuation `H_M` lies in `closedChamber`, resp. `chamber`, on `𝔞_M = V A`) and `componentPlus`, `componentStrict` (`A^+_M`, `A^{++}_M`, defined by the norm form). The data `(i, ν, J, f)` make the dependence on `P` explicit; reading `leviPlus` as `M^+` requires the Levi, its split component and their inclusion as inputs, which the definitions do not enforce (as for `dominantCentralizer`). Proved there: the valuation forms `mem_componentPlus_iff_order`, `mem_componentStrict_iff_order`; for split `A`, agreement with the source definition `A^+_M = A_M ∩ M^+` (`map_mem_leviPlus_iff`, `preimage_leviPlus`, and the same for `A^{++}_M`); the monoid laws; `⁰M ⊂ M^+`; and `leviPlus_minimal`: `M_∅^+` is the published `dominantCentralizer` of [RenardDominantValuation](../../Langlands/Representation/Plancherel/RenardDominantValuation.md). `CocharacterUniformizer.CAplus` and `CAstrict` are the lattice cuts of V.3.23 (`CAplus_eq_inter`, `CAstrict_eq_inter`). Earlier inline uses, such as the hypotheses `characterNorm F S α x ≤ 1` in `StandardCasselmanUniformAsymptotics.lean`, are not rewritten through these names | D; P for all the listed theorems. The module states no open target. The closed chamber is defined by nonstrict inequalities; its equality with the topological closure is not stated |
| V.3.21 (V.3.21.1) `A^+_M = ⊔_Q A^{++}_L` | none | Source issue I1 below |
| V.3.22 `A^+(ε)` (all `a ∈ A_M` with `\|α(a)\|_F < ε`) | `componentEpsilon` in [RenardLeviCones](../../Langlands/BruhatTits/Cartan/RenardLeviCones.md), defined for every real `ε`. Proved there: `componentEpsilon_one` (`A^+(1) = A^{++}_M`), `componentEpsilon_mono`, `componentEpsilon_subset_componentStrict` for `ε ≤ 1`, `componentEpsilon_eq_empty` for `ε ≤ 0` and nonempty `Δ(P)`, and `CAepsilon_eq_inter`: `CocharacterUniformizer.CAepsilon` is the lattice cut `C_A^+(ε) = C_A ∩ A^+(ε)` of V.3.23. Earlier inline forms remain: the condition on every `t ∈ A(F)` in `RP.GeneralizedJacquetContractingRangeStatement` (GeneralizedJacquetRemarksStatements.lean) and `standardCone` in `StandardCasselmanConstantTerm.lean` | D; P for the listed theorems |
| V.3.23 `C_A`, `F_M`, `C̃_A = C_A F_M`, `F_M ⊂ M^+`, `C_A^+`, `C_A^{++}`, `C_A^+(ε)` | `CocharacterUniformizer.CA`, `CAplus`, `CAstrict`, `CAepsilon`; `RC.FullLatticeRepresentativeStatement`, `RC.RenardDominantComparisonStatement`, `RC.IsChamberCompatibleTransversal` | D; P: `fullLatticeRepresentative` (representatives, Task 5679) and `renardDominantComparison` |
| V.3.24 the nonnegative integral model and quotient by the common annihilator | `GS.CocharacterCone.nonnegative`, `quotient`, `mkQ_mem_quotient_iff`, `latticeSection_mem_CAplus_iff` ([construction](../../Langlands/GroupScheme/Rational/CocharacterCone.md)) | D/P for the construction and intrinsic laws; published candidate `6d296d7f-cdc6-4d8a-bbb7-580fab06a4b9` |
| V.3.24 the integral kernel of the split-central quotient | `GS.SimpleRootSplitCentralImageStatement`: for every supplied compatible `f : A_G → A_∅`, the simple-root integral annihilator equals the integral cocharacter image of `f` | S: candidate `dc66d64a-3cac-4f23-868b-62c6c8270f89`; exact proof Task 6390 (`ded1c8b7-84b7-4c10-a243-eb0395d509d7`) |
| V.3.24 the common-uniformizer group quotient and its representative map | `GS.CocharacterUniformizer.QuotientComparisonStatement`: for split `T` and every commutative `A` and `f : A → T`, the integral quotient by `range(cocharacterMapInt f)` is multiplicatively equivalent to the image of `C_T` in `T(F)/f(C_A)`, by evaluation at the common uniformizer | S: candidate `ad918cde-8ea6-485b-a90b-88fdf44dc8c6`; exact proof Task 6391 (`ee278654-01f1-4cf6-a3f5-a11da91904f3`) |
| V.3.24 finite-generation replacement for the false `S ≅ ℕ^d` assertion | `GS.CocharacterConeFiniteGenerationStatement`: for every field, actual commutative group scheme `T` and finite set `R` of actual characters, `(CocharacterCone.quotient T R).FG` | S: published candidate `84ddf0c4-2efe-474c-87de-8461db6189e1`; exact proof Task 6429 (`7e019df7-e7ba-40e6-ac54-7fbd3d1b0dec`). No public proof or freeness assertion |
| V.3.24 actual nonnegative quotient `C^+_∅/C_{A_G}` | `GS.CocharacterUniformizer.CAplusMonoid`, `CAplusQuotient`, `mem_CAplusMonoid`, `mem_CAplusQuotient` ([construction](../../Langlands/Geometry/Building/CocharacterUniformizerCone.md)) | D/P for the construction and its representative laws; published candidate `e3a3c275-d6f7-4814-bc70-0a438466c38a` |
| V.3.24 comparison of the integral nonnegative quotient with that actual quotient | `GS.CocharacterUniformizer.ConeQuotientComparisonStatement`: a monoid equivalence prescribed by common-uniformizer evaluation on every nonnegative representative, for every supplied compatible split-component map | S: published candidate `e577f809-f957-4f53-bbdd-fe5bf315fba8`; exact proof Task 6505 (`93c053ed-559d-4a2b-a441-90c0dc072fb4`) remains open |
| V.3.24 strict faces of the integral quotient | `GS.CocharacterCone.strictFace`, `mkQ_mem_strictFace_iff`, `strictFace_subset_quotient`, `existsUnique_strictFace`, `iUnion_strictFace`, `strictFace_disjoint` ([construction](../../Langlands/GroupScheme/Rational/CocharacterConeFaces.md)) | D/P: published candidate `fd6d0153-2b3d-4684-8b3a-8fd00e1f3822`; these are integral faces, before comparison with actual Levi split components |
| V.3.24 strict uniformizer image of each actual standard Levi split component | `GS.CocharacterUniformizer.StandardLeviStrictImageStatement`: under every supplied compatible map, the strict section image equals the uniformizer image of `IsStandardCocharacter` | S: published candidate `55bbe167-ba81-42e2-8ce6-ac00610fdfc1`; exact proof Task 6472 (`f221e1b4-bd46-4391-9832-8df952b39f94`) |
| V.3.24 actual strict quotient pieces | `GS.CocharacterUniformizer.standardLeviStrictQuotientFace` takes the quotient images over all actual compatible standard-Levi representatives | D/P for the definition, introduction and invalid-index emptiness laws: published candidate `ccf31197-027a-486f-9b24-978b709baf46`. The unrestricted definition supplies no structural existence or partition proof |
| V.3.24 `S = ⊔ S^{++}_L` in the actual common-uniformizer quotient | `GS.CocharacterUniformizer.StandardLeviStrictQuotientPartitionStatement`: each actual piece is contained in the nonnegative quotient, and every point of that quotient belongs to exactly one indexed piece | S: published candidate `02bea613-2825-43dc-a40d-ad0ac98db228`; exact proof Task 6605 (`133b03c2-0411-438d-b273-36ea92402a88`) remains open. Its conditional draft retains the strict-image and nonnegative-comparison premises; source issue I2 prevents the printed free-monoid conclusion |
| V.3.25 `C_A/C_{A_G}(C_A ∩ ⁰G)` finite; `C^{++}_A ∩ ⁰G ≠ ∅` | not stated separately | St: step of VI.3.5 (`RPF.RationalCompactRestrictionCuspidalStatement`, proved) |

## Evidence for the focused V.3.6–V.3.13 update

Candidate `92aa130e-c278-47d0-8647-615541ba61c5` was independently approved by
Reviewer 1171 without qualifications and published at Library
`7f43c3c930ff92f76dae6589da1678ad729017e5`. Its exact Lean/Markdown pair agrees
with the current Library and this workspace. Recovery check
`152d5695-5c49-46e5-9551-acde4a9ba2ac` compiles the module and inspects
`Langlands.GroupScheme.RenardLeviCentralDecompositionStatement` as a
`Prop`-valued definition with universe parameter `u` and only standard axioms.
This is statement evidence. Task 6224 had no submitted proof as inspected on
13 November 2026. Its proof `renardLeviCentralDecomposition` was published at
Library `ba00e0970dd9ba6222ccc056ca2ee7f06bcc8181`; see the table of the third
Worker 4 pass at the top of this note.

Worker 4's candidate `89ad3e08-f0ca-4e7e-b9fb-5a257e4a4616` contains the
four component statements above and their conjunction
`Langlands.GroupScheme.RelativeRealCorootLinearAlgebraStatement` in module
`Langlands.GroupScheme.Rational.RelativeRealCorootStatements`. Reviewer 1315
independently approved it without qualifications. It is now public at Library
`0c3f30c24701c74d5474fca3fbb5324a99aa1d58`, integration
`dd40eb81b26d4460b63752e9161dcc49`. At the base used for this update its frozen,
public and workspace pairs agree exactly. Each of its four exact proof-successor tasks,
Tasks 6345–6348, has an accepted and published proof: each component statement is proved at Library
`ba00e0970dd9ba6222ccc056ca2ee7f06bcc8181` (table at the top of this note). The
conjunction itself awaits its exact proof Task 6830
(`8a9c5345-ee7d-44ea-85d4-a16abf746ebb`). Worker 4 retains ownership of this
linear-algebra unit.

Its statements are over arbitrary fields, on the shared actual torus spaces,
and universally quantify over supplied integral reflection data. Existence of
those data is a separate published statement; no new existence proof is
claimed here. The standard-Levi spaces are ambient root/coroot annihilators.
Their identification with the character and cocharacter spaces of actual split
components needs the existing standard-Levi comparisons and any remaining
comparison proof. Neither this candidate nor the compatible-diagram V.3.6
statement settles every geometric realization. The corrected projected-root
form of V.3.13 preserves source issue I4 below.

## Evidence for the focused V.3.24 update

The following three candidates are independently accepted and published at
Library `430cc03fe803c5dbf74bc3baf91e8f7a2c26ea9c`. Their frozen, public and
workspace Lean/Markdown pairs were compared byte for byte on 13 November 2026:

| Candidate | Public unit | Independent reviewer | Integration |
| --- | --- | --- | --- |
| `6d296d7f-cdc6-4d8a-bbb7-580fab06a4b9` | `Langlands.GroupScheme.Rational.CocharacterCone` | Reviewer 1452 | `cb4564b08521488b999d6e30590be06e` |
| `dc66d64a-3cac-4f23-868b-62c6c8270f89` | `Langlands.GroupScheme.SimpleRootSplitCentralImageStatement` | Reviewer 1487 | `164d5d383c0b49dcb2b9bb966ac39dda` |
| `ad918cde-8ea6-485b-a90b-88fdf44dc8c6` | `Langlands.GroupScheme.CocharacterUniformizer.QuotientComparisonStatement` | Reviewer 1521 | `92bfb6d3987a4709ac65ff67c1aec9a0` |

The cone uses actual integral cocharacters and actual character pairings. Its
quotient is the image in the integral lattice modulo the existing common
annihilator. Its intrinsic laws identify the invertible directions and
nonnegative representatives and compare their common-uniformizer evaluations
with the existing `CAplus`. It imposes no torus or reductivity assumption.

The central-image statement is over arbitrary fields, actual connected
reductive groups, a maximal split torus and a generic cocharacter. For every
actual split component and supplied compatible morphism into that torus it
states an integral equality of submodules. The uniformizer statement is over
nonarchimedean local fields with no characteristic restriction. Only its target
torus must be split; its commutative source and morphism are arbitrary. It
specifies the equivalence on every cocharacter representative. Both are derived
prerequisites motivated by V.2.5 and V.3.23–V.3.24, rather than literal statements
of the book.

Exact proof Tasks 6390 and 6391, respectively, have complete proof-only shared
drafts at revision 1. Recovery checks
`729710d5-8bc5-411c-9d98-7b18d65e36c3` and
`8ff97a1b-440a-4772-b14b-c586da42724d` compiled these drafts with zero errors
and warnings. The first uses simple-root generation, reductive root negation,
root-annihilator centrality and integral split-component factorization. The
second uses common-uniformizer naturality, injectivity of the split target
section, its exact quotient kernel and the first isomorphism theorem. These
private compilation results supply no independent proof acceptance.

Finite-generation statement candidate `84ddf0c4-2efe-474c-87de-8461db6189e1`
passed machine validation `56b81cb6-f4ca-4d43-b9dc-6565d7d43524`. Reviewer 1621
independently approved it without qualifications in review task
`e27bda22-25ae-41e3-961f-f02394a22182`. It is now published at
`85c2fe719cf62e96f22aaf4ca03961c5814d086b`, integration
`1e1aa3dbaa0a4c8aaaa045fe99db1307`. Its frozen, current Library and workspace
pairs agree exactly. The sole finiteness premise is finiteness of the selected actual
character set. No finite-generation hypothesis on the full cocharacter lattice
is added. The complete private proof evaluates into a finite product of
integers, identifies its nonnegative image with the casts of a subtractive
submonoid of a finite product of naturals, and applies Mathlib's
`AddSubmonoid.fg_of_subtractive`. Check
`af8c8573-398f-427b-a832-7016872e0be0` compiles that private proof and inspects
the statement as `Prop`, with zero errors and warnings. Exact proof Task 6429
has the complete proof-only shared draft at revision 1. It is ready with no
executor or submitted artifact as inspected for this update. The published
statement and unreviewed draft supply no accepted finite-generation proof.

Three further units are independently accepted and published at commit
`db8d6b3d466f2fd453a4df4624ce6c90db8eed46`, and their frozen pairs agree
with the current Library and workspace:

| Candidate | Public unit | Integration |
| --- | --- | --- |
| `e3a3c275-d6f7-4814-bc70-0a438466c38a` | `CocharacterUniformizerCone` | `c6310eb1e746456989e79a0f3fa4a65c` |
| `fd6d0153-2b3d-4684-8b3a-8fd00e1f3822` | `CocharacterConeFaces` | `aba2535876504065bc185d4fce49cdcc` |
| `55bbe167-ba81-42e2-8ce6-ac00610fdfc1` | `StandardLeviStrictUniformizerStatement` | `3e190bdd6ff6460f9c47d94e64a71c21` |

The first constructs the actual submonoid image in `T(F)/f(C_A)` for arbitrary
commutative group schemes and character sets, and identifies its representatives
with the existing `CAplus`. The second partitions the integral nonnegative
quotient by the existing standard-cocharacter predicate: standardness is
invariant under the exact common annihilator, and each class has a unique
vanishing-root index. Neither uses a reductivity, genericity or positive-rank
premise. The third states the strict image comparison for connected reductive
groups over all nonarchimedean local fields, with maximal split torus, generic
cocharacter, actual closed standard-Levi representative, split component and
every compatible map. It retains integral factorization and allows non-split
groups, nonreduced relative roots and rank zero.

The 14 November publication check verifies three further units. Each has
successful machine validation and independent semantic approval without
qualifications. The frozen Lean/Markdown hashes agree with both the exact
publication commit and Library `c0debd6f4dd02fdd68d70811cf610906b945a962`,
as well as this workspace.

| Candidate | Public unit | Independent reviewer | Publication commit |
| --- | --- | --- | --- |
| `e577f809-f957-4f53-bbdd-fe5bf315fba8` | `CocharacterUniformizerConeQuotientStatement` | Reviewer 1857 | `410c79471b79f65a02fb0f6070da7f2800793ff3` |
| `ccf31197-027a-486f-9b24-978b709baf46` | `StandardLeviStrictQuotientFaces` | Reviewer 1873 | `410c79471b79f65a02fb0f6070da7f2800793ff3` |
| `02bea613-2825-43dc-a40d-ad0ac98db228` | `StandardLeviStrictQuotientPartitionStatement` | Reviewer 2010 | `e5365902d74534dbf1622c06e695dffdc128d723` |

The first states the prescribed nonnegative monoid equivalence. It replaces
rejected `49565914-009b-4bf1-a02a-98bbf4877a9f`, whose construction dependency
was then unpublished. The second defines each strict piece inside the single
actual quotient `T(F)/f₀(C_{A₀})`, using all compatible actual closed
standard-Levi representatives, their split components and strict
common-uniformizer points. Its intrinsic laws give membership from any such
representative and emptiness for invalid indices. The unrestricted definition
allows empty pieces and supplies no structural existence theorem.

The third states containment, covering and unique indexed membership for
these actual pieces. Its hypotheses retain the actual connected reductive
group, maximal split torus, generic cocharacter, supplied ambient split
component and every compatible map into the torus. Neither an image
comparison nor representative existence nor a partition is an added premise.
Both statement targets include both field characteristics, non-split groups,
nonreduced relative roots and rank zero. They concern common-uniformizer
sections, not the full rational-point cones of issue I1.

Exact proof Task 6505 (`93c053ed-559d-4a2b-a441-90c0dc072fb4`) owns the
nonnegative comparison. Its shared draft at revision 1 is conditional on
`SimpleRootSplitCentralImageStatement` and `QuotientComparisonStatement`,
whose exact proof owners remain Tasks 6390 and 6391.
Task 6605 (`133b03c2-0411-438d-b273-36ea92402a88`) owns the actual partition.
Its shared draft at revision 1 identifies actual pieces with integral strict
faces, then transfers the published integral partition through the
nonnegative monoid equivalence. It assumes exactly
`StandardLeviStrictImageStatement` and `ConeQuotientComparisonStatement`;
their owners remain Tasks 6472 and 6505. The published
`standardLeviSplitComponentStatement` supplies actual canonical representative
data in that reduction, rather than an extra representative-existence premise.

Tasks 6472, 6505 and 6605 are ready, each with shared draft revision 1, no
executor and no submitted artifact as inspected on 14 November. Recovery
check `2b26c2cf-c127-45d7-a305-94789fca7a32` compiles the private partition
reduction with zero errors and warnings. That development check and the
shared drafts supply no independent proof acceptance. Both comparison
premises of the partition reduction remain open.

The source was reread at V.3.23–V.3.24, printed p.117 / PDF p.123. The correction
of the free-monoid assertion remains issue I2 below. Proofs of the integral and
nonnegative comparisons, finite generation after transport to the actual
quotient, and the strict-face decomposition over actual standard Levi split
components remain explicit obligations. Worker 4 retains the chamber,
parabolic split-component and closed-root-subset units. The nine
closed-root-subset proofs remain open obligations; this update counts no
published proof-successor tasks for them.

## V.4 Weyl groups (118–122 / 124–128)

| Item | Lean | Status |
| --- | --- | --- |
| V.4 opening: root subgroups `U_γ` | root-subgroup constructions under `Langlands.GroupScheme.Rational` | D |
| V.4.1 `W_G`, `S_∅`; Proposition ([7]): Tits system and Bruhat decomposition | `relativeWeylGroup`; `GS.RelativeTitsSystemStatement`, `GS.TitsStandardParabolicStatement` | P |
| V.4.2 closed, convex, symmetric and unipotent subsets; `G(T)`, `U(T)`; Proposition ([7] 3.22) | `GS.ClosedRootSubsetStatements` and its nine components ([statements and scope](../../Langlands/GroupScheme/Rational/ClosedRootSubsetStatements.md)); generated groups use closed minimality on all test schemes, with existence stated separately | Rec (S14); D for the notions and elementary laws, S for the nine targets: published candidate `cf347b48-66a3-4452-b3d4-0cbc3917dca8`. Intersection targets use reduced test schemes, and (ii) uses all relative roots; see I5 |
| V.4.2 Proposition ([7] 5.12–5.18): standard parabolics and subsets `Θ ⊂ Δ_∅` | `GS.StandardParabolicClassificationStatement`, `GS.StandardCocharacterStatement`, `GS.StandardParabolicPointsStatement`; new `GS.StandardParabolicRootTripleStatement` and `GS.StandardParabolicRootSubsetGroupStatement` give the generated root triples and their groups | P for the existing classification and points statements; S for the new root-triple and generated-group comparisons, in `ClosedRootSubsetStatements` |
| V.4.3 `W_M ↪ W_G`, `w·M`, `W(L, M)`, `W_M W(L,M) W_L = W(L,M)` | `standardRelativeWeylGroup`, [RelativeWeylConjugation](../../Langlands/Group/RelativeWeylConjugation.md), `GS.StandardLeviConjugationStatement` | D; P |
| V.4.3 (V.4.3.3) `W(M, M)/W_M ≃ W(A)` | `GS.StandardLeviNormalizerQuotientStatement`; finiteness consequence `RP.LeviNormalizerFiniteQuotientStatement` | P: `standardLeviNormalizerQuotient` (Task 5688; statement candidate `4d34998c`); P (finiteness) |
| V.4.4 `W(*, M)`, `W(M, *)`, `l(M)` | inline sets in `GS.StandardWeylElementaryChainStatement` (the VI.5.4 Lemma) and `GS.StandardMaximalLeviWeylStatement` | X/D (no named definition). Both statements are proved: `standardWeylElementaryChain` and `standardMaximalLeviWeyl` |
| V.4.5 Lemma: `Q`-orbits on `P\G` and `W_M\W_G/W_L`; Bruhat order and a finer total order | `GS.StandardParabolicPointsStatement` (double-coset bijections, for standard `P` and `Q`); [RationalGeometricOrbitOrdering](../../Langlands/Representation/Aubert/General/RationalGeometricOrbitOrdering.md) | P for standard `P`, `Q`; D |
| V.4.5 Corollary: finitely many orbits for arbitrary `P`, `Q` | `GS.RepresentedParabolicDoubleCosetStatement` | P: `representedParabolicDoubleCoset` |
| V.4.6 Lemma | `GS.StandardWeylMinimalRepresentativesStatement` | P: `standardWeylMinimalRepresentatives` (Task 5649) |
| V.4.7 representatives `W^{Q,P}` for arbitrary `P`, `Q` | `RP.RepresentedGeometricLemmaGeometryStatement` | P: `representedGeometricLemmaGeometry` |
| V.4.8 maximal standard Levis and `Δ_∅ ∖ {α}`; `M` maximal iff `l(M) = 2`; `w·P = P̄′` | `GS.StandardMaximalLeviWeylStatement`; related `GS.MaximalLeviParabolicCountStatement`, `GS.MaximalLeviParabolicFamilyStatement`, `GS.MaximalLeviContainmentStatement` | P: `standardMaximalLeviWeyl` (Task 5688); P for the related statements (`maximalLeviParabolicCount`, `maximalLeviParabolicFamily`, `maximalLeviContainment`). See remark R1 |

Worker 4's closed-root-subset candidate
`cf347b48-66a3-4452-b3d4-0cbc3917dca8` was independently approved by
Reviewer 1683 and published at
`db8d6b3d466f2fd453a4df4624ce6c90db8eed46`, integration
`1b9ef7e8c26d404e8d16743bf3179597`. Its frozen, current Library and workspace
pairs match exactly. Its nine proposition targets remain unproved in this unit.
Their proofs remain open obligations; this update counts no published
proof-successor tasks for them. The arbitrary-field
statements distinguish the indivisible and possibly nonreduced ambient root
sets. They do not identify scheme-theoretic intersections on arbitrary test
schemes, and the symmetric-subset target gives integral reflections and their
preservation of the subset rather than constructing a Mathlib root-system
object. The separate proof obligations and source correction I5 are retained.

## V.5 Compact subgroups (122–129 / 128–135)

The section refers to [14] (Bruhat–Tits).

| Item | Lean | Status |
| --- | --- | --- |
| V.5.1 Theorem: `K_0` with (1)–(5) | `SC.IsCompactOpenMaximal`, `SC.SpecialCompactProperties`, `SC.SpecialLeviInheritance`, `RPF.FiniteCartanCovering`; predicates `SC.HasParabolicFactorization`, `SC.HasWeylRepresentatives`. Existence: `SC.JointSpecialCompactBasisExistenceStatement` puts the special compact properties, standard-Levi inheritance, ambient and Levi Iwasawa products, Cartan comparisons and the V.5.2 basis at one apartment point. For every valid corrected KP assignment: `SC.AvailableSimultaneousStandardBasisStatement` and `Langlands.BruhatTits.Iwasawa.AvailableIwasawaStatement` | P, for valid corrected KP data, of these parts: `availableSimultaneousStandardBasis` (Task 5310, `8d4643b8`: special compact properties, Levi inheritance and simultaneous basis at every special vertex) and `Iwasawa.availableIwasawa` (task `5e9b97bd`: both product orders and compact-open maximality). S for unconditional existence: `JointSpecialCompactBasisExistenceStatement`, exact proof task `8c39faa0` (Task 4169). The published implication `SC.jointSpecialCompactBasisExistence_of_availability_and_basis` derives it from `AvailableSimultaneousStandardBasisStatement`, now proved, and `Langlands.Geometry.Building.BruhatTitsAvailabilityStatement` (some corrected KP assignment is valid), which is unproved. Tasks `7f9ba483` and `cdf027c8`, listed in this row before, prove Waldspurger consequences that take these properties as hypotheses; they are not proofs of the Theorem |
| V.5.1 Corollary: `G/P` compact | `RP.ArbitraryParabolicQuotientCompactStatement` | P: `arbitraryParabolicQuotientCompact` |
| V.5.1 Corollary: every parabolic is `K_0`-conjugate to a standard one | `Langlands.BruhatTits.SpecialCompactParabolicConjugacyStatement` (hypothesis: property (1) of the Theorem, `G(F) = P_∅(F) K = K P_∅(F)`, for any subgroup `K` over any field) | P: `specialCompactParabolicConjugacy` ([proof](../../Langlands/BruhatTits/Parabolic/SpecialCompactConjugacyProof.md), Worker 283). For an actual `K_0`, property (1) comes from the Theorem row above |
| V.5.2 Theorem ([24] 2.1) | `SC.AvailableSimultaneousStandardBasisStatement` (its third conjunct, `SC.SimultaneousStandardBasisAt` at every special vertex); `RP.PresentationConeContractionStatement` | P for valid corrected KP data: `availableSimultaneousStandardBasis` (Task 5310, `8d4643b8`); existence of such data is the open `BruhatTitsAvailabilityStatement` (see the V.5.1 Theorem row). P: `presentationConeContraction` (the contraction parts on root presentations). The task `44b8e3a8` listed here before was not found in the task records at this update |
| V.5.3 `H_0`, the two Lemmas, the Corollary, the finiteness Lemma in module form, the Theorem and the Remark | `Langlands.Hecke.IwahoriHeckeDecompositionStatement` | P: `Langlands.Hecke.iwahoriHeckeDecomposition`, exact proof from Task 5575 (`de85c579-484b-43a2-bba9-043299101602`), verified below. Renard writes that `A` is generated by the `a_z`, `z ∈ C_∅`; the statement uses the dominant generators `z ∈ C_∅^+`, which is what the second Lemma and all later uses concern (see the statement's [Markdown](../../Langlands/Representation/Hecke/IwahoriHeckeDecompositionStatement.md), "Formal choices") |
| V.5.3 finiteness Lemma for the generated subalgebra `M`: "L'algèbre `M` est un `A`-module de type fini" | none | G: not stated. The published statement states only the module form and keeps this assertion as an outstanding source obligation (its Markdown, "Not stated"): the generated subalgebra can be larger than the module span (`G_m` over `ℚ_3`, `K = 1 + 3ℤ_3`, `F_0 = {-1}`: the span is `Aε` and the algebra is `A ⊕ Aε`), and the source proof treats only products `a_{z₁} a_{z₂ f}` |
| V.5.4 Proposition: `G` unimodular | `RPF.RationalReductiveUnimodularityStatement` | P: `rationalReductiveUnimodularity` |
| V.5.4 Lemma: `δ_{P\G}(m) = δ_G(m)/δ_P(m) = δ_P(m)^{-1} = δ_N(m)^{-1} = δ_{N̄}(m)` on `M`, and the root-product formula on `A` | `RPF.RationalParabolicModulusStatement` (`G` unimodular and the modular character of a standard `P` is the Haar modulus of `N`), `RPF.RationalOppositeHaarReciprocityStatement` (the moduli of `N` and `N̄` are reciprocal), `RPF.DynamicUnipotentHaarDeterminantStatement` (Haar modulus = normalized absolute value of `det(Ad m \| Lie N)`), `GS.DynamicAdjointDeterminantFormulaStatement` and `GS.Dynamic.AdjointDeterminantTorusRestrictionStatement` (that determinant as a product of roots with multiplicities) | C: derived from these proved statements for standard `P`; no single statement states the Lemma, and Renard's modulus orientation (inverse to Mathlib's `modularCharacter`) must be tracked as in the cited Markdown |
| V.5.5 Proposition (127 / 133): nearest point on the closure of an open cone `C` and its characterizations (i)–(iii); Corollary (128 / 134): the decomposition along a basis and its dual basis | `Langlands.Renard.ConeProjectionStatements`, in a corrected formulation: `C` is a nonempty convex open cone, and the equivalence with (iii) is asserted only for `C ≠ E` (for `C = E` the strict dual cone `Č` is empty and (iii) fails, although the projection is `v` itself). The Corollary has no extra hypothesis | P: `coneProjectionStatements` (Task 5418). See source issue I3 |
| V.5.5, display before the Corollary (128 / 134): for the cone of the Corollary, `Č = {∑ sᵢ αᵢ, sᵢ > 0}` | not stated (the statement's Markdown explains why) | Source issue I3: false as printed |
| V.5.5 end: proof of V.3.18 | `GS.langlandsCombinatorialDecomposition` | P. The formal proof follows a different route: it uses the V.5.5 Corollary only for existence, and proves uniqueness and the three projection characterizations from variational inequalities (see the [proof Markdown](../../Langlands/GroupScheme/Rational/LanglandsDecompositionProof.md)) |

### Verified V.5.3 module-form proof

Worker 127's [proof and explanation](../../Langlands/Representation/Hecke/IwahoriHeckeDecompositionProof.md)
prove the unchanged seven-clause statement, including both left and right finite
generation of the specified module and both sandwich spanning formulas. Its
hypotheses retain the actual connected reductive group over a nonarchimedean
local field, available corrected building data, the special vertex, the compact
open subgroup normal in `K_0` with the supplied simultaneous standard-parabolic
basis properties, and an arbitrary finite lattice transversal. These structural
and topological premises are not discharged by the proof.

The finite-generation argument uses `IwahoriHeckeCore`: root-pairing floor
coordinates, finite tests for invariant subsets of a compact set, and Dickson's
lemma with finite labels. It uses neither the false free-monoid assertion of
V.3.24 nor a Gordan-lemma prerequisite. Commutation for the right-handed argument
is proved for the actual split-component images and centralizer representatives.
The source was rechecked at V.3.24 and V.5.3, printed pp.117, 123–125 / PDF
pp.123, 129–131. This alternate proof does not establish the generated-subalgebra
finiteness claim in the separate table row or correct the V.3.24 assertion.

Proof artifact `89acef8f-5eea-4013-8b16-98c6155a7ac4` is independently accepted
and public at commit `cc5aa77fa8dbdc6e723091c7b710ab0d81162c4e`.
Its `lean.proof@1` validation accepts the Lake build, exact target
`Langlands.Hecke.IwahoriHeckeDecompositionStatement`, unchanged statement and
frozen inputs. Reviewer 313 approved it without qualifications. At the Library
commit used for this update, the proof pair and both helper pairs
(`IwahoriHeckeCore`, `MassIndicatorProducts`) match their frozen accepted bytes.
This evidence supplies proof coverage for that exact conditional statement,
not whole-section or whole-book completion.

## Remarks and source issues

- **R1. V.4.8, `w · P = P̄′` (printed p.122 / PDF p.128).** The rendered page has the
  overline; text extraction loses it. Without it the assertion fails: in `GL_2` with `M` the
  diagonal torus and `w = s`, `s · B` is the lower triangular Borel subgroup. The published
  statement candidate `4d34998c` states the version with the overline, and
  `standardMaximalLeviWeyl` proves it.
- **R2. V.3.20, the real part (printed p.116 / PDF p.122).** Renard first defines `ℜ(χ)` by
  lifting through the `q^{-s}` exponential, then writes `ℜ(χ) = ln |χ|`. Under the fixed
  positive valuation the two differ by the negative factor `−ln q`. The Library uses the
  first (normalized) convention throughout and records the discrepancy in
  [ArbitraryParabolicTempered](../../Langlands/Representation/Exponents/ArbitraryParabolicTempered.md)
  ("Parameter convention and retained source discrepancy") and in
  [LanglandsTriplet](../../Langlands/Representation/LanglandsClassification/LanglandsTriplet.md).
- **I1. (V.3.21.1) (printed p.116 / PDF p.122).** The book writes `A^+_M = ⊔_Q A^{++}_L` over
  the standard `Q = LU ⊇ P`, with `A^{++}_L ⊂ A_L`. As an equality of subsets of `A_M` it
  fails. In `GL_2` with `P = B`, `M` the diagonal torus and `u ∈ 𝔒_F^×`, `u ≠ 1`, the
  element `diag(1, u)` satisfies `|α(diag(1, u))|_F = 1`. It therefore lies in `A^+_M` but
  not in `A^{++}_M`, and it is not central, so it is not in `A_G`. The decomposition holds on
  the valuation side, for the chambers in `𝔞_M` (V.3.16), and for the lattice parts `C_A`.
  It also holds modulo `⁰A_M`. V.3.24 uses it in the lattice form
  `S = ⊔ C^{++}_{A_L}/C_{A_G}`.
- **I2. V.3.24 (printed p.117 / PDF p.123).** The claim `S = C^+_∅/C_{A_G} ≅ ℕ^d` with
  `d = |Δ_∅|` is false in general. The published
  [IwahoriHeckeDecompositionStatement](../../Langlands/Representation/Hecke/IwahoriHeckeDecompositionStatement.md)
  records this source issue (Reviewer 1385): for the diagonal torus of `SL_3`, `C^+_∅` in
  simple-root coordinates is `{(p, q) ∈ ℕ² | p ≡ q mod 3}`, and `(3,0) + (0,3) = 3·(1,1)`.

- **I3. V.5.5 (printed pp.127–128 / PDF pp.133–134).** Two points, recorded in the Markdown of
  the published
  [RenardConeProjectionStatements](../../Langlands/Analysis/RenardConeProjectionStatements.md).
  First, the Proposition's characterization (iii) needs `C ≠ E`: for `C = E` the strict dual
  cone `Č = {u | ∀ w ∈ C, 0 < ⟨u, w⟩}` is empty (take `w = 0`), so (iii) fails although
  `p_C(v) = v`. The Lean statement also makes explicit that `C` is nonempty and convex.
  Second, the display `Č = {∑ sᵢ αᵢ, sᵢ > 0}` before the Corollary is false as an equality
  of sets. The exact set is `{∑ sᵢ αᵢ | sᵢ ≥ 0, not all zero}`. For the standard basis of
  `ℝ²` and `C = (0, ∞)²`, the vector `(1, 0)` pairs strictly positively with every point of
  `C` but has a zero second coefficient. In positive dimension both sets have the same
  closure `{∑ sᵢ αᵢ | sᵢ ≥ 0}`, which is all the proof uses. In dimension zero `Č` and its
  closure are empty, and the Corollary holds directly. The display is not stated; the
  proved Corollary does not depend on it.

- **I4. V.3.13 (printed pp.112–113 / PDF pp.118–119).** The book defines `(𝔞^L_M)^*` as the
  subspace of `𝔞^*_∅` spanned by the `α ∈ Δ^L_∅ ∖ Δ^M_∅` and writes `𝔞^*_M = 𝔞^*_L ⊕ (𝔞^L_M)^*`,
  in particular `𝔞^*_M = 𝔞^*_G ⊕ (𝔞^G_M)^*`. With `𝔞^*_M ⊂ 𝔞^*_∅` the annihilator of the coroots
  of `M`, this fails: for `G = L = GL_3` and `M = GL_2 × GL_1` standard, `𝔞^*_M = {(x, x, y)}`,
  while `α_2 = (0, 1, −1)` pairs with `α̌_1 = (1, −1, 0)` to `−1`, so `α_2 ∉ 𝔞^*_M`. The
  decomposition holds with the roots projected to `𝔞^*_M` (equivalently restricted to `𝔞_M`), as in
  the definition of `Δ(P)` in V.3.14. Reviewer 2262 found this point.

- **I5. V.4.2 (printed p.118 / PDF p.124).** The published
  [closed-root-subset statement Markdown](../../Langlands/GroupScheme/Rational/ClosedRootSubsetStatements.md)
  records a counterexample to (ii) when closedness is read in Renard's
  indivisible root set. For a quasi-split unitary group in five variables with
  relative system `BC₂`, put `S = {e₁}` and
  `T = {e₁ − e₂, e₁ + e₂}`. Both are closed among the indivisible roots, and
  `T` is unipotent. The commutator of its two root groups gives a nontrivial
  subgroup of `U_{2e₁} ⊆ G(S)`, although `S ∩ T` is empty. Thus
  `G(S) ∩ U(T) = U(S ∩ T)` fails in that reading. The published target uses
  all relative roots, as in Borel–Tits 3.22 c); there `T` is not closed.
  The same example prevents the more general closed-subset intersection
  assertion with only convex intersection from being transferred to the
  indivisible ambient set. The convex version (i) has a separate target in
  that set. All three intersection targets concern reduced test schemes,
  consistent with the original variety statements; none asserts arbitrary
  scheme-theoretic intersection equality. This source correction is documented
  by the published statement unit, not proved as a Lean counterexample here.

## Genuine gaps of Chapter V

1. V.3.14–V.3.16: the constructions are published in Worker 4's
   `ParabolicChamberStatements`, where the intersection formulas, convexity and
   both cell decompositions are proved. The other assertions are the published
   statements `ParabolicChamberLinearAlgebraStatement` and
   `ParabolicSplitComponentChamberStatement`. Their exact proof Tasks 6450 and
   6451 have no executor at this update. The conjunction `ParabolicChamberStatement`
   has no proof task of its own: once both are proved, it follows by pairing the
   two proofs. V.3.18 is no longer a gap; `langlandsCombinatorialDecomposition`
   proves it (Task 5923).
2. V.3.6–V.3.13 realization: the compatible-diagram decompositions for arbitrary
   Levis are proved (`renardLeviCentralDecomposition`, Task 6224). The four
   real-coroot, real-basis, fundamental-weight and corrected standard-Levi
   statements of candidate `89ad3e08-f0ca-4e7e-b9fb-5a257e4a4616` are proved
   (Tasks 6345–6348). Their conjunction awaits the exact proof Task 6830, which
   only pairs the four proofs. The geometric compatible-component realization and
   the actual split-component/ambient-annihilator comparisons remain distinct
   obligations; their necessary published inputs do not alone establish every
   source-Levi instance.
3. V.5.1 Corollary, `K_0`-conjugacy of every parabolic to a standard one: no longer a gap.
   `specialCompactParabolicConjugacy` proves the published statement for every subgroup
   with property (1). The unconditional existence of `K_0` (V.5.1 Theorem row) still
   depends on the unproved `BruhatTitsAvailabilityStatement`.
4. V.5.3, the finiteness Lemma for the generated subalgebra `M`. It is retained as an
   outstanding source obligation by the published `IwahoriHeckeDecompositionStatement`,
   which states the module form. The source proof covers only the module form.
5. V.3.20: the algebraic-torus structure of `X(M)` recovered through the exponential, and
   `Im X(M)` as a real submanifold of `X(M)`. The tensor identification, the pure-tensor
   formula and the compact imaginary quotient are proved (rows above).
6. Recalled assertions with remaining proofs: `P(M)` finite (V.3.1),
   `N_G(A_M) = N_G(M)` on rational points and `Z_G(A_M) = M` for arbitrary
   rational Levis (V.3.5) are stated in the public
   `LeviSplitComponentRecallStatements`. The general
   closed-subset assertions of V.4.2 are now stated by Worker 4's public
   `ClosedRootSubsetStatements`, with the ambient-root and reduced-test
   distinctions and source correction I5 above. Their nine proof targets
   remain open obligations. The maximal anisotropic subtorus and almost
   direct product (V.2.2 Remark 2), formerly listed here, are proved by
   `torusAnisotropicPart` (Task 6398). The split-component assertions of
   V.3.1 and the first sentence of V.3.2 are proved by Tasks 6452 and
   6454–6457; only their conjunction awaits Task 6866.
7. V.3.24: proofs of the nonnegative comparison with the actual split-central
   uniformizer quotient, finite generation after its identification and the
   strict-face decomposition with actual standard Levi split components.
   The integral and actual quotient constructions, integral strict-face
   laws, four comparison statements, finite-generation statement, actual-piece
   definition and actual partition statement are now public. Tasks 6390,
   6391, 6429, 6472, 6505 and 6605 retain the exact proof obligations.
   In particular, Task 6605's conditional partition draft still requires
   the strict-image and nonnegative-comparison proofs from Tasks 6472 and
   6505. No accepted proof of the actual partition or freeness is counted.

## Proof tasks of Worker 1222's Chapter V statements

`51acec26` (V.2.3, V.2.5, V.2.6: unimodularity of `⁰G`, `⁰A₁ = A₁ ∩ ⁰A₂`, compact centre) is
published; its proof task is Task 5711. `4d34998c` (V.4.3.3 and V.4.8) is published; its proof
task is Task 5688. Task 5679 is the proof task for the published `SplitComponentKernelStatement`
(V.2.6 Lemma) and `FullLatticeRepresentativeStatement` (V.3.23), which had none. At
Library `c0debd6f4dd02fdd68d70811cf610906b945a962` all seven statements of these three
tasks are proved (see the table at the top of this note).

The compatible-component V.3.6 statement
`92aa130e-c278-47d0-8647-615541ba61c5` is published and proved by
`renardLeviCentralDecomposition`, from its exact proof Task 6224
(`423ad442-9268-4104-a37f-3f1d8eb63388`). Its arbitrary-field scope, literal
restriction kernel and actual pairing annihilator are retained. The four component
statements of Worker 4's real-coroot unit are proved by Tasks 6345–6348; their
conjunction has exact proof Task 6830 (`8a9c5345-ee7d-44ea-85d4-a16abf746ebb`). The five
component statements of Worker 4's parabolic split-component unit (V.3.1–V.3.2) are proved
by Tasks 6452 and 6454–6457; their conjunction has exact proof Task 6866
(`e5eb891b-fc5e-4885-8241-647a8b70812f`). For V.3.24, exact proof
Tasks 6390 and 6391 have complete unreviewed shared drafts at revision 1.
Task 6398, the exact proof task for the public anisotropic-part statement, is
complete: its theorem `torusAnisotropicPart` is published. Task 6429 is the exact proof successor for the now-public
finite-generation statement; Task 6472 is the exact successor for the
now-public strict-image statement. Each has a complete unreviewed shared
proof-only draft at revision 1, with no proof artifact submitted as inspected
for this update. Neither draft supplies accepted proof coverage.
Task 6505 is the exact successor for the public nonnegative quotient
comparison, and Task 6605 for the public actual strict-piece partition.
Their shared revision 1 drafts are conditional reductions, with the
undischarged premises and existing proof owners recorded above.
