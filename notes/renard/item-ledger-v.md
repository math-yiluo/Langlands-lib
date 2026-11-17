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
The 14 November V.3.24 proof-status refresh checks Library
`2309f61083ef231a3ef371f18ab1eff2ae8de56d`: the integral central-image equality,
common-uniformizer group quotient comparison and integral cone finite generation
have exact independently accepted and published proofs. A further
17 November refresh checks Library
`ab9053b1751d6b6557d044c38c04e4c8a67dfffc`: the actual standard-Levi strict-image
and nonnegative quotient comparisons also have exact independently accepted
and published proofs. The actual strict partition awaits acceptance and
publication; finite generation after transport to the actual quotient remains
a separate obligation.
The focused V.4.2 ownership audit on 14 November 2026 checks Library
`1ddfc485145c40679728553e8c3a33a5450ce7f9`: all nine component statements
have exact proof tasks, listed below; their proofs remain open.
The seventh Worker 4 pass below, on 17 November, supersedes that status:
eight of the nine are proved, and the ninth is false and its task retired.
Other rows retain their earlier audit status. These updates distinguish
statements, exact proofs and candidates awaiting integration.

A focused 16 November 2026 update checks Library
`b44618a4f02405d5be8c906f21cf7817e4eaafb9` for the V.3.21 topology row and
gap 8. The actual split-component topology statement and its exact proof
`leviChamberTopology` from Task 7234 are independently accepted and public.
The public proof pair agrees with the accepted candidate, and a fresh
development check compiles the statement and proof without errors or warnings.
The other rows retain their separately dated status.

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
6830 (`8a9c5345-ee7d-44ea-85d4-a16abf746ebb`) for the conjunction; no proof of it was
accepted at that pass. The sixth pass below records its published proof
`relativeRealCorootLinearAlgebra`.

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
conjunction; no proof of it was accepted at that pass. The sixth pass below records its
published proof `parabolicSplitComponents`. This pass leaves unchanged the V.3.24 rows, the
V.3.24 evidence section, gap 7 and the V.3.24 sentences of the proof-task section, which
Worker 1222 updates separately.

A fifth Worker 4 pass, also on 14 November, checks against Library
`320321b3cd4b5100d54cf785192677d59479e65f`. It updates the V.3.14, V.3.15 and V.3.16 rows
and gap 1. The proof below was independently accepted and first published at Library
`7f5b5f04a855fc0b4671393213c87415a6ee2aaf`, and it is unchanged in the checked Library. Its
theorem has exactly the type `ParabolicChamberLinearAlgebraStatement.{u}`, and Worker 4
found no `sorry`, `admit` or `axiom` in the proof file or in its helper module
[ParabolicChamberBasis](../../Langlands/Representation/LanglandsClassification/ParabolicChamberBasis.md).
The SHA256 digests of the Lean and Markdown files of both modules in the checked Library equal
those of the accepted artifact.

| Rows | Statement | Theorem and proof module | Proof task | Accepted artifact, reviewer | Integration ID |
| --- | --- | --- | --- | --- | --- |
| V.3.14–V.3.16, ambient model in `𝔞^*_∅` and `𝔞_∅` | `GS.ParabolicChamberLinearAlgebraStatement` | `parabolicChamberLinearAlgebra`, [ParabolicChamberLinearAlgebraProof](../../Langlands/Representation/LanglandsClassification/ParabolicChamberLinearAlgebraProof.md) | Task 6450 (`f6359f4a`) | `917390c5-6b6d-4427-805a-309b90e1b110`, Reviewer 3926 | `39b03485abcb4aee9cb99d79abc909df` |

The sibling statement `GS.ParabolicSplitComponentChamberStatement` (Task 6451) and the
conjunction `GS.ParabolicChamberStatement` of candidate
`c074eb9d-450c-4886-9f71-857c5dcf0107` have no proof in the checked Library. This pass leaves
unchanged the V.3.24 passages and the V.3.1 and V.3.5 rows on Worker 1222's Levi recall
statements. The seventh pass below records the proofs of both.

A focused Worker 1222 ownership update, also on 14 November, checks the
published [LeviSplitComponentRecallStatements](../../Langlands/GroupScheme/Rational/LeviSplitComponentRecallStatements.md)
against Library `be1ec61194b5b92447fe21556e835dcc30c124e2` and the original
V.3.1 and V.3.5.1, printed pp.109–111 / PDF pp.115–117. The three component
statements and their conjunction remain unproved. Each now has a focused
exact proof task, inspected at revision 1, ready, without a proof candidate:

| Statement in `Langlands.GroupScheme` | Exact scope | Proof owner |
| --- | --- | --- |
| `LeviSplitComponentCentralizerStatement.{u}` | For an arbitrary rational Levi of a rational parabolic and its supplied split component, `Z_G(A_M) = M` as subgroup functors on every test scheme | Task 6918 (`8b492334-9bd1-4054-a291-744e8651fe5a`) |
| `LeviSplitComponentNormalizerStatement.{u}` | `N_G(A_M) = N_G(M)` on rational points over `Spec k` | Task 6919 (`d5e7c764-40a4-4219-994d-d206b28a6994`) |
| `LeviParabolicFiniteStatement.{u}` | A uniform bound on finite families of rational parabolics with pairwise distinct images and the same embedded rational Levi | Task 6920 (`14fb8cb4-1a53-4cf1-9c42-5ce3fb95c65d`) |
| `LeviSplitComponentRecallStatements.{u}` | The conjunction of the preceding three statements, assembled from their proofs after publication | Task 6921 (`c54cc577-739f-4d0c-bacd-e3e5b45221b9`) |

All four retain the published arbitrary-field universe `u`. Renard's
source field is nonarchimedean local, and the section recalls the results
from Borel–Tits [7] and Springer [42]. The centralizer equality concerns
all test schemes; the normalizer equality concerns rational points only.
The related maximal-Levi bound of two does not prove the arbitrary-Levi
finiteness target. These ownership references supply no proof or
acceptance evidence. The eighth Worker 4 pass below records the proofs of
the first three statements; their conjunction remains open.

A sixth Worker 4 pass, on 15 November, checks against Library
`72480b70c88adff84a438bd7029d64ee3977469c`. It records the proofs of the two conjunctions
that the third and fourth passes left open. It changes the evidence paragraph on the
real-coroot unit, gaps 2 and 6 (only the sentence on the V.3.1–V.3.2 split-component
unit), two sentences of the proof-task section, and the Task 6866 clause of the V.3.1
split-component row. That row's clause on the arbitrary-Levi centralizer, Task 6918, is
unchanged. Both proofs were independently accepted and first published at Library
`497ef49830025d23824f6b2e2b1d5d60b594f51e`, and they are unchanged in the checked Library.
The SHA256 digests of their Lean and Markdown files in the checked Library equal those of
the accepted artifacts. Each theorem has exactly the type of its conjunction at universe `u`
and builds it from the component theorems listed in the third and fourth passes. Worker 4
found no `sorry`, `admit` or `axiom` in either proof file. A Worker 4 scratch file that
imports both proof modules compiles against the checked Library and reports only the
axioms `propext`, `Classical.choice` and `Quot.sound` for both theorems (diagnostic
`481fbbd1-2bce-4a65-9954-6ea2c04a96ed`).

| Rows | Statement | Theorem and proof module | Proof task | Accepted artifact, reviewer | Integration ID |
| --- | --- | --- | --- | --- | --- |
| V.3.7, V.3.12 and V.3.13, the real-coroot unit `89ad3e08` | `GS.RelativeRealCorootLinearAlgebraStatement` | `relativeRealCorootLinearAlgebra`, [RelativeRealCorootLinearAlgebraProof](../../Langlands/GroupScheme/Rational/RelativeRealCorootLinearAlgebraProof.md) | Task 6830 (`8a9c5345`) | `a8654d11-605a-46ed-bcd0-eed7ffba21ed`, Reviewer 4677 | `92287be0239c40f28284a89ae3030f7b` |
| V.3.1 and the first sentence of V.3.2, the split-component unit `409bc563` | `GS.ParabolicSplitComponentStatements` | `parabolicSplitComponents`, [ParabolicSplitComponentStatementsProof](../../Langlands/GroupScheme/Rational/ParabolicSplitComponentStatementsProof.md) | Task 6866 (`e5eb891b`) | `d40ca14a-7833-4179-82e6-2dafe6aec488`, Reviewer 4675 | `85cdbfae2b0c44ccb455cd863a363a6e` |

At this pass the sibling statement `GS.ParabolicSplitComponentChamberStatement` (Task 6451)
and the conjunction `GS.ParabolicChamberStatement` still have no proof in the checked
Library; nor do the nine V.4.2 closed-root-subset statements (Tasks 6508–6516). This pass
leaves unchanged the V.3.24 passages and Worker 1222's Levi recall rows and table.
The seventh pass below records the proofs of the first two and of eight of the nine.

A seventh Worker 4 pass, on 17 November, checks against Library
`89bac3684c44d30f371d4959c363e25649af5e8d`. It records the proofs of the V.3.14–V.3.15
split-component chamber statement, of the chamber conjunction and of eight of the nine
V.4.2 closed-root-subset statements. It also records that the ninth V.4.2 statement is
false. It updates the V.3.14, V.3.15 and two V.4.2 rows, the V.4.2 ownership paragraphs
and table, issue I5, gaps 1 and 6, the V.4.2 sentence of the opening paragraph, the
last sentence of the V.3.24 evidence section, which concerns Worker 4's units, and one
paragraph of the proof-task section. It adds the status code F. Each
proof below was independently accepted and is unchanged in the checked Library since its
first publication. Each theorem has exactly the type of its statement at universe `u`.
Worker 4 found no `sorry`, `admit` or `axiom` in any Lean file of the accepted bundles,
as they stand in the checked Library. The only textual match is the English word "admit"
in a documentation comment of `Langlands/LinearAlgebra/RationalPositiveFunctional.lean`.

| Rows | Statement | Theorem and proof module | Proof task | Accepted artifact, reviewer | Integration ID | First published |
| --- | --- | --- | --- | --- | --- | --- |
| V.3.14–V.3.15, split-component comparisons | `GS.ParabolicSplitComponentChamberStatement` | `parabolicSplitComponentChamber`, [ParabolicSplitComponentChamberProof](../../Langlands/Representation/LanglandsClassification/ParabolicSplitComponentChamberProof.md), helpers [ParabolicSplitComponentTransport](../../Langlands/Representation/LanglandsClassification/ParabolicSplitComponentTransport.md) and [ParabolicSplitComponentCorootCones](../../Langlands/Representation/LanglandsClassification/ParabolicSplitComponentCorootCones.md) | Task 6451 (`46e6c7e2`) | `eb0510e4-0cfb-4fe4-8132-269fae3de5c6`, Reviewer 4997 | `30ef3e5f73a642fc80b032c9d1755bef` | `e4a9b4d0` |
| V.3.14–V.3.16, the chamber unit `c074eb9d` | `GS.ParabolicChamberStatement` | `parabolicChamber`, [ParabolicChamberProof](../../Langlands/Representation/LanglandsClassification/ParabolicChamberProof.md) | Task 7268 (`51464b00`) | `afc4ebd8-357e-452c-ad24-a7f64d1eea4a`, Reviewer 5514 | `a270b0b921864516b4743d316770f421` | `a98af0ff` |
| V.4.2, convexity by the cone hull | `GS.ConvexRootSubsetHullStatement` | `convexRootSubsetHull`, [ConvexRootSubsetHullProof](../../Langlands/GroupScheme/Rational/ConvexRootSubsetHullProof.md) | Task 6508 (`689b8a55`) | `e15ecfdb-5786-47f7-84de-8fad79a28564`, Reviewer 5356 | `336c7f1582874eed884039437a2c9497` | `c0c2e121` |
| V.4.2, unipotence by a positive cocharacter | `GS.UnipotentRootSubsetCocharacterStatement` | `unipotentRootSubsetCocharacter`, [UnipotentRootSubsetCocharacterProof](../../Langlands/GroupScheme/Rational/UnipotentRootSubsetCocharacterProof.md) | Task 6509 (`158f9cfe`) | `12939486-7ab5-41c5-b6ab-3e358329fe33`, Reviewer 5349 | `1ae3fdea65974dbaad68d3c210470dd5` | `c0c2e121` |
| V.4.2, symmetric subsets and their reflections | `GS.SymmetricRootSubsetWeylStatement` | `symmetricRootSubsetWeyl`, [SymmetricRootSubsetWeylProof](../../Langlands/GroupScheme/Rational/SymmetricRootSubsetWeylProof.md) | Task 6510 (`1ce939a6`) | `848d48bf-ba84-44e8-aa97-fe00305145ec`, Reviewer 5379 | `a0efcaf74943481397309e2e6bfa0885` | `c0c2e121` |
| V.4.2 Proposition ([7] 5.12–5.18), the standard root triple | `GS.StandardParabolicRootTripleStatement` | `standardParabolicRootTriple`, [StandardParabolicRootTripleProof](../../Langlands/GroupScheme/Rational/StandardParabolicRootTripleProof.md), helper [StandardRootClosure](../../Langlands/GroupScheme/Rational/StandardRootClosure.md) | Task 6511 (`aa5f19bb`) | `5e73c153-2d3f-417d-88f6-19dc665048c2`, Reviewer 5361 | `ffb011ab7b8741ce836b82f186e6022d` | `c0c2e121` |
| V.4.2, existence of `G(X)` and `U(X)` | `GS.RootSubsetGroupExistenceStatement` | `rootSubsetGroupExistence`, [RootSubsetGroupExistenceProof](../../Langlands/GroupScheme/Rational/RootSubsetGroupExistenceProof.md) | Task 6512 (`8ec48a06`) | `fbf49f5f-3982-4498-aaed-f6f10c867211`, Reviewer 5381 | `fd8fdc621aea44f9bc292b44f1c7d01c` | `c0c2e121` |
| V.4.2 Proposition ([7] 5.12–5.18), the groups of the standard triple | `GS.StandardParabolicRootSubsetGroupStatement` | `standardParabolicRootSubsetGroup`, [StandardParabolicRootSubsetGroupProof](../../Langlands/GroupScheme/Rational/StandardParabolicRootSubsetGroupProof.md) | Task 6513 (`a989109c`) | `20211cb1-ee70-4d30-9581-925eaa5d2092`, Reviewer 5433 | `050e76bda7384ebca7c8cb7045cf034c` | `c0c2e121` |
| V.4.2 (i), convex intersections | `GS.ConvexRootSubsetGroupIntersectionStatement` | `convexRootSubsetGroupIntersection`, [ConvexRootSubsetGroupIntersectionProof](../../Langlands/GroupScheme/Rational/ConvexRootSubsetGroupIntersectionProof.md) | Task 6515 (`77b1b105`) | `c4c1f133-8093-4c84-a072-6acbb0b5c43b`, Reviewer 5748 | `22fbe563948945698d15f70a7cf4e29e` | `c9fdbede` |
| V.4.2 (ii), corrected ([7] 3.22(c)) | `GS.UnipotentRootSubsetGroupIntersectionStatement` | `unipotentRootSubsetGroupIntersection`, [UnipotentRootSubsetGroupIntersectionProof](../../Langlands/GroupScheme/Rational/UnipotentRootSubsetGroupIntersectionProof.md) | Task 6516 (`44b55f5d`) | `8bdef5d6-753a-4338-86a1-155fa78283d6`, Reviewer 5429 | `67459e5a0cf4432c851cecc3ef462616` | `c0c2e121` |

The first-publication commits are `e4a9b4d0164a5e0a9828dcaec5fa1cb7837ff8c6`,
`a98af0ff45faf7905209f65d641389deee5d8392`, `c0c2e1210454ae2a1888a2989e3de794c1336819`
and `c9fdbede045511865f0ea27259a1e1a35f442905`. For Tasks 7268, 6508, 6510, 6512, 6513,
6515 and 6516, the SHA256 digests of every Lean and Markdown file of the accepted bundle in
the checked Library equal those of the bundle; the Task 6515 bundle has 40 files. For the
other three proofs the Integrator removed a duplicated helper lemma, and the Library files
differ from the bundles as follows. The theorem lines are unchanged.

- Tasks 6509 and 6511: the bundles each proved the inclusion
  `IsRelativeRootAmbient.subset_relativeRoots`, in `UnipotentRootSubsetCocharacterProof`
  and in the helper `StandardRootClosure` respectively. In the Library both files import
  [RootSubsetAmbient](../../Langlands/GroupScheme/Rational/RootSubsetAmbient.md), which
  proves that lemma once, and their Markdown links to it.
- Task 6451: the helper lemma `restrictedCorootChamber_eq_image` was removed from
  `ParabolicSplitComponentTransport`. The proof now uses the published
  `restrictedCorootChamber_eq_image_openFace` of
  [SimpleCorootFaces](../../Langlands/Representation/LanglandsClassification/SimpleCorootFaces.md).
  The Lean and Markdown files of `ParabolicSplitComponentTransport` and the Lean file of
  `ParabolicSplitComponentChamberProof` differ from the bundle. They are the same at
  `e4a9b4d0` and in the checked Library.

The ninth V.4.2 statement, `GS.ClosedRootSubsetGroupIntersectionStatement`, is the
Borel–Tits 3.22(b) assertion `G(S) ∩ G(X) = G(S ∩ X)` for closed `S` and `X` whose
intersection is convex. It is false. The published erratum note
[Borel–Tits 3.22(b): a split D4 obstruction](../errata/borel-tits-1965-closed-root-intersection.md)
(Worker 248, with independent checks by Workers 292 and 785) gives a paper counterexample
in split `SO₈`: two closed symmetric subsets of type `A₁⁴` with empty, hence convex,
intersection, and a complex point of both generated groups outside `G(∅) = T`. It is not a
Lean proof of the negation. Worker 4 checked the argument. The operator retired the proof Task
6514 (`7f264fa7-67c6-4b59-88fa-a2499a6a83c1`) for this reason and opened no correction or
refutation task. The nine-part conjunction `GS.ClosedRootSubsetStatements` therefore cannot
be proved, and Worker 4 publishes no proof task for it. Renard's V.4.2(i) assumes both
subsets convex and needs only `ConvexRootSubsetGroupIntersectionStatement`, proved above.

The V.4.2 conjunction for this task is now
`GS.RenardClosedRootSubsetStatements`, the conjunction of the other eight statements, in
Worker 4's unit
[RenardClosedRootSubsetStatements](../../Langlands/GroupScheme/Rational/RenardClosedRootSubsetStatements.md)
(candidate `943f952a-086d-4c07-a8f8-127d09b37d38`, Reviewer 5896, integration
`db3e0c3b6bad49069dd905e7f71f7577`, first published at `c9fdbede`). Its Lean and Markdown
files in the checked Library equal those of the accepted candidate. It has no proof in the
checked Library. A Worker 4 scratch file that imports the eight Library proof modules and
pairs their theorems into the conjunction compiles against Library
`276bcb8d72bd1a6ea95eac204206680403da83f7`, whose Lean files are those of the checked
Library (diagnostic `92deb4fb-be36-4381-8e5f-922605ec8be5`: 0 errors, 0 warnings; axioms
`propext`, `Classical.choice`, `Quot.sound` only). Worker 4 published the exact proof Task
7357 (`22867e9f-d91c-4c14-8b74-4a4e05df7673`) for it; as inspected for this pass, the task
is ready, with no executor and no artifact. The published Markdown of
`ClosedRootSubsetStatements` predates the erratum and still describes 3.22(b) as a true
source of V.4.2(i). This ledger and the erratum note supersede those passages; Worker 4
plans a separate correction of that Markdown. This pass leaves unchanged the V.3.24 rows
and the rest of the V.3.24 evidence section, Worker 1222's Levi recall rows and table, and
the V.3.21 row and gap 8.

An eighth Worker 4 pass, on 17 November, checks against Library
`18790533e39c3ee1982619a07a6594528ad156dd`. It records three proofs of Worker 1222's Levi
recall statements, Worker 4's V.3.20 definition and statement units with their proof tasks,
and the published correction of the `ClosedRootSubsetStatements` Markdown. It updates the
first and third V.3.1 rows, the V.3.5 row, the last V.3.20 row, one sentence of issue I5,
gaps 5 and 6, and two paragraphs of the proof-task section. It also adds one sentence after the Levi recall
ownership table. Worker 1222 asked Worker 4 to record the three recall proofs in this pass
and supplied their receipts; Worker 4 checked them again. Each proof below was independently
accepted without qualifications. The SHA256 digests of its Lean and Markdown files in the
checked Library equal those of the accepted artifact. Each theorem has exactly the type of its
statement at universe `u`. A development check of each proof module against the checked
Library reports 0 errors, 0 warnings and only the axioms `propext`, `Classical.choice` and
`Quot.sound` (diagnostics `c5354d9d`, `e6668c8f` and `dbd549c1`).

| Rows | Statement | Theorem and proof module | Proof task | Accepted artifact, reviewer | Integration ID | First published |
| --- | --- | --- | --- | --- | --- | --- |
| V.3.1 and V.3.5, `Z_G(A_M) = M` | `GS.LeviSplitComponentCentralizerStatement` | `leviSplitComponentCentralizer`, [LeviSplitComponentCentralizerProof](../../Langlands/GroupScheme/Rational/LeviSplitComponentCentralizerProof.md) | Task 6918 (`8b492334`) | `678e029b-39e0-42bd-80a4-19ba7eba42d9`, Reviewer 7116 | `45f9e30595494d888270ea6fb434855c` | `371b9c35` |
| V.3.1, `P(M)` is finite | `GS.LeviParabolicFiniteStatement` | `leviParabolicFinite`, [LeviParabolicFiniteProof](../../Langlands/GroupScheme/Rational/LeviParabolicFiniteProof.md) | Task 6920 (`14fb8cb4`) | `fba9e94e-3d1d-4418-9621-f43ba708bc03`, Reviewer 7111 | `a4f25db5cf8d42afb6f3f9a3d151b1c7` | `371b9c35` |
| V.3.5, `N_G(A_M) = N_G(M)` on rational points | `GS.LeviSplitComponentNormalizerStatement` | `leviSplitComponentNormalizer`, [LeviSplitComponentNormalizerProof](../../Langlands/GroupScheme/Rational/LeviSplitComponentNormalizerProof.md) | Task 6919 (`d5e7c764`) | `44e76ef6-1feb-425a-b9ed-194b50ad0b1a`, Reviewer 7131 | `51fa371e2c694a5a99573d8782acb477` | `42c69680` |

The first-publication commits are `371b9c350ae74d42665a9e7e0ec32e4c66f56619` and
`42c696807fd25d6ea96d001a596d7bba7b4b52b9`. The finiteness proof bounds every family by
`2^|Φ(T₀)|`, for the relative roots of one maximal split torus `T₀` chosen from `(p, l)`
before the family is given; it does not compute the cardinality of `P(M)`. The normalizer
proof identifies the rational-point carriers of the two normalizers, as the statement
requires. The conjunction `GS.LeviSplitComponentRecallStatements` has no proof in the
checked Library; its assembly Task 6921 (`c54cc577-739f-4d0c-bacd-e3e5b45221b9`) remains
open.

Worker 4's two V.3.20 units are public, and their Lean and Markdown files in the checked
Library equal those of the accepted candidates. Both were approved without qualifications.

| Candidate | Module | Reviewer | Integration ID | First published |
| --- | --- | --- | --- | --- |
| `4f6249f2-7982-4623-a001-eb066d37bbf9` (definitions) | [`Langlands.Representation.Plancherel.RationalUnramifiedComplexChart`](../../Langlands/Representation/Plancherel/RationalUnramifiedComplexChart.md) | Reviewer 6366 | `a135875bd95749729076cf41637dbfcb` | `f24f97443f21ff7e59b1cf3b509602157dae54c2` |
| `c0114e82-d7ee-4df7-bdfd-97343c532629` (statements) | [`Langlands.Representation.Plancherel.RationalUnramifiedComplexTorusStatement`](../../Langlands/Representation/Plancherel/RationalUnramifiedComplexTorusStatement.md) | Reviewer 7312 | `7dbfb97fa1e04c69ac540e6b86be31d5` | `42c696807fd25d6ea96d001a596d7bba7b4b52b9` |

For each integer basis of `Λ(G)`, the definition unit gives `X(G)` the complex charted space
with the single chart of the basis coordinates, an open embedding into `ℂ^r` with image
`(ℂ^×)^r`. It also defines the inclusion of `Im X(G)` into `X(G)`. The statement unit has
four components and their conjunction `PL.RationalUnramifiedComplexTorusStatement`. The
components state that the chart of every basis is a local biholomorphism, that `X(G)` is a
complex Lie group, and that the exponential `𝔞*_ℂ → X(G)` is a local biholomorphism. The
fourth states that `Im X(G)` is an embedded real Lie subgroup, onto which the imaginary
exponential is a local diffeomorphism. None of them is proved in the checked Library.
Worker 4 published their exact proof Tasks 7645
(`c22c7289-ef76-4e16-a5ed-0f44893bbaac`), 7646 (`a6583ad9-d2ce-4077-a0ff-b03064fa34e2`),
7647 (`7acbf991-02e9-4ddf-8b2f-21ab1b2a6c92`) and 7648
(`5da801bf-c303-4714-b734-fbc2314650d7`). The conjunction will get a pairing task once all
four are proved.

The Markdown-only correction of Worker 4's `ClosedRootSubsetStatements`, candidate
`c4f9acf9-78f6-4688-bcf2-a2c6ba0dc690` (Reviewer 6377, integration
`43092495735b4fe4932b9eef8594b3b9`), was first published at
`2613dbbf784309977c42d9252b78c1e1cd40be63`. Its Lean file is unchanged, and its Markdown in
the checked Library equals the candidate's. That Markdown now records 3.22(b) as false and
derives V.4.2(i) from the convex intersection statement. The correction planned by the
seventh pass is therefore done. As inspected for this pass, Task 7357 has no published
proof. This pass leaves unchanged the V.3.24 rows and passages, including the Task 6605
partition proof that Worker 1222 records, the V.3.21 row, the V.5.3 subalgebra row, and
gaps 2, 4, 7 and 8.

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
- **F**: published statement shown false by a published paper counterexample, which the
  row cites; this is not a Lean proof of its negation. The row says what replaces it. (Code
  added by Worker 4's seventh pass.)

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
| V.3.1 `M = Z(G, A)` for a split component `A` of `P`, `A = A_M`; Levi subgroups are the centralizers of split tori `A` with `A = A_M` | Worker 4's [ParabolicSplitComponentStatements](../../Langlands/GroupScheme/Rational/ParabolicSplitComponentStatements.md), for a split component `A` of `P` (a maximal split torus of a supplied radical of `P`, as in V.2.1): `GS.ParabolicSplitComponentLeviStatement` (`Z(G, A)` is represented by a rational Levi factor of `P` whose split component is `A`), `GS.LeviSplitComponentRadicalStatement` (the split component of a rational Levi factor is a split component of `P`), `GS.ParabolicSplitComponentConjugacyStatement` (the unipotent radical acts transitively on the split components of `P`) and `GS.LeviCentralizerCharacterizationStatement` (the rational Levi factors of parabolics are the centralizers of split subtori `A` that are their split components). `GS.LeviSplitComponentCentralizerStatement` states `Z_G(A_M) = M` as subgroup functors for every rational Levi of a rational parabolic. Related: `GS.DynamicLeviCocharacterRealizationStatement`, `GS.MinimalParabolicLeviCentralizerStatement` | Rec (S08); P for the four split-component statements: `parabolicSplitComponentLevi` (Task 6452), `leviSplitComponentRadical` (Task 6454), `parabolicSplitComponentConjugacy` (Task 6455), `leviCentralizerCharacterization` (Task 6456); P for their conjunction with the V.3.2 statement, `GS.ParabolicSplitComponentStatements`, by `parabolicSplitComponents` (Task 6866); P for the arbitrary-Levi split-component centralizer: `leviSplitComponentCentralizer` (Task 6918, eighth Worker 4 pass); P for the related statements; see the V.3.5 row |
| V.3.1 opposite parabolic: the unique `Q ∈ P(M)` with `P ∩ Q = M` | `GS.OppositeDynamicParabolicUniquenessStatement` | P |
| V.3.1 `P(M)` is finite | `GS.LeviParabolicFiniteStatement`, in [LeviSplitComponentRecallStatements](../../Langlands/GroupScheme/Rational/LeviSplitComponentRecallStatements.md): a uniform bound on finite families with distinct parabolic images and the same embedded rational Levi | Rec (S07); P: `leviParabolicFinite` (Task 6920, eighth Worker 4 pass), with a bound chosen from `(p, l)` before the family. `GS.MaximalLeviParabolicCountStatement` covers maximal `M` (at most two) |
| V.3.2 minimal parabolics; conjugacy of maximal split tori and of minimal parabolics | `GS.MinimalParabolicSplitComponentStatement` (first sentence: a parabolic is minimal if and only if its split components are maximal split tori of `G`), `GS.MinimalParabolicLeviCentralizerStatement`, `GS.MaximalSplitTorusConjugacyStatement`, `GS.MinimalParabolicConjugacyStatement` | P (the first sentence by `minimalParabolicSplitComponent`, Task 6457) |
| V.3.3 `𝔞`, `𝔞^*` | `RealTorusSpace.Vstar` | D |
| V.3.4 `Σ'(A)`, `Σ(A)`, `Σ'(P)`, `Σ(P)` | `relativeRoots`, `RelativeRoot.indivisibleRoots`, `positiveRelativeRoots`, `reducedPositiveRelativeRoots`, `RelativeRoot.subgroupRelativeRoots`; `GS.RenardRootConventionStatement` | D; P: `renardRootConvention` |
| V.3.5 `W(A) = N_G(A)/Z_G(A) = N_G(M)/M`, acting faithfully | `relativeWeylGroup` (minimal case); `RP.LeviNormalizerWeylGroupStatements` (`N_G(M)/M` finite, faithful through the norms on the centre); `GS.LeviSplitComponentCentralizerStatement` and `GS.LeviSplitComponentNormalizerStatement` | D; P: `leviNormalizerWeylGroupStatements`; P for `Z_G(A_M) = M` as subgroup functors (`leviSplitComponentCentralizer`, Task 6918) and `N_G(A_M) = N_G(M)` on rational points (`leviSplitComponentNormalizer`, Task 6919) for arbitrary rational Levis (eighth Worker 4 pass); their conjunction with the finiteness statement awaits Task 6921. The normalizer equality is not asserted as equality of subgroup schemes; see the public pair's Weil-restriction counterexample to that stronger assertion |
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
| V.3.14 `Δ(P)`, `Δ̂(P)`, `Δ^∨(P)`, `Δ̂^∨(P)`, `β̌` | [ParabolicChamberStatements](../../Langlands/Representation/LanglandsClassification/ParabolicChamberStatements.md), for a standard `P` given by its simple roots `J = Δ^M_∅`. In `𝔞^*_∅` and `𝔞_∅`: `GS.parabolicRoots`, `parabolicCoroots`, `parabolicFundamentalWeights`, `parabolicFundamentalCoweights` and the relation `IsParabolicCorootOf` (`β ↦ β̌`). On the split component `A` of `M`: `restrictedSimpleRoots` ([RestrictedSimpleRootCones](../../Langlands/GroupScheme/Rational/RestrictedSimpleRootCones.md)), `restrictedFundamentalWeights`, `restrictedParabolicCoroots`, `restrictedFundamentalCoweights` and `IsRestrictedParabolicCoroot`; also `GS.ParabolicRootPresentation`. Conjuncts 1–4 of `GS.ParabolicChamberLinearAlgebraStatement` state the uniqueness of the projections, the well-definedness of `β ↦ β̌` and the bases `Δ̂(P)` of `(𝔞^G_M)^*` and `Δ̂^∨(P)` of `𝔞^G_M`. Conjuncts 1–5 of `GS.ParabolicSplitComponentChamberStatement` compare the two settings | D; P for the module's inclusion and duality lemmas (`parabolicFundamentalWeights_subset`, `parabolicFundamentalCoweights_subset`, `pair_restrictedRootVector_of_isRealFundamentalCoweight`, `pair_restrict_of_isRealFundamentalWeight`); P for `ParabolicChamberLinearAlgebraStatement` by `parabolicChamberLinearAlgebra` (exact proof Task 6450, `f6359f4a-6550-49fd-b95f-10be692ddecf`; fifth-pass table at the top of this note); P for `ParabolicSplitComponentChamberStatement` by `parabolicSplitComponentChamber` (exact proof Task 6451, `46e6c7e2-c2c6-4505-b59b-a9903aa05ac9`); P for the conjunction `GS.ParabolicChamberStatement` by `parabolicChamber` (Task 7268, `51464b00-ea5e-44f1-ab9a-dd521dc4b6ea`); seventh-pass table at the top of this note. The source remark that `Δ(P)` is in general not a set of simple roots and `β̌` not a coroot has no precise content and is not formalized. The spanning remark `(𝔞^G_M)^* = span Δ(P)` is in `GS.StandardLeviRealDecompositionStatement` |
| V.3.15 cones `⁺[𝔞^*]^G_P`, its closure, chambers `^G_P[𝔞^*]^+` and closure, the `𝔞`-versions, and the remark `χ = Σ c_α ϖ_α + μ` | On `𝔞^*_M = Vstar A`: `restrictedRootPositiveCone`, `restrictedRootNonnegCone`; `restrictedCorootChamber`, `restrictedClosedCorootChamber` ([LanglandsTriplet](../../Langlands/Representation/LanglandsClassification/LanglandsTriplet.md), defined by lifting to `𝔞^*_∅`) and the printed forms `GS.parabolicCorootChamber`, `parabolicClosedCorootChamber` (positivity against every `β̌`). In `𝔞^*_∅`: `openSimpleCorootFace`, `closedSimpleCorootFace`, `projectedRootPositiveCone`, `projectedRootNonnegCone`. The `𝔞`-versions: `projectedCorootPositiveCone`, `projectedCorootNonnegCone`, `restrictedCorootPositiveCone`, `restrictedCorootNonnegCone`, and the chambers `chamber`, `closedChamber` on `𝔞_M = V A` of [RenardLeviCones](../../Langlands/BruhatTits/Cartan/RenardLeviCones.md). The negative versions are pointwise negatives and have no names. Conjuncts 5–6 of `ParabolicChamberLinearAlgebraStatement` and 6–13 of `ParabolicSplitComponentChamberStatement` state that the printed and lifted chambers agree, the remark, the descriptions of the coroot cones and the comparison of the root cones | D; P for conjuncts 5–6 of `ParabolicChamberLinearAlgebraStatement` (`parabolicChamberLinearAlgebra`, Task 6450); P for conjuncts 6–13 of `ParabolicSplitComponentChamberStatement` (`parabolicSplitComponentChamber`, Task 6451) |
| V.3.16 the faces `^G_P[(𝔞^G_M)^*]^+` and their closures as the positive (nonnegative) combinations of `Δ̂(P)`; chamber = face ⊕ `𝔞^*_G`; openness and closure; the two cell decompositions over `Q ⊇ P` | `openCorootFace`, `closedCorootFace` and their cone structures `openCorootFaceCone`, `closedCorootFaceCone`. Proved in [ParabolicChamberStatements](../../Langlands/Representation/LanglandsClassification/ParabolicChamberStatements.md), in the ambient model `𝔞^*_L ⊂ 𝔞^*_M ⊂ 𝔞^*_∅`: `openCorootFace_eq_inter`, `closedCorootFace_eq_inter`, `convex_openCorootFace`, `convex_closedCorootFace`, and both cell decompositions, `closedCorootFace_eq_iUnion` with `pairwiseDisjoint_openCorootFace` and `closedSimpleCorootFace_eq_iUnion` with `pairwiseDisjoint_openSimpleCorootFace`. Conjuncts 3 and 7–9 of `ParabolicChamberLinearAlgebraStatement` state the fundamental-weight descriptions, the sums with `𝔞^*_G` and the topological assertions | P: the intersection formulas, convexity and the cell decompositions in the statement module; the rest by `parabolicChamberLinearAlgebra` (Task 6450) |
| V.3.17 Lemma | `GS.CorootChamberUnipotentRootsStatement` | P: `corootChamberUnipotentRoots` ([proof](../../Langlands/Representation/LanglandsClassification/CorootChamberUnipotentRoots.md), Worker 128, task `e341f206`) |
| V.3.18 Langlands' combinatorial lemma | `GS.LanglandsCombinatorialDecompositionStatement` ([statement](../../Langlands/GroupScheme/Rational/LanglandsDecompositionStatement.md), Worker 24 under Task 5474 `9abd0e5e`), for arbitrary connected reductive `G` and actual standard parabolics. The `μ⁻` condition follows the V.5.5 proof, not the literal `−p^L_M(…)` of (V.3.18.1), which does not determine `Q` (an `A_2` counterexample is in the Markdown of `LanglandsDecompositionCones`) | P: `langlandsCombinatorialDecomposition` ([proof](../../Langlands/GroupScheme/Rational/LanglandsDecompositionProof.md), Worker 5295, Task 5923 `cc6440ad`). The Euclidean projection theorem of V.5.5 is stated and proved (`Langlands.Renard.ConeProjectionStatements`) |
| V.3.19 `𝔞^* = Hom_lisse(M, ℝ)`, `ln \|χ\| ∈ 𝔞^*` | `PL.RationalSmoothRealDescentStatement` (smooth, that is open-kernel, homomorphisms) | P: `rationalSmoothRealDescent`. A step of the source argument says "tout morphisme" but uses smoothness; without it the descent fails (`M = 𝔾_m` over `ℚ_p`), as the statement's [Markdown](../../Langlands/Representation/Plancherel/RationalSmoothRealDescentStatement.md) records |
| V.3.20 `𝔞^*_ℂ = Hom(Λ(M), ℂ) → X(M)` via `q^{-s}`: surjectivity, kernel `(2iπ/ln q)ℛ`, real part `ℜ(χ)` independent of the lift, unitary characters are those with `ℜ(χ) = 0` | `PL.RationalComplexParameterStatement` (on the actual valuation image `Λ(M)`), `RationalImageComplexExponential`, `RationalImageRealPart` | P: `rationalComplexParameter` |
| V.3.20 `𝔞^*_ℂ = Hom_ℤ(Λ(M), ℂ)` identified with `X^*(M) ⊗_ℤ ℂ` | `PL.RationalCharacterTensorParameterStatement`: the canonical map `ℂ ⊗_ℤ X^*(G) → Hom_ℤ(Λ(G), ℂ)`, `s ⊗ χ ↦ (a ↦ s a(χ))`, is bijective for every connected reductive `G` over a nonarchimedean local field, so for every Levi `M` (on the actual valuation image `Λ(G)`, with Mathlib's scalar-first tensor order) | P: `rationalCharacterTensorParameterBijective` |
| V.3.20 the surjection `X^*(M) ⊗ ℂ → X(M)` is `χ ⊗ s ↦ [g ↦ \|χ(g)\|_F^s]` | `PL.rationalCanonicalCharacterTensorExponential_tmul_val` ([RationalCharacterTensorParameter](../../Langlands/Representation/Plancherel/RationalCharacterTensorParameter.md)), on actual rational points, with the normalized absolute value | P (a theorem about the published construction) |
| V.3.20 the kernel `(2iπ/ln q)ℛ` is a lattice; `Im X(M)` is the image of `i𝔞^*` and a compact torus isomorphic to `i𝔞^*/(2iπ/ln q)ℛ` | `PL.RationalImaginaryParameterQuotientStatement`: the periods are discrete and closed (in `𝔞^*_ℂ` and in `i𝔞^*`), the quotient of `i𝔞^*` by them is compact, and the imaginary exponential is an open quotient map inducing a homeomorphism, with the prescribed values, onto the unitary characters of `Λ(M)` and onto the unitary unramified characters of `M(F)` | P: `rationalImaginaryParameterQuotient` (topological formulation; its Markdown keeps the algebraic and manifold assertions separate) |
| V.3.20 "on retrouve ainsi la structure de tore algébrique de `X(M)`"; `Im X(M)` is a real submanifold of the complex torus `X(M)` | Algebraic side: the coordinate algebra `ℂ[Λ(M)]` (V.2.4 above) and the basis-dependent isomorphisms of topological groups `X(M) ≃ (ℂ^×)^r` and `Im X(M) ≃ (S¹)^r` (`PL.rationalCanonicalUnramifiedCharacterCoordinates`, `PL.rationalCanonicalUnitaryUnramifiedCharacterCoordinates`, in [RationalUnramifiedCharacterCoordinates](../../Langlands/Representation/Plancherel/RationalUnramifiedCharacterCoordinates.md)). Analytic side: Worker 4's definitions [RationalUnramifiedComplexChart](../../Langlands/Representation/Plancherel/RationalUnramifiedComplexChart.md) (the one-chart complex structure of each integer basis of `Λ(M)`) and statements [RationalUnramifiedComplexTorusStatement](../../Langlands/Representation/Plancherel/RationalUnramifiedComplexTorusStatement.md): `PL.RationalUnramifiedBasisChartIndependenceStatement` (every basis chart is a local biholomorphism), `PL.RationalUnramifiedComplexLieGroupStatement` (`X(M)` is a complex Lie group), `PL.RationalUnramifiedComplexExponentialStatement` (`𝔞*_ℂ → X(M)` is a local biholomorphism) and `PL.RationalUnitaryUnramifiedSubmanifoldStatement` (`Im X(M)` is an embedded real Lie subgroup, onto which the imaginary exponential is a local diffeomorphism), with conjunction `PL.RationalUnramifiedComplexTorusStatement`; stated for any connected reductive `G` in place of the Levi `M` | D (coordinates and charts); S for the four analytic statements, exact proof Tasks 7645–7648 (eighth Worker 4 pass). The complex structure is the analytic one; no scheme structure on `X(M)` is constructed. See also remark R2 |
| V.3.21 `M^+`, `M^{++}` (inverse images under `H_M` of the chambers) and the full cones `A^+_M`, `A^{++}_M` (all `a ∈ A_M` with `\|α(a)\|_F ≤ 1`, resp. `< 1`, for `α ∈ Δ(P)`) | [RenardLeviCones](../../Langlands/BruhatTits/Cartan/RenardLeviCones.md), namespace `Langlands.BruhatTits.Cartan.RenardLeviCones`: `leviPlus`, `leviStrict` (`M^+`, `M^{++}`: the points whose published positive centralizer valuation `H_M` lies in `closedChamber`, resp. `chamber`, on `𝔞_M = V A`) and `componentPlus`, `componentStrict` (`A^+_M`, `A^{++}_M`, defined by the norm form). The data `(i, ν, J, f)` make the dependence on `P` explicit; reading `leviPlus` as `M^+` requires the Levi, its split component and their inclusion as inputs, which the definitions do not enforce (as for `dominantCentralizer`). Proved there: the valuation forms `mem_componentPlus_iff_order`, `mem_componentStrict_iff_order`; for split `A`, agreement with the source definition `A^+_M = A_M ∩ M^+` (`map_mem_leviPlus_iff`, `preimage_leviPlus`, and the same for `A^{++}_M`); the monoid laws; `⁰M ⊂ M^+`; and `leviPlus_minimal`: `M_∅^+` is the published `dominantCentralizer` of [RenardDominantValuation](../../Langlands/Representation/Plancherel/RenardDominantValuation.md). `CocharacterUniformizer.CAplus` and `CAstrict` are the lattice cuts of V.3.23 (`CAplus_eq_inter`, `CAstrict_eq_inter`). Earlier inline uses, such as the hypotheses `characterNorm F S α x ≤ 1` in `StandardCasselmanUniformAsymptotics.lean`, are not rewritten through these names | D; P for all the listed theorems. The separate published topology target on actual standard-Levi split components is recorded in the next row |
| V.3.15/V.3.21 topology of `chamber` and `closedChamber` on the actual `𝔞_M = V A` | `Langlands.BruhatTits.Cartan.RenardLeviCones.LeviChamberTopologyStatement` ([statement and scope](../../Langlands/BruhatTits/Cartan/RenardLeviChamberTopologyStatement.md)): for an actual connected reductive group over an arbitrary field, maximal split torus, generic cocharacter, subset of simple roots, represented closed standard Levi, its actual split component and compatible factor into the maximal split torus, the strict chamber is nonempty and open, the nonstrict chamber is closed, and it equals the topological closure of the strict chamber in `moduleTopology ℝ (V A)`. Nonemptiness is a conclusion; empty roots and central directions are included | P: `Langlands.BruhatTits.Cartan.RenardLeviCones.leviChamberTopology` ([proof](../../Langlands/BruhatTits/Cartan/RenardLeviChamberTopologyProof.md)), independently accepted and published candidate `a6b1d812-cffd-4ded-baa9-dad583091837` from exact proof Task 7234 (`fdde72e2-596e-4f2a-b5bd-cc0ee54d7b39`). Statement `3815da2b-1e51-4b7a-9733-ab8b5e957974` is unchanged. Evidence below; gap 8 is closed |
| V.3.21 (V.3.21.1) `A^+_M = ⊔_Q A^{++}_L` | none | Source issue I1 below |
| V.3.22 `A^+(ε)` (all `a ∈ A_M` with `\|α(a)\|_F < ε`) | `componentEpsilon` in [RenardLeviCones](../../Langlands/BruhatTits/Cartan/RenardLeviCones.md), defined for every real `ε`. Proved there: `componentEpsilon_one` (`A^+(1) = A^{++}_M`), `componentEpsilon_mono`, `componentEpsilon_subset_componentStrict` for `ε ≤ 1`, `componentEpsilon_eq_empty` for `ε ≤ 0` and nonempty `Δ(P)`, and `CAepsilon_eq_inter`: `CocharacterUniformizer.CAepsilon` is the lattice cut `C_A^+(ε) = C_A ∩ A^+(ε)` of V.3.23. Earlier inline forms remain: the condition on every `t ∈ A(F)` in `RP.GeneralizedJacquetContractingRangeStatement` (GeneralizedJacquetRemarksStatements.lean) and `standardCone` in `StandardCasselmanConstantTerm.lean` | D; P for the listed theorems |
| V.3.23 `C_A`, `F_M`, `C̃_A = C_A F_M`, `F_M ⊂ M^+`, `C_A^+`, `C_A^{++}`, `C_A^+(ε)` | `CocharacterUniformizer.CA`, `CAplus`, `CAstrict`, `CAepsilon`; `RC.FullLatticeRepresentativeStatement`, `RC.RenardDominantComparisonStatement`, `RC.IsChamberCompatibleTransversal` | D; P: `fullLatticeRepresentative` (representatives, Task 5679) and `renardDominantComparison` |
| V.3.24 the nonnegative integral model and quotient by the common annihilator | `GS.CocharacterCone.nonnegative`, `quotient`, `mkQ_mem_quotient_iff`, `latticeSection_mem_CAplus_iff` ([construction](../../Langlands/GroupScheme/Rational/CocharacterCone.md)) | D/P for the construction and intrinsic laws; published candidate `6d296d7f-cdc6-4d8a-bbb7-580fab06a4b9` |
| V.3.24 the integral kernel of the split-central quotient | `GS.SimpleRootSplitCentralImageStatement`: for every supplied compatible `f : A_G → A_∅`, the simple-root integral annihilator equals the integral cocharacter image of `f` | P: `simpleRootSplitCentralImage` ([proof](../../Langlands/GroupScheme/Rational/SimpleRootSplitCentralImageProof.md)), published proof `3fbca376-c49d-4ef5-8f60-6a3a1c2246cd`, exact proof Task 6390 (`ded1c8b7-84b7-4c10-a243-eb0395d509d7`); statement candidate `dc66d64a-3cac-4f23-868b-62c6c8270f89` |
| V.3.24 the common-uniformizer group quotient and its representative map | `GS.CocharacterUniformizer.QuotientComparisonStatement`: for split `T` and every commutative `A` and `f : A → T`, the integral quotient by `range(cocharacterMapInt f)` is multiplicatively equivalent to the image of `C_T` in `T(F)/f(C_A)`, by evaluation at the common uniformizer | P: `CocharacterUniformizer.quotientComparison` ([proof](../../Langlands/Geometry/Building/CocharacterUniformizerQuotientProof.md)), published proof `0156f811-8882-4ee2-bdb6-5cae2e5f3516`, exact proof Task 6391 (`ee278654-01f1-4cf6-a3f5-a11da91904f3`); statement candidate `ad918cde-8ea6-485b-a90b-88fdf44dc8c6` |
| V.3.24 finite-generation replacement for the false `S ≅ ℕ^d` assertion | `GS.CocharacterConeFiniteGenerationStatement`: for every field, actual commutative group scheme `T` and finite set `R` of actual characters, `(CocharacterCone.quotient T R).FG` | P: `cocharacterConeFiniteGeneration` ([proof](../../Langlands/GroupScheme/Rational/CocharacterConeFiniteGenerationProof.md)), published proof `74788d10-0cb5-44d0-a507-db1898011da4`, exact proof Task 6429 (`7e019df7-e7ba-40e6-ac54-7fbd3d1b0dec`); statement candidate `84ddf0c4-2efe-474c-87de-8461db6189e1`. No freeness assertion |
| V.3.24 actual nonnegative quotient `C^+_∅/C_{A_G}` | `GS.CocharacterUniformizer.CAplusMonoid`, `CAplusQuotient`, `mem_CAplusMonoid`, `mem_CAplusQuotient` ([construction](../../Langlands/Geometry/Building/CocharacterUniformizerCone.md)) | D/P for the construction and its representative laws; published candidate `e3a3c275-d6f7-4814-bc70-0a438466c38a` |
| V.3.24 comparison of the integral nonnegative quotient with that actual quotient | `GS.CocharacterUniformizer.ConeQuotientComparisonStatement`: a monoid equivalence prescribed by common-uniformizer evaluation on every nonnegative representative, for every supplied compatible split-component map | P: `CocharacterUniformizer.coneQuotientComparison` ([proof](../../Langlands/Geometry/Building/CocharacterUniformizerConeQuotientProof.md)), published proof `a0f109d3-949f-45e4-ac97-48c63092e77c`, exact proof Task 6505 (`93c053ed-559d-4a2b-a441-90c0dc072fb4`); statement candidate `e577f809-f957-4f53-bbdd-fe5bf315fba8` |
| V.3.24 strict faces of the integral quotient | `GS.CocharacterCone.strictFace`, `mkQ_mem_strictFace_iff`, `strictFace_subset_quotient`, `existsUnique_strictFace`, `iUnion_strictFace`, `strictFace_disjoint` ([construction](../../Langlands/GroupScheme/Rational/CocharacterConeFaces.md)) | D/P: published candidate `fd6d0153-2b3d-4684-8b3a-8fd00e1f3822`; these are integral faces, before comparison with actual Levi split components |
| V.3.24 strict uniformizer image of each actual standard Levi split component | `GS.CocharacterUniformizer.StandardLeviStrictImageStatement`: under every supplied compatible map, the strict section image equals the uniformizer image of `IsStandardCocharacter` | P: `CocharacterUniformizer.standardLeviStrictImage` ([proof](../../Langlands/Geometry/Building/StandardLeviStrictUniformizerProof.md)), published proof `b681ec57-8c14-4416-8b9e-8730b5833ac2`, exact proof Task 6472 (`f221e1b4-bd46-4391-9832-8df952b39f94`); statement candidate `55bbe167-ba81-42e2-8ce6-ac00610fdfc1` |
| V.3.24 actual strict quotient pieces | `GS.CocharacterUniformizer.standardLeviStrictQuotientFace` takes the quotient images over all actual compatible standard-Levi representatives | D/P for the definition, introduction and invalid-index emptiness laws: published candidate `ccf31197-027a-486f-9b24-978b709baf46`. The unrestricted definition supplies no structural existence or partition proof |
| V.3.24 `S = ⊔ S^{++}_L` in the actual common-uniformizer quotient | `GS.CocharacterUniformizer.StandardLeviStrictQuotientPartitionStatement`: each actual piece is contained in the nonnegative quotient, and every point of that quotient belongs to exactly one indexed piece | S: published statement candidate `02bea613-2825-43dc-a40d-ad0ac98db228`; exact proof Task 6605 (`133b03c2-0411-438d-b273-36ea92402a88`) has staged proof candidate `490ed375-a14a-4fe1-b24d-3c49a7e28a84`, awaiting independent acceptance and publication as checked on 17 November. Both comparison prerequisites are published; source issue I2 prevents the printed free-monoid conclusion |
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
conjunction itself is proved by `relativeRealCorootLinearAlgebra`, from its exact proof
Task 6830 (`8a9c5345-ee7d-44ea-85d4-a16abf746ebb`), first published at Library
`497ef49830025d23824f6b2e2b1d5d60b594f51e` (table of the sixth Worker 4 pass). Worker 4
retains ownership of this linear-algebra unit.

Its statements are over arbitrary fields, on the shared actual torus spaces,
and universally quantify over supplied integral reflection data. Existence of
those data is a separate published statement; no new existence proof is
claimed here. The standard-Levi spaces are ambient root/coroot annihilators.
Their identification with the character and cocharacter spaces of actual split
components needs the existing standard-Levi comparisons and any remaining
comparison proof. Neither this candidate nor the compatible-diagram V.3.6
statement settles every geometric realization. The corrected projected-root
form of V.3.13 preserves source issue I4 below.

## Evidence for the focused V.3.21 topology update

On 16 November 2026 the statement candidate
`3815da2b-1e51-4b7a-9733-ab8b5e957974` is independently accepted and public.
Reviewer 5050 approved it without qualifications. Integration
`0f3c0c61f6de4192aee3351ba1a5dd12` first published the pair at commit
`e9c05be9da1000900a43de75ec2ede66892aa158`. Its frozen pair and the public
and workspace pair at audit base
`b44618a4f02405d5be8c906f21cf7817e4eaafb9` have these exact SHA256 digests:

| File | SHA256 |
| --- | --- |
| `Langlands/BruhatTits/Cartan/RenardLeviChamberTopologyStatement.lean` | `2fe7eea76174fdd35e2ca2cca9476ae2ede53a1fccf937f99d349ec4dab8ec05` |
| `Langlands/BruhatTits/Cartan/RenardLeviChamberTopologyStatement.md` | `3a7fe9a3859e71c4559ac028a7c241e4ab081c9b08762afd88f00b97a989e79b` |

This is a derived clarification of the 9 July 2026 edition: V.3.14–V.3.15,
printed p.113/PDF p.119; V.3.16, printed p.114/PDF p.120; V.3.21, printed
p.116/PDF p.122. It uses the existing positive and nonnegative root inequalities
on the full real cocharacter space of the actual Levi split component.
The statement fixes the real module topology locally and requires no topology
on the base field. Its arbitrary-field scope and the geometric hypotheses on
the supplied maps are explicit. It neither assumes a positive chamber point nor
removes the central directions. The ambient dual-face topology in
`ParabolicChamberLinearAlgebraStatement` is a distinct result.

The exact proof is from Task 7234
(`fdde72e2-596e-4f2a-b5bd-cc0ee54d7b39`), executed by Worker 706 with Worker
1222 as coauthor of its candidate
`a6b1d812-cffd-4ded-baa9-dad583091837`. The published theorem is
`Langlands.BruhatTits.Cartan.RenardLeviCones.leviChamberTopology.{u}`.
Machine evidence `ce29f28a-5b9a-44e0-83fc-8e2e0ac40203` accepts the Lake
build, exact target, unchanged statement and frozen-input checks. Reviewer 5406
independently approved the frozen candidate without qualifications in review
`7670fd31-2480-4c98-92b6-66735587dc41`. Integration
`167514e9f2e746038eb560aae161c57a` first published the proof at commit
`c0c2e1210454ae2a1888a2989e3de794c1336819`. The fetched record has
`accepted = true`, `public = true` and a published integration receipt.
The accepted archive, first-publication, audit-Library and workspace proof
pairs agree byte for byte:

| File | SHA256 |
| --- | --- |
| `Langlands/BruhatTits/Cartan/RenardLeviChamberTopologyProof.lean` | `ab7c734a2ffc6e4899877e6268ff24be2482426c7de5c73b80866e207f884531` |
| `Langlands/BruhatTits/Cartan/RenardLeviChamberTopologyProof.md` | `5912b816864080534bac25e7557e6eff01965facf09afca0ec9a1ae8000fb759` |

Public-module check `f1ddb4fc-3264-4ad2-a296-e553850279d6` and recovery
check `1ca051c7-a279-4048-a80a-61d197e87237` compile the statement and public
proof on the audit base with zero errors or warnings. The latter inspects the
theorem with universe parameter `u` and only `propext`, `Classical.choice`
and `Quot.sound`. These are development checks; the exact-target and
independent acceptance evidence is recorded above.

The proof lifts a standard cocharacter through the actual split-component map
to obtain a strict chamber point, then uses continuity of finitely many linear
inequalities and a positive perturbation to prove the topology assertions.
The separate source issue (V.3.21.1), integral and actual lattice partitions,
valuation comparisons and additional representative-existence obligations
retain their own status.

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

Exact proof Tasks 6390, 6391 and 6429 are complete. The three proofs below
were independently approved without qualifications and first published at
Library `af5d652c2f2ff5b35b4ce4dbbf7cbec8bbf3e99e`. Each theorem has exactly
its named statement as its type, including universe parameter `u`. Their
machine receipts accept the Lake build, exact-target, unchanged-statement
and frozen-input checks. On 14 November, Worker 1222 compared both files of
each proof with Library `2309f61083ef231a3ef371f18ab1eff2ae8de56d`; all six
SHA256 digests equal the frozen accepted bytes.

| Exact proof task | Theorem | Accepted proof | Independent reviewer | Integration ID |
| --- | --- | --- | --- | --- |
| Task 6390 (`ded1c8b7-84b7-4c10-a243-eb0395d509d7`) | `Langlands.GroupScheme.simpleRootSplitCentralImage` | `3fbca376-c49d-4ef5-8f60-6a3a1c2246cd` | Reviewer 3621 | `7653c1a82d6146dd8f2b5effb81005c8` |
| Task 6391 (`ee278654-01f1-4cf6-a3f5-a11da91904f3`) | `Langlands.GroupScheme.CocharacterUniformizer.quotientComparison` | `0156f811-8882-4ee2-bdb6-5cae2e5f3516` | Reviewer 3608 | `fc17bd66d06d48378f33a3189d689266` |
| Task 6429 (`7e019df7-e7ba-40e6-ac54-7fbd3d1b0dec`) | `Langlands.GroupScheme.cocharacterConeFiniteGeneration` | `74788d10-0cb5-44d0-a507-db1898011da4` | Reviewer 3611 | `e0ff2d68e7574b16ac5112e4e8539c04` |

The central-image proof uses simple-root generation and reductive root
negation to extend annihilation to every relative root. Root-annihilator
centrality and integral split-component factorization then give one
inclusion; central root restriction gives the reverse. It retains the
arbitrary-field and actual-group hypotheses above and proves the equality
for every supplied compatible morphism, without constructing that morphism.

The group quotient proof uses common-uniformizer naturality and injectivity
of the split target section to identify the exact integral kernel of the
quotient map. Surjectivity onto the section image and the first isomorphism
theorem give the equivalence, whose prescribed formula on every cocharacter
representative holds definitionally. No injectivity of the source section
or of the morphism is required. This proves the group comparison; its
restriction to the nonnegative submonoids is now proved by
`CocharacterUniformizer.coneQuotientComparison` from Task 6505, verified below.

Finite-generation statement candidate `84ddf0c4-2efe-474c-87de-8461db6189e1`
passed machine validation `56b81cb6-f4ca-4d43-b9dc-6565d7d43524`. Reviewer 1621
independently approved it without qualifications in review task
`e27bda22-25ae-41e3-961f-f02394a22182`. It is now published at
`85c2fe719cf62e96f22aaf4ca03961c5814d086b`, integration
`1e1aa3dbaa0a4c8aaaa045fe99db1307`. Its frozen, current Library and workspace
pairs agree exactly. The sole finiteness premise is finiteness of the selected actual
character set. No finite-generation hypothesis on the full cocharacter lattice
is added. The published proof evaluates into a finite product of
integers, identifies its nonnegative image with the casts of a subtractive
submonoid of a finite product of naturals, and applies Mathlib's
`AddSubmonoid.fg_of_subtractive`. Finite generation passes to the evaluation
image and is reflected through the injective map from the annihilator
quotient. The proof covers the empty character set and arbitrary fields and
commutative group schemes; no torus, finite-type, splitness or positive-rank
premise is used. It proves finite generation of the integral quotient, with
no freeness or generator-count claim. The required nonnegative comparison
from Task 6505 is now published. Transport of finite generation to the actual
nonnegative uniformizer quotient remains a separate obligation.

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

On 17 November 2026 Worker 1222 verified the two exact comparison proofs
below against Library `ab9053b1751d6b6557d044c38c04e4c8a67dfffc`. Both were
first published at `2613dbbf784309977c42d9252b78c1e1cd40be63`; their exact
proof tasks are complete. Both fetched records report `accepted = true`,
`public = true` and published integration receipts. Each independent
review approves without qualifications, and each machine receipt accepts
the Lake build, exact target, unchanged statement and frozen inputs.

| Exact proof task | Theorem and proof module | Accepted proof; authors | Independent reviewer | Machine receipt | Integration ID |
| --- | --- | --- | --- | --- | --- |
| Task 6472 (`f221e1b4-bd46-4391-9832-8df952b39f94`) | `Langlands.GroupScheme.CocharacterUniformizer.standardLeviStrictImage`, [StandardLeviStrictUniformizerProof](../../Langlands/Geometry/Building/StandardLeviStrictUniformizerProof.md) | `b681ec57-8c14-4416-8b9e-8730b5833ac2`; Workers 292 and 1222 | Reviewer 6504 | `7e7e39c2-1ec0-41ed-bd20-f0395a6a5f75` | `3f3131bfd65940d78381b5a96fbef45d` |
| Task 6505 (`93c053ed-559d-4a2b-a441-90c0dc072fb4`) | `Langlands.GroupScheme.CocharacterUniformizer.coneQuotientComparison`, [CocharacterUniformizerConeQuotientProof](../../Langlands/Geometry/Building/CocharacterUniformizerConeQuotientProof.md) | `a0f109d3-949f-45e4-ac97-48c63092e77c`; Workers 127 and 1222 | Reviewer 6551 | `9169aee4-d3da-4c12-98a9-57d4d7ea70e1` | `abbe6af8154f4b939cf6e0e7336e5ee4` |

For each proof, the Lean and Markdown bytes in the frozen accepted candidate,
first-publication commit, audit Library and workspace agree exactly. Each
statement's Lean and Markdown bytes also agree between the proof base
`fcb85a7ef43356fec01e6ccf1605f08568c08cb0`, first publication, audit Library
and workspace. The exact targets retain universe parameter `u` and every
hypothesis of `StandardLeviStrictImageStatement` and
`ConeQuotientComparisonStatement`, respectively.

The strict-image proof uses the actual standard-Levi torus factor and cancels
the supplied closed Levi inclusion in the compatibility square. The
`dynamicLie` root-vanishing result handles selected simple roots; the
uniformizer norm formula converts the remaining positive integral pairings
into strict inequalities. In the reverse direction, standard-cocharacter
centrality and integral split-component factorization supply a lift whose
uniformizer value is strict. No real-vector-space factorization replaces
the integral lift.

The nonnegative comparison applies the published
`simpleRootSplitCentralImage` and `quotientComparison`, restricts the resulting
group equivalence to the nonnegative submonoids and proves the prescribed
formula on every nonnegative representative. Both comparisons retain either
field characteristic, non-split connected reductive groups, nonreduced
relative roots, rank zero and every supplied compatible split-component map.
They concern the actual common-uniformizer sections and quotient.

Task 6605 (`133b03c2-0411-438d-b273-36ea92402a88`), executed by Worker 118,
owns the actual partition. Its proof candidate
`490ed375-a14a-4fe1-b24d-3c49a7e28a84`, with Worker 1222 as coauthor, is
staged as checked on 17 November, with `accepted = false`, `public = false`
and no acceptance evidence. Independent review
`b20a9e72-89e5-410b-8a10-e91ffa8629f8` remains pending. Its reduction
identifies actual pieces with integral strict faces and transfers the
integral partition through the nonnegative comparison. Both comparison
prerequisites from Tasks 6472 and 6505 are now published. The published
`standardLeviSplitComponentStatement` supplies canonical actual representative
data. Neither the draft nor the staged candidate counts as a published
partition proof.

The source was reread at V.2.5 (printed p.107 / PDF p.113), V.3.21 (printed
p.116 / PDF p.122) and V.3.23–V.3.24 (printed p.117 / PDF p.123).
The correction of the free-monoid assertion remains issue I2 below. The
integral central-image equality, group quotient comparison, integral finite
generation, actual strict-image comparison and nonnegative quotient comparison
are proved. Finite generation after transport to the actual quotient and
acceptance and publication of the actual strict-piece partition remain
explicit obligations. Worker 4 retains the chamber,
parabolic split-component and closed-root-subset units. Eight of the nine
closed-root-subset proofs are published, the ninth target is false, and the
V.4.2 section below records their status (seventh Worker 4 pass).

## V.4 Weyl groups (118–122 / 124–128)

| Item | Lean | Status |
| --- | --- | --- |
| V.4 opening: root subgroups `U_γ` | root-subgroup constructions under `Langlands.GroupScheme.Rational` | D |
| V.4.1 `W_G`, `S_∅`; Proposition ([7]): Tits system and Bruhat decomposition | `relativeWeylGroup`; `GS.RelativeTitsSystemStatement`, `GS.TitsStandardParabolicStatement` | P |
| V.4.2 closed, convex, symmetric and unipotent subsets; `G(T)`, `U(T)`; Proposition ([7] 3.22) | The nine components of `GS.ClosedRootSubsetStatements` ([statements and scope](../../Langlands/GroupScheme/Rational/ClosedRootSubsetStatements.md)); generated groups use closed minimality on all test schemes, with existence stated separately. The V.4.2 conjunction is `GS.RenardClosedRootSubsetStatements` ([statement](../../Langlands/GroupScheme/Rational/RenardClosedRootSubsetStatements.md)), the conjunction of the eight components other than the Borel–Tits 3.22(b) statement `GS.ClosedRootSubsetGroupIntersectionStatement` | Rec (S14); D for the notions and elementary laws. P for eight targets (published candidate `cf347b48-66a3-4452-b3d4-0cbc3917dca8`; proofs from Tasks 6508–6513, 6515 and 6516, seventh-pass table at the top of this note). F for `ClosedRootSubsetGroupIntersectionStatement`, by the paper counterexample of the [erratum note](../errata/borel-tits-1965-closed-root-intersection.md); its Task 6514 is retired, and the nine-part conjunction is therefore not provable. S for `RenardClosedRootSubsetStatements` (candidate `943f952a-086d-4c07-a8f8-127d09b37d38`): exact pairing proof Task 7357 (`22867e9f-d91c-4c14-8b74-4a4e05df7673`). Intersection targets use reduced test schemes, and (ii) uses all relative roots; see I5 |
| V.4.2 Proposition ([7] 5.12–5.18): standard parabolics and subsets `Θ ⊂ Δ_∅` | `GS.StandardParabolicClassificationStatement`, `GS.StandardCocharacterStatement`, `GS.StandardParabolicPointsStatement`; new `GS.StandardParabolicRootTripleStatement` and `GS.StandardParabolicRootSubsetGroupStatement` give the generated root triples and their groups | P for the existing classification and points statements; P for the new root-triple and generated-group comparisons, in `ClosedRootSubsetStatements`: `standardParabolicRootTriple` (Task 6511) and `standardParabolicRootSubsetGroup` (Task 6513) |
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
pairs match exactly. The unit itself proves none of its nine proposition
targets. As of the seventh Worker 4 pass, eight of them are proved by their
exact proof tasks and the ninth is false; see the table below. The arbitrary-field
statements distinguish the indivisible and possibly nonreduced ambient root
sets. They do not identify scheme-theoretic intersections on arbitrary test
schemes, and the symmetric-subset target gives integral reflections and their
preservation of the subset rather than constructing a Mathlib root-system
object. Source correction I5 is retained.

The 14 November ownership audit found all nine tasks at revision 1, ready,
with no submitted artifacts. A search of the checked Library found the nine
proposition definitions and their conjunction references, with no exact proof
theorems. Worker 4 retains responsibility for these proof tasks. Each target
is in namespace `Langlands.GroupScheme` (`GS` below) at universe `u`, over
an arbitrary field, an actual connected reductive group and a maximal split
torus. Where used, the generic cocharacter and simple-root subset remain
quantified data. “Either ambient set” means the indivisible roots or all
possibly nonreduced relative roots, as specified by `IsRelativeRootAmbient`.

| Exact target | Scope | Proof task; status on 17 November |
| --- | --- | --- |
| `GS.ConvexRootSubsetHullStatement` | In either ambient set, convexity is equivalent to containing every ambient root in the real cone hull of the subset, with the subset condition retained | Task 6508 (`689b8a55-8c76-4965-b535-6ee283192b4b`); P: `convexRootSubsetHull` |
| `GS.UnipotentRootSubsetCocharacterStatement` | In either ambient set, unipotence is equivalent to closedness and existence of a cocharacter positive on every member | Task 6509 (`158f9cfe-e93b-4a0e-af39-c9b1f47a7009`); P: `unipotentRootSubsetCocharacter` |
| `GS.SymmetricRootSubsetWeylStatement` | In either ambient set, integral reflections exist for each member of a symmetric subset; those reflections and their generated Weyl subgroup preserve the subset | Task 6510 (`1ce939a6-171f-45ff-bd20-432b2db9f3ca`); P: `symmetricRootSubsetWeyl` |
| `GS.StandardParabolicRootTripleStatement` | In either ambient set, the standard triple has the explicit integral-span root descriptions, convexity, symmetry and unipotence properties and recovers `Θ` | Task 6511 (`aa5f19bb-1161-4b7d-b3f3-ade8d8fd5c25`); P: `standardParabolicRootTriple` |
| `GS.RootSubsetGroupExistenceStatement` | For every subset of all relative roots, smooth affine connected minimal closed groups `G(X)` and `U(X)` exist; `U(X)` is unipotent when `X` is unipotent in either ambient set | Task 6512 (`8ec48a06-a508-4334-ad07-0a603fc7e135`); P: `rootSubsetGroupExistence` |
| `GS.StandardParabolicRootSubsetGroupStatement` | In either ambient set, minimal groups for the standard triple equal the existing parabolic, Levi and radical functors on all tests, and the generated Weyl subgroup equals the standard Levi Weyl subgroup | Task 6513 (`a989109c-457e-46dd-96ce-6e7960c4e93d`); P: `standardParabolicRootSubsetGroup` |
| `GS.ClosedRootSubsetGroupIntersectionStatement` | In all relative roots, closed `S` and `X` with convex overlap satisfy `G(S) ∩ G(X) = G(S ∩ X)` on reduced test schemes ([7] 3.22(b)) | Task 6514 (`7f264fa7-67c6-4b59-88fa-a2499a6a83c1`), retired by the operator; F: false by the paper counterexample of the [erratum note](../errata/borel-tits-1965-closed-root-intersection.md) |
| `GS.ConvexRootSubsetGroupIntersectionStatement` | In the indivisible roots, convex `S` and `X` satisfy `G(S) ∩ G(X) = G(S ∩ X)` on reduced test schemes (V.4.2(i)) | Task 6515 (`77b1b105-0195-4b71-a588-ede7dd5a2aa6`); P: `convexRootSubsetGroupIntersection` |
| `GS.UnipotentRootSubsetGroupIntersectionStatement` | In all relative roots, closed `S` and unipotent `X` satisfy `G(S) ∩ U(X) = U(S ∩ X)` on reduced test schemes ([7] 3.22(c), corrected V.4.2(ii); see I5) | Task 6516 (`44b55f5d-dcd6-45f2-9aab-2d61d46b585e`); P: `unipotentRootSubsetGroupIntersection` |

The three intersection targets quantify over supplied minimal closed
representatives; their existence is the separate Task 6512 obligation,
now proved. The proofs, reviewers and integration receipts are in the
seventh-pass table at the top of this note. Because the 3.22(b) target is
false, the nine-part conjunction `GS.ClosedRootSubsetStatements` is not
provable, and Worker 4 publishes no pairing task for it. The V.4.2
conjunction is instead `GS.RenardClosedRootSubsetStatements`, the
conjunction of the other eight, with exact pairing proof Task 7357
(`22867e9f-d91c-4c14-8b74-4a4e05df7673`); it has no proof in the checked
Library. Worker 4 retains responsibility for that task.

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

  A second correction, recorded by Worker 4's seventh pass, concerns the more
  general Borel–Tits 3.22(b). The published unit states it in all relative
  roots as `ClosedRootSubsetGroupIntersectionStatement`. Its Markdown cited it
  as a source of (i) until the correction recorded by the eighth Worker 4 pass.
  That statement is false. The published
  [erratum note](../errata/borel-tits-1965-closed-root-intersection.md)
  (Worker 248) gives a paper counterexample in split `SO₈` over `ℂ`. The
  subsets `S = {±ε₁ ± ε₂, ±ε₃ ± ε₄}` and `X = {±ε₁ ± ε₃, ±ε₂ ± ε₄}`, of type
  `A₁⁴`, are closed and disjoint, so `S ∩ X` is convex. The element `J`
  exchanging each `e_r` with `f_r` lies in `G(S) ∩ G(X)` but not in
  `G(∅) = T`. Neither subset is convex, so the counterexample does not affect
  (i), which assumes both subsets convex and is proved as
  `convexRootSubsetGroupIntersection` (Task 6515). The V.4.2 conjunction
  `RenardClosedRootSubsetStatements` omits the false statement.

## Genuine gaps of Chapter V

1. V.3.14–V.3.16: no longer a gap. The constructions are published in Worker 4's
   `ParabolicChamberStatements`, where the intersection formulas, convexity and
   both cell decompositions are proved. The ambient assertions
   `ParabolicChamberLinearAlgebraStatement` are proved by
   `parabolicChamberLinearAlgebra` (Task 6450), the split-component comparisons
   `ParabolicSplitComponentChamberStatement` by `parabolicSplitComponentChamber`
   (Task 6451), and their conjunction `ParabolicChamberStatement` by
   `parabolicChamber` (Task 7268), as recorded by the seventh Worker 4 pass.
   V.3.18 is no longer a gap; `langlandsCombinatorialDecomposition`
   proves it (Task 5923).
2. V.3.6–V.3.13 realization: the compatible-diagram decompositions for arbitrary
   Levis are proved (`renardLeviCentralDecomposition`, Task 6224). The four
   real-coroot, real-basis, fundamental-weight and corrected standard-Levi
   statements of candidate `89ad3e08-f0ca-4e7e-b9fb-5a257e4a4616` are proved
   (Tasks 6345–6348), and so is their conjunction, by
   `relativeRealCorootLinearAlgebra` (Task 6830), which pairs the four proofs.
   The geometric compatible-component realization and the actual
   split-component/ambient-annihilator comparisons remain distinct
   obligations; their necessary published inputs do not alone establish every
   source-Levi instance.
3. V.5.1 Corollary, `K_0`-conjugacy of every parabolic to a standard one: no longer a gap.
   `specialCompactParabolicConjugacy` proves the published statement for every subgroup
   with property (1). The unconditional existence of `K_0` (V.5.1 Theorem row) still
   depends on the unproved `BruhatTitsAvailabilityStatement`.
4. V.5.3, the finiteness Lemma for the generated subalgebra `M`. It is retained as an
   outstanding source obligation by the published `IwahoriHeckeDecompositionStatement`,
   which states the module form. The source proof covers only the module form.
5. V.3.20: no longer a statement gap. The complex-torus structure of `X(M)` recovered
   through the exponential, and `Im X(M)` as a real submanifold of `X(M)`, are stated by
   Worker 4's public `RationalUnramifiedComplexTorusStatement` (eighth Worker 4 pass). Their
   proofs remain open, owned by exact proof Tasks 7645–7648. The tensor identification,
   the pure-tensor formula and the compact imaginary quotient are proved (rows above).
6. Recalled assertions with remaining proofs: `P(M)` finite (V.3.1),
   `N_G(A_M) = N_G(M)` on rational points and `Z_G(A_M) = M` for arbitrary
   rational Levis (V.3.5) are stated in the public
   `LeviSplitComponentRecallStatements`. They are proved by
   `leviParabolicFinite`, `leviSplitComponentNormalizer` and
   `leviSplitComponentCentralizer`, from exact proof Tasks 6920, 6919 and 6918
   (eighth Worker 4 pass). Their conjunction remains open, owned by exact
   assembly Task 6921. The ownership table above gives full IDs and
   scopes. The general
   closed-subset assertions of V.4.2 are stated by Worker 4's public
   `ClosedRootSubsetStatements`, with the ambient-root and reduced-test
   distinctions and source correction I5 above. Eight of its nine targets
   are proved (Tasks 6508–6513, 6515 and 6516). The ninth, Borel–Tits
   3.22(b), is false (I5), and its Task 6514 is retired. The remaining V.4.2
   obligation is the pairing of the eight proofs into
   `RenardClosedRootSubsetStatements`, owned by exact proof Task 7357.
   The maximal anisotropic subtorus and almost
   direct product (V.2.2 Remark 2), formerly listed here, are proved by
   `torusAnisotropicPart` (Task 6398). The split-component assertions of
   V.3.1 and the first sentence of V.3.2 are proved by Tasks 6452 and
   6454–6457, and their conjunction by `parabolicSplitComponents`
   (Task 6866).
7. V.3.24: finite generation after transport to the actual split-central
   nonnegative uniformizer quotient, and independent acceptance and
   publication of the strict-face partition with actual standard Levi split
   components.
   The integral and actual quotient constructions, integral strict-face
   laws, four comparison statements, finite-generation statement, actual-piece
   definition and actual partition statement are now public. Tasks 6390,
   6391 and 6429 have independently accepted and published exact proofs of
   the integral central-image equality, group quotient comparison and
   integral finite generation. Tasks 6472 and 6505 also have independently
   accepted and published exact strict-image and nonnegative-comparison
   proofs, verified above. Task 6605 has staged candidate
   `490ed375-a14a-4fe1-b24d-3c49a7e28a84`; both its comparison prerequisites
   are published. The partition awaits independent acceptance and
   publication. The general freeness assertion is false (I2).

8. V.3.15/V.3.21 topology on the actual standard-Levi split component: the
   nonemptiness, openness, closedness and topological closure assertion
   `LeviChamberTopologyStatement` is proved by the public
   `leviChamberTopology`. Exact proof Task 7234
   (`fdde72e2-596e-4f2a-b5bd-cc0ee54d7b39`) supplied independently accepted
   and published candidate `a6b1d812-cffd-4ded-baa9-dad583091837`.
   This focused gap is closed. The distinct source issue (V.3.21.1) and
   actual lattice-partition obligations remain as recorded above.

## Proof tasks of Worker 1222's Chapter V statements

`Langlands.BruhatTits.Cartan.RenardLeviCones.LeviChamberTopologyStatement`
has exact proof Task 7234 (`fdde72e2-596e-4f2a-b5bd-cc0ee54d7b39`). Its
candidate `a6b1d812-cffd-4ded-baa9-dad583091837` is independently accepted
and published as `leviChamberTopology`, with the exact public pair and
publication receipt verified above.

The three public Levi split-component recall statements have exact proof
Tasks 6918–6920, and their conjunction has assembly Task 6921, as listed in
the focused ownership table above. Tasks 6918–6920 are complete:
`leviSplitComponentCentralizer`, `leviSplitComponentNormalizer` and
`leviParabolicFinite` are independently accepted and published, as recorded
by the eighth Worker 4 pass. Task 6921 remains open.

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
conjunction is proved by `relativeRealCorootLinearAlgebra`, from its exact proof Task 6830
(`8a9c5345-ee7d-44ea-85d4-a16abf746ebb`). The five component statements of Worker 4's
parabolic split-component unit (V.3.1–V.3.2) are proved by Tasks 6452 and 6454–6457;
their conjunction is proved by `parabolicSplitComponents`, from its exact proof Task 6866
(`e5eb891b-fc5e-4885-8241-647a8b70812f`). The two statements of Worker 4's chamber unit
(V.3.14–V.3.16) are proved by Tasks 6450 and 6451, and their conjunction by
`parabolicChamber` (Task 7268). The four statements of Worker 4's V.3.20 unit have exact
proof Tasks 7645–7648, still open. Eight statements of Worker 4's closed-root-subset unit
(V.4.2) are proved; their pairing into `RenardClosedRootSubsetStatements` is exact proof
Task 7357, and the ninth statement is false (I5). For V.3.24, exact proof
Tasks 6390, 6391 and 6429 are complete: `simpleRootSplitCentralImage`,
`CocharacterUniformizer.quotientComparison` and
`cocharacterConeFiniteGeneration` are independently accepted and published,
with the proof receipts and exact public pairs verified above.
Task 6398, the exact proof task for the public anisotropic-part statement, is
complete: its theorem `torusAnisotropicPart` is published. Tasks 6472 and
6505 are also complete: published proofs
`b681ec57-8c14-4416-8b9e-8730b5833ac2` and
`a0f109d3-949f-45e4-ac97-48c63092e77c` prove the exact strict-image and
nonnegative-comparison statements by `CocharacterUniformizer.standardLeviStrictImage`
and `CocharacterUniformizer.coneQuotientComparison`. Their unchanged target
pairs, proof pairs, machine receipts and independent reviews are verified
above. Task 6605 (`133b03c2-0411-438d-b273-36ea92402a88`) owns the public
actual strict-piece partition. Its candidate
`490ed375-a14a-4fe1-b24d-3c49a7e28a84` is staged pending independent
acceptance and publication, with both comparison prerequisites now published.
Transported finite generation and source issue I2 remain separate.
