# Renard 2026, Chapter V: item-by-item coverage ledger

This note is the Chapter V part of the item ledger of the whole book
([coverage.md](coverage.md)), in the format of the
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
strict faces, actual strict-image statement and closed-root-subset module.
A focused 14 November update of V.3.24 uses Library
`c0debd6f4dd02fdd68d70811cf610906b945a962`: the nonnegative comparison,
actual strict-piece definition and actual partition statement are now in the Library;
the refreshes below record the proofs of the two new statements.
The 14 November V.3.24 proof-status refresh checks Library
`2309f61083ef231a3ef371f18ab1eff2ae8de56d`: the integral central-image equality,
common-uniformizer group quotient comparison and integral cone finite generation
have exact proofs in the Library. A further
17 November refresh checks Library
`ab9053b1751d6b6557d044c38c04e4c8a67dfffc`: the actual standard-Levi strict-image
and nonnegative quotient comparisons also have exact proofs in the Library. A focused
18 November refresh checks Library
`18c5dd82d119bef479b69de264324b22fe6f8d36`: the actual strict partition also
has an exact proof in the Library. Finite generation
after transport to the actual quotient was then a separate statement; the
tenth update records its statement and proof.
The focused V.4.2 audit on 14 November 2026 checks Library
`1ddfc485145c40679728553e8c3a33a5450ce7f9`: all nine component statements,
listed below, had no proofs at that commit.
The seventh update below, on 17 November, supersedes that status:
eight of the nine are proved, and the ninth is false.
The ninth update, on 18 November, records the proof of the conjunction
of the eight, `RenardClosedRootSubsetStatements`. The tenth update, also
on 18 November, records the proofs of the four V.3.20 and two V.3.6/V.3.13
component statements, of the Levi recall conjunction and of transported V.3.24
finite generation, the statements of the two new conjunctions, and the
statement of the V.5.3 subalgebra Lemma without (P). The eleventh update,
on 19 November, records the proofs of the V.5.3 subalgebra Lemma under (P) and of
the V.3.20 and V.3.6/V.3.13 conjunctions. It also records the paper counterexample
to the Lemma without (P) with the status correction of its statement, and the
corrected statement of (V.3.21.1).
The 20 November follow-up records the proof of the corrected
(V.3.21.1) and the V.5.3 Markdown correction in the Library. Other rows
retain their earlier audit status.

The V.5.3 subalgebra row, issue I6 and gap 4 record the paper counterexample to
the printed Lemma, the
[ramified `U(1,1)` example](v53-subalgebra-finiteness-counterexample.md), and the
building-assignment hypothesis needed to apply it to the Lean statement.

A focused 16 November 2026 update checks Library
`b44618a4f02405d5be8c906f21cf7817e4eaafb9` for the V.3.21 topology row and
gap 8. The actual split-component topology statement and its exact proof
`leviChamberTopology` are in the Library.
The proof pair in the Library agrees with the version checked, and a separate
check compiles the statement and proof without errors or warnings.
The other rows retain their separately dated status.

On 14 November 2026 the
rows V.3.14–V.3.18, V.3.21–V.3.22, the V.5.5 row "proof of V.3.18" and gap 1 were updated
against Library `c0debd6f4dd02fdd68d70811cf610906b945a962`. The update cites
two modules. Both are in that Library, and the SHA256 digests
of their Lean and Markdown files equal those recorded when they were checked:

| Module |
| --- |
| [`Langlands.Representation.LanglandsClassification.ParabolicChamberStatements`](../../Langlands/Representation/LanglandsClassification/ParabolicChamberStatements.md) (statements, V.3.14–V.3.16) |
| [`Langlands.BruhatTits.Cartan.RenardLeviCones`](../../Langlands/BruhatTits/Cartan/RenardLeviCones.md) (definitions, V.3.21–V.3.22) |

The update also records two proofs present in that Library: V.3.17 by
`corootChamberUnipotentRoots` and V.3.18 by `langlandsCombinatorialDecomposition`.
Each theorem has exactly the type of the published statement,
and neither proof file contains `sorry`, `admit` or `axiom`.

A second update on the same day is a full status refresh of every row outside
V.3.24 whose proof status was open, against the same Library. Every statement name in
these rows was compared with the Library theorems whose type is exactly that statement.
For each new proof the theorem line was read; its file has no `sorry`, `admit` or
`axiom`. The update records these proofs:

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

The update also escapes the vertical bars inside table cells of the V.1, V.2.3, V.3.19,
V.3.20 and V.5.4 Lemma rows, which otherwise split those cells. It leaves unchanged
the V.3.24 rows, the V.3.24 evidence section, gap 7 and the V.3.24 sentences of the
section on proofs; other updates treat those passages.

A third update, also on 14 November, updates the V.3.6 arbitrary-Levi row, the two
V.3.7 rows, the two V.3.12 real-form rows and the V.3.13 corrected-decomposition row against
Library `4f4af6baed8c8e029e87c8303ea44c8f1d9f2f86`. It also updates the V.3.6–V.3.13
evidence section, gap 2 and the V.3.6 and real-coroot sentences of the section on proofs.
The five proofs below first appeared in the Library at
`ba00e0970dd9ba6222ccc056ca2ee7f06bcc8181`. Each theorem has exactly the type of its
statement, and its file has no `sorry`, `admit` or `axiom`. For the first four
proofs, the SHA256 digests of the Lean and Markdown files in the checked Library equal those
recorded when the proof was checked. For the fifth, see the paragraph after the table.

| Row | Statement | Theorem and proof module |
| --- | --- | --- |
| V.3.6, arbitrary Levi | `GS.RenardLeviCentralDecompositionStatement` | `renardLeviCentralDecomposition`, [RenardLeviCentralDecompositionProof](../../Langlands/GroupScheme/Rational/RenardLeviCentralDecompositionProof.md) |
| V.3.7, real statement and coroots | `GS.RelativeRealCorootStatement` | `relativeRealCoroot`, [RelativeRealCorootProof](../../Langlands/GroupScheme/Rational/RelativeRealCorootProof.md) |
| V.3.12, real basis | `GS.RelativeRealSimpleRootBasisStatement` | `relativeRealSimpleRootBasis`, [RelativeRealSimpleRootBasisProof](../../Langlands/GroupScheme/Rational/RelativeRealSimpleRootBasisProof.md) |
| V.3.12, coroot basis, fundamental weights and coweights | `GS.RelativeFundamentalWeightStatement` | `relativeFundamentalWeight`, [RelativeFundamentalWeightProof](../../Langlands/GroupScheme/Rational/RelativeFundamentalWeightProof.md) |
| V.3.13, corrected decompositions | `GS.StandardLeviRealDecompositionStatement` | `standardLeviRealDecomposition`, [StandardLeviRealDecompositionProof](../../Langlands/GroupScheme/Rational/StandardLeviRealDecompositionProof.md), helper [StandardLeviLinearAlgebra](../../Langlands/GroupScheme/Rational/StandardLeviLinearAlgebra.md) |

The Library files of the V.3.13 proof are not byte-identical to the version first checked. That
version's proof file has SHA256 `d39a6c9b…` and its Markdown `1c8a3cb5…`; the Library copies
have `decd82eb…` and `7ac72b55…`, and the helper pair differs as well. These copies are the
same in `ba00e097` and `4f4af6ba`. The difference is the removal of a duplicated lemma.
The helper lemma `positive_orthogonal_isCompl`
was removed from `StandardLeviLinearAlgebra`. The proof now imports
`Langlands.GroupScheme.Rational.LanglandsCharacterRestriction` and uses its published
`Langlands.LinearAlgebra.isCompl_orthogonal_of_positive`, followed by `IsCompl.symm`. The
paragraph of the helper Markdown and the sentence of the proof Markdown that described the
removed lemma were changed to match. The theorem line is unchanged, and the helper file
contains no `sorry`, `admit` or `axiom` either.

The four real-coroot statements have a conjunction, `GS.RelativeRealCorootLinearAlgebraStatement`,
which is the entry statement of the real-coroot module
`Langlands.GroupScheme.Rational.RelativeRealCorootStatements`.
It has no proof in the checked Library (it is proved now, as `relativeRealCorootLinearAlgebra`
in `Langlands/GroupScheme/Rational/RelativeRealCorootLinearAlgebraProof.lean`). A scratch file that imports the four
Library proof modules and pairs their theorems into the conjunction compiles against this
Library (0 errors, 0 warnings; axioms
`propext`, `Classical.choice`, `Quot.sound` only). The sixth update below records its
proof `relativeRealCorootLinearAlgebra`.

A fourth update, also on 14 November, checks against Library
`58ad0f796899b4aa457077d0146815c24758f739`. It updates the V.2.2 Remarks row and the
anisotropic-part paragraph after the V.2 table, the V.3.1 split-component row, the V.3.2 row,
gap 6 and two sentences of the section on proofs. The six proofs below first appeared in the
Library at `af5d652c2f2ff5b35b4ce4dbbf7cbec8bbf3e99e`. They
are unchanged in the checked Library. Each theorem has exactly the type of its statement, and
its file has no `sorry`, `admit` or `axiom`. For each proof, the SHA256 digests
of the Lean and Markdown files in the checked Library equal those recorded when it was checked.

| Row | Statement | Theorem and proof module |
| --- | --- | --- |
| V.2.2 Remarks, maximal anisotropic subtorus and almost direct product | `GS.TorusAnisotropicPartStatement` | `torusAnisotropicPart`, [TorusAnisotropicPartProof](../../Langlands/GroupScheme/Rational/TorusAnisotropicPartProof.md) |
| V.3.1, `Z(G, A)` is a Levi factor with split component `A` | `GS.ParabolicSplitComponentLeviStatement` | `parabolicSplitComponentLevi`, [ParabolicSplitComponentLeviProof](../../Langlands/GroupScheme/Rational/ParabolicSplitComponentLeviProof.md) |
| V.3.1, `A_M` is a split component of `P` | `GS.LeviSplitComponentRadicalStatement` | `leviSplitComponentRadical`, [LeviSplitComponentRadicalProof](../../Langlands/GroupScheme/Rational/LeviSplitComponentRadicalProof.md) |
| V.3.1, `N` transitive on split components | `GS.ParabolicSplitComponentConjugacyStatement` | `parabolicSplitComponentConjugacy`, [ParabolicSplitComponentConjugacyProof](../../Langlands/GroupScheme/Rational/ParabolicSplitComponentConjugacyProof.md) |
| V.3.1, Levi subgroups as centralizers of split tori | `GS.LeviCentralizerCharacterizationStatement` | `leviCentralizerCharacterization`, [LeviCentralizerCharacterizationProof](../../Langlands/GroupScheme/Rational/LeviCentralizerCharacterizationProof.md) |
| V.3.2, first sentence | `GS.MinimalParabolicSplitComponentStatement` | `minimalParabolicSplitComponent`, [MinimalParabolicSplitComponentProof](../../Langlands/GroupScheme/Rational/MinimalParabolicSplitComponentProof.md) |

The last five statements are the components of the published module
[ParabolicSplitComponentStatements](../../Langlands/GroupScheme/Rational/ParabolicSplitComponentStatements.md).
Their conjunction,
`GS.ParabolicSplitComponentStatements`, has no proof in the checked Library (it is proved now,
as `parabolicSplitComponents` in
`Langlands/GroupScheme/Rational/ParabolicSplitComponentStatementsProof.lean`). A
scratch file that imports the five Library proof modules and pairs their theorems into the
conjunction compiles against this Library (0 errors, 0 warnings; axioms `propext`,
`Classical.choice`, `Quot.sound` only). The sixth update below records its
proof `parabolicSplitComponents`. This update leaves unchanged the V.3.24 rows, the
V.3.24 evidence section, gap 7 and the V.3.24 sentences of the section on proofs, which
other updates treat.

A fifth update, also on 14 November, checks against Library
`320321b3cd4b5100d54cf785192677d59479e65f`. It updates the V.3.14, V.3.15 and V.3.16 rows
and gap 1. The proof below first appeared in the Library at
`7f5b5f04a855fc0b4671393213c87415a6ee2aaf`, and it is unchanged in the checked Library. Its
theorem has exactly the type `ParabolicChamberLinearAlgebraStatement.{u}`, and neither
the proof file nor its helper module
[ParabolicChamberBasis](../../Langlands/Representation/LanglandsClassification/ParabolicChamberBasis.md)
contains `sorry`, `admit` or `axiom`.
The SHA256 digests of the Lean and Markdown files of both modules in the checked Library equal
those recorded when the proof was checked.

| Rows | Statement | Theorem and proof module |
| --- | --- | --- |
| V.3.14–V.3.16, ambient model in `𝔞^*_∅` and `𝔞_∅` | `GS.ParabolicChamberLinearAlgebraStatement` | `parabolicChamberLinearAlgebra`, [ParabolicChamberLinearAlgebraProof](../../Langlands/Representation/LanglandsClassification/ParabolicChamberLinearAlgebraProof.md) |

The other statement `GS.ParabolicSplitComponentChamberStatement` and the
conjunction `GS.ParabolicChamberStatement` of the module `ParabolicChamberStatements`
have no proof in the checked Library (both are proved now, as `parabolicSplitComponentChamber`
and `parabolicChamber` in `Langlands/Representation/LanglandsClassification/`). This update leaves
unchanged the V.3.24 passages and the V.3.1 and V.3.5 rows on the Levi recall
statements. The seventh update below records the proofs of both.

A focused update, also on 14 November, checks the
[LeviSplitComponentRecallStatements](../../Langlands/GroupScheme/Rational/LeviSplitComponentRecallStatements.md)
against Library `be1ec61194b5b92447fe21556e835dcc30c124e2` and the original
V.3.1 and V.3.5.1, printed pp.109–111 / PDF pp.115–117. The three component
statements and their conjunction were unproved at that commit. The last column gives
the proof that the later updates record:

| Statement in `Langlands.GroupScheme` | Exact scope | Proof in the Library |
| --- | --- | --- |
| `LeviSplitComponentCentralizerStatement.{u}` | For an arbitrary rational Levi of a rational parabolic and its supplied split component, `Z_G(A_M) = M` as subgroup functors on every test scheme | `leviSplitComponentCentralizer` (eighth update) |
| `LeviSplitComponentNormalizerStatement.{u}` | `N_G(A_M) = N_G(M)` on rational points over `Spec k` | `leviSplitComponentNormalizer` (eighth update) |
| `LeviParabolicFiniteStatement.{u}` | A uniform bound on finite families of rational parabolics with pairwise distinct images and the same embedded rational Levi | `leviParabolicFinite` (eighth update) |
| `LeviSplitComponentRecallStatements.{u}` | The conjunction of the preceding three statements, assembled from their proofs after publication | `leviSplitComponentRecall` (tenth update) |

All four retain the published arbitrary-field universe `u`. Renard's
source field is nonarchimedean local, and the section recalls the results
from Borel–Tits [7] and Springer [42]. The centralizer equality concerns
all test schemes; the normalizer equality concerns rational points only.
The related maximal-Levi bound of two does not prove the arbitrary-Levi
finiteness target. The eighth update below records the proofs of
the first three statements, and the tenth records the proof of their
conjunction.

A sixth update, on 15 November, checks against Library
`72480b70c88adff84a438bd7029d64ee3977469c`. It records the proofs of the two conjunctions
that the third and fourth updates left open. It changes the evidence paragraph on the
real-coroot module, gaps 2 and 6 (only the sentence on the V.3.1–V.3.2 split-component
module), two sentences of the section on proofs, and the clause of the V.3.1
split-component row on the conjunction. That row's clause on the arbitrary-Levi centralizer is
unchanged. Both proofs first appeared in the Library at
`497ef49830025d23824f6b2e2b1d5d60b594f51e`, and they are unchanged in the checked Library.
The SHA256 digests of their Lean and Markdown files in the checked Library equal those
recorded when they were checked. Each theorem has exactly the type of its conjunction at universe `u`
and builds it from the component theorems listed in the third and fourth updates. Neither
proof file contains `sorry`, `admit` or `axiom`. A scratch file that
imports both proof modules compiles against the checked Library and reports only the
axioms `propext`, `Classical.choice` and `Quot.sound` for both theorems.

| Rows | Statement | Theorem and proof module |
| --- | --- | --- |
| V.3.7, V.3.12 and V.3.13, the real-coroot module | `GS.RelativeRealCorootLinearAlgebraStatement` | `relativeRealCorootLinearAlgebra`, [RelativeRealCorootLinearAlgebraProof](../../Langlands/GroupScheme/Rational/RelativeRealCorootLinearAlgebraProof.md) |
| V.3.1 and the first sentence of V.3.2, the split-component module | `GS.ParabolicSplitComponentStatements` | `parabolicSplitComponents`, [ParabolicSplitComponentStatementsProof](../../Langlands/GroupScheme/Rational/ParabolicSplitComponentStatementsProof.md) |

At this update the other statement `GS.ParabolicSplitComponentChamberStatement`
and the conjunction `GS.ParabolicChamberStatement` still have no proof in the checked
Library; nor do the nine V.4.2 closed-root-subset statements. This update
leaves unchanged the V.3.24 passages and the Levi recall rows and table.
The seventh update below records the proofs of the first two and of eight of the nine.

A seventh update, on 17 November, checks against Library
`89bac3684c44d30f371d4959c363e25649af5e8d`. It records the proofs of the V.3.14–V.3.15
split-component chamber statement, of the chamber conjunction and of eight of the nine
V.4.2 closed-root-subset statements. It also records that the ninth V.4.2 statement is
false. It updates the V.3.14, V.3.15 and two V.4.2 rows, the V.4.2 paragraphs
and table, issue I5, gaps 1 and 6, the V.4.2 sentence of the opening paragraph, the
last sentence of the V.3.24 evidence section, which concerns the modules, and one
paragraph of the section on proofs. It adds the status code F. Each
proof below is unchanged in the checked Library since it first appeared there.
Each theorem has exactly the type of its statement at universe `u`.
No Lean file of these proofs, as they stand in the checked Library, contains `sorry`,
`admit` or `axiom`. The only textual match is the English word "admit"
in a documentation comment of `Langlands/LinearAlgebra/RationalPositiveFunctional.lean`.

| Rows | Statement | Theorem and proof module | First appeared at Library commit |
| --- | --- | --- | --- |
| V.3.14–V.3.15, split-component comparisons | `GS.ParabolicSplitComponentChamberStatement` | `parabolicSplitComponentChamber`, [ParabolicSplitComponentChamberProof](../../Langlands/Representation/LanglandsClassification/ParabolicSplitComponentChamberProof.md), helpers [ParabolicSplitComponentTransport](../../Langlands/Representation/LanglandsClassification/ParabolicSplitComponentTransport.md) and [ParabolicSplitComponentCorootCones](../../Langlands/Representation/LanglandsClassification/ParabolicSplitComponentCorootCones.md) | `e4a9b4d0` |
| V.3.14–V.3.16, the chamber module | `GS.ParabolicChamberStatement` | `parabolicChamber`, [ParabolicChamberProof](../../Langlands/Representation/LanglandsClassification/ParabolicChamberProof.md) | `a98af0ff` |
| V.4.2, convexity by the cone hull | `GS.ConvexRootSubsetHullStatement` | `convexRootSubsetHull`, [ConvexRootSubsetHullProof](../../Langlands/GroupScheme/Rational/ConvexRootSubsetHullProof.md) | `c0c2e121` |
| V.4.2, unipotence by a positive cocharacter | `GS.UnipotentRootSubsetCocharacterStatement` | `unipotentRootSubsetCocharacter`, [UnipotentRootSubsetCocharacterProof](../../Langlands/GroupScheme/Rational/UnipotentRootSubsetCocharacterProof.md) | `c0c2e121` |
| V.4.2, symmetric subsets and their reflections | `GS.SymmetricRootSubsetWeylStatement` | `symmetricRootSubsetWeyl`, [SymmetricRootSubsetWeylProof](../../Langlands/GroupScheme/Rational/SymmetricRootSubsetWeylProof.md) | `c0c2e121` |
| V.4.2 Proposition ([7] 5.12–5.18), the standard root triple | `GS.StandardParabolicRootTripleStatement` | `standardParabolicRootTriple`, [StandardParabolicRootTripleProof](../../Langlands/GroupScheme/Rational/StandardParabolicRootTripleProof.md), helper [StandardRootClosure](../../Langlands/GroupScheme/Rational/StandardRootClosure.md) | `c0c2e121` |
| V.4.2, existence of `G(X)` and `U(X)` | `GS.RootSubsetGroupExistenceStatement` | `rootSubsetGroupExistence`, [RootSubsetGroupExistenceProof](../../Langlands/GroupScheme/Rational/RootSubsetGroupExistenceProof.md) | `c0c2e121` |
| V.4.2 Proposition ([7] 5.12–5.18), the groups of the standard triple | `GS.StandardParabolicRootSubsetGroupStatement` | `standardParabolicRootSubsetGroup`, [StandardParabolicRootSubsetGroupProof](../../Langlands/GroupScheme/Rational/StandardParabolicRootSubsetGroupProof.md) | `c0c2e121` |
| V.4.2 (i), convex intersections | `GS.ConvexRootSubsetGroupIntersectionStatement` | `convexRootSubsetGroupIntersection`, [ConvexRootSubsetGroupIntersectionProof](../../Langlands/GroupScheme/Rational/ConvexRootSubsetGroupIntersectionProof.md) | `c9fdbede` |
| V.4.2 (ii), corrected ([7] 3.22(c)) | `GS.UnipotentRootSubsetGroupIntersectionStatement` | `unipotentRootSubsetGroupIntersection`, [UnipotentRootSubsetGroupIntersectionProof](../../Langlands/GroupScheme/Rational/UnipotentRootSubsetGroupIntersectionProof.md) | `c0c2e121` |

The first-publication commits are `e4a9b4d0164a5e0a9828dcaec5fa1cb7837ff8c6`,
`a98af0ff45faf7905209f65d641389deee5d8392`, `c0c2e1210454ae2a1888a2989e3de794c1336819`
and `c9fdbede045511865f0ea27259a1e1a35f442905`. For the proofs of the chamber conjunction
and of the V.4.2 convexity, symmetric-subset, existence, standard-triple-group, convex-intersection
and unipotent-intersection statements, the SHA256 digests of every Lean and Markdown file in
the checked Library equal those recorded when the proof was checked; the convex-intersection
proof has 40 files. For the
other three proofs a duplicated helper lemma was removed when they entered the Library, and the Library files
differ from the versions first checked as follows. The theorem lines are unchanged.

- The unipotence and standard-triple proofs: each first version proved the inclusion
  `IsRelativeRootAmbient.subset_relativeRoots`, in `UnipotentRootSubsetCocharacterProof`
  and in the helper `StandardRootClosure` respectively. In the Library both files import
  [RootSubsetAmbient](../../Langlands/GroupScheme/Rational/RootSubsetAmbient.md), which
  proves that lemma once, and their Markdown links to it.
- The split-component chamber proof: the helper lemma `restrictedCorootChamber_eq_image` was removed from
  `ParabolicSplitComponentTransport`. The proof now uses the published
  `restrictedCorootChamber_eq_image_openFace` of
  [SimpleCorootFaces](../../Langlands/Representation/LanglandsClassification/SimpleCorootFaces.md).
  The Lean and Markdown files of `ParabolicSplitComponentTransport` and the Lean file of
  `ParabolicSplitComponentChamberProof` differ from the first version. They are the same at
  `e4a9b4d0` and in the checked Library.

The ninth V.4.2 statement, `GS.ClosedRootSubsetGroupIntersectionStatement`, is the
Borel–Tits 3.22(b) assertion `G(S) ∩ G(X) = G(S ∩ X)` for closed `S` and `X` whose
intersection is convex. It is false. The published erratum note
[Borel–Tits 3.22(b): a split D4 obstruction](../errata/borel-tits-1965-closed-root-intersection.md)
(with two independent checks) gives a paper counterexample
in split `SO₈`: two closed symmetric subsets of type `A₁⁴` with empty, hence convex,
intersection, and a complex point of both generated groups outside `G(∅) = T`. It is not a
Lean proof of the negation. The argument was checked again for this ledger. The Library
has no proof of this statement and none is sought; the nine-part conjunction
`GS.ClosedRootSubsetStatements` therefore cannot be proved. Renard's V.4.2(i) assumes both
subsets convex and needs only `ConvexRootSubsetGroupIntersectionStatement`, proved above.

The V.4.2 conjunction for this ledger is now
`GS.RenardClosedRootSubsetStatements`, the conjunction of the other eight statements, in
the module
[RenardClosedRootSubsetStatements](../../Langlands/GroupScheme/Rational/RenardClosedRootSubsetStatements.md)
(first appeared in the Library at `c9fdbede`). Its Lean and Markdown
files in the checked Library equal those recorded when it was checked. It has no proof in the
checked Library. A scratch file that imports the eight Library proof modules and
pairs their theorems into the conjunction compiles against Library
`276bcb8d72bd1a6ea95eac204206680403da83f7`, whose Lean files are those of the checked
Library (0 errors, 0 warnings; axioms
`propext`, `Classical.choice`, `Quot.sound` only). The ninth update below records its
proof `renardClosedRootSubsets`. The Markdown of
`ClosedRootSubsetStatements` in the Library at that commit predates the erratum and still describes 3.22(b) as a true
source of V.4.2(i). This ledger and the erratum note supersede those passages; the eighth
update below records the correction of that Markdown. This update leaves unchanged the V.3.24 rows
and the rest of the V.3.24 evidence section, the Levi recall rows and table, and
the V.3.21 row and gap 8.

An eighth update, on 17 November, checks against Library
`18790533e39c3ee1982619a07a6594528ad156dd`. It records three proofs of the Levi
recall statements, the V.3.20 definition and statement modules,
and the correction of the `ClosedRootSubsetStatements` Markdown. It updates the
first and third V.3.1 rows, the V.3.5 row, the last V.3.20 row, one sentence of issue I5,
gaps 5 and 6, and two paragraphs of the section on proofs. It also adds one sentence after the Levi recall
table. The SHA256 digests of the Lean and Markdown files of each proof below in the
checked Library equal those recorded when it was checked. Each theorem has exactly the type of its
statement at universe `u`. A separate check of each proof module against the checked
Library reports 0 errors, 0 warnings and only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

| Rows | Statement | Theorem and proof module | First appeared at Library commit |
| --- | --- | --- | --- |
| V.3.1 and V.3.5, `Z_G(A_M) = M` | `GS.LeviSplitComponentCentralizerStatement` | `leviSplitComponentCentralizer`, [LeviSplitComponentCentralizerProof](../../Langlands/GroupScheme/Rational/LeviSplitComponentCentralizerProof.md) | `371b9c35` |
| V.3.1, `P(M)` is finite | `GS.LeviParabolicFiniteStatement` | `leviParabolicFinite`, [LeviParabolicFiniteProof](../../Langlands/GroupScheme/Rational/LeviParabolicFiniteProof.md) | `371b9c35` |
| V.3.5, `N_G(A_M) = N_G(M)` on rational points | `GS.LeviSplitComponentNormalizerStatement` | `leviSplitComponentNormalizer`, [LeviSplitComponentNormalizerProof](../../Langlands/GroupScheme/Rational/LeviSplitComponentNormalizerProof.md) | `42c69680` |

The first-publication commits are `371b9c350ae74d42665a9e7e0ec32e4c66f56619` and
`42c696807fd25d6ea96d001a596d7bba7b4b52b9`. The finiteness proof bounds every family by
`2^|Φ(T₀)|`, for the relative roots of one maximal split torus `T₀` chosen from `(p, l)`
before the family is given; it does not compute the cardinality of `P(M)`. The normalizer
proof identifies the rational-point carriers of the two normalizers, as the statement
requires. The conjunction `GS.LeviSplitComponentRecallStatements` has no proof in the
checked Library. The tenth update below records its proof.

The two V.3.20 modules are in the Library, and their Lean and Markdown files in the checked
Library equal those recorded when they were checked.

| Module | First appeared at Library commit |
| --- | --- |
| [`Langlands.Representation.Plancherel.RationalUnramifiedComplexChart`](../../Langlands/Representation/Plancherel/RationalUnramifiedComplexChart.md) (definitions) | `f24f97443f21ff7e59b1cf3b509602157dae54c2` |
| [`Langlands.Representation.Plancherel.RationalUnramifiedComplexTorusStatement`](../../Langlands/Representation/Plancherel/RationalUnramifiedComplexTorusStatement.md) (statements) | `42c696807fd25d6ea96d001a596d7bba7b4b52b9` |

For each integer basis of `Λ(G)`, the definition module gives `X(G)` the complex charted space
with the single chart of the basis coordinates, an open embedding into `ℂ^r` with image
`(ℂ^×)^r`. It also defines the inclusion of `Im X(G)` into `X(G)`. The statement module has
four components and their conjunction `PL.RationalUnramifiedComplexTorusStatement`. The
components state that the chart of every basis is a local biholomorphism, that `X(G)` is a
complex Lie group, and that the exponential `𝔞*_ℂ → X(G)` is a local biholomorphism. The
fourth states that `Im X(G)` is an embedded real Lie subgroup, onto which the imaginary
exponential is a local diffeomorphism. None of them is proved in the checked Library.
The tenth update below records the four proofs and the statement of their conjunction.

The Markdown-only correction of the `ClosedRootSubsetStatements`
first appeared in the Library at
`2613dbbf784309977c42d9252b78c1e1cd40be63`. Its Lean file is unchanged, and its Markdown in
the checked Library equals the corrected version. That Markdown now records 3.22(b) as false and
derives V.4.2(i) from the convex intersection statement. The correction planned in the
seventh update is therefore done. At this update the V.4.2 conjunction of the eight had no
proof. This update leaves unchanged the V.3.24 rows and passages, including the
partition proof recorded there, the V.3.21 row, the V.5.3 subalgebra row, and
gaps 2, 4, 7 and 8.

A ninth update, on 18 November, checks against Library
`d26f6985162bcc4b604d91d2fd1c35df9c7ce13c`. It records two statement modules
and the proof of the V.4.2 conjunction. It updates
the V.3.6 arbitrary-Levi row, the first and third V.3.13 rows, the first V.4.2 row, the
V.5.3 subalgebra row, and gaps 2, 4 and 6. It adds a paragraph to the evidence section on
V.3.6–V.3.13, and updates the V.4.2 sentences of the opening paragraph and of the V.3.24
evidence section, two paragraphs after the V.4 table, and one paragraph of the section
on proofs. The SHA256
digests of the Lean and Markdown files of both modules in the checked Library equal those
recorded when they were checked.

| Module | First appeared at Library commit |
| --- | --- |
| [`Langlands.Representation.Hecke.IwahoriHeckeSubalgebraFinitenessStatement`](../../Langlands/Representation/Hecke/IwahoriHeckeSubalgebraFinitenessStatement.md) (V.5.3 statement) | `18c5dd82d119bef479b69de264324b22fe6f8d36` |
| [`Langlands.GroupScheme.Rational.LeviCentralCompatibilityStatements`](../../Langlands/GroupScheme/Rational/LeviCentralCompatibilityStatements.md) (V.3.6 and V.3.13 statements) | `d26f6985162bcc4b604d91d2fd1c35df9c7ce13c` |

The V.5.3 module states the finiteness Lemma for the generated subalgebra under one added
hypothesis (P); see the V.5.3 subalgebra row and gap 4. It had no proof at this update. The
eleventh update below records its proof.

The V.3.6/V.3.13 module states two geometric inputs of the published linear algebra, over an
arbitrary field and for every choice of split components.
`GS.LeviSplitComponentInclusionStatement` says that for rational Levi factors `M ⊆ L` of
two parabolic subgroups, `A_L` factors through `A_M`. With `L = G` this gives the compatible
diagram that `GS.RenardLeviCentralDecompositionStatement` assumes, for every rational Levi
factor. `GS.StandardLeviCharacterAnnihilatorStatement` says that for a standard Levi `L`
of `J ⊆ Δ_∅`, the image of `ℝ ⊗ X*(L)` under restriction to the maximal split torus is the
annihilator of the coroots of `J`. Their conjunction is
`GS.LeviCentralCompatibilityStatements`. None of the three is proved in the checked
Library. The tenth update below records the proofs of the two components and the
statement of their conjunction.

The Library now has an exact proof of `GS.RenardClosedRootSubsetStatements`, the V.4.2 conjunction of
the eight true closed-root-subset statements.

| Row | Statement | Theorem and proof module | First appeared at Library commit |
| --- | --- | --- | --- |
| V.4.2, the eight true components | `GS.RenardClosedRootSubsetStatements` | `renardClosedRootSubsets`, [RenardClosedRootSubsetProof](../../Langlands/GroupScheme/Rational/RenardClosedRootSubsetProof.md) | `d26f6985` |

The SHA256 digests of the Lean and Markdown
files in the checked Library equal those recorded when the proof was checked. The theorem has exactly
the type `RenardClosedRootSubsetStatements.{u}`; it pairs the eight component
proofs listed in the seventh update's table. A separate check of the proof module against
the checked Library reports 0 errors, 0 warnings and only the axioms `propext`,
`Classical.choice` and `Quot.sound`.
The nine-part `GS.ClosedRootSubsetStatements` still cannot be proved, since its ninth
component is false (I5).

The published `langlandsCharacterRestriction` (module
[LanglandsCharacterRestriction](../../Langlands/GroupScheme/Rational/LanglandsCharacterRestriction.md))
was not cited in the V.3.13 rows before this update. For a standard Levi with a compatible
parabolic presentation and a Weyl-invariant inner product, it proves that restriction to
the split component maps the coroot annihilator bijectively onto `ℝ ⊗ X*(A_M)`. It
compares the annihilator with the characters of the split component, not with those of the
Levi itself. The new character-annihilator statement makes that second comparison.

In the checked Library the Levi recall conjunction and the four V.3.20 statements have no
proof. Apart from the sentence on the modules, this update leaves unchanged the V.3.24 rows and
passages, the V.3.21 row, and gaps 5, 7 and 8. The tenth update below
records the proofs of these statements.

A tenth update, on 18 November, checks against Library
`f050c0b1b525624bc32c1e7c25a8d2841bb2d4e0`. It records the statement of the
V.5.3 subalgebra Lemma without (P), the proof of the Levi
recall conjunction, and the statement of transported V.3.24
finite generation with its proof. It also records the proofs of the four
V.3.20 statements and of the two V.3.6/V.3.13 statements, and the statements of
their two conjunctions. The update changes the opening paragraph,
the Levi recall table and the paragraph after it, the V.3.5, V.3.6, V.3.20 and
V.5.3 subalgebra rows and the first and third V.3.13 rows, and adds a V.3.24 row on
finite generation. It updates the last paragraph of the V.3.6–V.3.13 evidence section,
two sentences of the V.3.24 evidence section, gaps 2, 4, 5, 6 and 7, and four paragraphs
of the section on proofs. It also adds one closing sentence to each of four paragraphs
of the eighth and ninth updates. The SHA256 digests of the Lean and Markdown files of both
statement modules below in the checked Library equal those recorded when they were checked.

| Module | First appeared at Library commit |
| --- | --- |
| [`Langlands.Representation.Hecke.RenardIwahoriHeckeSubalgebraFinitenessStatement`](../../Langlands/Representation/Hecke/RenardIwahoriHeckeSubalgebraFinitenessStatement.md) (V.5.3 statement without (P)) | `b86269dd36757fdbea2e51976499d645ca61a625` |
| [`Langlands.Geometry.Building.CocharacterUniformizerConeFiniteGenerationStatement`](../../Langlands/Geometry/Building/CocharacterUniformizerConeFiniteGenerationStatement.md) (V.3.24 finite generation) | `d26f6985162bcc4b604d91d2fd1c35df9c7ce13c` |

`Langlands.Hecke.RenardIwahoriHeckeSubalgebraFinitenessStatement` keeps the data of
`IwahoriHeckeDecompositionStatement` but requires the transversal `F_∅` to be
chamber-compatible (V.3.23, `C̃_∅^+ = C_∅^+ F_∅`), and adds no other hypothesis. With `A`
and `M` the unital subalgebras generated by the `a_z`, `z ∈ C_∅^+`, and by the `a_{zf}`,
`z ∈ C_∅^+`, `f ∈ F_∅`, it asserts `A ≤ M` and `M = ∑ₖ A D_k` for finitely many
`D_k ∈ M`. Its truth was not known at this update; see the V.5.3 subalgebra row and gap 4.
The eleventh update below records a counterexample to it.

`GS.CocharacterUniformizer.ConeQuotientFiniteGenerationStatement` asserts, for the data of
the published `ConeQuotientComparisonStatement` over a nonarchimedean local field, that
the actual nonnegative uniformizer quotient `CAplusQuotient F T (simpleRelativeRoots i ν) A f`
is a finitely generated submonoid. This is the finite generation after transport that
earlier passages of this note listed as a separate statement.

The following proofs are in the Library.

| Rows | Statement | Theorem and proof module | First appeared at Library commit |
| --- | --- | --- | --- |
| V.3.1 and V.3.5, the Levi recall conjunction | `GS.LeviSplitComponentRecallStatements` | `leviSplitComponentRecall`, [LeviSplitComponentRecallStatementsProof](../../Langlands/GroupScheme/Rational/LeviSplitComponentRecallStatementsProof.md) | `db14afe3` |
| V.3.24, finite generation of the actual quotient | `GS.CocharacterUniformizer.ConeQuotientFiniteGenerationStatement` | `CocharacterUniformizer.coneQuotientFiniteGeneration`, [CocharacterUniformizerConeFiniteGenerationProof](../../Langlands/Geometry/Building/CocharacterUniformizerConeFiniteGenerationProof.md) | `bb9e0861` |
| V.3.20, every basis chart is a local biholomorphism | `PL.RationalUnramifiedBasisChartIndependenceStatement` | `rationalUnramifiedBasisChartIndependence`, [RationalUnramifiedBasisChartIndependenceProof](../../Langlands/Representation/Plancherel/RationalUnramifiedBasisChartIndependenceProof.md); also `rationalUnramifiedBasisChartIndependence_of_basisTransition`, [RationalUnramifiedBasisChartTransitionProof](../../Langlands/Representation/Plancherel/RationalUnramifiedBasisChartTransitionProof.md) | `bb9e0861` |
| V.3.20, `X(M)` is a complex Lie group | `PL.RationalUnramifiedComplexLieGroupStatement` | `rationalUnramifiedComplexLieGroup`, [RationalUnramifiedComplexLieGroupProof](../../Langlands/Representation/Plancherel/RationalUnramifiedComplexLieGroupProof.md) | `bb9e0861` |
| V.3.20, the exponential is a local biholomorphism | `PL.RationalUnramifiedComplexExponentialStatement` | `rationalUnramifiedComplexExponential`, [RationalUnramifiedComplexExponentialProof](../../Langlands/Representation/Plancherel/RationalUnramifiedComplexExponentialProof.md) | `bb9e0861` |
| V.3.20, `Im X(M)` is an embedded real Lie subgroup | `PL.RationalUnitaryUnramifiedSubmanifoldStatement` | `rationalUnitaryUnramifiedSubmanifold`, [RationalUnitaryUnramifiedSubmanifoldProof](../../Langlands/Representation/Plancherel/RationalUnitaryUnramifiedSubmanifoldProof.md), helper [RationalUnitaryUnramifiedBasis](../../Langlands/Representation/Plancherel/RationalUnitaryUnramifiedBasis.md) | `bb9e0861` |
| V.3.6 and V.3.13, `A_L ⊂ A_M` | `GS.LeviSplitComponentInclusionStatement` | `leviSplitComponentInclusion`, [LeviSplitComponentInclusionProof](../../Langlands/GroupScheme/Rational/LeviSplitComponentInclusionProof.md) | `bb9e0861` |
| V.3.13, the real characters of a standard Levi | `GS.StandardLeviCharacterAnnihilatorStatement` | `standardLeviCharacterAnnihilator`, [StandardLeviCharacterAnnihilatorProof](../../Langlands/GroupScheme/Rational/StandardLeviCharacterAnnihilatorProof.md) | `bb9e0861` |

The first-publication commits are `db14afe3373dd1e402e436b7f53a35a278f3ee90`
and `bb9e086196d00484fd52204977452d922bf3c660` (the other seven proofs). Each theorem has
exactly the type of its statement at universe `u`. For every proof except those of the basis-chart
statement, the SHA256
digests of the Lean and Markdown files in the checked Library equal
those recorded when the proof was checked. The basis-chart statement has two proofs, and
both are in the Library. The first is
`RationalUnramifiedBasisChartIndependenceProof`, to which one import of
the other module and one Markdown link to it were added when it entered the Library. The second is
`RationalUnramifiedBasisChartTransitionProof`, with its theorem renamed
`rationalUnramifiedBasisChartIndependence_of_basisTransition`; the name is the only
difference from the version first checked, in both the Lean and the Markdown file. The finite-generation
proof applies the published `cocharacterConeFiniteGeneration` to the finite set of simple
relative roots and transports the result through the equivalence of the published
`coneQuotientComparison`. Separate checks of the Levi recall and finite-generation proof modules and of
both basis-chart modules against the checked Library report 0 errors, 0 warnings and only the
axioms `propext`, `Classical.choice` and `Quot.sound`.
The pairing checks below give the same axioms for the other five theorems.

The conjunctions `PL.RationalUnramifiedComplexTorusStatement` and
`GS.LeviCentralCompatibilityStatements` have no proof in the checked Library (both are proved
now, as `rationalUnramifiedComplexTorus` in
`Langlands/Representation/Plancherel/RationalUnramifiedComplexTorusProof.lean` and
`leviCentralCompatibility` in `Langlands/GroupScheme/Rational/LeviCentralCompatibilityProof.lean`). A file that
pairs the two
V.3.6/V.3.13 theorems compiles against the checked Library with 0 errors and 0 warnings,
and its theorem uses only those three axioms. The eleventh
update below records the proofs of both conjunctions.

The four V.3.20 proof modules cannot be imported together as they stand at this commit. The two
basis-chart modules and the helper `RationalUnitaryUnramifiedBasis` of the submanifold proof each declare an
anonymous `local instance` for the topology on `G(F)` in namespace `Langlands.Plancherel`.
Lean names the instances in `RationalUnramifiedBasisChartTransitionProof` and in the
helper `Langlands.Plancherel.instTopologicalSpaceRationalPoints`, so a module importing
both fails. The attribute is local, but the declaration name is
global. Other Library modules avoid this by naming such instances explicitly. The proof of
the conjunction needs one change to existing files: an explicit unique name for the helper's instance,
with no change to any statement, definition or proof. With that rename, a file
that pairs the four theorems compiles against the checked Library with 0 errors and
0 warnings, and its theorem uses only the three axioms above.

This update leaves unchanged the V.3.21 row, issue I1 and gap 8.
The eleventh update below records the proofs of the two conjunctions, a counterexample to the
V.5.3 Lemma without (P), and the corrected V.3.21.1 statement.

An eleventh update, on 19 November, checks against Library
`24390f9f6d7a3b7df9e5b9dd4d6e79e178c8ac85`. It records the proofs of the V.5.3 subalgebra
Lemma under (P) and of the V.3.20 and V.3.6/V.3.13 conjunctions, the paper counterexample to the
V.5.3 subalgebra Lemma without (P), and the status
correction of the Markdown of that statement. It also records the corrected
statement of (V.3.21.1). The update changes the opening paragraph, both V.3.6 rows,
the V.3.20, V.3.21.1 and V.5.3 subalgebra rows and the first and third V.3.13 rows, the
last paragraph of the V.3.6–V.3.13 evidence section, issue I1, gaps 2, 4 and 5, and one
paragraph of the section on proofs. The minimal-Levi V.3.6 row corrects an earlier
wording that called `M_∅` a maximal split torus: following V.3.8, `M_∅ = Z_G(T)` is the
centralizer of the maximal split torus `T = A_∅`, which is its split component, and the
statement's real spaces are those of `T`. It adds issue I6, a paragraph of the section on proofs on the
corrected (V.3.21.1), and one closing sentence to one paragraph of the ninth update and to each of
three paragraphs of the tenth update. The SHA256 digests of the Lean and Markdown files of the
statement module below in the checked Library equal those recorded when it was checked.

| Module | First appeared at Library commit |
| --- | --- |
| [`Langlands.BruhatTits.Cartan.RenardLeviConePartitionStatement`](../../Langlands/BruhatTits/Cartan/RenardLeviConePartitionStatement.md) (V.3.21.1 modulo `⁰A_M`) | `bb9e086196d00484fd52204977452d922bf3c660` |

`Langlands.BruhatTits.Cartan.RenardLeviCones.LeviConePartitionStatement` is the corrected
form of (V.3.21.1) (issue I1). Over a nonarchimedean local field, for every standard
index `J ⊆ Δ_∅`, every actual split component `A` of the standard Levi `M` of index `J`
and every compatible map `A → T`, it partitions the image of `A^+_M` in
`A_M(F)/⁰A_M`. Here `⁰A_M` is the common kernel of the norms of the rational characters.
The piece of index `K`, for `J ⊆ K ⊆ Δ_∅`, consists of the classes of points of the
strict cones `A^{++}_L` of actual split components of the standard Levi `L` of index
`K`, mapped into `A` by compatible maps. Each piece lies in the image of `A^+_M`, and
each class of that image lies in exactly one piece. Its proof was not in the Library at that
commit; see the 20 November follow-up.

A paper counterexample to the V.5.3
subalgebra Lemma without (P) is the note
[Renard V.5.3: the generated subalgebra `M` need not be a finitely generated `A`-module](v53-subalgebra-finiteness-counterexample.md)
(first appeared in the Library at
`7e12a30cd33f6905b3d1d7477b73eaff3c7342b3`). Every step was checked again on paper. The
group is the quasi-split unitary group `U(1,1)` of the ramified extension
`ℚ₂(ζ₈)/ℚ₂(√2)`, and the transversal `{1, f}` is chamber-compatible. The subgroup `K`,
built from a proper order of `𝒪_F`, is normal in the special maximal compact subgroup
and satisfies the hypotheses that the Lean statement places on `K`. Then `M` lies in
no finite left `A`-span `∑ₖ A D_k` (issue I6). The Lean statement
quantifies over the Kaletha–Prasad building assignments available for the group, and
the Library does not prove that one exists for this `U(1,1)`. The counterexample
therefore refutes the Lean proposition if such an assignment exists; otherwise the
proposition is vacuous for this group. No Lean proof of the negation exists. The
example does not satisfy (P), since `f` violates its contraction clause, so it does not
affect the conditional statement, now proved.

The status correction of
`Langlands.Hecke.RenardIwahoriHeckeSubalgebraFinitenessStatement` keeps the Lean file
unchanged (SHA256 `725773ec…`) and replaces the Markdown. The new Markdown records that
the assertion is false in general by this paper counterexample, with the scope just
described. At the
checked commit the correction was not yet in the Library. See the 20 November follow-up.

The following proofs are in the Library.

| Rows | Statement | Theorem and proof module | First appeared at Library commit |
| --- | --- | --- | --- |
| V.5.3, the subalgebra Lemma under (P) | `Langlands.Hecke.IwahoriHeckeSubalgebraFinitenessStatement` | `Langlands.Hecke.iwahoriHeckeSubalgebraFiniteness`, [IwahoriHeckeSubalgebraFinitenessProof](../../Langlands/Representation/Hecke/IwahoriHeckeSubalgebraFinitenessProof.md) | `5f5d3a91` |
| V.3.6 and V.3.13, the conjunction of `A_L ⊂ A_M` and the real characters of a standard Levi | `GS.LeviCentralCompatibilityStatements` | `leviCentralCompatibility`, [LeviCentralCompatibilityProof](../../Langlands/GroupScheme/Rational/LeviCentralCompatibilityProof.md) | `5f5d3a91` |
| V.3.20, the conjunction of the four analytic statements | `PL.RationalUnramifiedComplexTorusStatement` | `rationalUnramifiedComplexTorus`, [RationalUnramifiedComplexTorusProof](../../Langlands/Representation/Plancherel/RationalUnramifiedComplexTorusProof.md) | `5f5d3a91` |

The three proofs first appeared in the Library at
`5f5d3a914cd43b9dc1cd32c07887a973f561df96`. Each
theorem has exactly the type of its statement at universe `u`. For each proof,
the SHA256 digests of its files in the checked Library equal those recorded when it was checked. The
proof of the Lemma under (P) does not use the Noetherian step sketched in the statement's Markdown.
A Dickson-type argument (`exists_finite_stable_representatives`) writes every `a_t`, for
`t` in the monoid generated by `C̃_∅^+`, as a product `a_z D_k` with `z ∈ C_∅^+` and
`D_k` one of finitely many elements of `M`. The two pairing proofs combine the published
component proofs. The V.3.20 conjunction's proof also contains the rename described above: the helper
`RationalUnitaryUnramifiedBasis` now names its local topology instance
`instTopologicalSpaceRationalPoints_rationalUnitaryUnramifiedBasis`, and its Lean file
has no other change. Separate checks of the three proof modules against the checked Library report
0 errors, 0 warnings and only the axioms `propext`, `Classical.choice` and `Quot.sound`.

The 20 November 2026 follow-up checks Library
`7ae0d83b7cb2ad9aaca52ada487b3a5d3314323a`. Both changes below first entered the
Library at `95d37e11bd46972d484c6fc9e6b864ff7625cf9e`. Their Lean and Markdown
files match by SHA256 the versions that were checked.

- **V.3.21.1 modulo `⁰A_M`.** The [`leviConePartition` proof](../../Langlands/BruhatTits/Cartan/RenardLeviConePartitionProof.md)
  proves the exact
  `Langlands.BruhatTits.Cartan.RenardLeviCones.LeviConePartitionStatement.{u}`. It was
  checked by a Lake build against the exact target.
  The proof recovers the index `K` of a piece as the set of simple roots whose
  restricted character order on the quotient class is zero. All other simple-root
  orders are positive, so each piece lies in the nonnegative image. To show that
  every class occurs, the proof takes its uniformizer-section representative from
  a cocharacter of `A`. The image of the cocharacter in `T` selects `K` by the same
  zero set. The standard Levi inclusion and `leviSplitComponentInclusion` give the
  compatible map from the `K`-Levi's split component to `A`. The strict uniformizer
  image theorem and injectivity of `A(F) → T(F)` then give a strict point mapping to
  the section representative. This proves the partition on
  `A_M(F)/⁰A_M`, not the printed equality of point sets (I1).
- **V.5.3 without (P).** The
  [Markdown correction](../../Langlands/Representation/Hecke/RenardIwahoriHeckeSubalgebraFinitenessStatement.md)
  is in the Library. It changes no Lean code. The statement pair now records the paper
  counterexample and the unproved building-availability premise needed to refute
  the Lean proposition with this example. The proved statement
  under (P) and the proved module form are unaffected.

Chapter V is mostly a recall of algebraic-group and Bruhat–Tits theory with section-level
references. The published
[Chapter V structural-inputs ledger](chapter-v-structural-inputs.md) classifies
those recalled assertions (rows S01–S23) and the book's own deductions (rows D01–D08). This
note gives, for each paragraph, the Library declarations that now state or prove it.

## How the rows were checked

Chapter V was read in the text extraction and the displayed formulas with
overlines were checked in the rendered PDF. For each paragraph the Library Markdown files citing it were
listed, and their declarations were read. Proof status comes from a scan of the Library for
theorems whose type is exactly the statement (`proved by`).

Namespace abbreviations: `GS` = `Langlands.GroupScheme`, `PL` = `Langlands.Plancherel`,
`RC` = `Langlands.Plancherel.RenardCartan`, `RP` = `Langlands.Aubert.General.RepresentedParabolic`,
`RPF` = `Langlands.Aubert.General.RationalPointFamily`, `SC` = `Langlands.BruhatTits.SpecialCompact`.

Status codes, as in the Chapter VI ledger:

- **P**: proved; the named theorem has exactly the statement's type.
- **S**: statement published; its proof remains an obligation.
- **D**: definition or construction.
- **C**: covered by published statements that are stronger or equivalent, or derived from
  them; the row says which.
- **St**: a step of the proof of a stated result.
- **X**: expository, convention or attribution.
- **Rec**: an assertion recalled from the literature with a section-level reference (a row
  S.. of the structural-inputs ledger). The row says whether the Library states it.
- **G**: genuine gap.
- **F**: published statement shown false by a published paper counterexample, which the
  row cites; this is not a Lean proof of its negation. The row says what replaces it. (Code
  added by the seventh update.)

## V.1 Nonarchimedean local fields (103–104 / 109–110)

| Item | Lean | Status |
| --- | --- | --- |
| Normalized valuation, `𝔒_F`, `𝔓_F`, units, uniformizer decomposition, finite residue field, `\|x\|_F = q^{-v_F(x)}` | Mathlib's `IsNonarchimedeanLocalField` with `ValuativeRel`; `Langlands.FML.ord` and its laws, `LocalField.ResidueField`, `residueCardinality`, `residueNormalizedAbsoluteValue` ([ResidueNormalization](../../Langlands/LocalField/ResidueNormalization.md)); `PL.fieldNormUnits`, `PL.fieldOrderUnits` | Rec (ref. [21]); D |
| Additive Haar measure and `∫ f(ax) dx = \|a\|_F^{-1} ∫ f(x) dx` | `Langlands.HarmonicAnalysis.GeneralScalarHaarScalingStatement` and its specialization `Langlands.BaseChange.map_mul_residueAbsolute` for the actual residue-normalized absolute value | P for the pushforward equality. Bochner change of variables and the integral against a scaled measure give the formula for locally constant compactly supported functions |
| Topology of `F`, of `GL_n(F)` and the subgroups `K_n` | Mathlib local-field topology; `rationalPointTopology` and `rationalPoint_isTopologicalGroup`, `rationalPoint_locallyCompactSpace` | Rec; D |

## V.2 Reductive p-adic groups (104–109 / 110–115)

| Item | Lean | Status |
| --- | --- | --- |
| V.2.1 radicals, reductive groups, derived group, centre, maximal tori, conjugacy of maximal split tori | `IsConnectedReductive`, derived subgroup representability, `GS.MaximalSplitTorusConjugacyStatement` | Rec (S02–S03); conjugacy P: `maximalSplitTorusConjugacy` |
| V.2.1 split component and its uniqueness | `GS.IsSplitComponent`; `GS.SplitComponentStatement` (existence, uniqueness up to isomorphism over `G`) | D; P: `splitComponentStatement` |
| V.2.1 topology independent of the embedding; `G` unimodular | `rationalPointTopology`; unimodularity is V.5.4 below | Rec (S04); D |
| V.2.2 `X^*(G)`, triviality on `𝒟G`, finite-rank lattice, duals | `GroupScheme.rationalCharacters`; `GS.RationalCharacterLatticeStatement` | D; P: `rationalCharacterLattice` |
| V.2.2 Remarks (tori): cocharacter pairing `χ(φ(t)) = t^{⟨χ,φ⟩}`, coordinate algebra `F[X^*(T)]`, anisotropic and split tori, maximal split and anisotropic subtori, almost direct product | `latticePairing`, `rationalCharacterEval_cocharacterPoints`; `IsSplitTorus` (isomorphic to `splitTorus S I`); largest split subtorus (`Rational.TorusSplitPart`); `GS.TorusAnisotropicPartStatement` ([statement](../../Langlands/GroupScheme/Rational/TorusAnisotropicPartStatement.md)) | Rec (S05). D for the listed constructions; P for the named pairing laws and largest split subtorus; P for the maximal anisotropic subtorus and finite surjective multiplication `A × T_an → T`: `torusAnisotropicPart` |
| V.2.3 (V.2.3.1) `H_G`, `⁰G`, `Λ(G)`, exact sequence; `⁰G = ⋂ ker \|χ\|_F` | `PL.rationalCharacterValuation`, `PL.rationalCommonNormKernel`, `PL.rationalCharacterValuationImage`, `PL.rationalNormKernelQuotientEquiv`; `rationalCharacterValuation_ker` | D; P |
| V.2.3 Lemma: `\|χ\|_F` smooth, kernel contains every compact subgroup | `isLocallyConstant_rationalNormCharacter`, `compactSubgroup_le_rationalCommonNormKernel`; generic `PL.CommonNormKernelTopologyStatement` | P (`commonNormKernelTopology`) |
| V.2.3 Proposition: `⁰G` open, closed, normal; compact subgroups and `𝒟G` in `⁰G` | `isOpen_rationalCommonNormKernel`, `isClosed_rationalCommonNormKernel`, instance `rationalCommonNormKernel_normal`, `derivedPoints_le_rationalCommonNormKernel` | P |
| V.2.3 Proposition: `⁰G` unimodular | `PL.RationalNormKernelUnimodularStatement` | P: `rationalNormKernelUnimodular` |
| V.2.3 Definition: unramified characters | `PL.unramifiedCharacters` of the rational norm characters: continuous characters trivial on `⁰G`, which are all characters trivial on `⁰G` since `⁰G` is open | D |
| V.2.4 `X(G) ≃ Hom(Λ(G), ℂ^×)`, `Λ(G)` free of finite rank, `ℂ[Λ(G)]`, `ev_g`, `χ_un`, (V.2.4.1)–(V.2.4.2) | `PL.rationalImageCharacters`, [RationalImageLattice](../../Langlands/Representation/Plancherel/RationalImageLattice.md), [RationalUnramifiedCharacterCoordinates](../../Langlands/Representation/Plancherel/RationalUnramifiedCharacterCoordinates.md), [RationalUnramifiedCoordinateAlgebra](../../Langlands/Representation/Plancherel/RationalUnramifiedCoordinateAlgebra.md) (evaluation algebra ≅ `ℂ[Λ(G)]` ≅ Laurent polynomials), `universalUnramifiedRepresentation` | D. The complex-torus structure is given by its coordinate algebra; no complex variety is constructed |
| V.2.5 tori: `C_A`, section of `H_A`, `Λ(A) = X_*(A)` | `GS.CocharacterUniformizer.SplitTorusUniformizerSectionStatement`, `RC.uniformizerSection` | P: `splitTorusUniformizerSection` |
| V.2.5 `⁰A` is the maximal compact subgroup of a split torus `A` | `PL.TorusNormKernelCompactnessStatement` (every torus) and `compactSubgroup_le_rationalCommonNormKernel` | P: `torusNormKernelCompactness` |
| V.2.5 `A₁ ⊂ A₂` split: `⁰A₁ = A₁ ∩ ⁰A₂`, `Λ(A₁) ⊂ Λ(A₂)`, `C_{A₁} ⊂ C_{A₂}` | `PL.RationalNormKernelRestrictionStatement`; `RC.uniformizerSection_naturality` | P: `rationalNormKernelRestriction`; D |
| V.2.6 Lemma: `⁰A_G = ⁰G ∩ A_G` | `RC.SplitComponentKernelStatement` | P: `splitComponentKernel` |
| V.2.6 Lemma: `Λ(A_G) ↪ Λ(G)` with finite index | `RC.SplitComponentLatticeStatement`; `GS.CharacterRestrictionStatement` | P: `splitComponentLattice`, `characterRestriction` |
| V.2.6 Proposition: `G/⁰G A_G` finite; `⁰G ∩ Z(G)` compact | `PL.finite_rationalCentralQuotient` with `splitComponentLattice`; `PL.isCompact_rationalCommonNormKernel_inf_center` | P |
| V.2.6 Proposition: `Z(G)` compact implies `⁰G = G` | `PL.RationalNormKernelCompactCenterStatement` | P: `rationalNormKernelCompactCenter` |
| V.2.7 action of `X(G)` on `Irr(G)`, stabilizers | [RationalInertia](../../Langlands/Representation/CuspidalSupport/RationalInertia.md) | D |
| V.2.7 Lemma: `X(G)(π)` finite | `Langlands.CuspidalSupport.RationalTwistStabilizerFiniteStatement` | P: `rationalTwistStabilizerFinite` |
| V.2.7 Corollary and Notations: inertia orbits are complex tori; polynomial and rational functions on `D` | `Langlands.CuspidalSupport.RationalInertiaOrbitTorusStatement` (the Corollary and the identifications of the Notations paragraph; its Markdown explains the remaining definitions of polynomial and rational functions on `D`, which it does not restate) | P: `rationalInertiaOrbitTorus` |

The anisotropic-part entry corrects the previous ledger's claim that the assertion
was unstated. At Library `430cc03fe803c5dbf74bc3baf91e8f7a2c26ea9c`, the public
`TorusAnisotropicPartStatement` pair agrees with the version checked. It quantifies over
every field and actual torus, asserts a closed anisotropic subtorus through which
every closed anisotropic subtorus factors, and asserts finite surjective
multiplication with every largest split subtorus. This expresses uniqueness up to
isomorphism over the ambient torus and the scheme-level almost direct product.
A separate check compiled and inspected the existing
declaration as `Prop` with zero errors and warnings. No proof was found in the
Lean files of the Library at that time. The source was reread at V.2.2 Remark 2 and V.2.5, printed pp.105, 107 /
PDF pp.111, 113. Compilation of the statement supplies no proof evidence. At Library
`58ad0f796899b4aa457077d0146815c24758f739` the statement is proved: the
theorem `torusAnisotropicPart` is in the Library (fourth-update table at the top of this note).

## V.3 Parabolic subgroups (109–117 / 115–123)

The section refers to [7] (Borel–Tits) or [42] (Springer) for its recalled assertions.

| Item | Lean | Status |
| --- | --- | --- |
| V.3 opening: parabolic subgroups, rational radicals | `IsParabolicSubgroup` | D; Rec |
| V.3.1 Levi decomposition `P = M ⋉ N`; `N` acts simply transitively on the Levi factors | `GS.ParabolicRadicalTorusLeviStatement` and `GS.ParabolicRadicalTorusCentralizerLeviStatement` (a Levi factor is the centralizer of a maximal torus of the radical of `P`), `GS.RationalLeviConjugacyStatement` (two rational Levis are conjugate by a unique rational point of the unipotent radical), `GS.ParabolicRootPresentationExistenceStatement` | P (each has its proof) |
| V.3.1 `M = Z(G, A)` for a split component `A` of `P`, `A = A_M`; Levi subgroups are the centralizers of split tori `A` with `A = A_M` | the [ParabolicSplitComponentStatements](../../Langlands/GroupScheme/Rational/ParabolicSplitComponentStatements.md), for a split component `A` of `P` (a maximal split torus of a supplied radical of `P`, as in V.2.1): `GS.ParabolicSplitComponentLeviStatement` (`Z(G, A)` is represented by a rational Levi factor of `P` whose split component is `A`), `GS.LeviSplitComponentRadicalStatement` (the split component of a rational Levi factor is a split component of `P`), `GS.ParabolicSplitComponentConjugacyStatement` (the unipotent radical acts transitively on the split components of `P`) and `GS.LeviCentralizerCharacterizationStatement` (the rational Levi factors of parabolics are the centralizers of split subtori `A` that are their split components). `GS.LeviSplitComponentCentralizerStatement` states `Z_G(A_M) = M` as subgroup functors for every rational Levi of a rational parabolic. Related: `GS.DynamicLeviCocharacterRealizationStatement`, `GS.MinimalParabolicLeviCentralizerStatement` | Rec (S08); P for the four split-component statements: `parabolicSplitComponentLevi`, `leviSplitComponentRadical`, `parabolicSplitComponentConjugacy`, `leviCentralizerCharacterization`; P for their conjunction with the V.3.2 statement, `GS.ParabolicSplitComponentStatements`, by `parabolicSplitComponents`; P for the arbitrary-Levi split-component centralizer: `leviSplitComponentCentralizer` (eighth update); P for the related statements; see the V.3.5 row |
| V.3.1 opposite parabolic: the unique `Q ∈ P(M)` with `P ∩ Q = M` | `GS.OppositeDynamicParabolicUniquenessStatement` | P |
| V.3.1 `P(M)` is finite | `GS.LeviParabolicFiniteStatement`, in [LeviSplitComponentRecallStatements](../../Langlands/GroupScheme/Rational/LeviSplitComponentRecallStatements.md): a uniform bound on finite families with distinct parabolic images and the same embedded rational Levi | Rec (S07); P: `leviParabolicFinite` (eighth update), with a bound chosen from `(p, l)` before the family. `GS.MaximalLeviParabolicCountStatement` covers maximal `M` (at most two) |
| V.3.2 minimal parabolics; conjugacy of maximal split tori and of minimal parabolics | `GS.MinimalParabolicSplitComponentStatement` (first sentence: a parabolic is minimal if and only if its split components are maximal split tori of `G`), `GS.MinimalParabolicLeviCentralizerStatement`, `GS.MaximalSplitTorusConjugacyStatement`, `GS.MinimalParabolicConjugacyStatement` | P (the first sentence by `minimalParabolicSplitComponent`) |
| V.3.3 `𝔞`, `𝔞^*` | `RealTorusSpace.Vstar` | D |
| V.3.4 `Σ'(A)`, `Σ(A)`, `Σ'(P)`, `Σ(P)` | `relativeRoots`, `RelativeRoot.indivisibleRoots`, `positiveRelativeRoots`, `reducedPositiveRelativeRoots`, `RelativeRoot.subgroupRelativeRoots`; `GS.RenardRootConventionStatement` | D; P: `renardRootConvention` |
| V.3.5 `W(A) = N_G(A)/Z_G(A) = N_G(M)/M`, acting faithfully | `relativeWeylGroup` (minimal case); `RP.LeviNormalizerWeylGroupStatements` (`N_G(M)/M` finite, faithful through the norms on the centre); `GS.LeviSplitComponentCentralizerStatement` and `GS.LeviSplitComponentNormalizerStatement` | D; P: `leviNormalizerWeylGroupStatements`; P for `Z_G(A_M) = M` as subgroup functors (`leviSplitComponentCentralizer`) and `N_G(A_M) = N_G(M)` on rational points (`leviSplitComponentNormalizer`) for arbitrary rational Levis (eighth update); P for their conjunction with the finiteness statement, `GS.LeviSplitComponentRecallStatements` (`leviSplitComponentRecall`, tenth update). The normalizer equality is not asserted as equality of subgroup schemes; see the public pair's Weil-restriction counterexample to that stronger assertion |
| V.3.6 `𝔞^*_M = 𝔞^*_G ⊕ (𝔞^G_M)^*` and `𝔞_M = 𝔞_G ⊕ 𝔞^G_M`, for the minimal Levi `M_∅ = Z_G(T)`, the centralizer of the maximal split torus `T = A_∅` of V.3.8; `T` is the split component of `M_∅`, and in general `M_∅ ≠ T` (in the ramified `U(1,1)` example of issue I6, `T` has dimension one and `M_∅ ≅ Res_{E/F} 𝔾_m` has dimension two) | `GS.RelativeCentralDirectionsStatement` (conjunction of `RelativeCharacterRootComplementStatement` and `RelativeSplitCentralDirectionsStatement`), stated for the maximal split torus `T` itself (`i : T ⟶ G` with `IsMaximalSplitTorus i`), not for `M_∅`. The real spaces of the statement are those of `T`: `𝔞^*_{M_∅}` is identified with the real character space `Vstar T = ℝ ⊗ X^*(T)` through the restriction isomorphism `X^*(M_∅) ⊗ ℝ ≅ X^*(A_{M_∅}) ⊗ ℝ` given by Lemma V.2.6 (the upper horizontal arrow of V.3.6, with `A_{M_∅} = T`), and `𝔞_{M_∅}` with the dual real cocharacter space `V T = ℝ ⊗ X_*(T)`. The statement says that the root span and the restricted characters of `G` are complementary in `X^*(T) ⊗ ℝ`, and that the split component of `G` embeds in `T` with image the common root annihilator in `V T` | P (both conjuncts) |
| V.3.6 the same decompositions for an arbitrary Levi `M` | `GS.RenardLeviCentralDecompositionStatement` ([statement and scope](../../Langlands/GroupScheme/Rational/RenardLeviCentralDecompositionStatement.md)): over every field, for connected reductive `G`, `M` and actual split components with the compatible morphism diagram, both real restriction bijections, the canonical central-character inclusion, its complement with the literal restriction kernel, and the dual cocharacter complement with the pairing annihilator; both product equivalences have the specified addition formulas | P: `renardLeviCentralDecomposition` ([proof](../../Langlands/GroupScheme/Rational/RenardLeviCentralDecompositionProof.md)). P for the compatible component diagram of every rational Levi factor: the `GS.LeviSplitComponentInclusionStatement` ([statement and scope](../../Langlands/GroupScheme/Rational/LeviCentralCompatibilityStatements.md)), with `L = G`, gives `A_G ⊂ A_M` as the factorization the decomposition statement assumes; it is proved by `leviSplitComponentInclusion` ([proof](../../Langlands/GroupScheme/Rational/LeviSplitComponentInclusionProof.md)) (statement: ninth update; proof: tenth). P for its conjunction with the character-annihilator statement, `GS.LeviCentralCompatibilityStatements`: `leviCentralCompatibility` ([proof](../../Langlands/GroupScheme/Rational/LeviCentralCompatibilityProof.md)) (eleventh update) |
| V.3.7 `Σ(A_∅)` is a root system and `W` its Weyl group | `GS.RelativeRootSystemStatement` (a Mathlib root system on the rational span of the relative roots, Weyl group = the image of `W`), `GS.RelativeWeylCoxeterStatement`, `GS.RelativeTitsSystemStatement`; `GS.RelativeRealCorootStatement` adds existence of invariant scalar products on the actual real character and cocharacter spaces and real root-system realizations | P for the rational system and Weyl identification; P for the real statement: `relativeRealCoroot` ([proof](../../Langlands/GroupScheme/Rational/RelativeRealCorootProof.md)) |
| V.3.7 coroots `α̌ ∈ 𝔞_M`, the coroot system `Σ^∨(A_M)` in `𝔞_M`, and the spans `(𝔞^G_M)^*`, `𝔞^G_M` | `GS.RelativeRealCorootStatement`: the real image of each integral coroot from `RelativeRootReflectionData`, independence from those data, the formula and uniqueness for every invariant scalar product, the coroot span as the annihilator of restricted group characters, and crystallographic real root pairings for all roots and for the indivisible roots; minimal Levi only | P: `relativeRealCoroot`. For the projected generators for non-minimal standard Levis, see its V.3.13 component below |
| V.3.8 standard and semistandard parabolics; unique Levi factor containing `A_∅` | `GS.standardParabolic`, `GS.standardLevi`; `GS.StandardParabolicEndpointsStatement`, `GS.StandardLeviSplitComponentStatement` | D; P |
| V.3.9 every parabolic is conjugate to a standard one | `GS.StandardParabolicClassificationStatement` | P |
| V.3.10 semistandard intersections | `GS.DynamicSemistandardIntersectionStatement`, `GS.RepresentedParabolicLeviIntersectionStatement`, `GS.StandardLeviIntersectionStatement` | P |
| V.3.11 parabolics of `M` and parabolics of `G` contained in `P` | `GS.DynamicLeviParabolicCorrespondenceStatement`, `GS.DynamicNestedParabolicDecompositionStatement` | P |
| V.3.12 the simple roots form a basis of the root span; rank identities | `GS.RelativeRankStatement` (conjunction of `RelativeSimpleRootBasisStatement`: the simple relative roots form a basis of the rational span `relativeRootSpan` of the relative roots, and `RelativeRankIdentityStatement`: the rank identities and the rational character restriction) | P (both conjuncts) |
| V.3.12 the real form: `Δ_∅` is a basis of `(𝔞^G_∅)^*`, the kernel of restriction to `A_G` | `GS.RelativeSplitCentralDirectionsStatement` gives, for every split component `a : A_G → G`, an embedding `f : A_G → T` with `(rationalCharacterRestrictReal f).ker = relativeRootSpanReal i` (and the rational analogue). `GS.RelativeCharacterRootComplementStatement` gives the real complement. `GS.RelativeRealSimpleRootBasisStatement` states a real basis of `relativeRootSpanReal i` indexed by the actual simple roots, vector by vector `α ↦ 1 ⊗ α` | P (kernel identification and complement); P for the real basis: `relativeRealSimpleRootBasis` ([proof](../../Langlands/GroupScheme/Rational/RelativeRealSimpleRootBasisProof.md)) |
| V.3.12 `Δ_∅^∨` is a basis of `𝔞^G_∅`; fundamental weights and coweights | `GS.RelativeFundamentalWeightStatement`: the actual simple real coroot basis, bases dual to the simple coroots and simple roots, and uniqueness of each fundamental weight and coweight in its specified relative subspace | P: `relativeFundamentalWeight` ([proof](../../Langlands/GroupScheme/Rational/RelativeFundamentalWeightProof.md)) |
| V.3.13 `A_G ⊂ A_L ⊂ A_M ⊂ A_∅` and `𝔞_G ⊂ 𝔞_L ⊂ 𝔞_M ⊂ 𝔞_∅`, with `𝔞_M` the annihilator of `Δ^M_∅` | `GS.StandardLeviCentralDirectionsStatement`: for every standard Levi, the split component embeds into `A_∅` with real cocharacter image the annihilator of the selected simple roots, with the ranks. The `GS.LeviSplitComponentInclusionStatement` ([statement and scope](../../Langlands/GroupScheme/Rational/LeviCentralCompatibilityStatements.md)) states `A_L ⊂ A_M` for rational Levi factors `M ⊆ L`, and `A_G ⊂ A_L` with `L = G` | P (`standardLeviCentralDirections`). P for `A_G ⊂ A_L ⊂ A_M`: `leviSplitComponentInclusion` (statement: ninth update; proof: tenth). P for the conjunction `GS.LeviCentralCompatibilityStatements`: `leviCentralCompatibility` (eleventh update) |
| V.3.13 `𝔞^*_∅ = 𝔞^*_G ⊕ (𝔞^G_∅)^*`, with `(𝔞^G_∅)^*` the span of `Δ_∅` | the real part of `GS.RelativeCharacterRootComplementStatement` (the real root span and the restricted characters of `G` are complementary) | P |
| V.3.13 `𝔞^*_M` as the annihilator of the coroots of `M`; `𝔞_∅ = 𝔞_G ⊕ 𝔞^G_∅` with `𝔞^G_∅` the coroot span; `𝔞^*_M = 𝔞^*_L ⊕ (𝔞^L_M)^*` and its dual; orthogonality; projections `p^L_M` | `GS.StandardLeviRealDecompositionStatement`: for `J ⊆ K ⊆ Δ_∅`, root and coroot annihilator models, their perfect restricted pairing, the direct sums and projected spanning sets, and orthogonality for every invariant scalar product. The relative character space is the intersection of the coroot annihilator of `J` with the span of `K`, correcting I4; dually for cocharacters. The direct sums determine the projections | P: `standardLeviRealDecomposition` ([proof](../../Langlands/GroupScheme/Rational/StandardLeviRealDecompositionProof.md)). For the split component of a standard Levi with a compatible parabolic presentation, the published `langlandsCharacterRestriction` (P) maps the coroot annihilator bijectively onto `ℝ ⊗ X*(A_M)`. P for the characters of the Levi itself: the `GS.StandardLeviCharacterAnnihilatorStatement` ([statement and scope](../../Langlands/GroupScheme/Rational/LeviCentralCompatibilityStatements.md)) states that restriction maps `ℝ ⊗ X*(M)` onto the coroot annihilator of `Δ^M_∅`; it is proved by `standardLeviCharacterAnnihilator` ([proof](../../Langlands/GroupScheme/Rational/StandardLeviCharacterAnnihilatorProof.md)) (statement: ninth update; proof: tenth). P for the conjunction `GS.LeviCentralCompatibilityStatements`: `leviCentralCompatibility` (eleventh update). No named `p^L_M` map is added by these statements. The printed unprojected span remains false (I4) |
| V.3.14 `Δ(P)`, `Δ̂(P)`, `Δ^∨(P)`, `Δ̂^∨(P)`, `β̌` | [ParabolicChamberStatements](../../Langlands/Representation/LanglandsClassification/ParabolicChamberStatements.md), for a standard `P` given by its simple roots `J = Δ^M_∅`. In `𝔞^*_∅` and `𝔞_∅`: `GS.parabolicRoots`, `parabolicCoroots`, `parabolicFundamentalWeights`, `parabolicFundamentalCoweights` and the relation `IsParabolicCorootOf` (`β ↦ β̌`). On the split component `A` of `M`: `restrictedSimpleRoots` ([RestrictedSimpleRootCones](../../Langlands/GroupScheme/Rational/RestrictedSimpleRootCones.md)), `restrictedFundamentalWeights`, `restrictedParabolicCoroots`, `restrictedFundamentalCoweights` and `IsRestrictedParabolicCoroot`; also `GS.ParabolicRootPresentation`. Conjuncts 1–4 of `GS.ParabolicChamberLinearAlgebraStatement` state the uniqueness of the projections, the well-definedness of `β ↦ β̌` and the bases `Δ̂(P)` of `(𝔞^G_M)^*` and `Δ̂^∨(P)` of `𝔞^G_M`. Conjuncts 1–5 of `GS.ParabolicSplitComponentChamberStatement` compare the two settings | D; P for the module's inclusion and duality lemmas (`parabolicFundamentalWeights_subset`, `parabolicFundamentalCoweights_subset`, `pair_restrictedRootVector_of_isRealFundamentalCoweight`, `pair_restrict_of_isRealFundamentalWeight`); P for `ParabolicChamberLinearAlgebraStatement` by `parabolicChamberLinearAlgebra` (fifth-update table at the top of this note); P for `ParabolicSplitComponentChamberStatement` by `parabolicSplitComponentChamber`; P for the conjunction `GS.ParabolicChamberStatement` by `parabolicChamber`; seventh-update table at the top of this note. The source remark that `Δ(P)` is in general not a set of simple roots and `β̌` not a coroot has no precise content and is not formalized. The spanning remark `(𝔞^G_M)^* = span Δ(P)` is in `GS.StandardLeviRealDecompositionStatement` |
| V.3.15 cones `⁺[𝔞^*]^G_P`, its closure, chambers `^G_P[𝔞^*]^+` and closure, the `𝔞`-versions, and the remark `χ = Σ c_α ϖ_α + μ` | On `𝔞^*_M = Vstar A`: `restrictedRootPositiveCone`, `restrictedRootNonnegCone`; `restrictedCorootChamber`, `restrictedClosedCorootChamber` ([LanglandsTriplet](../../Langlands/Representation/LanglandsClassification/LanglandsTriplet.md), defined by lifting to `𝔞^*_∅`) and the printed forms `GS.parabolicCorootChamber`, `parabolicClosedCorootChamber` (positivity against every `β̌`). In `𝔞^*_∅`: `openSimpleCorootFace`, `closedSimpleCorootFace`, `projectedRootPositiveCone`, `projectedRootNonnegCone`. The `𝔞`-versions: `projectedCorootPositiveCone`, `projectedCorootNonnegCone`, `restrictedCorootPositiveCone`, `restrictedCorootNonnegCone`, and the chambers `chamber`, `closedChamber` on `𝔞_M = V A` of [RenardLeviCones](../../Langlands/BruhatTits/Cartan/RenardLeviCones.md). The negative versions are pointwise negatives and have no names. Conjuncts 5–6 of `ParabolicChamberLinearAlgebraStatement` and 6–13 of `ParabolicSplitComponentChamberStatement` state that the printed and lifted chambers agree, the remark, the descriptions of the coroot cones and the comparison of the root cones | D; P for conjuncts 5–6 of `ParabolicChamberLinearAlgebraStatement` (`parabolicChamberLinearAlgebra`); P for conjuncts 6–13 of `ParabolicSplitComponentChamberStatement` (`parabolicSplitComponentChamber`) |
| V.3.16 the faces `^G_P[(𝔞^G_M)^*]^+` and their closures as the positive (nonnegative) combinations of `Δ̂(P)`; chamber = face ⊕ `𝔞^*_G`; openness and closure; the two cell decompositions over `Q ⊇ P` | `openCorootFace`, `closedCorootFace` and their cone structures `openCorootFaceCone`, `closedCorootFaceCone`. Proved in [ParabolicChamberStatements](../../Langlands/Representation/LanglandsClassification/ParabolicChamberStatements.md), in the ambient model `𝔞^*_L ⊂ 𝔞^*_M ⊂ 𝔞^*_∅`: `openCorootFace_eq_inter`, `closedCorootFace_eq_inter`, `convex_openCorootFace`, `convex_closedCorootFace`, and both cell decompositions, `closedCorootFace_eq_iUnion` with `pairwiseDisjoint_openCorootFace` and `closedSimpleCorootFace_eq_iUnion` with `pairwiseDisjoint_openSimpleCorootFace`. Conjuncts 3 and 7–9 of `ParabolicChamberLinearAlgebraStatement` state the fundamental-weight descriptions, the sums with `𝔞^*_G` and the topological assertions | P: the intersection formulas, convexity and the cell decompositions in the statement module; the rest by `parabolicChamberLinearAlgebra` |
| V.3.17 Lemma | `GS.CorootChamberUnipotentRootsStatement` | P: `corootChamberUnipotentRoots` ([proof](../../Langlands/Representation/LanglandsClassification/CorootChamberUnipotentRoots.md)) |
| V.3.18 Langlands' combinatorial lemma | `GS.LanglandsCombinatorialDecompositionStatement` ([statement](../../Langlands/GroupScheme/Rational/LanglandsDecompositionStatement.md)), for arbitrary connected reductive `G` and actual standard parabolics. The `μ⁻` condition follows the V.5.5 proof, not the literal `−p^L_M(…)` of (V.3.18.1), which does not determine `Q` (an `A_2` counterexample is in the Markdown of `LanglandsDecompositionCones`) | P: `langlandsCombinatorialDecomposition` ([proof](../../Langlands/GroupScheme/Rational/LanglandsDecompositionProof.md)). The Euclidean projection theorem of V.5.5 is stated and proved (`Langlands.Renard.ConeProjectionStatements`) |
| V.3.19 `𝔞^* = Hom_lisse(M, ℝ)`, `ln \|χ\| ∈ 𝔞^*` | `PL.RationalSmoothRealDescentStatement` (smooth, that is open-kernel, homomorphisms) | P: `rationalSmoothRealDescent`. A step of the source argument says "tout morphisme" but uses smoothness; without it the descent fails (`M = 𝔾_m` over `ℚ_p`), as the statement's [Markdown](../../Langlands/Representation/Plancherel/RationalSmoothRealDescentStatement.md) records |
| V.3.20 `𝔞^*_ℂ = Hom(Λ(M), ℂ) → X(M)` via `q^{-s}`: surjectivity, kernel `(2iπ/ln q)ℛ`, real part `ℜ(χ)` independent of the lift, unitary characters are those with `ℜ(χ) = 0` | `PL.RationalComplexParameterStatement` (on the actual valuation image `Λ(M)`), `RationalImageComplexExponential`, `RationalImageRealPart` | P: `rationalComplexParameter` |
| V.3.20 `𝔞^*_ℂ = Hom_ℤ(Λ(M), ℂ)` identified with `X^*(M) ⊗_ℤ ℂ` | `PL.RationalCharacterTensorParameterStatement`: the canonical map `ℂ ⊗_ℤ X^*(G) → Hom_ℤ(Λ(G), ℂ)`, `s ⊗ χ ↦ (a ↦ s a(χ))`, is bijective for every connected reductive `G` over a nonarchimedean local field, so for every Levi `M` (on the actual valuation image `Λ(G)`, with Mathlib's scalar-first tensor order) | P: `rationalCharacterTensorParameterBijective` |
| V.3.20 the surjection `X^*(M) ⊗ ℂ → X(M)` is `χ ⊗ s ↦ [g ↦ \|χ(g)\|_F^s]` | `PL.rationalCanonicalCharacterTensorExponential_tmul_val` ([RationalCharacterTensorParameter](../../Langlands/Representation/Plancherel/RationalCharacterTensorParameter.md)), on actual rational points, with the normalized absolute value | P (a theorem about the published construction) |
| V.3.20 the kernel `(2iπ/ln q)ℛ` is a lattice; `Im X(M)` is the image of `i𝔞^*` and a compact torus isomorphic to `i𝔞^*/(2iπ/ln q)ℛ` | `PL.RationalImaginaryParameterQuotientStatement`: the periods are discrete and closed (in `𝔞^*_ℂ` and in `i𝔞^*`), the quotient of `i𝔞^*` by them is compact, and the imaginary exponential is an open quotient map inducing a homeomorphism, with the prescribed values, onto the unitary characters of `Λ(M)` and onto the unitary unramified characters of `M(F)` | P: `rationalImaginaryParameterQuotient` (topological formulation; its Markdown keeps the algebraic and manifold assertions separate) |
| V.3.20 "on retrouve ainsi la structure de tore algébrique de `X(M)`"; `Im X(M)` is a real submanifold of the complex torus `X(M)` | Algebraic side: the coordinate algebra `ℂ[Λ(M)]` (V.2.4 above) and the basis-dependent isomorphisms of topological groups `X(M) ≃ (ℂ^×)^r` and `Im X(M) ≃ (S¹)^r` (`PL.rationalCanonicalUnramifiedCharacterCoordinates`, `PL.rationalCanonicalUnitaryUnramifiedCharacterCoordinates`, in [RationalUnramifiedCharacterCoordinates](../../Langlands/Representation/Plancherel/RationalUnramifiedCharacterCoordinates.md)). Analytic side: the definitions [RationalUnramifiedComplexChart](../../Langlands/Representation/Plancherel/RationalUnramifiedComplexChart.md) (the one-chart complex structure of each integer basis of `Λ(M)`) and statements [RationalUnramifiedComplexTorusStatement](../../Langlands/Representation/Plancherel/RationalUnramifiedComplexTorusStatement.md): `PL.RationalUnramifiedBasisChartIndependenceStatement` (every basis chart is a local biholomorphism), `PL.RationalUnramifiedComplexLieGroupStatement` (`X(M)` is a complex Lie group), `PL.RationalUnramifiedComplexExponentialStatement` (`𝔞*_ℂ → X(M)` is a local biholomorphism) and `PL.RationalUnitaryUnramifiedSubmanifoldStatement` (`Im X(M)` is an embedded real Lie subgroup, onto which the imaginary exponential is a local diffeomorphism), with conjunction `PL.RationalUnramifiedComplexTorusStatement`; stated for any connected reductive `G` in place of the Levi `M` | D (coordinates and charts); P for the four analytic statements (statements: eighth update; proofs: tenth): `rationalUnramifiedBasisChartIndependence`, `rationalUnramifiedComplexLieGroup`, `rationalUnramifiedComplexExponential` and `rationalUnitaryUnramifiedSubmanifold`. P for the conjunction: `rationalUnramifiedComplexTorus` ([proof](../../Langlands/Representation/Plancherel/RationalUnramifiedComplexTorusProof.md)), whose proof includes the rename of a clashing instance name (statement: tenth update; proof: eleventh). The complex structure is the analytic one; no scheme structure on `X(M)` is constructed. See also remark R2 |
| V.3.21 `M^+`, `M^{++}` (inverse images under `H_M` of the chambers) and the full cones `A^+_M`, `A^{++}_M` (all `a ∈ A_M` with `\|α(a)\|_F ≤ 1`, resp. `< 1`, for `α ∈ Δ(P)`) | [RenardLeviCones](../../Langlands/BruhatTits/Cartan/RenardLeviCones.md), namespace `Langlands.BruhatTits.Cartan.RenardLeviCones`: `leviPlus`, `leviStrict` (`M^+`, `M^{++}`: the points whose published positive centralizer valuation `H_M` lies in `closedChamber`, resp. `chamber`, on `𝔞_M = V A`) and `componentPlus`, `componentStrict` (`A^+_M`, `A^{++}_M`, defined by the norm form). The data `(i, ν, J, f)` make the dependence on `P` explicit; reading `leviPlus` as `M^+` requires the Levi, its split component and their inclusion as inputs, which the definitions do not enforce (as for `dominantCentralizer`). Proved there: the valuation forms `mem_componentPlus_iff_order`, `mem_componentStrict_iff_order`; for split `A`, agreement with the source definition `A^+_M = A_M ∩ M^+` (`map_mem_leviPlus_iff`, `preimage_leviPlus`, and the same for `A^{++}_M`); the monoid laws; `⁰M ⊂ M^+`; and `leviPlus_minimal`: `M_∅^+` is the published `dominantCentralizer` of [RenardDominantValuation](../../Langlands/Representation/Plancherel/RenardDominantValuation.md). `CocharacterUniformizer.CAplus` and `CAstrict` are the lattice cuts of V.3.23 (`CAplus_eq_inter`, `CAstrict_eq_inter`). Earlier inline uses, such as the hypotheses `characterNorm F S α x ≤ 1` in `StandardCasselmanUniformAsymptotics.lean`, are not rewritten through these names | D; P for all the listed theorems. The separate published topology target on actual standard-Levi split components is recorded in the next row |
| V.3.15/V.3.21 topology of `chamber` and `closedChamber` on the actual `𝔞_M = V A` | `Langlands.BruhatTits.Cartan.RenardLeviCones.LeviChamberTopologyStatement` ([statement and scope](../../Langlands/BruhatTits/Cartan/RenardLeviChamberTopologyStatement.md)): for an actual connected reductive group over an arbitrary field, maximal split torus, generic cocharacter, subset of simple roots, represented closed standard Levi, its actual split component and compatible factor into the maximal split torus, the strict chamber is nonempty and open, the nonstrict chamber is closed, and it equals the topological closure of the strict chamber in `moduleTopology ℝ (V A)`. Nonemptiness is a conclusion; empty roots and central directions are included | P: `Langlands.BruhatTits.Cartan.RenardLeviCones.leviChamberTopology` ([proof](../../Langlands/BruhatTits/Cartan/RenardLeviChamberTopologyProof.md)), in the Library. The statement is unchanged. Evidence below; gap 8 is closed |
| V.3.21 (V.3.21.1) `A^+_M = ⊔_Q A^{++}_L` | the `Langlands.BruhatTits.Cartan.RenardLeviCones.LeviConePartitionStatement` ([statement and scope](../../Langlands/BruhatTits/Cartan/RenardLeviConePartitionStatement.md)): for every standard index `J`, actual split component `A` of the standard Levi `M` and compatible `A → T`, the image of `A^+_M` in `A_M(F)/⁰A_M` is partitioned by the images of the strict cones `A^{++}_L` of actual split components of the standard Levis `L ⊇ M`, mapped compatibly into `A`. The printed equality of point sets is false (I1); the statement is its correction modulo `⁰A_M` | P for the corrected quotient statement ([RenardLeviConePartitionStatement](../../Langlands/BruhatTits/Cartan/RenardLeviConePartitionStatement.md)): `Langlands.BruhatTits.Cartan.RenardLeviCones.leviConePartition` ([proof](../../Langlands/BruhatTits/Cartan/RenardLeviConePartitionProof.md)). See the 20 November follow-up and source issue I1 |
| V.3.22 `A^+(ε)` (all `a ∈ A_M` with `\|α(a)\|_F < ε`) | `componentEpsilon` in [RenardLeviCones](../../Langlands/BruhatTits/Cartan/RenardLeviCones.md), defined for every real `ε`. Proved there: `componentEpsilon_one` (`A^+(1) = A^{++}_M`), `componentEpsilon_mono`, `componentEpsilon_subset_componentStrict` for `ε ≤ 1`, `componentEpsilon_eq_empty` for `ε ≤ 0` and nonempty `Δ(P)`, and `CAepsilon_eq_inter`: `CocharacterUniformizer.CAepsilon` is the lattice cut `C_A^+(ε) = C_A ∩ A^+(ε)` of V.3.23. Earlier inline forms remain: the condition on every `t ∈ A(F)` in `RP.GeneralizedJacquetContractingRangeStatement` (GeneralizedJacquetRemarksStatements.lean) and `standardCone` in `StandardCasselmanConstantTerm.lean` | D; P for the listed theorems |
| V.3.23 `C_A`, `F_M`, `C̃_A = C_A F_M`, `F_M ⊂ M^+`, `C_A^+`, `C_A^{++}`, `C_A^+(ε)` | `CocharacterUniformizer.CA`, `CAplus`, `CAstrict`, `CAepsilon`; `RC.FullLatticeRepresentativeStatement`, `RC.RenardDominantComparisonStatement`, `RC.IsChamberCompatibleTransversal` | D; P: `fullLatticeRepresentative` (representatives) and `renardDominantComparison` |
| V.3.24 the nonnegative integral model and quotient by the common annihilator | `GS.CocharacterCone.nonnegative`, `quotient`, `mkQ_mem_quotient_iff`, `latticeSection_mem_CAplus_iff` ([construction](../../Langlands/GroupScheme/Rational/CocharacterCone.md)) | D/P for the construction and intrinsic laws |
| V.3.24 the integral kernel of the split-central quotient | `GS.SimpleRootSplitCentralImageStatement`: for every supplied compatible `f : A_G → A_∅`, the simple-root integral annihilator equals the integral cocharacter image of `f` | P: `simpleRootSplitCentralImage` ([proof](../../Langlands/GroupScheme/Rational/SimpleRootSplitCentralImageProof.md)) |
| V.3.24 the common-uniformizer group quotient and its representative map | `GS.CocharacterUniformizer.QuotientComparisonStatement`: for split `T` and every commutative `A` and `f : A → T`, the integral quotient by `range(cocharacterMapInt f)` is multiplicatively equivalent to the image of `C_T` in `T(F)/f(C_A)`, by evaluation at the common uniformizer | P: `CocharacterUniformizer.quotientComparison` ([proof](../../Langlands/Geometry/Building/CocharacterUniformizerQuotientProof.md)) |
| V.3.24 finite-generation replacement for the false `S ≅ ℕ^d` assertion | `GS.CocharacterConeFiniteGenerationStatement`: for every field, actual commutative group scheme `T` and finite set `R` of actual characters, `(CocharacterCone.quotient T R).FG` | P: `cocharacterConeFiniteGeneration` ([proof](../../Langlands/GroupScheme/Rational/CocharacterConeFiniteGenerationProof.md)). No freeness assertion |
| V.3.24 actual nonnegative quotient `C^+_∅/C_{A_G}` | `GS.CocharacterUniformizer.CAplusMonoid`, `CAplusQuotient`, `mem_CAplusMonoid`, `mem_CAplusQuotient` ([construction](../../Langlands/Geometry/Building/CocharacterUniformizerCone.md)) | D/P for the construction and its representative laws |
| V.3.24 comparison of the integral nonnegative quotient with that actual quotient | `GS.CocharacterUniformizer.ConeQuotientComparisonStatement`: a monoid equivalence prescribed by common-uniformizer evaluation on every nonnegative representative, for every supplied compatible split-component map | P: `CocharacterUniformizer.coneQuotientComparison` ([proof](../../Langlands/Geometry/Building/CocharacterUniformizerConeQuotientProof.md)) |
| V.3.24 strict faces of the integral quotient | `GS.CocharacterCone.strictFace`, `mkQ_mem_strictFace_iff`, `strictFace_subset_quotient`, `existsUnique_strictFace`, `iUnion_strictFace`, `strictFace_disjoint` ([construction](../../Langlands/GroupScheme/Rational/CocharacterConeFaces.md)) | D/P; these are integral faces, before comparison with actual Levi split components |
| V.3.24 strict uniformizer image of each actual standard Levi split component | `GS.CocharacterUniformizer.StandardLeviStrictImageStatement`: under every supplied compatible map, the strict section image equals the uniformizer image of `IsStandardCocharacter` | P: `CocharacterUniformizer.standardLeviStrictImage` ([proof](../../Langlands/Geometry/Building/StandardLeviStrictUniformizerProof.md)) |
| V.3.24 actual strict quotient pieces | `GS.CocharacterUniformizer.standardLeviStrictQuotientFace` takes the quotient images over all actual compatible standard-Levi representatives | D/P for the definition, introduction and invalid-index emptiness laws. The unrestricted definition supplies no structural existence or partition proof |
| V.3.24 `S = ⊔ S^{++}_L` in the actual common-uniformizer quotient | `GS.CocharacterUniformizer.StandardLeviStrictQuotientPartitionStatement`: each actual piece is contained in the nonnegative quotient, and every point of that quotient belongs to exactly one indexed piece | P: `CocharacterUniformizer.standardLeviStrictQuotientPartition` ([proof](../../Langlands/Geometry/Building/StandardLeviStrictQuotientPartitionProof.md)). The 18 November verification is recorded below; source issue I2 still prevents the printed free-monoid conclusion |
| V.3.24 finite generation of the actual nonnegative quotient `C^+_∅/C_{A_G}` | the `GS.CocharacterUniformizer.ConeQuotientFiniteGenerationStatement` ([statement and scope](../../Langlands/Geometry/Building/CocharacterUniformizerConeFiniteGenerationStatement.md)): for the data of `ConeQuotientComparisonStatement`, the actual quotient submonoid `CAplusQuotient F T (simpleRelativeRoots i ν) A f` is finitely generated | P: `CocharacterUniformizer.coneQuotientFiniteGeneration` ([proof](../../Langlands/Geometry/Building/CocharacterUniformizerConeFiniteGenerationProof.md)). The proof transports the integral finite generation through the nonnegative comparison. No freeness or generator-count assertion (I2). Tenth update |
| V.3.25 `C_A/C_{A_G}(C_A ∩ ⁰G)` finite; `C^{++}_A ∩ ⁰G ≠ ∅` | not stated separately | St: step of VI.3.5 (`RPF.RationalCompactRestrictionCuspidalStatement`, proved) |

## Evidence for the focused V.3.6–V.3.13 update

The statement module first appeared in the Library at
`7f43c3c930ff92f76dae6589da1678ad729017e5`. Its exact Lean/Markdown pair agrees
with the Library at the time of this update. A separate check compiles the module and inspects
`Langlands.GroupScheme.RenardLeviCentralDecompositionStatement` as a
`Prop`-valued definition with universe parameter `u` and only standard axioms.
This is statement evidence. The statement had no proof on
13 November 2026. Its proof `renardLeviCentralDecomposition` first appeared in the
Library at `ba00e0970dd9ba6222ccc056ca2ee7f06bcc8181`; see the table of the third update
at the top of this note.

The module `Langlands.GroupScheme.Rational.RelativeRealCorootStatements` contains the
four component statements above and their conjunction
`Langlands.GroupScheme.RelativeRealCorootLinearAlgebraStatement`. It first appeared in the
Library at `0c3f30c24701c74d5474fca3fbb5324a99aa1d58`. At the base used for this update the
pair in the Library agrees exactly with the one checked. Each component statement is proved at Library
`ba00e0970dd9ba6222ccc056ca2ee7f06bcc8181` (table at the top of this note). The
conjunction itself is proved by `relativeRealCorootLinearAlgebra`, which first appeared in the Library at
`497ef49830025d23824f6b2e2b1d5d60b594f51e` (table of the sixth update).

Its statements are over arbitrary fields, on the shared actual torus spaces,
and universally quantify over supplied integral reflection data. Existence of
those data is a separate published statement; no new existence proof is
claimed here. The standard-Levi spaces are ambient root/coroot annihilators.
Their identification with the character and cocharacter spaces of actual split
components needs the existing standard-Levi comparisons and any remaining
comparison proof. Neither this module nor the compatible-diagram V.3.6
statement settles every geometric realization. The corrected projected-root
form of V.3.13 preserves source issue I4 below.

The module `LeviCentralCompatibilityStatements`, recorded by the ninth update,
states the two remaining geometric inputs. The first,
`LeviSplitComponentInclusionStatement`, gives the split-component inclusion
`A_L ⊂ A_M` for rational Levi factors `M ⊆ L`; with `L = G` it supplies the
compatible diagram of the V.3.6 statement for every rational Levi factor. The
second, `StandardLeviCharacterAnnihilatorStatement`, identifies the image of
the real characters of a standard Levi with the ambient coroot annihilator.
On the cocharacter side, the corresponding identification is the proved
`standardLeviCentralDirections`, and for the characters of a compatible split
component it is the proved `langlandsCharacterRestriction`. Both new
statements are proved, by `leviSplitComponentInclusion` and
`standardLeviCharacterAnnihilator`, as
recorded by the tenth update. Their conjunction is proved by
`leviCentralCompatibility`, as recorded by the eleventh update.

## Evidence for the focused V.3.21 topology update

On 16 November 2026 the statement pair is in the Library. It first appeared at commit
`e9c05be9da1000900a43de75ec2ede66892aa158`. The pair as checked and the pair in the
Library at
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

The exact proof is the theorem
`Langlands.BruhatTits.Cartan.RenardLeviCones.leviChamberTopology.{u}`.
It was checked by a Lake build against the exact target, with the statement and its
inputs unchanged, and first appeared in the Library at commit
`c0c2e1210454ae2a1888a2989e3de794c1336819`.
The proof pairs as checked, at that first commit and in the Library at the audit
base agree byte for byte:

| File | SHA256 |
| --- | --- |
| `Langlands/BruhatTits/Cartan/RenardLeviChamberTopologyProof.lean` | `ab7c734a2ffc6e4899877e6268ff24be2482426c7de5c73b80866e207f884531` |
| `Langlands/BruhatTits/Cartan/RenardLeviChamberTopologyProof.md` | `5912b816864080534bac25e7557e6eff01965facf09afca0ec9a1ae8000fb759` |

Two separate checks compile the statement and the
proof on the audit base with zero errors or warnings. The second inspects the
theorem with universe parameter `u` and only `propext`, `Classical.choice`
and `Quot.sound`.

The proof lifts a standard cocharacter through the actual split-component map
to obtain a strict chamber point, then uses continuity of finitely many linear
inequalities and a positive perturbation to prove the topology assertions.
The separate source issue (V.3.21.1), integral and actual lattice partitions,
valuation comparisons and additional representative-existence obligations
retain their own status.

## Evidence for the focused V.3.24 update

The following three modules first appeared in the Library at
Library `430cc03fe803c5dbf74bc3baf91e8f7a2c26ea9c`. Their Lean/Markdown pairs, as checked
and in the Library, were compared byte for byte on 13 November 2026:

| Public module |
| --- |
| `Langlands.GroupScheme.Rational.CocharacterCone` |
| `Langlands.GroupScheme.SimpleRootSplitCentralImageStatement` |
| `Langlands.GroupScheme.CocharacterUniformizer.QuotientComparisonStatement` |

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

The three proofs below first appeared in the Library at
`af5d652c2f2ff5b35b4ce4dbbf7cbec8bbf3e99e`. Each theorem has exactly
its named statement as its type, including universe parameter `u`. Each was
checked by a Lake build against the exact target, with the statement and its inputs
unchanged. On 14 November both files of
each proof were compared with Library `2309f61083ef231a3ef371f18ab1eff2ae8de56d`; all six
SHA256 digests equal those recorded when the proofs were checked.

| Theorem |
| --- |
| `Langlands.GroupScheme.simpleRootSplitCentralImage` |
| `Langlands.GroupScheme.CocharacterUniformizer.quotientComparison` |
| `Langlands.GroupScheme.cocharacterConeFiniteGeneration` |

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
`CocharacterUniformizer.coneQuotientComparison`, verified below.

The finite-generation statement first appeared in the Library at
`85c2fe719cf62e96f22aaf4ca03961c5814d086b`. The pair as checked and the pair in the
Library agree exactly. The sole finiteness premise is finiteness of the selected actual
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
is now in the Library. Transport of finite generation to the actual
nonnegative uniformizer quotient was a separate statement. It is now stated
by the `ConeQuotientFiniteGenerationStatement` and proved by
`CocharacterUniformizer.coneQuotientFiniteGeneration`, as recorded
by the tenth update.

Three further modules first appeared in the Library at commit
`db8d6b3d466f2fd453a4df4624ce6c90db8eed46`, and their pairs as checked agree
with the Library at the time of this update:

| Public module |
| --- |
| `CocharacterUniformizerCone` |
| `CocharacterConeFaces` |
| `StandardLeviStrictUniformizerStatement` |

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

The 14 November check verifies three further modules. Their
Lean/Markdown hashes as checked agree with both the commit where each
first appeared and Library `c0debd6f4dd02fdd68d70811cf610906b945a962`.

| Public module | First appeared at Library commit |
| --- | --- |
| `CocharacterUniformizerConeQuotientStatement` | `410c79471b79f65a02fb0f6070da7f2800793ff3` |
| `StandardLeviStrictQuotientFaces` | `410c79471b79f65a02fb0f6070da7f2800793ff3` |
| `StandardLeviStrictQuotientPartitionStatement` | `e5365902d74534dbf1622c06e695dffdc128d723` |

The first states the prescribed nonnegative monoid equivalence. The second defines each strict piece inside the single
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

On 17 November 2026 the two exact comparison proofs
below were verified against Library `ab9053b1751d6b6557d044c38c04e4c8a67dfffc`. Both
first appeared in the Library at `2613dbbf784309977c42d9252b78c1e1cd40be63`. Each
was checked by a Lake build against the exact target, with the statement and its
inputs unchanged.

| Theorem and proof module |
| --- |
| `Langlands.GroupScheme.CocharacterUniformizer.standardLeviStrictImage`, [StandardLeviStrictUniformizerProof](../../Langlands/Geometry/Building/StandardLeviStrictUniformizerProof.md) |
| `Langlands.GroupScheme.CocharacterUniformizer.coneQuotientComparison`, [CocharacterUniformizerConeQuotientProof](../../Langlands/Geometry/Building/CocharacterUniformizerConeQuotientProof.md) |

For each proof, the Lean and Markdown bytes as checked, at the
first-publication commit and in the audit Library agree exactly. Each
statement's Lean and Markdown bytes also agree between the proof base
`fcb85a7ef43356fec01e6ccf1605f08568c08cb0`, first publication and audit Library. The exact targets retain universe parameter `u` and every
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

On 18 November 2026 the exact actual-partition
proof was verified against Library `18c5dd82d119bef479b69de264324b22fe6f8d36`. It
was checked by a Lake build against the exact target, with the statement and its
inputs unchanged.

| Theorem and proof module |
| --- |
| `Langlands.GroupScheme.CocharacterUniformizer.standardLeviStrictQuotientPartition`, [StandardLeviStrictQuotientPartitionProof](../../Langlands/Geometry/Building/StandardLeviStrictQuotientPartitionProof.md) |

Both proof files agree byte for byte between the version checked,
first-publication commit `42c696807fd25d6ea96d001a596d7bba7b4b52b9` and audit
Library. Both target files agree between proof base
`08ff6d3c99370355ef21ffa0fdf9bd7532aafaa8`, first publication and audit Library.
A separate check compiles the proof with zero errors
or warnings and reports only `propext`, `Classical.choice` and `Quot.sound`.
Its final theorem has the exact type
`StandardLeviStrictQuotientPartitionStatement.{u}`.

The proof identifies each actual piece with its integral strict-face image
and transports the integral partition through the nonnegative comparison.
The forward inclusion uses the strict-image theorem on every supplied actual
representative. For the reverse inclusion, the published
`standardLeviSplitComponentStatement` supplies a canonical actual
representative and its compatible split-component map. The comparison
equivalence then gives containment, covering and unique indexed membership.
The final theorem discharges both comparison premises with the published
strict-image and nonnegative-comparison proofs. No representative-existence, image-equality
or partition premise is added. The result retains universe `u`, both field
characteristics, non-split ambient groups, nonreduced relative roots and
rank zero. It concerns the common-uniformizer quotient and asserts neither
finite generation nor freeness nor a full rational-point cone decomposition.

The source was reread at V.2.5 (printed p.107 / PDF p.113), V.3.21 (printed
p.116 / PDF p.122) and V.3.23–V.3.24 (printed p.117 / PDF p.123).
The correction of the free-monoid assertion remains issue I2 below. The
integral central-image equality, group quotient comparison, integral finite
generation, actual strict-image comparison, nonnegative quotient comparison
and actual strict-piece partition are proved. Finite generation after
transport to the actual quotient is also proved (tenth update). The chamber,
parabolic split-component and closed-root-subset modules are treated in the rows
above and below. Eight of the nine
closed-root-subset proofs are in the Library, and so is the proof of their
conjunction `RenardClosedRootSubsetStatements`. The ninth target is false. The
V.4.2 section below records their status (seventh and ninth updates).

## V.4 Weyl groups (118–122 / 124–128)

| Item | Lean | Status |
| --- | --- | --- |
| V.4 opening: root subgroups `U_γ` | root-subgroup constructions under `Langlands.GroupScheme.Rational` | D |
| V.4.1 `W_G`, `S_∅`; Proposition ([7]): Tits system and Bruhat decomposition | `relativeWeylGroup`; `GS.RelativeTitsSystemStatement`, `GS.TitsStandardParabolicStatement` | P |
| V.4.2 closed, convex, symmetric and unipotent subsets; `G(T)`, `U(T)`; Proposition ([7] 3.22) | The nine components of `GS.ClosedRootSubsetStatements` ([statements and scope](../../Langlands/GroupScheme/Rational/ClosedRootSubsetStatements.md)); generated groups use closed minimality on all test schemes, with existence stated separately. The V.4.2 conjunction is `GS.RenardClosedRootSubsetStatements` ([statement](../../Langlands/GroupScheme/Rational/RenardClosedRootSubsetStatements.md)), the conjunction of the eight components other than the Borel–Tits 3.22(b) statement `GS.ClosedRootSubsetGroupIntersectionStatement` | Rec (S14); D for the notions and elementary laws. P for eight targets (seventh-update table at the top of this note). F for `ClosedRootSubsetGroupIntersectionStatement`, by the paper counterexample of the [erratum note](../errata/borel-tits-1965-closed-root-intersection.md), and the nine-part conjunction is therefore not provable. P for `RenardClosedRootSubsetStatements`, the conjunction of the eight: `renardClosedRootSubsets` ([proof](../../Langlands/GroupScheme/Rational/RenardClosedRootSubsetProof.md)) (ninth update). Intersection targets use reduced test schemes, and (ii) uses all relative roots; see I5 |
| V.4.2 Proposition ([7] 5.12–5.18): standard parabolics and subsets `Θ ⊂ Δ_∅` | `GS.StandardParabolicClassificationStatement`, `GS.StandardCocharacterStatement`, `GS.StandardParabolicPointsStatement`; new `GS.StandardParabolicRootTripleStatement` and `GS.StandardParabolicRootSubsetGroupStatement` give the generated root triples and their groups | P for the existing classification and points statements; P for the new root-triple and generated-group comparisons, in `ClosedRootSubsetStatements`: `standardParabolicRootTriple` and `standardParabolicRootSubsetGroup` |
| V.4.3 `W_M ↪ W_G`, `w·M`, `W(L, M)`, `W_M W(L,M) W_L = W(L,M)` | `standardRelativeWeylGroup`, [RelativeWeylConjugation](../../Langlands/Group/RelativeWeylConjugation.md), `GS.StandardLeviConjugationStatement` | D; P |
| V.4.3 (V.4.3.3) `W(M, M)/W_M ≃ W(A)` | `GS.StandardLeviNormalizerQuotientStatement`; finiteness consequence `RP.LeviNormalizerFiniteQuotientStatement` | P: `standardLeviNormalizerQuotient`; P (finiteness) |
| V.4.4 `W(*, M)`, `W(M, *)`, `l(M)` | inline sets in `GS.StandardWeylElementaryChainStatement` (the VI.5.4 Lemma) and `GS.StandardMaximalLeviWeylStatement` | X/D (no named definition). Both statements are proved: `standardWeylElementaryChain` and `standardMaximalLeviWeyl` |
| V.4.5 Lemma: `Q`-orbits on `P\G` and `W_M\W_G/W_L`; Bruhat order and a finer total order | `GS.StandardParabolicPointsStatement` (double-coset bijections, for standard `P` and `Q`); [RationalGeometricOrbitOrdering](../../Langlands/Representation/Aubert/General/RationalGeometricOrbitOrdering.md) | P for standard `P`, `Q`; D |
| V.4.5 Corollary: finitely many orbits for arbitrary `P`, `Q` | `GS.RepresentedParabolicDoubleCosetStatement` | P: `representedParabolicDoubleCoset` |
| V.4.6 Lemma | `GS.StandardWeylMinimalRepresentativesStatement` | P: `standardWeylMinimalRepresentatives` |
| V.4.7 representatives `W^{Q,P}` for arbitrary `P`, `Q` | `RP.RepresentedGeometricLemmaGeometryStatement` | P: `representedGeometricLemmaGeometry` |
| V.4.8 maximal standard Levis and `Δ_∅ ∖ {α}`; `M` maximal iff `l(M) = 2`; `w·P = P̄′` | `GS.StandardMaximalLeviWeylStatement`; related `GS.MaximalLeviParabolicCountStatement`, `GS.MaximalLeviParabolicFamilyStatement`, `GS.MaximalLeviContainmentStatement` | P: `standardMaximalLeviWeyl`; P for the related statements (`maximalLeviParabolicCount`, `maximalLeviParabolicFamily`, `maximalLeviContainment`). See remark R1 |

The closed-root-subset module
first appeared in the Library at
`db8d6b3d466f2fd453a4df4624ce6c90db8eed46`. The pair as checked and the pair in the
Library match exactly. The module itself proves none of its nine proposition
targets. As of the seventh update, eight of them are proved and the ninth is
false; see the table below. The ninth update
records the proof of the conjunction of the eight. The arbitrary-field
statements distinguish the indivisible and possibly nonreduced ambient root
sets. They do not identify scheme-theoretic intersections on arbitrary test
schemes, and the symmetric-subset target gives integral reflections and their
preservation of the subset rather than constructing a Mathlib root-system
object. Source correction I5 is retained.

The 14 November audit searched the checked Library and found the nine
proposition definitions and their conjunction references, with no exact proof
theorems. Each target
is in namespace `Langlands.GroupScheme` (`GS` below) at universe `u`, over
an arbitrary field, an actual connected reductive group and a maximal split
torus. Where used, the generic cocharacter and simple-root subset remain
quantified data. “Either ambient set” means the indivisible roots or all
possibly nonreduced relative roots, as specified by `IsRelativeRootAmbient`.

| Exact target | Scope | Status on 17 November |
| --- | --- | --- |
| `GS.ConvexRootSubsetHullStatement` | In either ambient set, convexity is equivalent to containing every ambient root in the real cone hull of the subset, with the subset condition retained | P: `convexRootSubsetHull` |
| `GS.UnipotentRootSubsetCocharacterStatement` | In either ambient set, unipotence is equivalent to closedness and existence of a cocharacter positive on every member | P: `unipotentRootSubsetCocharacter` |
| `GS.SymmetricRootSubsetWeylStatement` | In either ambient set, integral reflections exist for each member of a symmetric subset; those reflections and their generated Weyl subgroup preserve the subset | P: `symmetricRootSubsetWeyl` |
| `GS.StandardParabolicRootTripleStatement` | In either ambient set, the standard triple has the explicit integral-span root descriptions, convexity, symmetry and unipotence properties and recovers `Θ` | P: `standardParabolicRootTriple` |
| `GS.RootSubsetGroupExistenceStatement` | For every subset of all relative roots, smooth affine connected minimal closed groups `G(X)` and `U(X)` exist; `U(X)` is unipotent when `X` is unipotent in either ambient set | P: `rootSubsetGroupExistence` |
| `GS.StandardParabolicRootSubsetGroupStatement` | In either ambient set, minimal groups for the standard triple equal the existing parabolic, Levi and radical functors on all tests, and the generated Weyl subgroup equals the standard Levi Weyl subgroup | P: `standardParabolicRootSubsetGroup` |
| `GS.ClosedRootSubsetGroupIntersectionStatement` | In all relative roots, closed `S` and `X` with convex overlap satisfy `G(S) ∩ G(X) = G(S ∩ X)` on reduced test schemes ([7] 3.22(b)) | F: false by the paper counterexample of the [erratum note](../errata/borel-tits-1965-closed-root-intersection.md) |
| `GS.ConvexRootSubsetGroupIntersectionStatement` | In the indivisible roots, convex `S` and `X` satisfy `G(S) ∩ G(X) = G(S ∩ X)` on reduced test schemes (V.4.2(i)) | P: `convexRootSubsetGroupIntersection` |
| `GS.UnipotentRootSubsetGroupIntersectionStatement` | In all relative roots, closed `S` and unipotent `X` satisfy `G(S) ∩ U(X) = U(S ∩ X)` on reduced test schemes ([7] 3.22(c), corrected V.4.2(ii); see I5) | P: `unipotentRootSubsetGroupIntersection` |

The three intersection targets quantify over supplied minimal closed
representatives; their existence is the separate statement
`GS.RootSubsetGroupExistenceStatement`, now proved. The proofs are in the
seventh-update table at the top of this note. Because the 3.22(b) target is
false, the nine-part conjunction `GS.ClosedRootSubsetStatements` is not
provable. The V.4.2
conjunction is instead `GS.RenardClosedRootSubsetStatements`, the
conjunction of the other eight. Its proof
`renardClosedRootSubsets` is in the Library; see the ninth-update table at the top of this note.

## V.5 Compact subgroups (122–129 / 128–135)

The section refers to [14] (Bruhat–Tits).

| Item | Lean | Status |
| --- | --- | --- |
| V.5.1 Theorem: `K_0` with (1)–(5) | `SC.IsCompactOpenMaximal`, `SC.SpecialCompactProperties`, `SC.SpecialLeviInheritance`, `RPF.FiniteCartanCovering`; predicates `SC.HasParabolicFactorization`, `SC.HasWeylRepresentatives`. Existence: `SC.JointSpecialCompactBasisExistenceStatement` puts the special compact properties, standard-Levi inheritance, ambient and Levi Iwasawa products, Cartan comparisons and the V.5.2 basis at one apartment point. For every valid corrected KP assignment: `SC.AvailableSimultaneousStandardBasisStatement` and `Langlands.BruhatTits.Iwasawa.AvailableIwasawaStatement` | P, for valid corrected KP data, of these parts: `availableSimultaneousStandardBasis` (special compact properties, Levi inheritance and simultaneous basis at every special vertex) and `Iwasawa.availableIwasawa` (both product orders and compact-open maximality). S for unconditional existence: `JointSpecialCompactBasisExistenceStatement`. The published implication `SC.jointSpecialCompactBasisExistence_of_availability_and_basis` derives it from `AvailableSimultaneousStandardBasisStatement`, now proved, and `Langlands.Geometry.Building.BruhatTitsAvailabilityStatement` (some corrected KP assignment is valid), which is unproved (the Library derives it from `GroupAxiomsExistenceStatement` by `bruhatTitsAvailabilityReduction`). Library results that prove Waldspurger consequences take these properties as hypotheses; they are not proofs of the Theorem |
| V.5.1 Corollary: `G/P` compact | `RP.ArbitraryParabolicQuotientCompactStatement` | P: `arbitraryParabolicQuotientCompact` |
| V.5.1 Corollary: every parabolic is `K_0`-conjugate to a standard one | `Langlands.BruhatTits.SpecialCompactParabolicConjugacyStatement` (hypothesis: property (1) of the Theorem, `G(F) = P_∅(F) K = K P_∅(F)`, for any subgroup `K` over any field) | P: `specialCompactParabolicConjugacy` ([proof](../../Langlands/BruhatTits/Parabolic/SpecialCompactConjugacyProof.md)). For an actual `K_0`, property (1) comes from the Theorem row above |
| V.5.2 Theorem ([24] 2.1) | `SC.AvailableSimultaneousStandardBasisStatement` (its third conjunct, `SC.SimultaneousStandardBasisAt` at every special vertex); `RP.PresentationConeContractionStatement` | P for valid corrected KP data: `availableSimultaneousStandardBasis`; existence of such data is the open `BruhatTitsAvailabilityStatement` (see the V.5.1 Theorem row). P: `presentationConeContraction` (the contraction parts on root presentations) |
| V.5.3 `H_0`, the two Lemmas, the Corollary, the finiteness Lemma in module form, the Theorem and the Remark | `Langlands.Hecke.IwahoriHeckeDecompositionStatement` | P: `Langlands.Hecke.iwahoriHeckeDecomposition`, verified below. Renard writes that `A` is generated by the `a_z`, `z ∈ C_∅`; the statement uses the dominant generators `z ∈ C_∅^+`, which is what the second Lemma and all later uses concern (see the statement's [Markdown](../../Langlands/Representation/Hecke/IwahoriHeckeDecompositionStatement.md), "Formal choices") |
| V.5.3 finiteness Lemma for the generated subalgebra `M`: "L'algèbre `M` est un `A`-module de type fini" | the `Langlands.Hecke.IwahoriHeckeSubalgebraFinitenessStatement` ([statement and scope](../../Langlands/Representation/Hecke/IwahoriHeckeSubalgebraFinitenessStatement.md)). It keeps the data of `IwahoriHeckeDecompositionStatement` and adds one hypothesis (P): every `t ∈ C̃_∅^+` satisfies the V.5.2 (ii) clauses for the minimal standard parabolic (`t` contracts `K ∩ N_∅`, `t⁻¹` contracts `K ∩ N̄_∅`, and `t` normalizes `K ∩ M_∅`). Let `A` and `M` be the unital subalgebras generated by the `a_z`, `z ∈ C_∅^+`, and by the `a_t`, `t ∈ C̃_∅^+`. The statement asserts `A ≤ M` and `M = ∑ₖ A D_k` for finitely many `D_k ∈ M` | P: `Langlands.Hecke.iwahoriHeckeSubalgebraFiniteness` ([proof](../../Langlands/Representation/Hecke/IwahoriHeckeSubalgebraFinitenessProof.md)) (statement: ninth update; proof: eleventh). F for the Lemma without (P): the `Langlands.Hecke.RenardIwahoriHeckeSubalgebraFinitenessStatement` ([statement and scope](../../Langlands/Representation/Hecke/RenardIwahoriHeckeSubalgebraFinitenessStatement.md)) states it for Renard's chamber-compatible transversal (V.3.23, `C̃_∅^+ = C_∅^+ F_∅`), with `A` generated by the `a_z`, `z ∈ C_∅^+` (a documented correction of the printed `z ∈ C_∅`), and with `M` generated by the `a_{zf}`, `z ∈ C_∅^+`, `f ∈ F_∅`. It is false in general by the paper counterexample, the [ramified `U(1,1)` example](v53-subalgebra-finiteness-counterexample.md) (I6). The example refutes the Lean proposition whenever a building assignment is available for that group, which the Library does not prove; no Lean proof of the negation is published. The Markdown correction in the Library records this without changing the Lean proposition (20 November follow-up). (Statement: tenth update; counterexample: eleventh; gap 4.) The (P) statement's Markdown argues that (P) holds when `G` is split; this is not formalized. The Markdown of the module-form statement in the row above still lists the unconditional assertion as an outstanding source obligation ("Not stated"); by I6 it is false in general. The generated subalgebra can be larger than the module span (`G_m` over `ℚ_3`, `K = 1 + 3ℤ_3`, `F_0 = {-1}`: the span is `Aε` and the algebra is `A ⊕ Aε`), and the source proof treats only products `a_{z₁} a_{z₂ f}` |
| V.5.4 Proposition: `G` unimodular | `RPF.RationalReductiveUnimodularityStatement` | P: `rationalReductiveUnimodularity` |
| V.5.4 Lemma: `δ_{P\G}(m) = δ_G(m)/δ_P(m) = δ_P(m)^{-1} = δ_N(m)^{-1} = δ_{N̄}(m)` on `M`, and the root-product formula on `A` | `RPF.RationalParabolicModulusStatement`, `RPF.RationalOppositeHaarReciprocityStatement`, `RPF.DynamicUnipotentHaarDeterminantStatement`, `GS.DynamicAdjointDeterminantFormulaStatement` and `GS.Dynamic.AdjointDeterminantTorusRestrictionStatement` give the modular character, the opposite-radical reciprocity and the determinant with its full weight multiplicities | C: the proved comparisons use the inverse of Renard's `δ_P` as Mathlib's `modularCharacter`. The displayed grouping `m_γ + 2m_{2γ}` uses the minimal parabolic. For arbitrary standard `P`, the all-weight determinant keeps the contributions of higher multiples, as in the split `G_2` example in the [torus restriction statement](../../Langlands/GroupScheme/Dynamic/AdjointDeterminantTorusRestrictionStatement.md) |
| V.5.5 Proposition (127 / 133): nearest point on the closure of an open cone `C` and its characterizations (i)–(iii); Corollary (128 / 134): the decomposition along a basis and its dual basis | `Langlands.Renard.ConeProjectionStatements`, in a corrected formulation: `C` is a nonempty convex open cone, and the equivalence with (iii) is asserted only for `C ≠ E` (for `C = E` the strict dual cone `Č` is empty and (iii) fails, although the projection is `v` itself). The Corollary has no extra hypothesis | P: `coneProjectionStatements`. See source issue I3 |
| V.5.5, display before the Corollary (128 / 134): for the cone of the Corollary, `Č = {∑ sᵢ αᵢ, sᵢ > 0}` | not stated (the statement's Markdown explains why) | Source issue I3: false as printed |
| V.5.5 end: proof of V.3.18 | `GS.langlandsCombinatorialDecomposition` | P. The formal proof follows a different route: it uses the V.5.5 Corollary only for existence, and proves uniqueness and the three projection characterizations from variational inequalities (see the [proof Markdown](../../Langlands/GroupScheme/Rational/LanglandsDecompositionProof.md)) |

### Verified V.5.3 module-form proof

The [proof and explanation](../../Langlands/Representation/Hecke/IwahoriHeckeDecompositionProof.md)
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

The proof first appeared in the Library at commit `cc5aa77fa8dbdc6e723091c7b710ab0d81162c4e`.
It was checked as a proof by a Lake build against the exact target
`Langlands.Hecke.IwahoriHeckeDecompositionStatement`, with the statement and its
inputs unchanged. At the Library
commit used for this update, the proof pair and both helper pairs
(`IwahoriHeckeCore`, `MassIndicatorProducts`) match the bytes recorded when the proof was checked.
This evidence supplies proof coverage for that exact conditional statement,
not whole-section or whole-book completion.

## Remarks and source issues

- **R1. V.4.8, `w · P = P̄′` (printed p.122 / PDF p.128).** The rendered page has the
  overline; text extraction loses it. Without it the assertion fails: in `GL_2` with `M` the
  diagonal torus and `w = s`, `s · B` is the lower triangular Borel subgroup. The published
  `GS.StandardMaximalLeviWeylStatement` states the version with the overline, and
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
  `S = ⊔ C^{++}_{A_L}/C_{A_G}`. The public `LeviConePartitionStatement`
  states the correction modulo `⁰A_M` for actual split components (V.3.21.1 row,
  eleventh update). In the image modulo `⁰A_M`, the class of `diag(1, u)` is
  the class of the identity, which lies in the piece of `Q = G`. Its exact proof
  `leviConePartition` is in the Library (20 November follow-up).
- **I2. V.3.24 (printed p.117 / PDF p.123).** The claim `S = C^+_∅/C_{A_G} ≅ ℕ^d` with
  `d = |Δ_∅|` is false in general. The published
  [IwahoriHeckeDecompositionStatement](../../Langlands/Representation/Hecke/IwahoriHeckeDecompositionStatement.md)
  records this source issue: for the diagonal torus of `SL_3`, `C^+_∅` in
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
  the definition of `Δ(P)` in V.3.14.

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
  by the published statement module, not proved as a Lean counterexample here.

  A second correction, recorded by the seventh update, concerns the more
  general Borel–Tits 3.22(b). The published module states it in all relative
  roots as `ClosedRootSubsetGroupIntersectionStatement`. Its Markdown cited it
  as a source of (i) until the correction recorded by the eighth update.
  That statement is false. The published
  [erratum note](../errata/borel-tits-1965-closed-root-intersection.md)
  gives a paper counterexample in split `SO₈` over `ℂ`. The
  subsets `S = {±ε₁ ± ε₂, ±ε₃ ± ε₄}` and `X = {±ε₁ ± ε₃, ±ε₂ ± ε₄}`, of type
  `A₁⁴`, are closed and disjoint, so `S ∩ X` is convex. The element `J`
  exchanging each `e_r` with `f_r` lies in `G(S) ∩ G(X)` but not in
  `G(∅) = T`. Neither subset is convex, so the counterexample does not affect
  (i), which assumes both subsets convex and is proved as
  `convexRootSubsetGroupIntersection`. The V.4.2 conjunction
  `RenardClosedRootSubsetStatements` omits the false statement.

- **I6. V.5.3, the finiteness Lemma for the generated subalgebra (printed pp.124–125 /
  PDF pp.130–131).** "L'algèbre `M` est un `A`-module de type fini" is false in general,
  even for Renard's chamber-compatible transversal and with the dominant generators of
  `A`. The published
  [ramified `U(1,1)` example](v53-subalgebra-finiteness-counterexample.md) (checked on paper) takes the quasi-split `U(1,1)` of `ℚ₂(ζ₈)/ℚ₂(√2)`, the
  chamber-compatible transversal `{1, f}`, and a subgroup `K` built from the proper order
  `ℤ₂ + 2√2 ℤ₂` of `𝒪_F`. This `K` is normal in the special maximal compact subgroup and
  satisfies the Iwahori decompositions and the V.5.2 clauses for both standard
  parabolics. For every `z ∈ C_∅^+`, `a_f a_z = (a_{fz} + a_{x₁fz})/2` with a fixed
  unipotent `x₁ ∈ K₀`, so `a_{x₁fz}` lies in `M`. Given finitely many `D_k`, a tree
  argument gives a `z` for which `a_{x₁fz}` lies outside `∑ₖ A D_k`. The source proof
  treats only products `a_{z₁} a_{z₂ f}`, where the contraction properties of `z₁` and
  `z₂` suffice; in `a_f a_z` the element `f` would have to contract `K ∩ N_∅`, and it
  does not. The
  example refutes the `RenardIwahoriHeckeSubalgebraFinitenessStatement` whenever a
  building assignment is available for this group, which the Library does not prove. No
  Lean proof of the negation exists. The module form, proved by
  `iwahoriHeckeDecomposition`, and the conditional statement under (P), proved by
  `iwahoriHeckeSubalgebraFiniteness`, are unaffected. This issue was recorded by the
  eleventh update.

## Genuine gaps of Chapter V

1. V.3.14–V.3.16: no longer a gap. The constructions are published in the `ParabolicChamberStatements`, where the intersection formulas, convexity and
   both cell decompositions are proved. The ambient assertions
   `ParabolicChamberLinearAlgebraStatement` are proved by
   `parabolicChamberLinearAlgebra`, the split-component comparisons
   `ParabolicSplitComponentChamberStatement` by `parabolicSplitComponentChamber`,
   and their conjunction `ParabolicChamberStatement` by
   `parabolicChamber`, as recorded by the seventh update.
   V.3.18 is no longer a gap; `langlandsCombinatorialDecomposition`
   proves it.
2. V.3.6–V.3.13 realization: no longer a gap. The compatible-diagram
   decompositions for arbitrary Levis are proved (`renardLeviCentralDecomposition`). The four
   real-coroot, real-basis, fundamental-weight and corrected standard-Levi
   statements of the module `RelativeRealCorootStatements` are proved,
   and so is their conjunction, by
   `relativeRealCorootLinearAlgebra`, which pairs the four proofs.
   The geometric inputs are no longer a statement gap. The public
   `LeviCentralCompatibilityStatements` (ninth update) states the
   split-component inclusion `A_L ⊂ A_M` for rational Levi factors `M ⊆ L`,
   which with `L = G` realizes the compatible diagram for every rational Levi
   factor, and the identification of the real characters of a standard Levi
   with the ambient coroot annihilator. The cocharacter side is proved by
   `standardLeviCentralDirections`, and the comparison through a compatible
   split component by `langlandsCharacterRestriction`. The two new statements
   are proved by `leviSplitComponentInclusion` and
   `standardLeviCharacterAnnihilator`, as recorded by the tenth update.
   Their conjunction is proved by `leviCentralCompatibility`,
   as recorded by the eleventh update.
3. V.5.1 Corollary, `K_0`-conjugacy of every parabolic to a standard one: no longer a gap.
   `specialCompactParabolicConjugacy` proves the published statement for every subgroup
   with property (1). The unconditional existence of `K_0` (V.5.1 Theorem row) still
   depends on the unproved `BruhatTitsAvailabilityStatement`.
4. V.5.3, the finiteness Lemma for the generated subalgebra `M`, without additional
   hypotheses: no longer a gap, since the Lemma is false in general (I6). The
   published `IwahoriHeckeDecompositionStatement` states the module form, which is all
   that the source proof covers, and `iwahoriHeckeDecomposition` proves it. The public `IwahoriHeckeSubalgebraFinitenessStatement` states the Lemma under the added
   hypothesis (P) of the V.5.3 subalgebra row (ninth update), and
   `iwahoriHeckeSubalgebraFiniteness` proves it (eleventh update). The
   public `RenardIwahoriHeckeSubalgebraFinitenessStatement`
   (tenth update) states the Lemma without (P), for Renard's chamber-compatible
   transversal and with the corrected dominant generators of `A` (see the V.5.3 row). Its
   Markdown argues, without formalization, that the Lemma follows from a contraction
   condition (C) on the dominant elements `t` of `Z(F)`, and that (C) holds for the
   powers `t^k`, `k = [Λ(Z) : Λ(S)]`, and for every dominant `t` when `Λ(Z) = Λ(S)`. The
   published [ramified `U(1,1)` example](v53-subalgebra-finiteness-counterexample.md)
   has `Λ(Z)/Λ(S) = ℤ/2`, fails (C) at the transversal element `f`, and refutes the Lemma
   (I6). It refutes the Lean statement whenever a building assignment is available for
   that group, which the Library does not prove. The statement's Markdown also gives
   `Res_{E/F} SL₃`, `E/F` ramified, as a group with no chamber-compatible transversal,
   for which the statement is vacuous. The Markdown correction
   is in the Library (20 November follow-up),
   and the Lean statement is unchanged. No proof obligation remains for this Lemma.
5. V.3.20: no longer a gap. The complex-torus structure of `X(M)` recovered
   through the exponential, and `Im X(M)` as a real submanifold of `X(M)`, are stated by
   the public `RationalUnramifiedComplexTorusStatement` (eighth update). Its
   four component statements are proved (tenth update), and so is
   their conjunction, by `rationalUnramifiedComplexTorus`
   (eleventh update). The tensor identification,
   the pure-tensor formula and the compact imaginary quotient are proved (rows above).
6. Recalled assertions formerly with remaining proofs, all now proved: `P(M)` finite (V.3.1),
   `N_G(A_M) = N_G(M)` on rational points and `Z_G(A_M) = M` for arbitrary
   rational Levis (V.3.5) are stated in the public
   `LeviSplitComponentRecallStatements`. They are proved by
   `leviParabolicFinite`, `leviSplitComponentNormalizer` and
   `leviSplitComponentCentralizer`
   (eighth update). Their conjunction is proved by
   `leviSplitComponentRecall` (tenth update). The table of the Levi recall
   statements above gives their scopes. The general
   closed-subset assertions of V.4.2 are stated by the public
   `ClosedRootSubsetStatements`, with the ambient-root and reduced-test
   distinctions and source correction I5 above. Eight of its nine targets
   are proved. The ninth, Borel–Tits
   3.22(b), is false (I5). The V.4.2
   conjunction of the eight, `RenardClosedRootSubsetStatements`, is proved by
   `renardClosedRootSubsets` (ninth update). No V.4.2
   proof obligation remains; the false 3.22(b) form is excluded (I5).
   The maximal anisotropic subtorus and almost
   direct product (V.2.2 Remark 2), formerly listed here, are proved by
   `torusAnisotropicPart`. The split-component assertions of
   V.3.1 and the first sentence of V.3.2 are proved (fourth-update table), and their
   conjunction by `parabolicSplitComponents`.
7. V.3.24: finite generation after transport to the actual split-central
   nonnegative uniformizer quotient: no longer a gap. The public
   `CocharacterUniformizer.ConeQuotientFiniteGenerationStatement` states it, and
   `CocharacterUniformizer.coneQuotientFiniteGeneration` proves it, as
   recorded by the tenth update.
   The integral and actual quotient constructions, integral strict-face
   laws, four comparison statements, finite-generation statement, actual-piece
   definition and actual partition statement are now in the Library. The Library
   has exact proofs of the integral central-image equality, group quotient
   comparison and integral finite generation, and of the strict-image and
   nonnegative comparisons, verified above. It also has an exact proof of the
   actual strict-piece partition,
   `CocharacterUniformizer.standardLeviStrictQuotientPartition`, verified on 18 November. The
   finite-generation transport is separate from this partition. Neither
   result asserts freeness: the general freeness assertion is false (I2).

8. V.3.15/V.3.21 topology on the actual standard-Levi split component: the
   nonemptiness, openness, closedness and topological closure assertion
   `LeviChamberTopologyStatement` is proved by the public
   `leviChamberTopology`.
   This focused gap is closed. The distinct source issue (V.3.21.1) and
   actual lattice-partition obligations remain as recorded above.

## Proofs of the Chapter V statements

`Langlands.BruhatTits.Cartan.RenardLeviCones.LeviChamberTopologyStatement`
is proved by `leviChamberTopology`, with the exact pair verified above.

`Langlands.BruhatTits.Cartan.RenardLeviCones.LeviConePartitionStatement`, the
corrected (V.3.21.1), is proved by `leviConePartition`, with the evidence in the
20 November follow-up.

The three Levi split-component recall statements are proved by
`leviSplitComponentCentralizer`, `leviSplitComponentNormalizer` and
`leviParabolicFinite`, as recorded by the eighth update, and their conjunction by
`leviSplitComponentRecall`, as recorded by the tenth update.

The statements of the V.2.3, V.2.5 and V.2.6 module (unimodularity of `⁰G`,
`⁰A₁ = A₁ ∩ ⁰A₂`, compact centre), of the V.4.3.3 and V.4.8 module, and the
`SplitComponentKernelStatement` (V.2.6 Lemma) and `FullLatticeRepresentativeStatement`
(V.3.23): at Library `c0debd6f4dd02fdd68d70811cf610906b945a962` all seven
are proved (see the table at the top of this note).

The compatible-component V.3.6 statement `GS.RenardLeviCentralDecompositionStatement`
is proved by `renardLeviCentralDecomposition`. Its arbitrary-field scope, literal
restriction kernel and actual pairing annihilator are retained. The four component
statements of the real-coroot module are proved (third-update table); their
conjunction is proved by `relativeRealCorootLinearAlgebra`. The five component statements
of the parabolic split-component module (V.3.1–V.3.2) are proved (fourth-update table);
their conjunction is proved by `parabolicSplitComponents`. The two statements of the chamber module
(V.3.14–V.3.16) are proved by `parabolicChamberLinearAlgebra` and
`parabolicSplitComponentChamber`, and their conjunction by
`parabolicChamber`. The four statements of the V.3.20 module are proved
(tenth update), and their conjunction by `rationalUnramifiedComplexTorus`. Eight statements
of the closed-root-subset module (V.4.2) are proved, and so is their conjunction
`RenardClosedRootSubsetStatements`, by `renardClosedRootSubsets`; the ninth statement is false (I5).
The two statements of the V.3.6/V.3.13 module `LeviCentralCompatibilityStatements`
are proved by `leviSplitComponentInclusion` and `standardLeviCharacterAnnihilator`, and their
conjunction by `leviCentralCompatibility`. Of the two V.5.3
subalgebra statements, the one under (P) is proved by `iwahoriHeckeSubalgebraFiniteness`.
The one without (P) is false in general (I6). These outcomes are recorded by the
eleventh update. For V.3.24, `simpleRootSplitCentralImage`,
`CocharacterUniformizer.quotientComparison` and
`cocharacterConeFiniteGeneration` are in the Library,
with the exact pairs verified above.
The anisotropic-part statement is proved by `torusAnisotropicPart`.
`CocharacterUniformizer.standardLeviStrictImage`
and `CocharacterUniformizer.coneQuotientComparison` prove the exact strict-image and
nonnegative-comparison statements; their unchanged target
pairs and proof pairs are verified above.
`CocharacterUniformizer.standardLeviStrictQuotientPartition` proves the
actual strict-piece partition, verified above.
`CocharacterUniformizer.coneQuotientFiniteGeneration` proves the transported
finite-generation statement, as recorded by the tenth update. Source issue I2 remains separate.
