# KP Bundles A–F: source ledger and construction boundaries

This source ledger covers Bundle A, initial Bundle B targets and Bundles C–F of the standing KP program
`f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703`. It records mathematical source targets
and their verified formal status. Both parts of Theorem 1.1.15, Corollary
1.1.19 and Proposition 1.1.20 have independently accepted, published proofs,
recorded below in three of the
fifty-two rows. The separately verified metric fixed-point aggregate assembles
six published component proofs and adds no source row. The separately verified
finite separable-unramified prerequisite is recorded below without adding a KP
source row. Propositions 4.2.7, 4.2.24 and 4.4.4, both assertions of
Theorem 4.2.10, Corollary 4.2.14, corrected Corollary 4.4.5, Theorem 5.3.3,
replaced Lemma 5.3.5, Lemma 6.7.1, Section 6.7.2 and Corollary 7.4.9 have
published conditional formalizations: they are proved on supplied building
data, whose general construction is open. Theorem
5.2.1 with corrected (5.2.2), Theorem 5.3.4 and corrected Proposition
13.5.2 are proved on available Bruhat–Tits data in the sense of
corrected Definition 4.1.26, which is equally conditional. Section
13.2.6 is proved for supplied integral models
and reductive quotients, together with its inflation and compact-induction
consumer; the congruence-basis premise of its local-field corollary is
proved, and an intertwining and double-coset theorem for compact
induction is proved and specialized to its depth-zero compact
inductions. On the same supplied data with finite residue
field, the reductive quotient has finitely many points; over a Henselian
base their number is the index of the radical preimage in the integral
points, and over a local field the radical preimage is a compact open
subgroup of the rational points. Standard models of the split groups
`G_m`, `G_m^I`, `GL_N`, `Sp_{2l}` and `SL_n` over the integers of a
nonarchimedean local field give actual instances of these data, with
proved reductive quotients and indices; they are not identified with
parahoric models at a building point. Corrected Theorem 7.8.1
and the `G(F)^0` branch of Theorem 7.5.3 have independently accepted,
published statements on supplied building data, and part (4) of Theorem
7.8.1 is proved; six of the seven inputs of the published reduction to the
`G(F)^0` branch of Theorem 7.5.3 are proved. Proposition 13.2.5 is
proved on supplied data: its opening sentence at finite depths and parts
(1)–(6), part (3) with indivisible-root blocks, parts (5) and (6) at
positive depth for the parabolic subgroups containing the split torus,
and parts (1), (2) and (4) with an extra double-root premise that their
source proofs use. An unformalized paper counterexample shows that the
supplied-filtration statements of parts (1), (2) and (4) without that
premise are false.
Section 9.2.1 (a Galois-fixed point
of a stable apartment) is proved for supplied Galois-stable apartment
data. Proposition 9.3.4, Theorem 9.6.5 and Lemma 9.8.1
have published statements, and Theorem 9.6.5 also a proved reduction to
five statements, two of which are proved; published implications reduce
its descent input to three unproved statements. Published theorems also
reduce both existence statements of Lemma 9.8.1 to two unproved
statements: the group properties of the Moy–Prasad groups over the
maximal unramified extension and the existence of a comparison of the
building data with that extension. A further published theorem
reduces the second to special-torus existence, the descent input of
Theorem 9.6.5 and four field statements. Lemma 11.5.2, Proposition
11.5.4 and Corollaries 11.7.5 and 11.7.6 have published statements for
the rational Kottwitz map selected by its characterizing property, the
chamber clause of Corollary 11.7.5 on supplied building data. Published
theorems reduce Lemma 11.5.2, Proposition 11.5.4 and Corollary 11.7.5
to focused statements, one of which is proved. Corrected
Definition 4.1.26 has a
published definition, the corrected Definition 4.1.26 part of Theorem 9.2.7
a published existence statement, reduced by two proved implications to
four focused statements, and Definition 6.6.1 a partial published
definition. Theorems 8.3.2, 8.3.13, 8.4.10 and 8.4.19 and Corollary
8.4.12 have partial published statements on supplied building data, for
models over the integers of the maximal unramified extension or, for
facets, over the integers of a nonarchimedean local field; the full
model of Theorem 8.3.2 also has a proved construction from five
statements, two of which are proved. The other fifteen rows retain
empty formal-status and evidence fields. The remaining Bundle B
targets still require public ledger entries. Private source audits and
unsubmitted drafts are not publication evidence.

## Refresh of 8 November 2026

The task was carried over to a new TaskHub instance on 8 November 2026. The
Library base of that instance is commit
`c4a16df784376405a45b60df82583e8c26d8a4e3`. Acceptance artifact IDs of the
previous instance cannot be fetched in the new one. The six rows updated in
this refresh (Propositions 4.2.7 and 4.4.4, Theorem 4.2.10, Corollary 4.4.5,
Definition 4.1.26 and Theorem 7.5.3) therefore cite that commit as their
publication evidence and leave `acceptance_artifact_ids` empty. Each
declaration was located in the modules listed in its row and inspected with
`lean_check` in environment `bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`. The
inspection IDs are in the `axiom_reports`; every reported axiom set is
`propext`, `Classical.choice`, `Quot.sound`. Each row's last `hypotheses`
entry, beginning "Recorded Lean scope", states the Lean hypotheses and their
differences from the source.

`conditional` means the following here. The theorem is proved on supplied
`ValuationBuildingData` or `ParahoricBuildingData` with the listed axiom
predicates as hypotheses, or (for Proposition 4.4.4) for abstract
group-action data. It stays conditional until the data and witnesses are
constructed. For the Section 4.2 rows that construction is the published
target `RootValuationBuildingConstructionStatement`, whose proof task is
`00b6788c-23c3-4b22-88f5-41fdbc6d3654`. The source and correction fields
of the updated rows are unchanged; they were compared with the originals
afterwards, as described below.

A second pass on the same day recorded five Bundle C rows on the same
terms. Theorem 5.2.1, Theorem 5.3.3, Theorem 5.3.4 and replaced Lemma 5.3.5
are recorded as `statement`. Their Lean targets are unproved Prop-valued
statements. Those for 5.2.1 and 5.3.4 assume the full corrected Definition
4.1.26 through `KPBuildingAssignment.IsAvailableFor`. Those for 5.3.3 and
5.3.5 assume only the Chapter 7 apartment axioms on supplied
`ParahoricBuildingData`, together with the Chapter 5 Henselian and
perfect-residue hypotheses. Definition 6.6.1 is recorded as a partial
`definition`: `Wtilde^0` and `W_aff` are formalized, `Wtilde^1` is not.
The inspection IDs are in the `axiom_reports`, with the same axiom set
as above.

Both passes were first prepared while the original PDFs could not be
opened in this instance. On 9 November 2026 they were readable again, with
the SHA-256 fingerprints recorded in the rows, and the source and correction
fields of all eleven updated rows were compared with the originals: book
PDF pages 196, 199–204, 213–215, 217–222, 261–262, 266–267 and 291–292,
and corrections PDF pages 1–2, 24–25, 27–30, 33 and 35. They agree with
the originals. The only change is that the Theorem 5.3.4 locator was
narrowed to the page carrying the theorem and its proof. The same day the
Theorem 7.5.3 row was corrected: three of the eight fields of
`AffineIwahoriTitsInputs` have published proofs and are no longer
described as unproved.

A third pass on 9 November 2026 records Corollary 4.2.14 as `statement`.
Its target `BoundedSubgroupFixedPointStatement` was accepted in this
instance as artifact `32a5231a-64e5-47b2-abb5-08c7ee214f7c` and published
in Library commit `3f0bcbd4638c9c42befdc9f7e1578d62fde2c959`, so the row
cites both. It assumes the same seven axiom predicates as the Proposition
4.2.7 row and covers both assertions of the corollary. The row's source and
correction fields are unchanged and agree with the originals, compared on
9 November 2026 at book PDF pages 101 (Definition 2.2.1) and 204 and
corrections PDF pages 1–2 and 28–29. Its unproved target has the
published proof task
`a20a7c6a-18e6-430e-9ebd-f4e7046e075d`.

A fourth pass on 9 November 2026 records Theorem 5.3.3 as `conditional`.
The theorem `iwasawaDecomposition` proves `IwasawaDecompositionStatement`
on supplied `ParahoricBuildingData` satisfying the Chapter 7 apartment
axioms. It was accepted as artifact
`937be117-c6a0-42d8-be70-cd5c630935ac` and first appears in Library commit
`0646cc6120e56febaf6f88f723f3b147d0e23d59`. The same pass records the
proof task `5e9b97bd-7a9c-43fb-bb8f-b017b7028adc` for the Theorem 5.3.4
target and the conditional assemblies now available for replaced Lemma
5.3.5. It also replaces the remarks in the Theorem 5.3.3 and Theorem 7.8.1 rows that
`standardUnipotentPoints` had not been compared with `Dynamic.unipotent`.
The Library now proves this equality for every cocharacter of a maximal split
torus of a connected reductive group; no genericity hypothesis is needed.

The fourth pass, completed on 10 November 2026, also records two statements
accepted in this instance and first published in Library commit
`230ec08a058832bd6941fa887c30897e4826429b`. Their rows cite both.
`FacetClosureUnionClosedStatement` (artifact
`7c30292c-a01f-472c-b967-5859043e2755`) is the second assertion of Theorem
4.2.10, under the hypotheses of the published completeness theorem. Its
proof task is `cd045e44-eb03-481f-aabf-0e086965dd25`. The Theorem 4.2.10
row stays `conditional`, a status that refers to its first assertion.
`BruhatTitsAvailabilityStatement` (artifact
`f81d0fe7-8c61-4e05-bfcc-e7d6b14a3f04`) states the corrected Definition
4.1.26 part of Theorem 9.2.7: some `KPBuildingAssignment` satisfies
`IsValid`. The Theorem 9.2.7 row therefore becomes `statement`. That
statement omits Axiom 4.1.27 and asserts the existence of some data
rather than the source's descended construction, so it is not the full
certificate. Its proof belongs to this program and has no proof task yet.
The same day the proof task `14dc145a-14d4-47d6-97a6-d89ea0c558ab` was
published for the Theorem 5.2.1 target `AvailableCartanStatement`.
The source and correction fields of both rows are unchanged. On 10
November 2026 their statement locators were compared again with book PDF
pages 202 and 360 and corrections PDF page 27; they agree. The statements'
independent reviewers read the originals at book PDF pages 196–197, 199,
202–203, 230, 354 and 360 and corrections PDF pages 1 and 27–29.

A fifth pass on 10 November 2026 records proofs first published in Library
commit `e449cde988d4e97ab280b8d4d11262887ccc26e0`; each row cites its
acceptance artifact and that commit. Corollary 4.2.14 becomes
`conditional`: `boundedSubgroupFixedPoint` (artifact
`48dd155d-28ec-4a80-9278-241f507a6013`) proves its statement. The second
assertion of Theorem 4.2.10 is proved by `facetClosureUnionClosed`
(artifact `b4a3ec65-43a1-4685-b99b-38916a8ba603`), so both assertions of
that row are now proved on supplied data. Theorem 5.3.4 becomes
`conditional`: `availableIwasawa` (artifact
`42bb1c08-a7ac-49f5-a197-dc1d5707a42e`) proves `AvailableIwasawaStatement`
under `IsAvailableFor`, while `IwasawaExistenceStatement` stays unproved.
Corollary 7.4.9 becomes `conditional`:
`ParahoricBuildingData.chamberIwahoriDecomposition` (artifact
`4493a3f5-fe76-417d-8239-cbb2e5149465`) proves its statement for every
supplied datum. `unipotentIwahoriDoubleCoset` (artifact
`dce35461-bb3e-429c-9068-cf0465a14731`) proves part (4) of Theorem 7.8.1.
That row stays `statement`, because parts (1)–(3) are unproved. The same
commit proves that `Z(F)^0` is normal in `N(F)` for every supplied datum
(`ParahoricBuildingData.normal_normalizerZero`). This updates the Definition
6.6.1 row and supplies both inputs of the published reduction for replaced
Lemma 5.3.5. That row stays `statement`, because no theorem of its exact type
is published. The Theorem 9.2.7 row also lists three statements of task
`7dc04fe2-f965-4f59-b63c-75f5012b3f64` that assume availability or validity,
with their proof tasks. Each new declaration was inspected with `lean_check`
at commit `e449cde9`; every reported axiom set is `propext`,
`Classical.choice`, `Quot.sound`. The source and correction fields of these
rows are unchanged.

A sixth pass on 10 November 2026 adds three rows, so the ledger now has
forty-eight. Proposition 4.2.24, Lemma 6.7.1 and Section 6.7.2 are
recorded as `statement`. Their targets
`ApartmentConjugacyFixingIntersectionStatement`,
`LeviApartmentRestrictionStatement` and
`LeviSpecialPointRestrictionStatement` were accepted in this instance as
artifacts `8a396dca-5fc1-4680-94bb-f07abc3a4749`,
`851e3550-d582-4076-a891-8d9b00badf3e` and
`d664e902-3b89-4fdd-b136-5b2f070a1844` and first published in Library
commit `d39b5aee822fe2ad1aadf07861ebd9a4c2df62a8`. Their proof tasks are
Tasks 5413, 5414 and 5415. The source and correction fields of the new
rows were compared on 10 November 2026 with book PDF pages 60–61,
207–208, 226, 230–232, 249 and 264–265 and corrections PDF pages 28–30
and 32. Theorem 5.2.1 becomes `conditional`: `availableCartan` (artifact
`c3a16a8e-fad7-484f-9e90-64f897f020eb`, first published in the same
commit) proves `AvailableCartanStatement` under `IsAvailableFor`; its
proof does not use the unproved Proposition 4.2.24. The Theorem 9.2.7
row now records how `BruhatTitsAvailabilityStatement` is split into six
statements first published in Library commit
`58a91d4ff65b8d6dcb8aa417bfc63399feb8b4af`, with their proof tasks. It
also records Task 4749's published reduction of
`RootValuationBuildingConstructionStatement` and
`ChapterSevenBuildingAxiomsStatement`, first published in Library commit
`8c11c93f98b439395e0e7da779c98bb27e24bd6d`. The Lemma 6.7.1 row names
`LeviApartmentAxiomsInheritanceStatement` from the same commit as a
consumer. The four declarations added to the rows' `lean_declarations`
were inspected with `lean_check` at commit `e7487341`; every reported
axiom set is `propext`, `Classical.choice`, `Quot.sound`. The source and
correction fields of the Theorem 5.2.1 and 9.2.7 rows are unchanged.

A seventh pass on 11 November 2026 updates two Bundle D and E rows.
Section 13.2.6 becomes `conditional`. The depth-zero reduction
`depthZeroQuotientEquiv` (artifact
`f3a39f0a-0b63-4218-a72a-b3958c3b3740`, first published in Library
commit `7047367a78583edbe335517824e30403414aa3f0`) and its inflation and
compact-induction consumer (artifact
`a6b89c9a-222a-4977-b85b-1983338fa594`, first published in Library
commit `7103f5282c4897716543f227940fdb2a0e12e70e`) are proved on
supplied `RelativeComponentModelData` and `SpecialFibreQuotientData`
whose projection is the represented fppf quotient by the unipotent
radical. Here `conditional` means that the row stays conditional until
the actual parahoric model, its radical and reductive quotient are
constructed and Corollary 8.4.12 identifies the radical-preimage kernel
with the Moy–Prasad group `P_{x,0+}`. The local-field corollary
additionally assumes the unproved
`CongruenceNeighborhoodBasisStatement`. The five declarations added to
the row were inspected with `lean_check` at commit `389dbc16`.

Proposition 13.2.5 becomes `statement`. Its target
`MoyPrasadFiltrationStatement` (artifact
`cdc002e4-4628-4026-91c9-c4add6280308`, first published in Library
commit `642008d6b3b837d8bd76de0cabcaff3db00088c0`) states separatedness,
bounded openness at finite real depths, and parts (1), (2) and (4) for
supplied `ParahoricBuildingData` and a supplied centralizer filtration
with explicit axioms; the Section 9.8 filtration is not constructed.
Parts (3), (5) and (6) remain unformalized, and the printed root-index
discrepancy of part (3) recorded below is unchanged. Each of its four
conjuncts has a proof task, listed in the row. Its six declarations were
inspected on a workspace at commit `389dbc16` holding the published
pair, byte-identical to commit `642008d6`. Every reported axiom set of
this pass is `propext`, `Classical.choice`, `Quot.sound`. The source and
correction fields of both rows are unchanged.

An eighth pass on 11 November 2026 adds four Bundle B rows for the
unramified descent of Chapter 9, so the ledger now has fifty-two rows.
All four are `statement`. Section 9.2.1 (a Galois-fixed point of a
stable apartment) and Proposition 9.3.4 record
`UnramifiedGaloisFixedApartmentStatement` and
`SpecialTorusExistenceStatement` (artifact
`528e1be2-9d8b-452b-ad68-e956bf9179ee`, first published in Library
commit `9bc92c384fa84da7ce5811a5979d408fb69d40b0`). Theorem 9.6.5
records Task 4749's `ValuationApartmentAxiomsExistenceStatement`
(artifact `e0b14a71-bc99-4ac1-b5b5-041d9f4ca3e6`, first published in
Library commit `58a91d4ff65b8d6dcb8aa417bfc63399feb8b4af`) and this
program's descent module (artifact
`cab86217-ea50-409b-9d4d-3440ee3e3a43`, first published in Library
commit `3c9b0579a8f2d36d16294ce48b465d1ec5aee273`). That module adds two
statements and their conjunction and proves
`valuationApartmentAxiomsExistenceReduction`, which derives
`ValuationApartmentAxiomsExistenceStatement` from five statements. None
of the five is proved yet, so the row stays `statement`. Lemma 9.8.1
records `CentralizerFiltrationExistenceStatement` (artifact
`fb1bc376-7e9b-41dd-b6e1-efa863d4f68b`, first published in Library
commit `3c9b0579a8f2d36d16294ce48b465d1ec5aee273`). The Section 9.2.1
row records the zero-section embedding into the enlarged building as
G(k)^1-equivariant, not G(k)-equivariant as printed; the Bundle B notes
explain the discrepancy. Each row lists its
proof tasks, and the Theorem 9.2.7 row points to the new rows. The pass
also adds part (3) of Proposition 13.2.5, with indivisible-root blocks,
to that row: `MoyPrasadProductStatement` and its product map (artifact
`38dd6045-a386-43d6-a804-1de56fa51d14`, first published in Library
commit `63d9b857523edf47443b7bf30844159e526d00b0`), with its proof task.
The row stays `statement`. The seventh pass's remark that parts (3), (5)
and (6) remain unformalized now applies to parts (5) and (6) only.

The source and correction fields of the new rows and of the part (3)
update were compared on 11 November 2026 with book PDF pages 162,
209–211, 278, 281, 283, 354, 356–357, 363–365, 394–398, 405–406 and 500 and
corrections PDF pages 33, 39–41 and 50. Eleven declarations were
inspected with `lean_check`: `SpecialTorusExistenceStatement` at commit
`3c9b0579`, the two part (3) declarations at commit `8964b41f`, the
others at commit `529b851c`. The inspected Lean files are byte-identical
to their first publications. Every reported axiom set is `propext`,
`Classical.choice`, `Quot.sound`.

A ninth pass on 12 November 2026 updates three rows and adds none.
Proposition 13.2.5 gains parts (5) and (6): `MoyPrasadLeviStatement` and
its two conjuncts (artifact `abed4e85-f69b-404f-ab1b-76a194d2d0d0`,
first published in Library commit
`6bff2655fd831aefb39f6688f904aa7410cb0f73`), stated at positive real
depth for the parabolic subgroups containing the split torus of the
data. The seventh pass's remark that parts (5) and (6) remain
unformalized no longer applies. The same row gains
`MoyPrasadDoubleRootStatement`, its two conjuncts and the predicate
`IsDoubleRootCommutatorFriendly` (artifact
`a10cf7b9-8244-4125-94c1-9eb4aa404e35`, first published in Library
commit `297a8ef0ba780a488196cf62285af3ded2e2baa6`). They restate parts
(1), (2) and (4) with an extra premise on the centralizer component of
commutators involving a double root. The source proofs of these parts
use that bound, but Definition 7.2.1 does not give it; the Bundle E
notes explain the gap. The Lemma 9.8.1 row gains the matching existence
statement. Both rows stay `statement` and list their new proof tasks.
The Theorem 9.2.7 row records that `ActualApartmentSplittingStatement`
and `AffineIwahoriTitsBuildingStatement`, two of the four inputs of the
published reduction to `RootValuationBuildingConstructionStatement`, are
proved; the row stays `statement`.

The source and correction fields of the Proposition 13.2.5 and Lemma
9.8.1 rows were compared on 11 November 2026 with book PDF pages 162,
264, 268, 270–273, 276–277, 283–284, 296, 302, 399–401, 405–406 and
499–500 and corrections PDF pages 33–36, 41 and 49–50. Ten declarations
were inspected with `lean_check`: `MoyPrasadLeviStatement` at commit
`4ed6d979`, its two conjuncts and the theorems
`actualApartmentSplitting` and `affineIwahoriTitsBuilding` at commit
`14c08c22`, and the five double-root declarations at commit `16c60abd`.
The inspected Lean files are byte-identical to their first publications.
Every reported axiom set is `propext`, `Classical.choice`, `Quot.sound`.

A tenth pass on 12 November 2026 updates three rows and adds none.
Section 13.2.6 stays `conditional`. Its local-field corollary
`localFieldDepthZeroInductionHomEquiv` no longer depends on an unproved
statement: `congruenceNeighborhoodBasis_proof` (Task 5447, artifact
`69074fc3-6f69-402f-a73b-084d3e30c551`, first published in Library
commit `ba77b83f98d4cbe92842b4645577633e0541fdab`) proves
`CongruenceNeighborhoodBasisStatement`, which also makes the integral
points of every supplied model compact. The seventh pass's remark that
the corollary assumes that statement no longer applies. The row also
gains `CompactInductionIntertwiningStatement` and its three conjuncts
(artifact `14c308d9-57df-4b0b-9b87-e08f078a61ae`, first published in
Library commit `79de65ce5fcd6dc5f182612988e1b529d49a63b4`), statements
after Vignéras 1996, I.8.5, that describe the maps between compactly
induced representations from an open subgroup by intertwining kernels
and by their values at double-coset representatives. They state the
intertwining and double-coset theorem that the row's consumer asked for;
their proofs are Tasks 5700, 5701 and 5702. Proposition 9.3.4 stays
`statement` and gains `SpecialTorusIntegralModelStatement` (artifact
`d4896ec2-435c-4b28-a7a0-52eb74b82756`, first published in Library
commit `ba77b83f98d4cbe92842b4645577633e0541fdab`), a derived statement
of the building input of its source proof, with proof Task 5707. Theorem
9.2.7 stays `statement`; its dependencies now record that two
conditional statements on available or valid data,
`ValidAssignmentTorusRebasingStatement` and
`AvailableSpecialVertexExistenceStatement`, are proved.

The source and correction fields of the Proposition 9.3.4 row were
compared on 12 November 2026 with book PDF pages 194, 317, 358–359, 363
and 687; the Vignéras locators of the Section 13.2.6 row were compared
with PDF pages 82–86 of that book. Seven declarations were inspected
with `lean_check`: the four intertwining statements at commit
`9951a27f`, `SpecialTorusIntegralModelStatement` and the theorem
`congruenceNeighborhoodBasis_proof` at commit `c5b9c2cf`, and the
theorem `availableSpecialVertexExistence` at commit `24a49431`. The
first six inspected Lean files are byte-identical to their first
publications. Every reported axiom set is `propext`, `Classical.choice`,
`Quot.sound`.

An eleventh pass on 13 November 2026 updates ten rows and adds none. The
Library had meanwhile advanced through commits
`ed924aef420de137b4cbaa3b063a3618afcd73fd`,
`17dd94ea3f677b20fb5ab95b285cbc3fd7cde03e` and
`8ff9abe94fbb8d61ec05e4a00fc92f7cf1534b96`. The acceptance artifacts of
proofs that first appear in them cannot be identified in this instance, so
their rows cite the commit in which the proof is present and leave
`acceptance_artifact_ids` unchanged. Proposition 4.2.24, Lemma 6.7.1,
Section 6.7.2 and replaced Lemma 5.3.5 change from `statement` to
`conditional`: `apartmentConjugacyFixingIntersection`,
`leviApartmentRestriction`, `leviSpecialPointRestriction` and
`unipotentNormalizerCoset` prove their statements on supplied data.
Proposition 13.5.2 changes from an empty status to `statement`:
`Langlands.BruhatTits.MaximalProP.AvailableMaximalProPStatement` states
the corrected proposition, with ambient group `G(F)^0` in both parts, on
available Bruhat–Tits data; it has no proof task. Theorems 7.5.3, 7.8.1,
9.2.7 and 9.6.5 stay `statement` and record newly proved inputs and
published reductions. Six of the seven inputs of the reduction to the
`G(F)^0` branch of Theorem 7.5.3 are proved; the seventh, Theorem
7.8.1(1), and Theorem 7.8.2 reduce through published reductions to
`SimplyConnectedFacetFixingStatement` (proof task
`c5ad9ef0-554c-4af8-be60-3607ad0e7e9b`). Proposition 13.2.5 stays
`statement`. Its separation and finite-depth bounded-openness conjuncts
are proved, and the row records Worker 46's unformalized paper
counterexample: for ramified quasi-split SU(3) over `Q_2` and the smallest
centralizer filtration satisfying the four published filtration axioms,
`MoyPrasadCovarianceStatement` and `MoyPrasadCommutatorStatement` fail.
The double-root variants and KP's own filtration are not affected.

The source and correction fields of the Proposition 13.5.2 row were
compared on 13 November 2026 with book PDF pages 507–508 and corrections
PDF page 49. Twenty-three declarations were inspected with `lean_check`
in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`: nineteen at commit
`ed924aef` and `doubleCosetStatementReduction`, `moyPrasadSeparated`,
`moyPrasadBoundedOpen` and `unipotentNormalizerCoset` at commit
`8ff9abe9`. Every reported axiom set is `propext`, `Classical.choice`,
`Quot.sound`.

A twelfth pass on 13 November 2026 updates the Section 13.2.6 row and
adds none. The row stays `conditional` and gains two modules, both first
published in Library commit `cfedefb680f317b0ea5d351023e1c9dd886b2547`.
`Langlands.BruhatTits.IntegralModels.FiniteReductiveQuotient` (artifact
`b52c4590-0a68-4f37-a097-c66650f5d9ab`) proves that an affine group
scheme locally of finite type over a finite commutative ring has finitely
many points. It obtains this from the published
`LangWeil.CurvePlane.finite_algHom_of_finiteType`. For supplied data over
a local domain with finite residue field and a quotient locally of finite
type, the module packages the residue-field points of the quotient as a
finite group (`finiteQuotientGroup`) and shows that the radical preimage
has finite index in the integral points of the neutral model. Over a
Henselian base, `index_positivePoints_subgroupOf` computes that index as
the number of residue-field points of the quotient; a separate theorem
specializes it to the integer ring of a nonarchimedean local field.
`Langlands.BruhatTits.IntegralModels.DepthZeroCompactOpen` (artifact
`f228edd9-7de3-41af-b12a-6be4746af741`) shows that the level-one
congruence subgroup lies in the radical preimage. Over a nonarchimedean
local field, for `G` affine and locally of finite type with the canonical
topology on `G(F)`, it shows that the radical preimage is open and compact
in `G(F)`, bundled as `localFieldPositiveOpenSubgroup`.
These results discharge, on supplied data, the finiteness, compactness
and openness parts of the row's consumer test. The identification of the
radical preimage with `P_{x,0+}`, the construction of the actual models
and the proofs of the intertwining statements remain open. Eleven
declarations were inspected with `lean_check` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` at commit `cfedefb6`. Every
reported axiom set is `propext`, `Classical.choice`, `Quot.sound`. The
source and correction fields of the row are unchanged.

A thirteenth pass on 13 November 2026 updates eight rows and adds none;
no formal status changes. The Theorem 9.2.7 row records the two
implication statements that this program published in Library commit
`cfedefb680f317b0ea5d351023e1c9dd886b2547` to split
`BruhatTitsAvailabilityStatement`:
`BruhatTitsAvailabilityReductionStatement` (artifact
`f147f7c0-08ca-4572-a5b9-d27efde033b8`) derives it from
`GroupAxiomsExistenceStatement`, and
`GroupAxiomsExistenceReductionStatement` (artifact
`432145f3-166b-4c77-af14-c477854c91bc`) derives that from four focused
statements. Both implications are proved, by Task 5926 and Task 5927,
in Library commit `730bd1f25b056b8106a2697e003c1ef1733a6b30`, so
`BruhatTitsAvailabilityStatement` now follows from those four statements.
The Theorem 9.6.5 row records a proved part of
`ValuationBuildingApartmentAxiomsStatement`:
`ValuationBuildingQuasiSplitAdjointTranslationStatement`, the translation
part of the quasi-split adjoint sentence of AS 5, is proved by Task 5708
(Library commit `7f43c3c930ff92f76dae6589da1678ad729017e5`) from
`QuasiSplitAdjointSimpleRootTransitivityStatement` (Task 5784, artifact
`f396351f-ca57-4ef9-99dc-472193bf573d`), which Task 5933 proves (Library
commit `51e4d8972659f1ffcf0ca89e8eee9540a30b52d3`). The
Proposition 13.5.2 row records its proof task, Task 5903, now executing.
The Proposition 13.2.5 row records that Worker 46's counterexample note
is public and that the Markdown of the affected statements now reports
it. Lemma 11.5.2, Proposition 11.5.4 and Corollaries 11.7.5
and 11.7.6 stay source-only; their owner task is now Task 5912
(`13897846-41bc-48ee-ac17-46b6ca3eebfe`), which is to construct the
actual Kottwitz homomorphism and state them; it is executing. Nine
declarations were inspected with `lean_check` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`: four in modules first published
in commit `cfedefb6`, the two assembly proofs (commit `730bd1f2`),
`quasiSplitAdjointSimpleRootTransitivity` (commit `51e4d897`),
`valuationBuildingQuasiSplitAdjointTranslation` (commit `7f43c3c9`) and
`ValuationBuildingQuasiSplitAdjointTranslationStatement`. Every reported
axiom set is `propext`, `Classical.choice`, `Quot.sound`. The source
and correction fields of every row are unchanged.

A fourteenth pass on 13 November 2026 updates six rows and adds none.
Theorems 8.3.2, 8.3.13, 8.4.10 and 8.4.19 and Corollary 8.4.12 change
from an empty status to `statement`, each for the part described in its
Recorded Lean scope entry. `UnramifiedParahoricModelStatement` (artifact
`41339d18-6b2c-4c79-a9e1-9ef821fe6038`, Library commit
`cc5aa77fa8dbdc6e723091c7b710ab0d81162c4e`) asks, over the integers of
the maximal unramified extension `K` of a nonarchimedean local field and
on supplied building data of `G_K`, for a smooth model with integral
points `G(K)^1_Ω` and its relative identity component, which has
connected fibres and integral points `G(K)^0_Ω`. It covers Theorem
8.3.13 and the `G(K)^1_Ω` part of Theorem 8.3.2; the dagger model is
absent. Its full-model part is proved from five statements, then all
unproved, by `exists_smoothFullModel_of_vertexInputs` (artifact
`63d25099-b07d-4806-8ec0-e5b2587c6bf5`, commit
`7f43c3c930ff92f76dae6589da1678ad729017e5`); the nineteenth pass records
two of them as proved.
`UnramifiedModelKernelStatement` (artifact
`a9987a70-ad07-49f0-adca-afbc31ec89df`, commit
`51e4d8972659f1ffcf0ca89e8eee9540a30b52d3`) states the smooth connected
unipotent kernel of Proposition 8.4.15, the valid first assertion of
Theorem 8.4.19(1), without the product decomposition.
`UnramifiedFacetRootDatumStatement` and
`UnramifiedFacetPositiveRadicalStatement` (artifacts
`adc6a005-db54-4eea-ab15-802f0f62e17f` and
`bf9958e9-6ff4-49bc-8d10-7c32126dffad`, commit
`73b1430a339b037d27e9096762b0400adb4fbd19`) state Axiom 4.1.22(6) and
the inclusion of Axiom 4.1.22(7) for descended facet models over the
integers of the local field; KP 4.1.28 derives these axioms from Theorem
8.4.10 and Corollary 8.4.12. Each of the five rows also cites
`IntegralModelAxiomsStatement`, the descended supplied-data form of
Axioms 4.1.20 and 4.1.22, which contains the only Lean form of Theorem
8.4.19(2)–(4). None of these statements is proved; their proof tasks are
Task 5976, Task 6203, Task 6218, Task 6219 and Task 5429. The Section
13.2.6 row stays `conditional`. It records the proofs of the three
intertwining statements by Tasks 5700, 5701 and 5702 (commit
`730bd1f25b056b8106a2697e003c1ef1733a6b30`) and their depth-zero
specialization
`Langlands.BruhatTits.IntegralModels.DepthZeroIntertwining` (artifact
`8fac015b-ad45-42d1-b1a8-fa15c6755a7c`, commit `73b1430a`), which over a
local field needs only the supplied model and quotient. Twenty-four
declarations were inspected with `lean_check` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`: eight at commit `eded01f2`, five
at commit `451cce4c` and eleven at commit `aae8cb82`. Each inspected
module is byte-identical to the commit cited for it and to commit
`a0627c91`. Every reported axiom set is `propext`, `Classical.choice`,
`Quot.sound`. The source and correction fields of every row are
unchanged.

A fifteenth pass on 13 November 2026 updates seven rows and adds none.
The Section 9.2.1 row changes from `statement` to `conditional`: the
theorem `unramifiedGaloisFixedApartment` (proof Task 5513, artifact
`fdd6f633-f0f7-4d1b-8a1c-0437cb2ef450`, Library commit
`b128d289028bf75629e9e364ecf151c484b27a85`) proves
`UnramifiedGaloisFixedApartmentStatement` for every supplied Γ-stable
class of valuations. Lemma 11.5.2, Proposition 11.5.4 and Corollaries
11.7.5 and 11.7.6 change from an empty status to `statement`: Task 5912
published `CharacterKernelStatement`, `ZeroKernelStatement`,
`ChamberStatement` and `QuotientStatement` (Library commit
`0c3f30c24701c74d5474fca3fbb5324a99aa1d58`) for the rational Kottwitz map
`reductiveKottwitzRational`, which is selected by its characterizing
property. The unproved `ReductiveKottwitzExistenceStatement` and
`ReductiveKottwitzDescentStatement` assert that the selections have
those properties. The chamber clause of Corollary 11.7.5 is stated on
supplied building data. Worker 304 published proof tasks for the four
targets (Tasks 6366, 6367, 6368 and 6376) and for the two map statements
(Tasks 6363 and 6365). The Theorem 9.6.5 row records that four published
theorems reduce `UnramifiedValuationDescentStatement` to
`UnramifiedTorusUnitFixedApartmentStatement` and
`UnramifiedFixedOppositeStatement`, whose proof tasks are Tasks 6010 and
6012; no published declaration states this composite. The Proposition
13.5.2 row lists the five intermediate statements of Task 5903. Thirteen
declarations were inspected with `lean_check` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` at Library commit `6948120d`;
each inspected module is byte-identical to the commit that first
published it. Every reported axiom set is `propext`, `Classical.choice`,
`Quot.sound`. The source and correction fields of every row are
unchanged.

A sixteenth pass on 13 November 2026 updates four rows and adds none.
The Proposition 13.2.5 row changes from `statement` to `conditional`. On
supplied building data and a supplied centralizer filtration,
`moyPrasadProduct` (Task 5579), `moyPrasadLevi` (Task 5620),
`moyPrasadDoubleRootCovariance` (Task 5645) and
`moyPrasadDoubleRootCommutator` (Task 5646) prove part (3), parts (5)
and (6), and the double-root forms of parts (1), (2) and (4) (Library
commits `cfedefb680f317b0ea5d351023e1c9dd886b2547` and
`cc5aa77fa8dbdc6e723091c7b710ab0d81162c4e`). With the earlier proofs of
separation and bounded openness, whose acceptance artifacts the row now
records, every part is proved on supplied data. The supplied-filtration
covariance and commutator statements without the double-root premise
remain refuted on paper. The Theorem 9.2.7 row records that
`availableSimultaneousStandardBasis` (Task 5310) proves
`AvailableSimultaneousStandardBasisStatement`, so five of the six
conditional statements of the joint-basis reduction are proved. The
Theorem 9.6.5 row records the proof `torusEquivariantCharacterValueDescent`
(Task 5959) of `TorusEquivariantCharacterValueDescentStatement`. It also
records three declarations from Task 6012 (Library commit
`430cc03fe803c5dbf74bc3baf91e8f7a2c26ea9c`):
`UnramifiedFixedWallInvarianceStatement`, the proved implication
`unramifiedFixedOpposite_of_wallInvariance` from it to
`UnramifiedFixedOppositeStatement`, and
`UnramifiedFixedDepthZeroOppositeStatement`. The Theorem 5.3.4 row
records that `parahoricLeCompactStabilizer` proves
`ParahoricLeCompactStabilizer` for all supplied data. Nine declarations
were inspected with `lean_check` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, eight at Library commit
`0f84a0d8` and one at Library commit `1bd55dea`; each inspected module
is byte-identical to the commit that first published it. Every reported
axiom set is `propext`, `Classical.choice`, `Quot.sound`. The source and
correction fields of every row are unchanged.

A seventeenth pass on 14 November 2026 updates one row and adds none.
The Section 13.2.6 row stays `conditional` and records five published
regression modules in `Langlands.BruhatTits.IntegralModels`:
`MultiplicativeDepthZero` and `SplitTorusDepthZero` (artifacts
`3a66ce4a-0da3-4c10-a0a7-0950c9263bcd` and
`fb196e9b-3556-4f49-92d8-214b6a45bad8`, Library commit
`85c2fe719cf62e96f22aaf4ca03961c5814d086b`), `GeneralLinearDepthZero`
(artifact `1d98759b-e9fb-4fe5-8eed-cf3c2b20c5ac`, commit
`db8d6b3d466f2fd453a4df4624ce6c90db8eed46`), and `SymplecticDepthZero`
and `SpecialLinearDepthZero` (artifacts
`d2114602-84e9-4570-bb92-d2f5ae6ba87f` and
`c1bbf8bb-a63a-4c88-a6d8-70976a4c2ab7`, commit
`410c79471b79f65a02fb0f6070da7f2800793ff3`). For `G_m`, `G_m^I`, `GL_N`,
`Sp_{2l}` and `SL_n` over a nonarchimedean local field whose residue
field has `q` elements, the standard model over the integers gives
actual model data whose special fibre is its own reductive quotient,
with trivial radical, so the supplied-data theorems of the row apply.
The index of the radical preimage in the integral points is `q-1` (and
`1` when `q=2`), `(q-1)^|I|`, `∏_{i<N}(q^N-q^i)` and `|Sp_{2l}(f)|`; for
`SL_N` the index times `q-1` is `∏_{i<N}(q^N-q^i)`. For `GL_{n+1}` the
integral points and the radical preimage are carried onto the Library's
`Conductor.integralSubgroup` and level-one
`Conductor.principalLevelSubgroup`, and for `SL_{n+1}` the radical
preimage is the preimage of the latter. No building point appears, and
the models are not identified with KP's `G^0_x` at a hyperspecial
vertex. Anisotropic tori, multipliable roots, nontrivial unipotent
radicals and nontrivial component groups still have no regression
instance. Thirty-two declarations were inspected with `lean_check` in
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`, one at Library
commit `3489c503` and thirty-one at Library commit `410c7947`; each
inspected module is byte-identical to the commit that first published
it. Every reported axiom set is `propext`, `Classical.choice`,
`Quot.sound`. The source and correction fields of every row are
unchanged.

An eighteenth pass on 14 November 2026 updates three rows and adds none.
The corrected Proposition 13.5.2 row changes from `statement` to
`conditional`: `availableMaximalProP` (Task 5903, artifact
`c86654f8-89f0-4107-b4af-6473d7fd30e0`, Library commit
`410c79471b79f65a02fb0f6070da7f2800793ff3`) proves
`AvailableMaximalProPStatement` for every available Bruhat–Tits
assignment, and the existence of available data,
`BruhatTitsAvailabilityStatement`, remains unproved. The row also records
that four of the five intermediate statements of Task 5903 are proved.
The Lemma 9.8.1 row records that published theorems reduce both of its
existence statements to `LocalMoyPrasadGroupPropertiesStatement` (proof
Task 6191) and `UnramifiedComparisonExistenceStatement` (proof Task
6424); its status stays `statement`. The Theorem 9.6.5 row records that
`UnramifiedQuasiSplitStatement`, one of the five inputs of its proved
reduction, now holds: `henselianDiscreteQuasiSplit` (artifact
`61c429ea-c09c-4298-b74f-48a84aedf42b`, Library commit `410c7947`)
proves `HenselianDiscreteQuasiSplitStatement`, and the published
`unramifiedQuasiSplit_of_henselianDiscrete` applies it to the maximal
unramified extension. Two of the five inputs are now proved, and the row
stays `statement`. Eight declarations were inspected with `lean_check`
in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`, five at Library
commit `410c7947` and three at Library commit `757a6793`. Each inspected
module is byte-identical to the commit that first published it, or, if
that commit is unknown, to commit `ed924aef`. Every reported axiom set is
`propext`, `Classical.choice`, `Quot.sound`. The source and correction
fields of every row are unchanged.

A nineteenth pass on 14 November 2026 updates two rows and adds none.
The Theorem 8.3.2 row records that two of the five inputs of its
conditional full-model construction are proved, both first published in
Library commit `410c79471b79f65a02fb0f6070da7f2800793ff3`:
`finiteVertexFixerApproximation` (artifact
`e92ec689-8a24-4193-85a4-cdd1533c0817`) proves
`FiniteVertexFixerApproximationStatement`, and `finiteIndexEnlargement`
(artifact `6722356c-5ad2-43dd-bb70-d007825bd50d`) proves
`FiniteIndexEnlargementStatement`, the finite-index part of KP
Proposition A.7.1. `VertexOneStabilizerMaximalBoundedStatement`,
`MaximalBoundedIntegralModelStatement` and `SmoothIntersectionStatement`
remain unproved, and the row stays `statement`. The proof of
`finiteIndexEnlargement` uses the helper module
`Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargement.SubHopf`,
which artifact `6722356c-5ad2-43dd-bb70-d007825bd50d` adapts from the
`TakK` section of the Anthropic FLT file
`P2M/Sol/S_HopfAlgebra_faithfullyFlat_subalgebra_of_isReduced_of_fg_of_isAlgClosed.lean`
at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (Copyright 2026
Anthropic, PBC; Apache License 2.0; licence, notice and attribution
files under `licenses/Anthropic-FLT/`). The row's `external_code` field
records this reuse through the accepted artifact, with its pin and
licence. The Definition 6.6.1 row records that
`unramifiedZeroPointsIndependence` (artifact
`4375075b-73b6-48e2-9b4a-f6cddf7e67e3`, Library commit
`db8d6b3d466f2fd453a4df4624ce6c90db8eed46`) proves
`UnramifiedZeroPointsIndependenceStatement`, the independence part of KP
Lemma 2.6.24, so the earlier route `normalizerZero_normal` to the
normality of `Z(F)^0` in `N(F)` now needs no premise; the row stays
`definition`. Three declarations were inspected with `lean_check` in
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` at Library commit
`20f83141`; each inspected module is byte-identical to the commit that
first published it. Every reported axiom set is `propext`,
`Classical.choice`, `Quot.sound`. The source and correction fields of
every row are unchanged.

A twentieth pass on 14 November 2026 updates five rows, adds none and changes
no status. The Theorem 9.6.5 row corrects a stale sentence: since
Library commit `85c2fe71`, `unramifiedFixedWallInvariance_of_depthZero_of_leviTransport`
takes `UnramifiedFixedDepthZeroOppositeStatement` as a hypothesis. The
row also records the published split of
`UnramifiedTorusUnitFixedApartmentStatement` (KP Proposition 9.3.13 as
corrected) into three statements, of which
`UnramifiedSplitTranslationFixerStatement` is proved by
`unramifiedSplitTranslationFixer` (artifact
`ac1b808f-0768-46ed-9378-548d34cb0653`, Library commit
`c40a01345b2f4172fa41e07ff31644b40e695003`), and the published reductions
of the transporter statement to KP Proposition 9.3.11(1) and of the
depth-zero statement to recovered models and KP Theorem 8.2.9. Its
descent input now rests on three unproved statements. The Lemma 9.8.1
row records Task 6540's reduction of `UnramifiedComparisonExistenceStatement`
to special-torus existence, valuation descent and four field statements,
and that Task 6191 now has executors. The Lemma 11.5.2, Proposition
11.5.4 and Corollary 11.7.5 rows record their published reductions to
four, three and seven statements; the only proved input among them is
`UnramifiedSmoothModelDescentStatement`. Two composites that no
published declaration states were checked with private `lean_check`
runs. Ten declarations were inspected with `lean_check` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` at Library commit `c40a0134`; each
inspected module is byte-identical to the commit that first published
it. Every reported axiom set is `propext`, `Classical.choice`,
`Quot.sound`. The source and correction fields of every row are
unchanged.

The normative sources are Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), registered as `kaletha-prasad-2023-bruhat-tits-new-approach`, and the
authors' corrections of 1 November 2024, registered as
`kaletha-prasad-2024-corrections`. Both readable originals are in
`/home/taskhub/central-library/Kaletha-Prasad--Bruhat-Tits theory, a new approach (book)--2023/`.
Their fingerprints and precise locators are included in every relevant row.
The operator roadmap is design guidance, not theorem evidence.

## Reading and scope

The original passages behind these rows were read at PDF pages 34–40, 161–163,
188, 199–205 and 213–215, together with corrections PDF pages 1–3, 25 and 27–29.
Book PDF pages 35–36 and 202 were visually checked. In particular, the overbar
in Theorem 4.2.10 matters: the closed union is a union of **facet closures**.
The OCR text alone drops that overbar. The theorem does not require the building
to be locally finite; that is only the first case in its proof.

The Chapter 4 targets are consequences of specified building axioms. They do
not supply a general reductive-group building construction. The program still
requires the descended construction and every corrected axiom in its
Theorem 9.2.7 certificate. None of the source-only rows below closes that boundary.

For the initial Bundle B extension, the original-source audit also covered book
PDF pages 188–197, 266–267, 280–292, 307, 353–360 and 393–399, and
corrections PDF pages 27, 30–41. Axiom 4.1.22 at PDF page 195 was visually
checked to distinguish the special fibre from its maximal reductive quotient.
The extension has three new rows: corrected Definition 4.1.26, Theorem 7.5.3
and Theorem 9.2.7. Source references in the assembly map below are dependencies
of those rows; they are not additional completed formal targets.

The Bundle C extension adds eleven source-only rows for the Iwahori–Weyl
quotient, Cartan and Iwasawa decompositions, the replaced Lemma 5.3.5,
Iwahori factorization, all four corrected Theorem 7.8.1 clauses, and the
narrow component/Kottwitz interfaces in Sections 11.5 and 11.7. Its source
audit covered book PDF pages 133–136, 217–222, 261–263, 286–288, 292–293,
299–304, 451–456 and 460–465, and corrections PDF pages 24–25, 30, 33–36
and 42–46. Book PDF page 465 was visually checked for the placement of
invariants and the torsion-free quotient notation. This extends the ledger
to twenty-three rows without assigning a formal status to any new target.

The Bundle D extension adds six source-only rows for Theorems 8.3.2,
8.3.13 and 8.4.10, Corollary 8.4.12, Theorem 8.4.19 and Section 13.2.6.
Its original-source audit covered book PDF pages 112–115, 314–316,
326–331, 333–341, 358–363, 394–395 and 497–502, and corrections PDF
pages 37–41 and 49–50. A further check of book PDF pages 327–328,
335 and 337–340, including visual inspection of pages 328, 335, 338 and
340, establishes the source discrepancy in the restricted kernel index of
Theorem 8.4.19(1) described below. The kernel target instead uses the
general product in Proposition 8.4.15. This extends the ledger to
twenty-nine rows. All six added formal-status fields and evidence arrays
remain empty; the source dependencies below supply no formal construction.

The Bundle E extension adds nine source-only rows for Proposition 13.2.5,
Sections 13.3.1–4, Theorem 13.5.1, corrected Proposition 13.5.2 and
the later Propositions 13.6.7 and 13.7.4. Its original-source audit
covered book PDF pages 97–98, 230, 274–282, 497–515 and corrections PDF
pages 49–50. Book PDF pages 281 and 500 were visually checked for
the printed root indices. The discrepancy in Proposition 13.2.5(3)
remains an explicit independent formal-resolution obligation. The
optimal-point clauses in Definition 13.4.2, Lemma 13.4.4 and Proposition
13.6.7 were checked at book PDF pages 503–504 and 512: the empty-root
case has no literal optimal point, as the G_m/Q_2 zero-coset regression
below shows. Its separate instability target is retained, and the
general program scope is unchanged. The 2024 corrections do not supply
an empty-root extension; none is proved here. Section
1.6 and Corollary 7.3.14 independently justify restricting openness to
finite augmented depths; the separated infinite term is recorded
separately and need not be open. This clarification is absent from the
2024 corrections. The
Remark 13.6.6 example at book PDF page 512 was also visually checked;
the explicit contracting cocharacter below invalidates its claimed
role as a witness. This is an independent source discrepancy, absent
from the 2024 corrections, with no Lean proof recorded here. This
extends the ledger to thirty-eight rows with all new formal-status
fields and evidence arrays empty. Positive-depth implementation
and the later instability targets retain their separate release gates.

The Bundle F extension adds five source-only rows for corrected
Proposition 12.4.1, Theorem 12.9.2, Proposition 12.9.4 and
Propositions 14.6.1 and 14.8.4. Its original-source audit covered
book PDF pages 467–473, 476–479, 488–496 and 521–540, together
with corrections PDF pages 47–50. Book PDF page 539 was visually
checked for the enlarged-building and full-stabilizer notation;
PDF pages 495–496 and 523 were rechecked for the actual-model
identity and the simple-factor lift condition. The nearest-point
dependency was checked at book PDF pages 38–40 and corrections PDF
pages 1–3, including visual inspection of corrections page 2.
The proof repairs below are independently derived, separate from the authors'
corrections, and are implemented in the verified Proposition 1.1.20 proof.
The five Bundle F rows retain
null formal status and empty formal-evidence arrays. The later verification of
Theorem 1.1.15 and its two metric successors below leaves the release order
and construction gates open.

## Structured ledger

The JSON block is the structured ledger. Each row has the same fields.
`lean_declarations`, `modules`, acceptance, publication and trust reports stay
empty until their exact results have been verified. An owner task records an
obligation; it is not evidence of its fulfillment. Conditional code will remain
`conditional` until its missing instance is constructed.

```json
{
  "schema_version": 1,
  "program_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
  "coverage": "Bundle A named targets, Bundle B targets (corrected Definition 4.1.26, Theorem 7.5.3, Theorem 9.2.7 and the Chapter 9 descent inputs Section 9.2.1, Proposition 9.3.4, Theorem 9.6.5 and Lemma 9.8.1), Bundle C decompositions and narrow component/Kottwitz interfaces, Bundle D parahoric models, maximal reductive quotients and depth-zero reduction with Chapter 9 descent, Bundle E group/Lie/dual filtrations, all three comparison alternatives, corrected pro-p ambient group and later degeneracy/instability targets, and Bundle F corrected finite-action fixed loci, tame building and integral-model descent, and embeddings from adapted data with their strict-Henselian and general-k existence boundaries. Remaining Bundle B items still need public rows. Both parts of Theorem 1.1.15, Corollary 1.1.19 and Proposition 1.1.20 have verified published proofs; Propositions 4.2.7, 4.2.24 and 4.4.4, both assertions of Theorem 4.2.10, Corollary 4.2.14, corrected Corollary 4.4.5, Theorem 5.3.3, replaced Lemma 5.3.5, Lemma 6.7.1, Section 6.7.2 and Corollary 7.4.9 have published conditional formalizations on supplied building data, Theorems 5.2.1 and 5.3.4 and corrected Proposition 13.5.2 have them on available data, and Section 13.2.6 on supplied integral models and reductive quotients, with a proved intertwining and double-coset theorem, specialized to depth zero, for its compact-induction consumer, finitely many quotient points over a finite residue field and a compact open radical preimage over a local field, and regression instances from the standard models of split G_m, G_m^I, GL_N, Sp_{2l} and SL_n over a local field; corrected Theorem 7.8.1, whose part (4) is proved, and the G(F)^0 branch of Theorem 7.5.3, six of the seven inputs of whose published reduction are proved, have published statements on supplied building data; corrected Definition 4.1.26 has a published definition; Section 9.2.1 is proved for supplied Galois-stable apartment data; Proposition 9.3.4 (also its integral-model input), Theorem 9.6.5 (with a proved reduction to five statements, two of them proved, and its descent input reduced by published implications to three unproved statements) and Lemma 9.8.1 (both existence statements reduced by published theorems to two unproved statements, the second of them further to six) have published statements, Lemma 11.5.2, Proposition 11.5.4 and Corollaries 11.7.5 and 11.7.6 published statements for the selected rational Kottwitz map, the first three with published reductions to focused statements, Proposition 13.2.5 a published statement of its opening sentence at finite depths and of parts (1)–(6) on supplied data, part (3) with indivisible-root blocks, parts (5) and (6) at positive depth for parabolics containing the split torus, and parts (1), (2) and (4) also with a double-root premise, all proved on supplied data except the supplied-filtration parts (1), (2) and (4) without that premise, which an unformalized paper counterexample refutes, the corrected Definition 4.1.26 part of Theorem 9.2.7 a published existence statement, reduced by two proved implications to four focused statements, and Definition 6.6.1 a partial published definition; Theorems 8.3.2, 8.3.13, 8.4.10 and 8.4.19 and Corollary 8.4.12 have partial published statements on supplied building data, the full model of Theorem 8.3.2 with a proved construction from five statements, two of them proved; the other fifteen rows remain source-only. The building construction and release gates remain open.",
  "status_convention": "A null formal_status means no verified Lean declaration of this target is recorded. Non-null values are definition, statement, proved or conditional; acceptance and publication are separate mandatory evidence.",
  "rows": [
    {
      "source_item": "Proposition 2.11.1",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.130–131 / PDF pp.161–162"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.25, Section 2.11",
        "change": "Notation corrections to P_G(lambda), U_G(lambda), Z_G(lambda) and the corresponding H-subgroups."
      },
      "hypotheses": [
        "A is a commutative unital ring; G is an affine A-group scheme with a G_m-action by group-scheme automorphisms, denoted lambda. Conjugation by a cocharacter is an instance.",
        "Part (4): H is a closed G_m-stable subgroup scheme of G.",
        "Part (5): A is a field, G and H are connected of finite type, and G→H is a faithfully flat surjective equivariant homomorphism.",
        "Part (6): G is of finite type over A."
      ],
      "conclusion": "Representability of P and U as closed subgroup schemes, with U normal in P; Z=P(lambda)∩P(-lambda); compatibility with arbitrary base change and stable closed subgroups; induced quotient maps in (5); unipotence of U fibres in (6).",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Dynamic orbit extension from G_m to A^1; schematic subgroup functors; equivariant quotient maps"
      ],
      "consumer_or_regression": "General valued root-group and integral-model inputs; compare the existing GL_n dynamic instance.",
      "formal_status": null,
      "owner_task": "2b5e4a00-9d44-49a4-9c89-979fb5b6233e",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Proposition 2.11.2",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.131 / PDF p.162"
      },
      "erratum": null,
      "hypotheses": [
        "The affine A-group scheme G with its G_m-action is of finite presentation.",
        "Connectedness of P and Z fibres in (2) additionally assumes connected G fibres."
      ],
      "conclusion": "P,U,Z are finitely presented; U has connected fibres; the stated Lie algebras are the zero and positive weight spaces, with Lie(P)=Lie(G)_0 ⊕ Lie(G)_+; multiplication gives the stated semidirect decomposition with ordered factors Z and U.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Proposition 2.11.1; weight decomposition; Lie algebras; semidirect products"
      ],
      "consumer_or_regression": "Compare the ordered Z/U product to the GL_n block-Levi construction and later root-group models.",
      "formal_status": null,
      "owner_task": "2b5e4a00-9d44-49a4-9c89-979fb5b6233e",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Proposition 2.11.3",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.131–132 / PDF pp.162–163"
      },
      "erratum": null,
      "hypotheses": [
        "G is a smooth affine A-group scheme of finite presentation with the G_m-action.",
        "The open immersion is an isomorphism when A is a field and G is connected and solvable.",
        "Part (3) additionally assumes G is a reductive group scheme.",
        "Part (4) assumes A is a field."
      ],
      "conclusion": "Z,P,U are smooth; multiplication U(-lambda)×P(lambda)→G is an open immersion; P is parabolic and U its unipotent radical in the reductive case; U is split over a field.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Propositions 2.11.1–2.11.2; smoothness; scheme-theoretic open immersion; reductive groups"
      ],
      "consumer_or_regression": "General big-cell input to building/root-group constructions. GL_n or split-only results remain intermediate instances.",
      "formal_status": null,
      "owner_task": "2b5e4a00-9d44-49a4-9c89-979fb5b6233e",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Theorem 1.1.15",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.6–7 / PDF pp.37–38"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF pp.1–2, Section 1.1",
        "change": "Convex subsets are nonempty; geodesic hypothesis restored in the convex-ball/hull discussion; in the theorem proof take positive epsilon<r and a nonnegative approximating epsilon sequence."
      },
      "hypotheses": [
        "X is a complete nonpositively curved geodesic metric space.",
        "Part (1): M⊆X is nonempty, bounded, closed and geodesically convex.",
        "Part (2): M⊆X is nonempty and bounded; it need not itself be closed or convex."
      ],
      "conclusion": "Part (1): M has a unique barycenter, fixed by every isometry carrying M onto itself. Part (2): the setwise stabilizer of M in the isometry group has a fixed point in X.",
      "lean_declarations": [
        "Langlands.Geometry.Metric.KP.BarycenterStatement",
        "Langlands.Geometry.Metric.KP.barycenter",
        "Langlands.Geometry.Metric.KP.BoundedSetStabilizerFixedPointStatement",
        "Langlands.Geometry.Metric.KP.boundedSetStabilizerFixedPoint"
      ],
      "modules": [
        "Langlands.Geometry.Metric.KPFixedPointStatement",
        "Langlands.Geometry.Metric.KPBarycenterProof",
        "Langlands.Geometry.Metric.KPBoundedSetStabilizerProof"
      ],
      "dependencies": [
        "Definitions 1.1.2, 1.1.4, 1.1.8, corrected 1.1.12, and 1.1.14; Lemmas 1.1.11 and 1.1.13; completeness"
      ],
      "consumer_or_regression": "Bounded isometric actions (Corollary 1.1.19), then the constructed-building instance and Corollary 4.2.14.",
      "formal_status": "proved",
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [
        "0af16116-fa33-42dd-9681-06303b9efce9",
        "52258019-2d1f-40af-9214-6243cad21009"
      ],
      "publication_commits": [
        "11dedf3c6982c420e1eee5dc7a82ee37ad2dcc0e"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Metric.KP.barycenter",
          "environment_artifact": "3b864ddf-f0af-4c18-8903-c6f813a0ce0f",
          "inspection_id": "844de534-f7cd-4803-bc90-ac4d44a481c7",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection; independent proof acceptance and publication are recorded separately."
        },
        {
          "declaration": "Langlands.Geometry.Metric.KP.boundedSetStabilizerFixedPoint",
          "environment_artifact": "3b864ddf-f0af-4c18-8903-c6f813a0ce0f",
          "inspection_id": "abf204b5-dc18-491a-944b-d03b1ab28f22",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection; independent proof acceptance and publication are recorded separately."
        }
      ],
      "external_code": []
    },
    {
      "source_item": "Corollary 1.1.19",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.7 / PDF p.38; Lemma 1.1.17 and Definition 1.1.18 on the same page"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF pp.1–2, Section 1.1",
        "change": "No change to Corollary 1.1.19. The geodesic premise of Theorem 1.1.15 is not a premise of this corollary; the formal proof constructs geodesics from completeness and the primitive NPC condition."
      },
      "hypotheses": [
        "X is a nonempty complete nonpositively curved metric space; geodesic existence is not an additional hypothesis.",
        "An arbitrary group acts on X by isometries and has a bounded orbit. The group and metric carrier may belong to independent universes."
      ],
      "conclusion": "The given action has a common fixed point in X, chosen before quantifying over group elements.",
      "lean_declarations": [
        "Langlands.Geometry.Metric.KP.BoundedActionFixedPointStatement",
        "Langlands.Geometry.Metric.KP.boundedActionFixedPoint"
      ],
      "modules": [
        "Langlands.Geometry.Metric.KPFixedPointStatement",
        "Langlands.Geometry.Metric.KPBoundedActionFixedPointProof"
      ],
      "dependencies": [
        "The published completeNPCGeodesic theorem supplies geodesics; boundedSetStabilizerFixedPoint applies to the actual nonempty bounded orbit. Each action map is a preserving isometry equivalence, using its inverse to prove setwise equality."
      ],
      "consumer_or_regression": "Fixed-point inputs for the constructed building and the embedding-space argument of Proposition 14.7.2; the needed complete NPC instances and nonempty embedding spaces remain separate obligations.",
      "formal_status": "proved",
      "owner_task": "a3eadfc8-c446-402c-a08e-dd4d9edbf042",
      "acceptance_artifact_ids": [
        "a67bd9ea-5ff4-4b0f-a38c-46350535ec88"
      ],
      "publication_commits": [
        "7543113c99690e18b45f3b22d252e8cf77c3964e"
      ],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Proposition 1.1.20",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.7–8 / PDF pp.38–39"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF pp.1–2, Section 1.1",
        "change": "Convexity includes nonemptiness. The printed coefficient-2 minimizing-sequence estimate is false, and the added multiplicative continuity argument misses zero minimum distance. The accepted proof uses the independent squared midpoint deficit and division-free continuity repair described below; the theorem statement is unchanged."
      },
      "hypotheses": [
        "X is a complete nonpositively curved geodesic metric space, with arbitrary carrier universe.",
        "Y is a closed nonempty geodesically convex subset of X. It need not be bounded, and the distance infimum may be zero or attained."
      ],
      "conclusion": "There exists one subtype-valued nearest-point projection X→Y with minimality and uniqueness at every ambient point, continuity for the inherited metric topology, and simultaneous equivariance under every ambient isometry equivalence carrying Y onto itself.",
      "lean_declarations": [
        "Langlands.Geometry.Metric.KP.NearestPointProjectionStatement",
        "Langlands.Geometry.Metric.KP.nearestPointProjection"
      ],
      "modules": [
        "Langlands.Geometry.Metric.KPNearestPointStatement",
        "Langlands.Geometry.Metric.KPNearestPointProof"
      ],
      "dependencies": [
        "The published geodesic-midpoint NPC inequality gives d(y,z)^2≤2d(x,y)^2+2d(x,z)^2−4r^2 for a nonnegative lower distance bound r. A real-infimum minimizing sequence is Cauchy; completeness and closedness give its minimizing limit. The same deficit proves uniqueness and division-free continuity. Setwise preservation and the inverse isometry give equivariance of the same chosen projection."
      ],
      "consumer_or_regression": "The closest-point step in Proposition 14.8.3/14.8.4; actual enlarged base buildings, their closed nonempty convex inclusion and adapted-data existence remain separate obligations.",
      "formal_status": "proved",
      "owner_task": "023897fd-dccb-460b-831b-41b55d5622de",
      "acceptance_artifact_ids": [
        "c81fc3b9-e90a-4b1a-b55f-605ee138f50f"
      ],
      "publication_commits": [
        "7a2e42fd31831029d34cafb155ffad911920df25"
      ],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Proposition 4.2.7",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.170 / PDF p.201"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF pp.28–29, Section 4.2",
        "change": "Add Axiom 4.1.6 to the opening hypotheses; the metric of Proposition 4.2.1 is G-invariant and the apartment-independence argument is corrected."
      },
      "hypotheses": [
        "k has a discrete valuation, its valuation ring is Henselian and its residue field is perfect; G is connected reductive over k.",
        "B is the Chapter 4 building satisfying Axioms 4.1.1, 4.1.2, 4.1.4, 4.1.6 and 4.1.9, with the compatible Weyl-invariant Euclidean apartment metrics of Section 4.2.",
        "Recorded Lean scope: for every nonarchimedean local field F of either characteristic, connected reductive G/F and supplied P : ParahoricBuildingData G with realization R and splitting T satisfying the Library predicates SatisfiesBuildingAxiom R (one-group 4.1.1), HasBoundedOpenStabilizers (4.1.2), SatisfiesAffineApartmentAxiom T (4.1.4), HasRootReflections, SatisfiesApartmentAxioms and HasCompatibleApartmentFacets (4.1.6) and HasTitsSystem (4.1.9), metricRealization gives Nonempty P.toValuationBuildingData.MetricRealization: a complete metric on the existing quotient satisfying the Library NPC predicate, with isometric G(F)-action and orbit maps continuous for rationalPointTopology F G.X. The metric is existential and its normalization is not fixed. The Henselian discretely valued generality of the source is not covered, and no existence of the supplied data or witnesses is asserted."
      ],
      "conclusion": "The apartment metric on B satisfies the midpoint nonpositive-curvature inequality of Definition 1.1.8.",
      "lean_declarations": [
        "Langlands.Geometry.Metric.KP.IsRetractionGluedDistance.isNonpositivelyCurved",
        "Langlands.Geometry.Building.ValuationBuildingData.nonempty_metricRealization_of_isRetractionBuildingDistance",
        "Langlands.Geometry.Building.metricRealization"
      ],
      "modules": [
        "Langlands.Geometry.Metric.RetractionGluing",
        "Langlands.Geometry.Building.ValuationBuildingMetricAssembly",
        "Langlands.Geometry.Building.MetricRealizationStatement",
        "Langlands.Geometry.Building.MetricRealizationProof"
      ],
      "dependencies": [
        "Section 4.2 metric; apartment midpoints; retractions and their nonexpansion/distance laws; Euclidean parallelogram identity",
        "Formal route: the abstract predicate IsRetractionGluedDistance (common members, NPC metric on each member, distance-nonincreasing retractions preserving the distance from a centre) gives the NPC inequality by retracting onto a common apartment centred at an NPC midpoint; only the inequality form of the midpoint law is used. metricRealization supplies the distance buildingDist of Proposition 4.2.1 and the retractions on the existing quotient P.ReducedBuilding."
      ],
      "consumer_or_regression": "Theorem 1.1.15 applied to the actual constructed building after Theorem 4.2.10.",
      "formal_status": "conditional",
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [
        "c4a16df784376405a45b60df82583e8c26d8a4e3"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Metric.KP.IsRetractionGluedDistance.isNonpositivelyCurved",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "a3b24b7e-96fe-45fe-b7fd-dbc07565ca24",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-08 at Library commit c4a16df7."
        },
        {
          "declaration": "Langlands.Geometry.Building.metricRealization",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "99f5d6d1-6a78-4e22-8054-ec9414595c00",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-08 at Library commit c4a16df7."
        }
      ],
      "external_code": []
    },
    {
      "source_item": "Theorem 4.2.10",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.171–172 / PDF pp.202–203"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF pp.28–29, Section 4.2",
        "change": "Add Axiom 4.1.6 to the opening hypotheses; the metric of Proposition 4.2.1 is G-invariant and the apartment-independence argument is corrected."
      },
      "hypotheses": [
        "k has a discrete valuation, its valuation ring is Henselian and its residue field is perfect; G is connected reductive over k.",
        "B is the Chapter 4 building satisfying Axioms 4.1.1, 4.1.2, 4.1.4, 4.1.6 and 4.1.9, with the compatible Weyl-invariant Euclidean apartment metrics of Section 4.2.",
        "Recorded Lean scope (first assertion only): completeSpace_of_isometry_apartmentMap_of_satisfiesApartmentAxioms takes supplied B : ValuationBuildingData G over a nonarchimedean local field, an arbitrary metric on B.ReducedBuilding with isometric G(F)-action, common apartments for every point (HasCommonApartmentWith), B.SatisfiesApartmentAxioms, and an isometric apartment map for the Euclidean root metric on A(S), and concludes CompleteSpace. metricRealization applies it on supplied P : ParahoricBuildingData G under the seven Library predicates for the five axioms, listed in the Proposition 4.2.7 row. Here B.SatisfiesApartmentAxioms covers V 6, V 7 (KP Definition 6.1.2) and AS 2–AS 5 (KP Axiom 4.1.6); V 6 is part of the data B, and V 7 (compatibility of the root filtrations with the topology of G(F)) is an additional premise.",
        "Recorded Lean scope (second assertion): the published FacetClosureUnionClosedStatement quantifies over every nonarchimedean local field F in universe u, group scheme G over Spec F and supplied B : ValuationBuildingData G, with the same metric, isometric-action, common-apartment, SatisfiesApartmentAxioms and isometric-apartment-map premises as the completeness theorem. For every X : Set (Set B.ReducedBuilding) with B.IsFacet Y for all Y ∈ X it concludes IsClosed (⋃ Y ∈ X, closure Y), with the topological closure of each facet. Neither the data nor the premises are asserted to exist. The theorem facetClosureUnionClosed (module FacetClosureUnionClosedProof) proves this statement; it was accepted as artifact b4a3ec65-43a1-4685-b99b-38916a8ba603 and first published in Library commit e449cde988d4e97ab280b8d4d11262887ccc26e0. Both assertions are therefore proved on supplied data, and the row stays conditional until the data and premises are constructed."
      ],
      "conclusion": "B is complete; for every collection of facets, the union of their CLOSED facets (the closures of those facets) is closed. Local finiteness is not a hypothesis of the theorem.",
      "lean_declarations": [
        "Langlands.Geometry.Building.ValuationBuildingData.completeSpace_of_isometry_apartmentMap",
        "Langlands.Geometry.Building.ValuationBuildingData.completeSpace_of_isometry_apartmentMap_of_satisfiesApartmentAxioms",
        "Langlands.Geometry.Building.ValuationBuildingData.exists_forall_dist_smul_lt_imp_eq",
        "Langlands.Geometry.Building.metricRealization",
        "Langlands.Geometry.Building.FacetClosureUnionClosedStatement",
        "Langlands.Geometry.Building.facetClosureUnionClosed"
      ],
      "modules": [
        "Langlands.Geometry.Metric.DiscreteOrbitCompleteness",
        "Langlands.Geometry.Building.AffineRootOrbitDiscreteness",
        "Langlands.Geometry.Building.ValuationBuildingCompleteness",
        "Langlands.Geometry.Building.MetricRealizationProof",
        "Langlands.Geometry.Building.FacetClosureUnionClosedStatement",
        "Langlands.Geometry.Building.FacetClosureUnionClosedProof"
      ],
      "dependencies": [
        "Section 4.2 metric; Lemma 4.2.11 and discrete affine-root hyperplane spacing; compact closed chamber",
        "Formal route, differing from the source: discreteness of N(F)-orbits in A(S) (AS 3 local finiteness and AS 5 via the stabilizer of a locally finite arrangement) gives discreteness of G(F)-orbits in B(G) for the full group G(F); completeness then follows from the abstract discrete-orbit completeness criterion with closed balls of the proper apartment, instead of chambers and Proposition 1.5.13.",
        "Proof of FacetClosureUnionClosedStatement: facetClosureUnionClosed, from lean.proof@1 task cd045e44-eb03-481f-aabf-0e086965dd25 (artifact b4a3ec65-43a1-4685-b99b-38916a8ba603). It follows the first part of Lemma 4.2.11: local finiteness at an apartment coordinate of x gives a ball meeting only facets whose closures contain x, after moving each facet into a common apartment chart with x; a combinatorial closed facet lies in the topological closure of its facet. Both assertions are conditional on the data and premises, whose construction is RootValuationBuildingConstructionStatement (task 00b6788c-23c3-4b22-88f5-41fdbc6d3654)."
      ],
      "consumer_or_regression": "Fixed-point theorem on the constructed building; finite-residue and non-locally-finite cases must not be conflated.",
      "formal_status": "conditional",
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [
        "7c30292c-a01f-472c-b967-5859043e2755",
        "b4a3ec65-43a1-4685-b99b-38916a8ba603"
      ],
      "publication_commits": [
        "c4a16df784376405a45b60df82583e8c26d8a4e3",
        "230ec08a058832bd6941fa887c30897e4826429b",
        "e449cde988d4e97ab280b8d4d11262887ccc26e0"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.ValuationBuildingData.completeSpace_of_isometry_apartmentMap_of_satisfiesApartmentAxioms",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "19c58ff8-7223-425b-bc1f-6d855f29bbff",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-08 at Library commit c4a16df7."
        },
        {
          "declaration": "Langlands.Geometry.Building.FacetClosureUnionClosedStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "89896ed1-e9f6-4245-9941-e43989a63e76",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-10 at Library commit 230ec08a; statement_returns_prop true. The acceptance artifact 7c30292c covers this statement only; the 2026-11-08 declarations were published in the previous instance."
        },
        {
          "declaration": "Langlands.Geometry.Building.facetClosureUnionClosed",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "af281650-cd6f-40cc-96e3-eb3da4b2fa21",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-10 at Library commit e449cde9; a theorem, acceptance artifact b4a3ec65."
        }
      ],
      "external_code": []
    },
    {
      "source_item": "Corollary 4.2.14",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.173 / PDF p.204"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF pp.28–29, Section 4.2",
        "change": "Add Axiom 4.1.6 to the opening hypotheses; the metric of Proposition 4.2.1 is G-invariant and the apartment-independence argument is corrected."
      },
      "hypotheses": [
        "k has a discrete valuation, its valuation ring is Henselian and its residue field is perfect; G is connected reductive over k.",
        "B is the Chapter 4 building satisfying Axioms 4.1.1, 4.1.2, 4.1.4, 4.1.6 and 4.1.9, with the compatible Weyl-invariant Euclidean apartment metrics of Section 4.2.",
        "H is a bounded subgroup of G(k), with boundedness in the algebraic sense of Definition 2.2.1.",
        "For the second assertion, H preserves a nonempty closed convex subset Y of B; Y need not be bounded.",
        "Recorded Lean scope: BoundedSubgroupFixedPointStatement quantifies over every nonarchimedean local field F of either characteristic in universe u, every group scheme G over Spec F with hG : IsConnectedReductive G, and supplied P : ParahoricBuildingData G with a polysimplicial realization R and an apartment splitting T of P.toValuationBuildingData. Its premises are the seven Library predicates of MetricRealizationStatement expressing the five axioms: SatisfiesBuildingAxiom R (4.1.1), HasBoundedOpenStabilizers (4.1.2), SatisfiesAffineApartmentAxiom T (4.1.4), HasRootReflections, SatisfiesApartmentAxioms and HasCompatibleApartmentFacets (4.1.6) and HasTitsSystem (4.1.9). For every subgroup H of rationalPoints G with IsAlgebraicallyBounded F G.X H (Definition 2.2.1) it concludes (1) some x : ReducedBuilding has h • x = x for all h ∈ H, and (2) for every MetricRealization M, with M.metric installed, every closed Y with IsGeodesicallyConvex Y (which includes nonemptiness) and h • y ∈ Y for h ∈ H, y ∈ Y contains such a fixed x. The source's Henselian discretely valued fields with perfect residue field are specialized to nonarchimedean local fields; the specific metric of Proposition 4.2.1 is replaced by an arbitrary complete NPC realization with isometric action and continuous orbit maps, which includes the source metric through metricRealization. Existence of the data, of the axiom witnesses or of a realization is not asserted. The theorem boundedSubgroupFixedPoint (module BoundedSubgroupFixedPointProof) proves this statement; it was accepted as artifact 48dd155d-28ec-4a80-9278-241f507a6013 and first published in Library commit e449cde988d4e97ab280b8d4d11262887ccc26e0."
      ],
      "conclusion": "H fixes a point of B, and fixes a point in Y when such a preserved Y is specified.",
      "lean_declarations": [
        "Langlands.Geometry.Building.BoundedSubgroupFixedPointStatement",
        "Langlands.Geometry.Building.boundedSubgroupFixedPoint"
      ],
      "modules": [
        "Langlands.Geometry.Building.BoundedSubgroupFixedPointStatement",
        "Langlands.Geometry.Building.BoundedSubgroupFixedPointProof",
        "Langlands.Geometry.Building.MetricRealizationStatement",
        "Langlands.AlgebraicGeometry.PointTopology.AffineBoundedness"
      ],
      "dependencies": [
        "Theorem 1.1.15; Proposition 4.2.7; Theorem 4.2.10; Proposition 4.2.13 relating algebraic boundedness and bounded action",
        "Proof: boundedSubgroupFixedPoint, from lean.proof@1 task a20a7c6a-18e6-430e-9ebd-f4e7046e075d (artifact 48dd155d-28ec-4a80-9278-241f507a6013). Its route differs from the source: compactness of the closure of an algebraically bounded set and continuity of orbit maps give bounded orbits, then Theorem 1.1.15(2) and the equivariant nearest-point projection of Proposition 1.1.20 give the fixed points; Proposition 4.2.13 is not used. The statement is conditional on the data and witnesses, whose construction is RootValuationBuildingConstructionStatement (task 00b6788c-23c3-4b22-88f5-41fdbc6d3654)."
      ],
      "consumer_or_regression": "Actual parahoric/fixer and compact-subgroup consumers, retaining the reduced/enlarged and G(k)^0/G(k)^1 distinctions.",
      "formal_status": "conditional",
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [
        "32a5231a-64e5-47b2-abb5-08c7ee214f7c",
        "48dd155d-28ec-4a80-9278-241f507a6013"
      ],
      "publication_commits": [
        "3f0bcbd4638c9c42befdc9f7e1578d62fde2c959",
        "e449cde988d4e97ab280b8d4d11262887ccc26e0"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.BoundedSubgroupFixedPointStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "160d94bb-4f5d-45b2-8eaf-27c9d7e5e2a0",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-09 at Library commit 3f0bcbd4; statement_returns_prop true."
        },
        {
          "declaration": "Langlands.Geometry.Building.boundedSubgroupFixedPoint",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "d676ac8b-f41d-4802-a5fb-f18018a93f4d",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-10 at Library commit e449cde9; a theorem, acceptance artifact 48dd155d."
        }
      ],
      "external_code": []
    },
    {
      "source_item": "Proposition 4.2.24",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.176–177 / PDF pp.207–208; opening of Section 4.2 at printed p.168 / PDF p.199"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF pp.28–30, Sections 4.2 and 5.2",
        "change": "Add Axiom 4.1.6 to the opening hypotheses of Section 4.2. The statement of Proposition 4.2.24 is unchanged; the corrected proofs of Proposition 4.2.1 (PDF p.29) and Theorem 5.2.1 (PDF p.30) cite it."
      },
      "hypotheses": [
        "k has a discrete valuation, its valuation ring is Henselian and its residue field is perfect; G is connected reductive over k.",
        "B is the Chapter 4 building satisfying Axioms 4.1.1, 4.1.2, 4.1.4, 4.1.6 and 4.1.9, with the metric of Section 4.2. A1 and A2 are any two apartments of B.",
        "Recorded Lean scope: ApartmentConjugacyFixingIntersectionStatement quantifies over every nonarchimedean local field F of either characteristic in universe u, every group scheme G over Spec F with [IsAffineHom G.X.hom], and supplied P : ParahoricBuildingData G with a polysimplicial realization R and an apartment splitting T. Its premises are the seven Library predicates of the Corollary 4.2.14 row: SatisfiesBuildingAxiom R (Axiom 4.1.1 for G alone), HasBoundedOpenStabilizers (4.1.2), SatisfiesAffineApartmentAxiom T (4.1.4), HasRootReflections, SatisfiesApartmentAxioms and HasCompatibleApartmentFacets (4.1.6, including V 7) and HasTitsSystem (4.1.9). For all A1 A2 : Set P.toValuationBuildingData.ReducedBuilding with P.IsApartment A1 and P.IsApartment A2 (G(F)-translates of the image of A(S)) it concludes ∃ g ∈ P.zeroSubgroup, g • A1 = A2 ∧ ∀ y ∈ A1 ∩ A2, g • y = y, where P.zeroSubgroup is G(F)^0. The comparisons of Axiom 4.1.1 between groups are not premises. The source's Henselian discretely valued fields with perfect residue field are specialized to nonarchimedean local fields. KPBuildingAssignment.IsAvailableFor supplies all seven premises. Existence of the data or of the axiom witnesses is not asserted. The theorem apartmentConjugacyFixingIntersection (module ApartmentConjugacyFixingIntersectionProof) proves this statement under exactly these seven premises, including the case of an empty intersection; it is present in Library commit ed924aef420de137b4cbaa3b063a3618afcd73fd. The row is therefore conditional until the data and witnesses are constructed."
      ],
      "conclusion": "There is g ∈ G(k)^0 with gA1 = A2 and gx = x for every x ∈ A1 ∩ A2.",
      "lean_declarations": [
        "Langlands.Geometry.Building.ApartmentConjugacyFixingIntersectionStatement",
        "Langlands.Geometry.Building.apartmentConjugacyFixingIntersection"
      ],
      "modules": [
        "Langlands.Geometry.Building.ApartmentConjugacyFixingIntersectionStatement",
        "Langlands.Geometry.Building.ApartmentConjugacyFixingIntersectionProof"
      ],
      "dependencies": [
        "Proposition 1.5.13(1) for the Tits system of Axiom 4.1.9; the Section 4.2 metric and segments (Propositions 4.2.1 and 4.2.3, Definition 4.2.4); A1 ∩ A2 is closed, convex and a union of facets.",
        "The source proof does not treat an empty intersection; that case is the transitivity of G(k)^0 on apartments, used in the corrected proof of Proposition 4.2.1.",
        "Proof: apartmentConjugacyFixingIntersection (module ApartmentConjugacyFixingIntersectionProof), present in Library commit ed924aef420de137b4cbaa3b063a3618afcd73fd. The recorded proof successor was lean.proof@1 Task 5413 (4e839bbd-8290-40d8-9add-333c46e63847), which is absent from the current TaskHub instance, so the acceptance artifact cannot be identified here. The proof follows the source's convex-intersection and facet-fixer strategy. The NPC metric built by MetricRealizationProof makes every translated apartment chart an isometry, which gives segment-convexity of the intersection without closedness or completeness. A point maximizing the dimension of the common kernel of its vanishing roots replaces the source's facet of maximal dimension. A two-facet Tits transport and the normalizer action on the apartment then show that the transporter fixes the intersection pointwise. An empty intersection is handled by the transitivity of G(F)^0 on apartments. The construction of the data and witnesses is RootValuationBuildingConstructionStatement (task 00b6788c-23c3-4b22-88f5-41fdbc6d3654)."
      ],
      "consumer_or_regression": "Corollaries 4.2.25 and 4.2.26, and the corrected source proof of Theorem 5.2.1. The published formal proof availableCartan (task 14dc145a-14d4-47d6-97a6-d89ea0c558ab) uses the sharp fixer and a two-facet Tits transport instead.",
      "formal_status": "conditional",
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [
        "8a396dca-5fc1-4680-94bb-f07abc3a4749"
      ],
      "publication_commits": [
        "d39b5aee822fe2ad1aadf07861ebd9a4c2df62a8",
        "ed924aef420de137b4cbaa3b063a3618afcd73fd"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.ApartmentConjugacyFixingIntersectionStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "0bcd437a-6578-4912-bcb4-baef39b1dc03",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-10 at Library commit e7487341; statement_returns_prop true."
        },
        {
          "declaration": "Langlands.Geometry.Building.apartmentConjugacyFixingIntersection",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "15e79dc4-e3f6-41ab-b40c-fe1543b01405",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit ed924aef; a theorem. Its acceptance artifact cannot be identified in this instance."
        }
      ],
      "external_code": []
    },
    {
      "source_item": "Proposition 4.4.4",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.182–183 / PDF pp.213–214"
      },
      "erratum": null,
      "hypotheses": [
        "k has a discrete valuation, Henselian valuation ring and perfect residue field; G is connected reductive over k.",
        "B satisfies Axioms 4.1.1, 4.1.4 and 4.1.9. S is a maximal k-split torus, N its normalizer, and A its associated affine apartment.",
        "Recorded Lean scope: only the group-action algebra of the presentation is formalized, for an arbitrary group H, subgroup N, N-set A and conjugation-covariant subgroup family P. ApartmentQuotient.mk_eq_mk_iff gives exactly the fibres (g,x)~(h,y) iff some n∈N has n·x=y and g⁻¹hn∈P x; stabilizer_apartment_eq_sup identifies the stabilizer of [(1,x)] with P x ⊔ N_x; map_id_bijective_iff_le_sup is the replacement criterion for an intermediate family. ApartmentQuotient.liftEquiv identifies the quotient H-equivariantly with any H-set carrying an injective N-equivariant apartment map whose point stabilizers contain P x, under common translated apartments and orbit coverage, all as explicit hypotheses. The Library's constructed quotient ValuationBuildingData.ReducedBuilding is by definition ApartmentQuotient of the sharp point-fixer family (the Chapter 7 quotient of Remark 7.6.5), so the presentation holds for it by construction. The source statement for an arbitrary building satisfying 4.1.1, 4.1.4 and 4.1.9 has no separate Lean declaration."
      ],
      "conclusion": "The G(k)-equivariant map (g,x)↦g·x from G(k)×A onto B has fibres given by (g,x)~(h,y) iff some n∈N(k) has n·x=y and g^(-1)hn∈G(k)_x. The full stabilizer can be replaced by G(k)^natural_x or an intermediate subgroup, subject to the source comparison.",
      "lean_declarations": [
        "Langlands.Geometry.Building.ApartmentQuotient.mk_eq_mk_iff",
        "Langlands.Geometry.Building.ApartmentQuotient.stabilizer_apartment_eq_sup",
        "Langlands.Geometry.Building.ApartmentQuotient.map_id_bijective_iff_le_sup",
        "Langlands.Geometry.Building.ApartmentQuotient.liftEquiv",
        "Langlands.Geometry.Building.ApartmentQuotient.liftEquiv_smul"
      ],
      "modules": [
        "Langlands.Geometry.Building.ApartmentQuotient",
        "Langlands.Geometry.Building.ApartmentQuotientComparison",
        "Langlands.Geometry.Building.KPBuilding"
      ],
      "dependencies": [
        "Apartment conjugacy; transporter to the normalizer; point stabilizers; Proposition 4.4.3 for the affine apartment conventions"
      ],
      "consumer_or_regression": "Actual building quotient presentation; conditional algebraic quotient child cd3fd695-b511-4653-8f4d-769e99d8aab0 supplies only a reusable prerequisite.",
      "formal_status": "conditional",
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [
        "c4a16df784376405a45b60df82583e8c26d8a4e3"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.ApartmentQuotient.liftEquiv_smul",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "cd5b34df-3104-4c43-beb8-052a9b5adf18",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-08 at Library commit c4a16df7."
        }
      ],
      "external_code": []
    },
    {
      "source_item": "Corollary 4.4.5",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.183–184 / PDF pp.214–215"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.29, Section 4.4",
        "change": "Replace the existential pair by EVERY corresponding pair and remove the intervening such-that wording."
      },
      "hypotheses": [
        "B1 and B2 are buildings for the same G satisfying Axioms 4.1.1, 4.1.4 and 4.1.9; A1 and A2 correspond to the same maximal k-split torus.",
        "For EVERY pair x1∈A1 and x2∈A2 corresponding under the canonical affine isomorphism of Proposition 4.4.3, G(k)^0_(x1) is a subgroup of G(k)^0_(x2).",
        "The field and reductive-group conventions are those of Chapter 4 (discrete valuation, Henselian valuation ring, perfect residue field, connected reductive G).",
        "Recorded Lean scope: for two supplied B1, B2 : ValuationBuildingData G over the same nonarchimedean local field, an affine equivalence e : A1 ≃ᵃ[ℝ] A2 with the normalizer-equivariance hypothesis hN, and the fixer inclusion hfix : ∀ x, B1.sharpFixer {x} ≤ B2.fixer (B2.apartmentMap (e x)) quantified over EVERY source apartment point, quotientComparison is the unique equivariant extension; it is bijective under common source apartments (supplied by SatisfiesBuildingAxiom.hasCommonApartments from a 4.1.1 witness) and injectivity of the target apartment map, and with equality of the transported affine-root sets (hroots) quotientComparisonEquiv satisfies IsEquivariantBuildingIso with the identity on G(F). The Lean hypothesis compares source sharp fixers with full target point fixers, not G(k)^0_(x1) with G(k)^0_(x2); the comparison of these subgroup families, the canonical isomorphism of Proposition 4.4.3 and the agreement of facet subgroups are not formalized."
      ],
      "conclusion": "The canonical apartment isomorphism extends uniquely to a G(k)-equivariant building isomorphism B1→B2; corresponding facet subgroups G(k)^0_F agree.",
      "lean_declarations": [
        "Langlands.Geometry.Building.ApartmentQuotient.map_bijective_of_common_translated_apartment",
        "Langlands.Geometry.Building.ApartmentQuotient.lift_unique",
        "Langlands.Geometry.Building.ValuationBuildingData.quotientComparison",
        "Langlands.Geometry.Building.ValuationBuildingData.quotientComparisonEquiv",
        "Langlands.Geometry.Building.ValuationBuildingData.quotientComparisonEquiv_isEquivariantBuildingIso"
      ],
      "modules": [
        "Langlands.Geometry.Building.ApartmentQuotient",
        "Langlands.Geometry.Building.ApartmentQuotientComparison",
        "Langlands.Geometry.Building.ValuationBuildingQuotientComparison"
      ],
      "dependencies": [
        "Propositions 4.4.3 and 4.4.4; apartments containing point pairs; facet recovery from stabilizers"
      ],
      "consumer_or_regression": "Regression must reject a single-pair replacement for the universal hypothesis; quotient surjectivity alone does not establish the building isomorphism.",
      "formal_status": "conditional",
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [
        "c4a16df784376405a45b60df82583e8c26d8a4e3"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.ValuationBuildingData.quotientComparisonEquiv_isEquivariantBuildingIso",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "3da4920a-c96f-4ec6-bd42-dedb0926b0a5",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-08 at Library commit c4a16df7."
        }
      ],
      "external_code": []
    },
    {
      "source_item": "Definition 4.1.26",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.165 / PDF p.196; axioms at printed pp.157–164 / PDF pp.188–195"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.27, Section 4.1",
        "change": "Replace the definition's shorter axiom list by 4.1.1, 4.1.2, 4.1.4, 4.1.6, 4.1.8, 4.1.9, 4.1.16, 4.1.17, 4.1.20 and 4.1.22. AS3 includes the identity in U_psi and U_psi+; 4.1.8(2) requires a nonempty bounded subset; 4.1.9 uses the restricted building and its corrected parabolic wording."
      },
      "hypotheses": [
        "The Chapter 4 ambient conventions are a discretely valued field k with Henselian valuation ring and perfect residue field, and a connected reductive k-group G. Finiteness of the residue field is not required.",
        "Building, apartment, action, root-group and integral-model data must satisfy all ten listed axioms. This is a definition of availability, not an existence assertion or permission to assume these data at the general endpoint.",
        "Recorded Lean scope: KPBuildingAssignment.IsAvailableFor 𝔅 F G hG is a Prop-valued structure with exactly one field for each of the ten corrected axioms, on supplied data KPBuildingDatum G (base ParahoricBuildingData, polysimplicial realization, apartment splitting, integral-model family over 𝒪[F], special-fibre quotient family and relative root reflection data) chosen by an assignment 𝔅 for every nonarchimedean local field F in universe u and every connected reductive G/F. KPBuildingAssignment.IsValid quantifies it over all (F, G). Axiom 4.1.27 is not a field. The Henselian discretely valued fields of the source are replaced by nonarchimedean local fields of either characteristic, also in the cross-field Axiom 4.1.17. The comparison clauses of 4.1.1 and 4.1.17 ask for existence of equivariant building isomorphisms and do not formalize canonicity. No predicate is asserted to hold for any data."
      ],
      "conclusion": "Bruhat–Tits theory is available precisely when every axiom in the corrected ten-item list holds. In the program, the general constructed instance must also satisfy unramified descent Axiom 4.1.27; a conditional package of axioms alone does not meet that requirement.",
      "lean_declarations": [
        "Langlands.Geometry.Building.KPBuildingDatum",
        "Langlands.Geometry.Building.KPBuildingDatum.SatisfiesGroupAxioms",
        "Langlands.Geometry.Building.KPBuildingAssignment",
        "Langlands.Geometry.Building.KPBuildingAssignment.IsAvailableFor",
        "Langlands.Geometry.Building.KPBuildingAssignment.IsValid"
      ],
      "modules": [
        "Langlands.Geometry.Building.FullValidity.Realization",
        "Langlands.Geometry.Building.FullValidity.AffineApartment",
        "Langlands.Geometry.Building.FullValidity.ChamberAxioms",
        "Langlands.Geometry.Building.FullValidity.Assignment",
        "Langlands.BruhatTits.IntegralModels.ModelFamily",
        "Langlands.BruhatTits.IntegralModels.FacetAxioms"
      ],
      "dependencies": [
        "Axioms 4.1.1, 4.1.2, 4.1.4, 4.1.6, 4.1.8, 4.1.9, 4.1.16, 4.1.17, 4.1.20 and 4.1.22, with the corrections applied",
        "Source construction map 4.1.28 and Chapter 9; see the certificate map below for the separately derived 4.1.16 route and the full isomorphism scope of 4.1.17"
      ],
      "consumer_or_regression": "Theorem 9.2.7 certificate on the descended instance; tests must retain parahoric/full-fixer, reduced/enlarged and special-fibre/reductive-quotient distinctions.",
      "formal_status": "definition",
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [
        "c4a16df784376405a45b60df82583e8c26d8a4e3"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.KPBuildingAssignment.IsAvailableFor",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "570b2f45-35c5-44da-b480-eb7300e4ec92",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-08 at Library commit c4a16df7."
        }
      ],
      "external_code": []
    },
    {
      "source_item": "Theorem 7.5.3",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.260–261 / PDF pp.291–292; Chapter 7 hypotheses at printed pp.235–236 / PDF pp.266–267"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF pp.33 and 35, Chapter 7 and Section 7.5",
        "change": "Add AS5 of Axiom 4.1.6 to the Chapter 7 hypotheses. The proof of 7.5.1 uses AS5 for the affine Weyl identification; its saturation intersection is over conjugates n I n^(-1). Corrections to 7.5.2 use Z' and the preimage of I^sharp intersect Z(k)."
      },
      "hypotheses": [
        "k has a discrete valuation omega with Henselian valuation ring and omega(k^times)=Z, as stipulated outside Section 7.10. The residue field need not be perfect.",
        "G is connected reductive. To each maximal k-split torus S is assigned an affine apartment A(S), an equipollence class of root-datum valuations in the sense of 6.1.2 and 6.1.7, with the normalizer action of 6.1.8 and the equivariance required by Axiom 4.1.4.",
        "AS5 of Axiom 4.1.6 is assumed in addition. For general G, valuations and AS5 are not constructed merely by stating the Chapter 7 hypotheses; in the perfect-residue setting Chapter 9 supplies them.",
        "Write N=N_G(S) and Z=Z_G(S). Fix a chamber C in A(S), I=G(k)^0_C and the wall reflections R. The two ambient groups are G(k)^0 and G(k)^natural, with N intersected with the respective group. As in Section 7.5, I^natural=I^sharp Z^natural, where Z^natural is the image of Z'(k)^0 and Z' is the inverse image of Z in G_sc.",
        "Recorded Lean scope: AffineIwahoriTitsStatement states only the G(F)^0 branch of 7.5.3(1),(2), for every nonarchimedean local field F, affine F-group scheme G and supplied P : ParahoricBuildingData G with P.apartment.SatisfiesApartmentAxioms P.centralizer and every chamber C of A(S): normality of P.normalizerZero and P.zeroSubgroup, and P.AffineIwahoriTits C (a multiplicative equivalence of the affine part of N(F) ∩ G(F)^0 with the affine Weyl group W(Ψ) realizing the actual apartment action, the published IsTitsSystem for G(F)^0, the generated parahoric of C, N(F) ∩ G(F)^0 and the chamber-simple reflections, and the corrected saturation as an intersection of conjugates). The G(F)^natural branch and the conjugacy of choices are not stated. affineIwahoriTits_of_inputs derives P.AffineIwahoriTits C from normality of P.normalizerZero, an action comparison and the eight fields of AffineIwahoriTitsInputs C, which are explicit hypotheses of that lemma. At c4a16df7 three fields are proved under the apartment axioms: closure_chamberSimpleReflections (closure_chamberSimpleReflections_affineRoots, KP Proposition 1.3.22(1)), parahoric_le_zeroSubgroup (from ApartmentRootCover) and zeroSubgroup_le_sup (chamberParahoricGeneration : ChamberParahoricGenerationStatement). affineIwahoriTitsStatement_of_inputStatements derives AffineIwahoriTitsStatement from IwahoriWeylExactSequenceStatement (KP 7.8.1(1), which supplies both normalities and the comparison), AffineRankOneTwoCellStatement (KP Lemma 7.1.5(3)) and the five statements of AffineIwahoriTitsInputStatements. Of these seven, six have published proofs, all present in Library commit ed924aef420de137b4cbaa3b063a3618afcd73fd: chamberParahoricGeneration, chamberParahoricNormalizer, rootGroupParahoricFiltration, chamberConjugateIntersection, chamberSimpleFactorization and affineRankOneTwoCell. Only IwahoriWeylExactSequenceStatement (KP 7.8.1(1)) is open. The published reduction iwahoriWeylNormalizerAffineWeylReduction derives it, together with IwahoriWeylChamberSplittingStatement (KP 7.8.2), from SimplyConnectedNormalizerAffineWeylStatement (the range part of 7.5.3(2); proof task 5210ae85-2886-4b9f-af36-d57d6dba2607). The published reduction simplyConnectedNormalizerAffineWeylReduction derives that statement from SimplyConnectedFacetFixingStatement (proof task c5ad9ef0-554c-4af8-be60-3607ad0e7e9b) and Langlands.GroupScheme.DerivedCentralSplitTorusProductStatement, which is proved by Langlands.GroupScheme.derivedCentralSplitTorusProduct. So AffineIwahoriTitsStatement now waits only on SimplyConnectedFacetFixingStatement. The published module SimplyConnectedFacetFixingReduction reduces that statement further to SimplyConnectedReflectionTranslationStatement, to SimplyConnectedRankOneCentralizerGenerationStatement or to SimplyConnectedKneserTitsCentralizerStatement, none of them proved."
      ],
      "conclusion": "The two tuples (G(k)^0,I,N(k) intersect G(k)^0,R) and (G(k)^natural,I^natural,N(k) intersect G(k)^natural,R) are saturated Tits systems. Their Weyl groups identify with the affine Weyl group of Psi through the apartment action. Choices of torus and chamber give systems conjugate under G(k)^natural. This statement does not replace either ambient group by full G(k).",
      "lean_declarations": [
        "Langlands.Geometry.Building.AffineIwahoriTitsStatement",
        "Langlands.Geometry.Building.ParahoricBuildingData.affineIwahoriTits_of_inputs",
        "Langlands.Geometry.Building.ParahoricBuildingData.affineIwahoriTitsInputs_of_statements",
        "Langlands.Geometry.Building.affineIwahoriTitsStatement_of_inputStatements",
        "Langlands.Geometry.Building.chamberParahoricGeneration",
        "Langlands.Geometry.Building.chamberParahoricNormalizer",
        "Langlands.Geometry.Building.rootGroupParahoricFiltration",
        "Langlands.Geometry.Building.chamberConjugateIntersection",
        "Langlands.Geometry.Building.chamberSimpleFactorization",
        "Langlands.Geometry.Building.affineRankOneTwoCell",
        "Langlands.Geometry.Building.iwahoriWeylNormalizerAffineWeylReduction",
        "Langlands.Geometry.Building.simplyConnectedNormalizerAffineWeylReduction",
        "Langlands.GroupScheme.derivedCentralSplitTorusProduct",
        "Langlands.Geometry.Building.simplyConnectedFacetFixingReduction"
      ],
      "modules": [
        "Langlands.Geometry.Building.AffineIwahoriTits",
        "Langlands.Geometry.Building.AffineIwahoriTitsStatement",
        "Langlands.Geometry.Building.AffineIwahoriTitsInputStatements",
        "Langlands.Geometry.Building.AffineIwahoriTitsAssembly",
        "Langlands.Geometry.Building.ChamberParahoricGenerationProof",
        "Langlands.Geometry.Building.ChamberParahoricNormalizerProof",
        "Langlands.Geometry.Building.RootGroupParahoricFiltrationProof",
        "Langlands.Geometry.Building.ChamberConjugateIntersectionProof",
        "Langlands.Geometry.Building.ChamberSimpleFactorizationProof",
        "Langlands.Geometry.Building.AffineRankOneTwoCellProof",
        "Langlands.Geometry.Building.IwahoriWeylNormalizerAffineWeylReduction",
        "Langlands.Geometry.Building.SimplyConnectedNormalizerAffineWeylAssembly",
        "Langlands.GroupScheme.Derived.CentralSplitTorusProductProof",
        "Langlands.Geometry.Building.SimplyConnectedFacetFixingReduction"
      ],
      "dependencies": [
        "Chapter 6 affine roots, valuation and normalizer action; corrected AS5 assumption",
        "Theorem 7.5.1, Lemma 7.5.2 and Lemma 1.4.12; Section 7.4 parahoric construction and Corollary 7.4.9",
        "For the general perfect-residue construction: Proposition 9.4.35, Theorem 9.6.5 and the every-point comparison in 9.6.6",
        "Open proof tasks: 20fbe465-f4ae-4fe9-9846-2201f1c31d28 (AffineIwahoriTitsStatement), 5210ae85-2886-4b9f-af36-d57d6dba2607 (SimplyConnectedNormalizerAffineWeylStatement, range part of 7.5.3(2)) and c5ad9ef0-554c-4af8-be60-3607ad0e7e9b (SimplyConnectedFacetFixingStatement). On 13 November 2026 the first two follow from the third through the published reductions listed in the last hypotheses entry; the third is the only open input of AffineIwahoriTitsStatement."
      ],
      "consumer_or_regression": "Restricted building construction 7.6.1 and the affine part of later double-coset decompositions. A nontrivial length-zero/component example must retain the full Iwahori–Weyl data separately.",
      "formal_status": "statement",
      "owner_task": "20fbe465-f4ae-4fe9-9846-2201f1c31d28",
      "acceptance_artifact_ids": [],
      "publication_commits": [
        "c4a16df784376405a45b60df82583e8c26d8a4e3",
        "ed924aef420de137b4cbaa3b063a3618afcd73fd"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.AffineIwahoriTitsStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "31806803-3dfd-4221-80b8-655c4a2b3201",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-08 at Library commit c4a16df7; statement_returns_prop true."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.affineIwahoriTits_of_inputs",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "1108a1a2-4e0e-4e08-a273-ad69165fc7ed",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-08 at Library commit c4a16df7."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.affineIwahoriTitsInputs_of_statements",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "b2562934-5c25-4838-84db-14f12b92c520",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-09 at Library commit c4a16df7."
        },
        {
          "declaration": "Langlands.Geometry.Building.affineIwahoriTitsStatement_of_inputStatements",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "8a6e9492-784f-4730-b714-7b43639240e6",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-09 at Library commit c4a16df7."
        },
        {
          "declaration": "Langlands.Geometry.Building.chamberParahoricGeneration",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "945f41b4-347c-413e-8dd7-7a88471248df",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-09 at Library commit c4a16df7."
        },
        {
          "declaration": "Langlands.Geometry.Building.chamberParahoricNormalizer",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "6c97181e-94d3-42bc-9e4d-086f26d71e83",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit ed924aef; a theorem proving ChamberParahoricNormalizerStatement. Its acceptance artifact cannot be identified in this instance."
        },
        {
          "declaration": "Langlands.Geometry.Building.rootGroupParahoricFiltration",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "160ec648-5d00-4333-9993-08ef1ac08318",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit ed924aef; a theorem proving RootGroupParahoricFiltrationStatement. Its acceptance artifact cannot be identified in this instance."
        },
        {
          "declaration": "Langlands.Geometry.Building.chamberConjugateIntersection",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "1fbe15ec-69a9-466b-a781-d8542ccc75e5",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit ed924aef; a theorem proving ChamberConjugateIntersectionStatement. Its acceptance artifact cannot be identified in this instance."
        },
        {
          "declaration": "Langlands.Geometry.Building.chamberSimpleFactorization",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "d9477702-8b84-42fa-852b-616c3270d5f8",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit ed924aef; a theorem proving ChamberSimpleFactorizationStatement. Its acceptance artifact cannot be identified in this instance."
        },
        {
          "declaration": "Langlands.Geometry.Building.affineRankOneTwoCell",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "cca5d177-4f8e-4817-bf57-1e48c3b46989",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit ed924aef; a theorem proving AffineRankOneTwoCellStatement. Its acceptance artifact cannot be identified in this instance."
        },
        {
          "declaration": "Langlands.Geometry.Building.iwahoriWeylNormalizerAffineWeylReduction",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "826bc372-1a07-4ece-86ae-c5eb8a507551",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit ed924aef; a theorem proving IwahoriWeylNormalizerAffineWeylReductionStatement (SimplyConnectedNormalizerAffineWeylStatement implies IwahoriWeylExactSequenceStatement and IwahoriWeylChamberSplittingStatement)."
        },
        {
          "declaration": "Langlands.Geometry.Building.simplyConnectedNormalizerAffineWeylReduction",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "65803d96-5a8c-4091-ac67-6b30a31362b6",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit ed924aef; a theorem proving SimplyConnectedNormalizerAffineWeylReductionStatement (SimplyConnectedFacetFixingStatement and DerivedCentralSplitTorusProductStatement imply SimplyConnectedNormalizerAffineWeylStatement)."
        },
        {
          "declaration": "Langlands.GroupScheme.derivedCentralSplitTorusProduct",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "44f2ebb5-c275-45c0-8405-b7287c2e3640",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit ed924aef; a theorem proving Langlands.GroupScheme.DerivedCentralSplitTorusProductStatement. Its acceptance artifact cannot be identified in this instance."
        },
        {
          "declaration": "Langlands.Geometry.Building.simplyConnectedFacetFixingReduction",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "09220f6e-1ec6-409b-ab73-df00674e8b50",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit ed924aef; a theorem proving SimplyConnectedFacetFixingReductionStatement (SimplyConnectedReflectionTranslationStatement implies SimplyConnectedFacetFixingStatement)."
        }
      ],
      "external_code": []
    },
    {
      "source_item": "Theorem 9.2.7",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.329 / PDF p.360; construction 9.2.1–9.2.6 at PDF pp.354–360; assembly 9.5 at printed pp.363–364 / PDF pp.394–395"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.27 (corrected Definition 4.1.26), pp.39–41 (Section 9.2 and Section 9.3); Chapter 7 AS5 addition at p.33",
        "change": "Read availability against the corrected ten-axiom definition, rather than the shorter printed theorem list. The corrected finite-Gamma-orbit argument uses a finite Galois unramified splitting extension; the added bounded-Gamma-stable-subgroup fixed-point argument uses Theorem 1.1.15. Proposition 9.3.12 uses a bounded subset contained in an apartment. The replacement 9.3.25 proof distinguishes restricted from full Tits buildings."
      },
      "hypotheses": [
        "k is discretely valued with omega(k^times)=Z and Henselian valuation ring o; its residue field is perfect. G is any connected reductive k-group. No global splitness, quasi-splitness, tame splitting or finite-residue hypothesis is imposed.",
        "K is the maximal unramified extension in a fixed separable closure, O its valuation ring, and Gamma=Gal(K/k). Corollary 2.3.8 makes G_K quasi-split; its building and models are the actual Chapter 6–8 constructions, not assumed general existence data.",
        "B is B(G_K)^Gamma with the restricted metric. Apartments are Gamma-fixed apartments attached to special k-tori of 9.2.2. Facets are intersections with Gamma-stable K-facets as in 9.2.4. Models are the smooth affine o-models descended in 9.2.5, with their relative identity components.",
        "Recorded Lean scope (corrected Definition 4.1.26 part only): the published, unproved BruhatTitsAvailabilityStatement is ∃ 𝔅 : KPBuildingAssignment.{u}, 𝔅.IsValid. It asserts that one assignment of KPBuildingDatum to every connected reductive G over every nonarchimedean local field F in universe u satisfies all ten corrected axioms of the Definition 4.1.26 row, including the comparisons of 4.1.1 and 4.1.17 between the data assigned to different groups and fields. It differs from the source in four ways: it uses the corrected ten-axiom list rather than the seven printed in the theorem; Axiom 4.1.27 is not part of it; it asserts existence of some data rather than availability for the descended construction B(G_K)^Gamma, its apartments, facets and models; and the source's Henselian discretely valued fields with perfect residue field are specialized to nonarchimedean local fields. The building, apartment, chamber and facet assertions of the theorem have no separate Lean declaration. The status statement of this row covers only this part, which is not the program's certificate."
      ],
      "conclusion": "B with these apartments and polysimplices is a building whose apartments correspond bijectively to maximal k-split tori. Chambers and facets are fixed parts of Gamma-chambers and Gamma-facets, and G(k) acts by polysimplicial isometries. For the program's certificate, the constructed geometry and descended models must satisfy every axiom of corrected Definition 4.1.26 and Axiom 4.1.27, using the source assembly and the explicitly derived completion routes below.",
      "lean_declarations": [
        "Langlands.Geometry.Building.BruhatTitsAvailabilityStatement",
        "Langlands.Geometry.Building.BruhatTitsAvailabilityReductionStatement",
        "Langlands.Geometry.Building.GroupAxiomsExistenceReductionStatement",
        "Langlands.Geometry.Building.bruhatTitsAvailabilityReduction",
        "Langlands.Geometry.Building.groupAxiomsExistenceReduction"
      ],
      "modules": [
        "Langlands.Geometry.Building.BruhatTitsAvailabilityStatement",
        "Langlands.Geometry.Building.FullValidity.Assignment",
        "Langlands.Geometry.Building.BruhatTitsAvailabilityReductionStatement",
        "Langlands.Geometry.Building.GroupAxiomsExistenceReductionStatement",
        "Langlands.Geometry.Building.BruhatTitsAvailabilityReductionProof",
        "Langlands.Geometry.Building.GroupAxiomsExistenceReduction"
      ],
      "dependencies": [
        "Quasi-split Chapter 6–8 building and actual integral models; Corollary 2.3.8; descent Fact 2.10.16; special k-tori Proposition 9.3.4",
        "Complete NPC fixed-point theory (Theorem 1.1.15), corrected 9.2.1; geometry and restricted-building arguments of Sections 9.3–9.4, including corrected 9.3.25 and AS5 Proposition 9.4.35",
        "Axiom-by-axiom source map in Section 9.5, expanded below; for 4.1.16 use Sections 9.6 and 7.3–7.4 with corrected every-point Corollary 4.4.5",
        "For 4.1.17, Proposition 7.9.5 and transport of the descended construction under all covering field/group isomorphisms; a Gamma action alone is not the full axiom",
        "G(k)^0=G(K)^0 intersect G(k) (9.3.24) and the G(k)^1 intersection identity; model base change and root compatibility for Axiom 4.1.27",
        "Published partial target, not the certificate: Langlands.Geometry.Building.RootValuationBuildingConstructionStatement (module of the same name) asks, for every nonarchimedean local field F and connected reductive G/F, for constructed P : ParahoricBuildingData G, realization and splitting with only the five Section 4.2 axiom witnesses (one-group 4.1.1, 4.1.2, 4.1.4, 4.1.6, 4.1.9) on the existing valuation quotient. Its proof task is 00b6788c-23c3-4b22-88f5-41fdbc6d3654. Together with metricRealization it would make the Proposition 4.2.7 and Theorem 4.2.10 rows unconditional; it does not supply 4.1.8, 4.1.16, 4.1.17, 4.1.20, 4.1.22, 4.1.27 or the 4.1.1 comparison clauses.",
        "Open proof obligation: BruhatTitsAvailabilityStatement has no proof task. Its proof belongs to this program and is split into the focused statements of the next entry; task 00b6788c-23c3-4b22-88f5-41fdbc6d3654 covers only the five Section 4.2 axioms above. Published statements with the hypothesis 𝔅.IsAvailableFor F G hG or 𝔅.IsValid are conditional on it. Among them are AvailableCartanStatement (Theorem 5.2.1 row, proved by availableCartan, artifact c3a16a8e-fad7-484f-9e90-64f897f020eb) and AvailableIwasawaStatement (Theorem 5.3.4 row, proved by availableIwasawa, artifact 42bb1c08-a7ac-49f5-a197-dc1d5707a42e), and two Renard-sourced statements whose proof tasks belong to proof task 8c39faa0-2a70-4fc4-a027-914987aba924: Langlands.Plancherel.RenardCartan.AvailableRenardCartanStatement (task be989fac-448d-4a56-ad1b-663853caf8cd) and Langlands.BruhatTits.SpecialCompact.AvailableSimultaneousStandardBasisStatement (task 8d4643b8-dcf9-476e-a86f-04b62b8d738f). Task 7dc04fe2-f965-4f59-b63c-75f5012b3f64 published three more statements in Langlands.BruhatTits.SpecialCompact, first in Library commit e449cde988d4e97ab280b8d4d11262887ccc26e0: ValidAssignmentTorusRebasingStatement and AvailableSpecialLeviCompactStatement assume 𝔅.IsValid, and AvailableSpecialVertexExistenceStatement assumes 𝔅.IsAvailableFor F G hG. Their proof tasks are Task 5348 (9ec91e66-99df-4afa-be5c-3e5c59207196), Task 5350 (bbd398f5-8ddc-4b82-85ab-bf3f0ef59d81) and Task 5349 (8ecbd7c3-bf60-4c93-a0ef-afa198caf8b3); none of the three tasks is present in the current TaskHub instance. All three are proved. validAssignmentTorusRebasing (module Langlands.BruhatTits.SpecialCompact.ValidTorusRebasingProof, artifact 1ad050ff-f388-4c2e-9276-97aa6080b19d, first published in Library commit 47820896f9935b0f378578d8609dc6e7ee353c79) proves ValidAssignmentTorusRebasingStatement by applying rebaseAssignmentFromDatumTransport to the proved kpBuildingDatumTransportStatement; its official lean.proof@1 validation 7ee53f31-2d37-4969-b19f-2d3ed178fe5f (lake-build, exact-target, unchanged-statement, frozen-inputs) is accepted, and a declaration inspection by Worker 3557 did not complete. availableSpecialVertexExistence (module Langlands.BruhatTits.SpecialCompact.AvailableSpecialVertexProof, artifact 8fbf039f-0ede-4921-9405-d9aaf3119ad1, present in Library commit 529b851ca9671cd9807187e571a5ea50ea7dd328; official validation a8a82aa9-0674-4117-8f1e-eda2d41a15f6) proves AvailableSpecialVertexExistenceStatement: Axiom 4.1.6 (AS 3) of available data makes the apartment roots an affine root system, IsAffineRootSystemWithRankZero.exists_isSpecialPoint (module Langlands.Geometry.Building.SpecialPointExistence) gives a special point and AffineRootSystem.isVertex_of_isSpecialPoint shows that it is a vertex; lean_check inspection 836b932f-d272-4e20-8231-3dd8aafeaa59 by Worker 3557 on 2026-11-12 at Library commit 24a49431 reports kind theorem and only propext, Classical.choice and Quot.sound. availableSpecialLeviCompact (module Langlands.BruhatTits.SpecialCompact.AvailableSpecialLeviCompactProof, present in Library commit ed924aef420de137b4cbaa3b063a3618afcd73fd; acceptance artifact not identifiable in this instance) proves AvailableSpecialLeviCompactStatement; lean_check inspection bc9c3cd0-0aa9-42c7-b7b0-2d4ec8efd3dc by Worker 3557 on 2026-11-13 at Library commit ed924aef reports kind theorem and only propext, Classical.choice and Quot.sound. All three proved theorems keep the premise 𝔅.IsValid or 𝔅.IsAvailableFor F G hG, and none of these tasks proves that available data exist. The published reduction jointBasisReduction (module Langlands.BruhatTits.SpecialCompact.JointBasisReductionProof, present in Library commit ed924aef; inspection f0afa0c2-2d10-48e2-a6b5-635c061dd7ed on 2026-11-13, same axioms) proves JointBasisReductionStatement: the existence of a valid assignment together with six conditional statements implies JointSpecialCompactBasisExistenceStatement, which places the special compact properties, standard-Levi inheritance, the ambient and Levi Iwasawa products, the Cartan comparisons and the simultaneous Renard basis at one apartment class and one point. Five of the six are proved (ValidAssignmentTorusRebasingStatement, AvailableSpecialVertexExistenceStatement, AvailableIwasawaStatement, AvailableSpecialLeviCompactStatement and AvailableSimultaneousStandardBasisStatement); AvailableRenardCartanStatement is not. availableSimultaneousStandardBasis (module Langlands.BruhatTits.SpecialCompact.AvailableBasisProof; proof Task 5310, 8d4643b8-dcf9-476e-a86f-04b62b8d738f; artifact 0a999553-7620-4d51-a8d4-c6f98a168d23, first in Library commit 51e4d8972659f1ffcf0ca89e8eee9540a30b52d3) proves AvailableSimultaneousStandardBasisStatement. Its only building premise is 𝔅.IsValid. For every generic cocharacter ν and every special vertex x of the apartment of the datum it gives the three conjuncts SpecialCompactProperties, SpecialLeviInheritance and SimultaneousStandardBasisAt for the special compact subgroup at x. The first two come from availableSpecialCompactProperties_of_omegaCompatibleApartment and availableSpecialLeviInheritance_of_omegaCompatibleApartment, the third from CongruenceGL.available_simultaneousStandardBasisAt through IsValid.isAvailableFor; lean_check inspection e1902707-d619-4529-9b06-4a679f6e1dff by Worker 3557 on 2026-11-13 at Library commit 0f84a0d8 reports kind theorem and only propext, Classical.choice and Quot.sound.",
        "Decomposition (KP 4.1.28 assigns the axioms to Chapters 6–8). Six published statements of this program, first in Library commit 58a91d4ff65b8d6dcb8aa417bfc63399feb8b4af, split availability. KPBuildingAssignment.isAvailableFor_iff separates IsAvailableFor into KPBuildingDatum.SatisfiesGroupAxioms, the comparison clauses of Axiom 4.1.1 and Axiom 4.1.17. Accordingly GroupAxiomsExistenceStatement (every connected reductive G over every nonarchimedean local field has some KPBuildingDatum satisfying the clauses of the ten axioms that concern G alone), BuildingComparisonAxiomStatement (the comparison clauses of Axiom 4.1.1 for all supplied valuation-building data; proof task Task 5427, 45fca8a2-fdf4-4530-98eb-a6307a31f6cf) and IsomorphismCompatibilityAxiomStatement (Axiom 4.1.17 for all supplied data; proof task Task 5428, fa830bf4-4cc7-4e50-9b79-c65dfb6110c4) are intended to give BruhatTitsAvailabilityStatement. The two comparison statements are proved: buildingComparisonAxiom (module BuildingComparisonAxiomProof) and isomorphismCompatibilityAxiom (module IsomorphismCompatibilityAxiomProof), both present in Library commit ed924aef420de137b4cbaa3b063a3618afcd73fd; lean_check inspections a47f35ec-2d5b-484f-98e1-0bc4442035be and 3197efea-91c5-4d27-9b4c-31f9f382d385 by Worker 3557 on 2026-11-13 report kind theorem and only propext, Classical.choice and Quot.sound. Their acceptance artifacts cannot be identified in this instance; Task 5427 is absent from it, and Task 5428 was carried into it with a resubmitted candidate under verification on 13 November 2026. BruhatTitsAvailabilityStatement therefore waits only on GroupAxiomsExistenceStatement, by the proved implication BruhatTitsAvailabilityReductionStatement described below. GroupAxiomsExistenceStatement is in turn intended to follow from RootValuationBuildingConstructionStatement together with RootGroupActionAxiomStatement (Axiom 4.1.8(2),(3); Task 5425, 7aba1f84-72ba-4b7d-b839-5e1bb849fcf2), IwahoriDecompositionAxiomStatement (Axiom 4.1.16; Task 5426, 96685786-b196-4cbf-83bc-4bdee7ffb004) and IntegralModelAxiomsStatement (Axioms 4.1.20 and 4.1.22; Task 5429, cd2ad671-3edf-4905-a0e2-e7aa2b160b91). Both implications are published statements of this program, first in Library commit cfedefb680f317b0ea5d351023e1c9dd886b2547. BruhatTitsAvailabilityReductionStatement (module of the same name, artifact f147f7c0-08ca-4572-a5b9-d27efde033b8) is GroupAxiomsExistenceStatement → BruhatTitsAvailabilityStatement. GroupAxiomsExistenceReductionStatement (module of the same name, artifact 432145f3-166b-4c77-af14-c477854c91bc) is RootValuationBuildingConstructionStatement → RootGroupActionAxiomStatement → IwahoriDecompositionAxiomStatement → IntegralModelAxiomsStatement → GroupAxiomsExistenceStatement. Both implications are proved, and both proofs are present in Library commit 730bd1f25b056b8106a2697e003c1ef1733a6b30. The theorem bruhatTitsAvailabilityReduction (module Langlands.Geometry.Building.BruhatTitsAvailabilityReductionProof; proof Task 5926, 47b47ccd-a059-40f4-bbc1-169685c862ea; artifact e160a237-a0d7-4683-9ba1-68a4ec9777fa) proves BruhatTitsAvailabilityReductionStatement. It chooses a datum for each group with Classical.choose and takes the comparison clauses from buildingComparisonAxiom and isomorphismCompatibilityAxiom through KPBuildingAssignment.isAvailableFor_iff. The theorem groupAxiomsExistenceReduction (module Langlands.Geometry.Building.GroupAxiomsExistenceReduction; proof Task 5927, 0d9b0a78-1f62-4c8e-bab7-78a4445383ce; artifact 48a1463c-593b-41f7-b7ea-9a02b0df2adf) proves GroupAxiomsExistenceReductionStatement. It builds SatisfiesGroupAxioms field by field and obtains Axiom 4.1.8 from KPBuildingDatum.satisfiesRootGroupActionAxiom_iff. So BruhatTitsAvailabilityStatement follows from RootValuationBuildingConstructionStatement, RootGroupActionAxiomStatement, IwahoriDecompositionAxiomStatement and IntegralModelAxiomsStatement, none of which is proved. On the same date each proof task of the four open inputs had an executor: Task 4749 (00b6788c), Task 5425 (7aba1f84) and Task 5426 (96685786) were waiting, and Task 5429 (cd2ad671) had two active executors. The published reduction rootValuationBuildingConstructionReduction (module RootValuationBuildingConstructionReduction, Task 4749) derives RootValuationBuildingConstructionStatement from ValuationApartmentAxiomsExistenceStatement (KP Theorem 9.6.5; proof task 17c6d83c-1e02-4345-b9d6-0a8f711e778b), ActualApartmentSplittingStatement (Task 5439, 4d8b4782-7726-4ab3-bb88-fc3df18693fc), AffineIwahoriTitsStatement (task 20fbe465-f4ae-4fe9-9846-2201f1c31d28) and AffineIwahoriTitsBuildingStatement (Task 5440, 81a85d8b-3e8d-454c-97f4-d9b0a3c7e748). Through ParahoricBuildingData.fiveAxioms_of_statements the last three also give ChapterSevenBuildingAxiomsStatement (published by this program, first in Library commit 8c11c93f98b439395e0e7da779c98bb27e24bd6d; proof task Task 5470, 4aa6902d-5c5f-4ca6-9502-061842714858): for supplied ParahoricBuildingData satisfying V 7 and AS 2–AS 5, a polysimplicial realization and a splitting with the other six predicates of the corrected opening of Section 4.2. Two of the four inputs of rootValuationBuildingConstructionReduction are proved: actualApartmentSplitting (module Langlands.Geometry.Building.ActualApartmentSplittingProof, artifact 94af3c4e-b313-44ad-adce-6b6383233dc9, first published in Library commit 8401ccd1f8b9caa18ded91cbfb9c1a31f423ecfd) proves ActualApartmentSplittingStatement (Task 5439), and affineIwahoriTitsBuilding (module Langlands.Geometry.Building.AffineIwahoriTitsBuildingProof, artifact 75baba4f-16d0-4518-87d3-e7e88493aaa9, first published in Library commit cd03c1042f631409e39a0b2a833ed70c0ad78d55) proves AffineIwahoriTitsBuildingStatement (Task 5440). lean_check inspections 3edd4041-7f28-44e5-b70b-7a648f7aeb04 and f2116893-5218-4bcf-9fe1-b6edbb684aa2 by Worker 3557 on 2026-11-12 at Library commit 14c08c22 report kind theorem and only propext, Classical.choice and Quot.sound. ValuationApartmentAxiomsExistenceStatement and AffineIwahoriTitsStatement remain unproved, so RootValuationBuildingConstructionStatement and ChapterSevenBuildingAxiomsStatement remain open.",
        "Chapter 9 descent rows: Section 9.2.1, Proposition 9.3.4 and Theorem 9.6.5 record the published statements of the unramified-descent route to ValuationApartmentAxiomsExistenceStatement, including the proved reduction valuationApartmentAxiomsExistenceReduction; Lemma 9.8.1 records the existence statement for the §9.8 filtration of Z(k)."
      ],
      "consumer_or_regression": "Release 1 general-instance certificate, then actual parahoric reduction, inflation and compact induction. Check anisotropic and torus reduced/enlarged factors, a multipliable root and a nontrivial component example. A Gamma-chamber or Gamma-vertex need not be a K-chamber or K-vertex.",
      "formal_status": "statement",
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [
        "f81d0fe7-8c61-4e05-bfcc-e7d6b14a3f04",
        "f147f7c0-08ca-4572-a5b9-d27efde033b8",
        "432145f3-166b-4c77-af14-c477854c91bc"
      ],
      "publication_commits": [
        "230ec08a058832bd6941fa887c30897e4826429b",
        "cfedefb680f317b0ea5d351023e1c9dd886b2547"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.BruhatTitsAvailabilityStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "f84d7d5e-94fd-4deb-b771-14d57bcf1815",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-10 at Library commit 230ec08a; statement_returns_prop true."
        },
        {
          "declaration": "Langlands.Geometry.Building.BruhatTitsAvailabilityReductionStatement",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "7bfcbb0d-6581-466e-92a5-7003a75ac5be",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 of the module as published in Library commit cfedefb6; kind definition; statement_returns_prop true."
        },
        {
          "declaration": "Langlands.Geometry.Building.GroupAxiomsExistenceReductionStatement",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "1bc98bb0-b21c-4d31-bae8-d64d785cfd89",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 of the module as published in Library commit cfedefb6; kind definition; statement_returns_prop true."
        },
        {
          "declaration": "Langlands.Geometry.Building.bruhatTitsAvailabilityReduction",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "75f0eabc-5824-4f8a-9bce-ee9e712b03e2",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 of the module as first published in Library commit 730bd1f2; kind theorem, proving BruhatTitsAvailabilityReductionStatement."
        },
        {
          "declaration": "Langlands.Geometry.Building.groupAxiomsExistenceReduction",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "59655099-69b2-4fa3-8d80-cd1bde021020",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 of the module as first published in Library commit 730bd1f2; kind theorem, proving GroupAxiomsExistenceReductionStatement."
        }
      ],
      "external_code": []
    },
    {
      "source_item": "Section 9.2.1",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.325–326 / PDF pp.356–357; special k-tori and special k-apartments in §9.2.2 at printed p.326 / PDF p.357; a Γ-fixed point in a special k-apartment in the proof of Proposition 9.3.6 at printed pp.333–334 / PDF pp.364–365"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.39 (Section 9.2)",
        "change": "The second full paragraph on printed p.326 is replaced: for x in an apartment A with maximal K-split torus T, choose a finite Galois k' ⊂ K over which T is defined and split; Gal(K/k') fixes A pointwise, so the Γ-orbit of x factors through Gal(k'/k) and is finite. A paragraph is added at the end of 9.2.1: a bounded Γ-stable subgroup of G(K) has a Γ-fixed fixed point in B(G_K), by Corollary 4.2.14, Proposition 4.2.18, Proposition 4.2.7 with Lemma 1.1.11, and Theorem 1.1.15 applied to the closed convex hull of a Γ-orbit."
      },
      "hypotheses": [
        "Chapter 9 standing hypotheses (printed p.323 / PDF p.354): k is discretely valued with Henselian valuation ring o and perfect residue field f; K is the maximal unramified extension in a fixed separable closure, with valuation ring O, and Γ = Gal(K/k). G is a connected reductive k-group; no quasi-splitness or tameness is assumed.",
        "B(G_K) is the Chapter 7 building of the quasi-split group G_K, with the Γ-action of Proposition 7.9.5 satisfying γ(g·x) = γ(g)·γ(x). T is a maximal K-split torus of G_K with apartment A_T; its Γ-stability uses that T is defined over k, as for the special k-tori of §9.2.2.",
        "Recorded Lean scope: UnramifiedGaloisFixedApartmentStatement (module Langlands.Geometry.Building.UnramifiedSpecialApartmentStatement) quantifies over every nonarchimedean local field F, every connected reductive G over Spec F and every commutative group scheme T with i : T.toGrp ⟶ G whose scalar extension i_K is a maximal split torus of G_K. K is the Library's maximal unramified extension inertiaFixedField F (definitionally UnramifiedClosure F) with its F-algebra structure, and scalar extension is base change along algebraBaseMap F K. For every D : KPApartmentData i_K ω, with ω the order of the normalized integer valuation MaximalUnramified.valuation F, an N(K)-stable equipollence class of valuations of the root datum of (G_K, T_K) that stands for A_T by §6.1, it assumes KPApartmentData.GaloisStable F K i D (each σ : K ≃ₐ[F] K maps members of D into D under the coefficient transport RootFunctionFamily.galoisAction) and asserts a point x : D.Apartment with galoisAction σ x = x for every σ. The Γ-stability that KP derive from the action on B(G_K) is a premise; the published IntegerValuation.IsOmegaCompatible.galoisStable proves it for every class satisfying V 6 for a scalar-extended centralizer datum. T need not contain a maximal F-split torus. The source's Henselian discretely valued fields with perfect residue field are specialized to nonarchimedean local fields of either characteristic in universe u. The Γ-action on B(G_K), the finiteness of all Γ-orbits, the embedding into the enlarged building and the added bounded-subgroup assertion have no declaration in this row."
      ],
      "conclusion": "If T is defined and split over a finite unramified k'/k, Gal(K/k') fixes A_T pointwise. If T is defined over k, then A_T is Γ-stable and Γ acts on it by affine maps through a finite quotient Gal(k'/k). Every Γ-orbit on B(G_K) is finite, so B(G_K) has a Γ-fixed point (Corollary 4.2.12). The zero section x ↦ (0, x) of the enlarged building V(Z^0_{G,K}) × B(G_K) is Γ-equivariant and G(K)^1-equivariant, so it restricts to a G(k)^1-equivariant embedding of B(G_K)^Γ into the Γ-fixed enlarged building, where G(k)^1 = G(K)^1 ∩ G(k) (§9.5, printed p.364 / PDF p.395); the projection of the enlarged building onto B(G_K) is Γ- and G(K)-equivariant. The printed text calls the zero section equivariant under ΓG(K) and its restriction G(k)-equivariant; this fails whenever the center of G contains a nontrivial k-split torus (see the regression), and the 2024 corrections do not address it. As corrected, a bounded Γ-stable subgroup of G(K) has a Γ-fixed fixed point. In the proof of Proposition 9.3.6 this gives a Γ-fixed point in every special k-apartment.",
      "lean_declarations": [
        "Langlands.Geometry.Building.UnramifiedGaloisFixedApartmentStatement",
        "Langlands.Geometry.Building.unramifiedGaloisFixedApartment"
      ],
      "modules": [
        "Langlands.Geometry.Building.UnramifiedSpecialApartmentStatement",
        "Langlands.Geometry.Building.UnramifiedGaloisFixedApartmentProof"
      ],
      "dependencies": [
        "Proposition 7.9.5; Proposition 4.4.3 and H^1(Gal(K/k'), V) = 0 for the pointwise fixation; Corollary 4.2.12; for the equivariance of the zero section, the central action of Section 4.3 (printed pp.178–180 / PDF pp.209–211), whose kernel is G(K)^1 by Lemma 4.3.1; for the corrected addition, Corollary 4.2.14, Proposition 4.2.18, Proposition 4.2.7, Lemma 1.1.11 and Theorem 1.1.15.",
        "Library inputs named by the statement's Markdown: KPApartmentData.exists_galoisFixed (the analogue for finite extensions K/k), the affine subspace galoisFixedApartment with mem_galoisFixedApartment_iff, under which the conclusion says that galoisFixedApartment is nonempty, and IntegerValuation.IsOmegaCompatible.galoisStable.",
        "Proof: the theorem unramifiedGaloisFixedApartment (module UnramifiedGaloisFixedApartmentProof; proof Task 5513, a23aef86-8894-44b0-b1c9-b76314d0865f; artifact fdd6f633-f0f7-4d1b-8a1c-0437cb2ef450; first in Library commit b128d289028bf75629e9e364ecf151c484b27a85) proves UnramifiedGaloisFixedApartmentStatement. The status is conditional: the class D and its Γ-stability are supplied, and the Γ-action on B(G_K), the finiteness of Γ-orbits, the enlarged-building embedding and the added bounded-subgroup assertion still have no declaration (see the Recorded Lean scope). The published reduction unramifiedValuationDescent_of_fixedLocus (Theorem 9.6.5 row) takes this statement as its first input."
      ],
      "consumer_or_regression": "The apartments A^Γ of §9.2.3 and Construction 9.6.1. The fixed-point set of UnramifiedValuationDescentStatement (Theorem 9.6.5 row) is nonempty only by this statement. Regression: for the norm-one torus T of the unramified quadratic extension in SL_2, T_K is a maximal K-split torus, Frobenius acts on V(T_K) by −1 and the Γ-fixed part of A_T is a single point; T is not special, which the Lean statement allows. Regression for the zero section: for k = Q_2 and G = G_m, B(G_K)^Γ is a single point and the Γ-fixed enlarged building is R, on which 2 ∈ G(k) (normalized valuation 1) acts by t ↦ t − 1; no G(k)-equivariant map from the point exists, while G(k)^1 = Z_2^× acts trivially on R.",
      "formal_status": "conditional",
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [
        "528e1be2-9d8b-452b-ad68-e956bf9179ee",
        "fdd6f633-f0f7-4d1b-8a1c-0437cb2ef450"
      ],
      "publication_commits": [
        "9bc92c384fa84da7ce5811a5979d408fb69d40b0",
        "b128d289028bf75629e9e364ecf151c484b27a85"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.UnramifiedGaloisFixedApartmentStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "d1da49d0-bde2-4462-b14a-ec1c5c1f8046",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-11 at Library commit 529b851c; kind definition; statement_returns_prop true; the module is byte-identical to commit 9bc92c38."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedGaloisFixedApartment",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "3336b98c-d2bd-4903-ad9a-544f2365a720",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit 6948120d; kind theorem, proving UnramifiedGaloisFixedApartmentStatement; the module is byte-identical to commit b128d289."
        }
      ],
      "external_code": []
    },
    {
      "source_item": "Proposition 9.3.4",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.332 / PDF p.363; special k-tori in §9.2.2 at printed p.326 / PDF p.357; for the integral-model input, Axiom 4.1.20 at printed p.163 / PDF p.194, Section 9.2.5 at printed pp.327–328 / PDF pp.358–359, Proposition 8.2.1 at printed p.286 / PDF p.317 and Proposition B.2.4 at printed p.656 / PDF p.687"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF pp.39–41 (Sections 9.2 and 9.3)",
        "change": "No entry changes Proposition 9.3.4 or its proof. The proof cites the finite-quotient action of 9.2.1, whose paragraph on printed p.326 is replaced (PDF p.39). The Section 9.3 entries concern Propositions 9.3.11, 9.3.12, 9.3.13, 9.3.24 and 9.3.25."
      },
      "hypotheses": [
        "Chapter 9 standing hypotheses (printed p.323 / PDF p.354): k is discretely valued with Henselian valuation ring o and perfect residue field f; K is the maximal unramified extension in a fixed separable closure, with valuation ring O, and Γ = Gal(K/k). G is a connected reductive k-group; no quasi-splitness or tameness is assumed.",
        "A special k-torus (§9.2.2) is a k-torus T ⊂ G that contains a maximal k-split torus of G and such that T_K is a maximal K-split torus of G_K.",
        "Recorded Lean scope: SpecialTorusExistenceStatement (module Langlands.Geometry.Building.UnramifiedSpecialApartmentStatement) quantifies over every nonarchimedean local field F, every connected reductive G over Spec F and every maximal split torus iS : S.toGrp ⟶ G (IsMaximalSplitTorus). K is the Library's maximal unramified extension inertiaFixedField F (definitionally UnramifiedClosure F) with its F-algebra structure, and scalar extension is base change along algebraBaseMap F K. It asserts a commutative group scheme T with iT : T.toGrp ⟶ G and f : S ⟶ T such that CommGroupScheme.groupHom f ≫ iT = iS, iT is a closed subgroup (IsClosedSubgroup), and the scalar extension iT_K is a maximal split torus of G_K. That T is an F-torus follows from the last condition and is not stated separately. The source's Henselian discretely valued fields with perfect residue field are specialized to nonarchimedean local fields of either characteristic in universe u. SpecialTorusIntegralModelStatement (module Langlands.Geometry.Building.SpecialTorusIntegralModelStatement, Task 5660 (56e61dcd-bec4-4329-a5c0-21e291e1b0bc), published by Worker 110 from Worker 224's draft) states the building input of the source proof under the same quantifiers: there is an IntegralModel M of G over 𝒪[F] with M.IsSmooth and connected special fibre, a closed split 𝒪[F]-torus j : 𝒮 → M.group whose generic fibre is iS (M.genericTorusMap 𝒮 j = groupHom e.hom ≫ iS for an isomorphism e of the generic fibre of 𝒮 with S), and a closed split torus of the base change M.baseChangeUnramified to the integers of K whose generic fibre is a maximal split torus of G_K. It is derived: the source proof uses G^1_x, while the statement asks for a model with connected special fibre (the role of G^0_x), and it asks for a split integral torus where Proposition B.2.4 gives a torus. It records neither the point x, nor an identification of M with a Bruhat–Tits model, nor reductivity of the special fibre."
      ],
      "conclusion": "Every maximal k-split torus S of G is contained in a special k-torus.",
      "lean_declarations": [
        "Langlands.Geometry.Building.SpecialTorusExistenceStatement",
        "Langlands.Geometry.Building.SpecialTorusIntegralModelStatement"
      ],
      "modules": [
        "Langlands.Geometry.Building.UnramifiedSpecialApartmentStatement",
        "Langlands.Geometry.Building.SpecialTorusIntegralModelStatement"
      ],
      "dependencies": [
        "Source proof: S(K)^1 is Γ-stable and acts boundedly on B(G_K) (Proposition 4.2.13); with the finite-quotient action of corrected 9.2.1, Theorem 1.1.15 gives a point x fixed by Γ and S(K)^1. The schematic closure of S in the descended model G^1_x of 9.2.5 is a torus (Proposition B.2.4); Proposition 8.2.1(1) gives a closed o-torus containing it whose special fibre is a maximal f-torus of the special fibre, and its generic fibre is the special torus.",
        "Split of the source proof: SpecialTorusIntegralModelStatement covers the building input up to the schematic closure of S (point x, the descended model of Section 9.2.5, Proposition B.2.4) and the torus that Axiom 4.1.20(3) gives over O at x. The remaining algebraic step, Proposition 8.2.1(1) lifting a maximal torus of the special fibre that contains the closure of S, and the conclusion that its generic fibre is special stay with Task 5514.",
        "Proof successor: lean.proof@1 Task 5514 (632bdfae-d1a6-4680-acf6-e5c1d32a17d8). SpecialTorusIntegralModelStatement has proof successor lean.proof@1 Task 5707 (f502c3c7-c095-4c74-bf82-ad8ffb916f57), whose contract forbids routes through SpecialTorusExistenceStatement, UnramifiedSpecialApartmentStatement and ValuationApartmentAxiomsExistenceStatement."
      ],
      "consumer_or_regression": "Special k-apartments (§9.2.2–9.2.3); Axiom 4.1.27 in §9.5; the proof of Lemma 9.8.1; the published reduction valuationApartmentAxiomsExistenceReduction (Theorem 9.6.5 row), which takes SpecialTorusExistenceStatement as an input. Regression: for anisotropic G the maximal split torus is trivial, and the statement asserts a k-torus that is maximally split over K. SpecialTorusIntegralModelStatement is the intended input of Task 5514's proof of SpecialTorusExistenceStatement.",
      "formal_status": "statement",
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [
        "528e1be2-9d8b-452b-ad68-e956bf9179ee",
        "d4896ec2-435c-4b28-a7a0-52eb74b82756"
      ],
      "publication_commits": [
        "9bc92c384fa84da7ce5811a5979d408fb69d40b0",
        "ba77b83f98d4cbe92842b4645577633e0541fdab"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.SpecialTorusExistenceStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "8ffb183d-c0ab-46a7-9a9f-4234b0c5f135",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-11 at Library commit 3c9b0579; kind definition; statement_returns_prop true; the module is byte-identical to commit 9bc92c38."
        },
        {
          "declaration": "Langlands.Geometry.Building.SpecialTorusIntegralModelStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "83166943-ef2e-4443-8071-27ca7c6b2508",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-12 at Library commit c5b9c2cf; kind definition; statement_returns_prop true; the module is byte-identical to commit ba77b83f."
        }
      ],
      "external_code": []
    },
    {
      "source_item": "Theorem 9.6.5",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.366–367 / PDF pp.397–398; §9.6 opening, Construction 9.6.1 and Remark 9.6.2 at printed pp.364–365 / PDF pp.395–396; Lemma 9.6.3 at printed p.366 / PDF p.397; §9.6.6 at printed p.367 / PDF p.398; §9.5 at printed pp.363–364 / PDF pp.394–395"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF pp.39–41 (Chapter 9)",
        "change": "No entry concerns Section 9.6. The corrections replace the first lines of the proof of Proposition 9.3.24 and delete the word \"non-divisible\" in the proof of Proposition 9.4.8; neither statement, both of which the proofs of Lemma 9.6.3 and Theorem 9.6.5 use, changes. The depth reading of Lemma 9.6.3 recorded in Bundle B below is not an authors' correction."
      },
      "hypotheses": [
        "Chapter 9 standing hypotheses (printed p.323 / PDF p.354): k is discretely valued with Henselian valuation ring o and perfect residue field f; K is the maximal unramified extension in a fixed separable closure, with valuation ring O, and Γ = Gal(K/k). G is a connected reductive k-group; no quasi-splitness or tameness is assumed.",
        "S is a maximal k-split torus with apartment A in B(G) = B(G_K)^Γ, N and Z its normalizer and centralizer. A point x ∈ A is, by Remark 9.6.2, a Γ-invariant valuation of the root datum of (G_K, T_K) for a special k-torus T ⊇ S, and ϕ^x_a(u) = ψ^a_u(x) by Construction 9.6.1.",
        "Recorded Lean scope: ValuationApartmentAxiomsExistenceStatement (module of the same name, Task 4749) asserts, for every nonarchimedean local field F and connected reductive G over Spec F, some B : ValuationBuildingData G (a maximal split torus, an N(F)-stable equipollence class of localFieldOrder F-compatible valuations of its root datum, the actual centralizer and V 6) with B.SatisfiesApartmentAxioms (V 7 and AS 2–AS 5). It asks for some torus and some class, whereas KP's class is canonical for every torus, and it includes the §9.5 apartment axioms transported by §9.6.6. This program's module Langlands.Geometry.Building.UnramifiedValuationDescentStatement splits it. K is the Library's maximal unramified extension inertiaFixedField F (definitionally UnramifiedClosure F) with its F-algebra structure, and scalar extension is base change along algebraBaseMap F K. UnramifiedValuationDescentStatement takes a maximal split torus iS, a torus T with iT and f : S ⟶ T, groupHom f ≫ iT = iS and iT_K a maximal split torus of G_K, opposite factor pairs hE for iT_K (a Prop that the published rootRankOneFactorization proves), a class D : KPApartmentData iT_K ω for the order ω of MaximalUnramified.valuation F, and a centralizer datum C with full V 6 (IntegerValuation.IsOmegaCompatible). Call x fixed when galoisAction σ x = x for every σ : K ≃ₐ[F] K, and let φ x be the published torus-then-field restriction torusFieldRestrictedRootFunctionFamily of x along f_K. The statement asserts DS : KPApartmentData iS (localFieldOrder F) and CS : CentralizerDatum iS with DS.IsOmegaCompatible CS (V 6 over F), such that ψ ∈ DS.carrier iff ψ = φ x for a fixed x, φ is injective on fixed points, and for every n ∈ N(F) and fixed x some fixed y has φ y = n • φ x and D.apartmentMap y = n • D.apartmentMap x in D.ReducedBuilding. ValuationBuildingApartmentAxiomsStatement asserts B.SatisfiesApartmentAxioms for every B : ValuationBuildingData G with [IsAffineHom G.X.hom]; quantifying over every class instead of the constructed one relies on the uniqueness of Proposition 6.2.6. UnramifiedValuationDescentPackageStatement is their conjunction. The theorem valuationApartmentAxiomsExistenceReduction proves ValuationApartmentAxiomsExistenceReductionStatement: UnramifiedQuasiSplitStatement, QuasiSplitIntegerApartmentExistenceStatement, SpecialTorusExistenceStatement and the two statements above imply ValuationApartmentAxiomsExistenceStatement. KP construct ϕ^x from the descended building; the Lean statement uses the restriction, which agrees with ϕ^x by Lemma 9.6.3 read with depth m·r for upstairs roots restricting to m·a. The source's Henselian discretely valued fields with perfect residue field are specialized to nonarchimedean local fields of either characteristic in universe u."
      ],
      "conclusion": "For x ∈ A, ϕ^x = (ϕ^x_a)_{a∈Φ} is a valuation of the root datum (U_a(k))_{a∈Φ} compatible with ω in the sense of Definition 6.1.2. The map x ↦ ϕ^x is equivariant under V(S) ⋊ N(k), and its image is an equipollence class. By §9.6.6, z ↦ ϕ^z is an isomorphism of affine spaces that identifies the affine root systems and the G(k)^0 stabilizers, and it extends to a G(k)-equivariant bijection between the descended building and the Chapter 7 building of this class.",
      "lean_declarations": [
        "Langlands.Geometry.Building.ValuationApartmentAxiomsExistenceStatement",
        "Langlands.Geometry.Building.UnramifiedValuationDescentStatement",
        "Langlands.Geometry.Building.ValuationBuildingApartmentAxiomsStatement",
        "Langlands.Geometry.Building.UnramifiedValuationDescentPackageStatement",
        "Langlands.Geometry.Building.ValuationApartmentAxiomsExistenceReductionStatement",
        "Langlands.Geometry.Building.valuationApartmentAxiomsExistenceReduction",
        "Langlands.Geometry.Building.quasiSplitIntegerApartmentExistence",
        "Langlands.Geometry.Building.ValuationBuildingQuasiSplitAdjointTranslationStatement",
        "Langlands.Geometry.Building.QuasiSplitAdjointSimpleRootTransitivityStatement",
        "Langlands.Geometry.Building.valuationBuildingQuasiSplitAdjointTranslation_of_simpleRootTransitivity",
        "Langlands.Geometry.Building.quasiSplitAdjointSimpleRootTransitivity",
        "Langlands.Geometry.Building.valuationBuildingQuasiSplitAdjointTranslation",
        "Langlands.Geometry.Building.unramifiedValuationDescent_of_fixedLocus",
        "Langlands.Geometry.Building.unramifiedFixedCentralizerCompatibility_of_leviTransport",
        "Langlands.Geometry.Building.unramifiedFixedLeviTransport_of_fixedApartment_and_leviSharp",
        "Langlands.Geometry.Building.unramifiedLeviSharpApartmentTransport",
        "Langlands.Geometry.Building.UnramifiedTorusUnitFixedApartmentStatement",
        "Langlands.Geometry.Building.UnramifiedFixedOppositeStatement",
        "Langlands.Geometry.Building.unramifiedFixedOpposite_of_wallInvariance",
        "Langlands.Geometry.Building.UnramifiedFixedWallInvarianceStatement",
        "Langlands.Geometry.Building.unramifiedQuasiSplit_of_henselianDiscrete",
        "Langlands.GroupScheme.henselianDiscreteQuasiSplit",
        "Langlands.Geometry.Building.unramifiedFixedWallInvariance_of_depthZero_of_leviTransport",
        "Langlands.Geometry.Building.unramifiedTorusUnitFixedApartmentReduction",
        "Langlands.Geometry.Building.unramifiedSplitTranslationFixer",
        "Langlands.Geometry.Building.unramifiedFixedPointTransporter_of_fixedPairSpecialApartment",
        "Langlands.Geometry.Building.unramifiedFixedDepthZeroOpposite_of_recoveredParabolicModels"
      ],
      "modules": [
        "Langlands.Geometry.Building.ValuationApartmentAxiomsExistenceStatement",
        "Langlands.Geometry.Building.UnramifiedValuationDescentStatement",
        "Langlands.Geometry.Building.QuasiSplitIntegerApartmentExistenceProof",
        "Langlands.Geometry.Building.ValuationQuasiSplitAdjointTranslation",
        "Langlands.Geometry.Building.QuasiSplitAdjointSimpleRootTransitivityStatement",
        "Langlands.Geometry.Building.ValuationQuasiSplitAdjointTranslationReduction",
        "Langlands.Geometry.Building.QuasiSplitAdjointSimpleRootTransitivityProof",
        "Langlands.Geometry.Building.ValuationQuasiSplitAdjointTranslationProof",
        "Langlands.Geometry.Building.UnramifiedValuationDescentReduction",
        "Langlands.Geometry.Building.UnramifiedFixedCentralizerReduction",
        "Langlands.Geometry.Building.UnramifiedFixedLeviTransportReduction",
        "Langlands.Geometry.Building.UnramifiedLeviSharpApartmentTransportProof",
        "Langlands.Geometry.Building.UnramifiedTorusUnitFixedApartmentStatement",
        "Langlands.Geometry.Building.UnramifiedFixedLocusStatement",
        "Langlands.Geometry.Building.UnramifiedFixedOppositeReduction",
        "Langlands.Geometry.Building.UnramifiedFixedWallInvarianceStatement",
        "Langlands.Geometry.Building.UnramifiedQuasiSplitReduction",
        "Langlands.GroupScheme.Rational.HenselianDiscreteQuasiSplitProof",
        "Langlands.Geometry.Building.UnramifiedFixedWallInvarianceReduction",
        "Langlands.Geometry.Building.UnramifiedTorusUnitFixedApartmentReduction",
        "Langlands.Geometry.Building.UnramifiedSplitTranslationFixerProof",
        "Langlands.Geometry.Building.UnramifiedFixedPointTransporterReduction",
        "Langlands.Geometry.Building.UnramifiedRecoveredDepthZeroOpposite"
      ],
      "dependencies": [
        "Source proof: V 0 and V 1 from Construction 9.6.1 and Proposition 9.4.3; equivariance from Lemma 9.4.15; V 2 from the same computation; V 6 from Proposition 9.3.16; V 3 from Proposition 9.4.8 and Remark 9.6.4; V 4 and V 5 from Corollary 9.4.10. Lemma 9.6.3 (Lemma 9.4.21, Propositions 7.3.12 and 9.3.24) compares U_{a,x,r} with the upstairs filtrations.",
        "Recorded Lean route: valuationApartmentAxiomsExistenceReduction takes a maximal split torus from exists_maximalSplitTorus and a special torus T ⊇ S from SpecialTorusExistenceStatement (Proposition 9.3.4 row). It makes G_K connected reductive by connectedReductiveFieldExtensionStatement and quasi-split by UnramifiedQuasiSplitStatement. QuasiSplitIntegerApartmentExistenceStatement, applied to K with MaximalUnramified.valuation_surjective and valuationSubring_isHenselian, gives the upstairs class with V 6. rootRankOneFactorization gives hE. UnramifiedValuationDescentStatement descends the class, and ValuationBuildingApartmentAxiomsStatement supplies the apartment axioms.",
        "Proof obligations: ValuationApartmentAxiomsExistenceStatement has proof task Task 5441 (17c6d83c-1e02-4345-b9d6-0a8f711e778b), which the reduction reduces to its five inputs. UnramifiedValuationDescentStatement has proof task Task 5553 (4401e3df-51b5-4132-892c-74e02328d7ee), and ValuationBuildingApartmentAxiomsStatement Task 5554 (265c7ec0-42c1-44ad-9e4f-06f38c5e51d3). SpecialTorusExistenceStatement is in the Proposition 9.3.4 row. UnramifiedQuasiSplitStatement holds. The theorem unramifiedQuasiSplit_of_henselianDiscrete (module UnramifiedQuasiSplitReduction, present in Library commit ed924aef420de137b4cbaa3b063a3618afcd73fd; its acceptance artifact cannot be identified in this instance) proves UnramifiedQuasiSplitReductionStatement, that HenselianDiscreteQuasiSplitStatement implies UnramifiedQuasiSplitStatement; it applies the Henselian statement to the maximal unramified extension K with the integer-normalized valuation, whose valuation ring is Henselian and whose residue field is algebraically closed. The theorem Langlands.GroupScheme.henselianDiscreteQuasiSplit (module Langlands.GroupScheme.Rational.HenselianDiscreteQuasiSplitProof; proof task 7568ebe8-7b19-4e71-8918-de7d3492bacc; artifact 61c429ea-c09c-4298-b74f-48a84aedf42b, first in Library commit 410c79471b79f65a02fb0f6070da7f2800793ff3) proves HenselianDiscreteQuasiSplitStatement (KP Corollary 2.3.8) by applying the published reduction henselianDiscreteQuasiSplit_of_dimensionLEOne to dimensionLEOneQuasiSplit (Steinberg's theorem, KP Theorem 2.3.3(2)). lean_check inspections by Worker 3557 on 2026-11-14 at Library commit 757a6793 report kind theorem and only propext, Classical.choice and Quot.sound for both: efef4435-11fa-47f0-8291-e778429f90f1, whose type is exactly UnramifiedQuasiSplitReductionStatement.{u}, and 752cdf97-f8d2-4158-927e-445bbb7a0c0d, whose type is exactly HenselianDiscreteQuasiSplitStatement.{u}. No published theorem has UnramifiedQuasiSplitStatement as its type; Worker 3557 checked the composite with a private lean_check (diagnostic 63303259-874b-4c99-b930-9df8534af5c7, Library commit 757a6793, only propext, Classical.choice and Quot.sound). The published conditional reduction henselianDiscreteQuasiSplitReduction derives HenselianDiscreteQuasiSplitStatement from QuasiSplitRegularClassRationalStatement, and that statement is proved as well: the theorem Langlands.GroupScheme.quasiSplitRegularClassRational (module Langlands.GroupScheme.Rational.QuasiSplitRegularClassRational; artifact b5ba58cd-67d1-4010-8554-231c2c136831, first in Library commit db8d6b3d466f2fd453a4df4624ce6c90db8eed46) has it as its type; inspection 9535f39d-a2ba-4ee5-b70a-d5390ab133cd by Worker 3557 on 2026-11-14 at Library commit 757a6793 reports kind theorem, a type that is exactly QuasiSplitRegularClassRationalStatement.{u}, and only propext, Classical.choice and Quot.sound. QuasiSplitIntegerApartmentExistenceStatement (proof task 8ffe0456-3bbd-46c6-9fe1-91be8c433458) is proved: the theorem quasiSplitIntegerApartmentExistence (module QuasiSplitIntegerApartmentExistenceProof) is present in Library commit ed924aef420de137b4cbaa3b063a3618afcd73fd, and its acceptance artifact cannot be identified in this instance. So two of the five inputs of the reduction are proved. On 14 November 2026 the other three (SpecialTorusExistenceStatement, UnramifiedValuationDescentStatement and ValuationBuildingApartmentAxiomsStatement) have no published proof. The modules UnramifiedQuasiSplitReduction, HenselianDiscreteQuasiSplitProof and QuasiSplitRegularClassRational are byte-identical between the commits cited above and Library commit 757a6793. The entry \"Partial route inside UnramifiedValuationDescentStatement\" below reduces the descent statement to three unproved statements.",
        "Partial route inside ValuationBuildingApartmentAxiomsStatement (Task 5554): the last sentence of AS 5 (KP Axiom 4.1.6, Proposition 6.6.2), that for quasi-split adjoint G the image of N(F) in the affine automorphisms of the apartment is W(Ψ)^ext. The module Langlands.Geometry.Building.ValuationQuasiSplitAdjointTranslation, present in Library commit 17dd94ea3f677b20fb5ab95b285cbc3fd7cde03e, states its translation part ValuationBuildingQuasiSplitAdjointTranslationStatement: for every B : ValuationBuildingData G of a quasi-split adjoint G over a nonarchimedean local field, every translation of the apartment that preserves the affine roots Ψ is the translation by ν(z) for some z ∈ Z(F). Its theorem range_eq_extendedAffineWeylGroup_of_quasiSplitAdjointTranslation derives the last sentence of AS 5 for B from this statement and the first sentence. Task 5784 (6e16b5de-eb88-4e8a-a1b4-c9efd76595ff; artifact f396351f-ca57-4ef9-99dc-472193bf573d, first in Library commit cfedefb680f317b0ea5d351023e1c9dd886b2547) published QuasiSplitAdjointSimpleRootTransitivityStatement, the group-theoretic content behind KP Lemma 6.4.10: for every field k, quasi-split adjoint G over k, maximal split torus S and representative Z of its centralizer, some finite family Δ of relative roots generates every relative root, and for each a ∈ Δ and all u, u' ∈ U_a(k) outside U_{2a}(k) some z ∈ Z(k) commutes with U_b(k) for every other b ∈ Δ and conjugates u into u' U_{2a}(k). The theorem valuationBuildingQuasiSplitAdjointTranslation_of_simpleRootTransitivity (module ValuationQuasiSplitAdjointTranslationReduction, same commit) proves the translation statement from it. The theorem quasiSplitAdjointSimpleRootTransitivity (module QuasiSplitAdjointSimpleRootTransitivityProof; proof Task 5933, a4943c55-06f3-4473-a909-0c252cccd77b; artifact 91a862bd-07ef-429f-be2c-f70578275244; first in Library commit 51e4d8972659f1ffcf0ca89e8eee9540a30b52d3) proves QuasiSplitAdjointSimpleRootTransitivityStatement. Its unit also proves the Galois descent of torus points with prescribed character values as exists_rationalPoint_characterValue_eq_of_equivariant (module Langlands.GroupScheme.Torus.EquivariantCharacterValueDescent): for a Galois extension L/k and a commutative k-group scheme T whose base change to L is a split torus, every Galois-equivariant homomorphism X^*(T_L) → L^× is the evaluation of characters at some k-point of T. The theorem valuationBuildingQuasiSplitAdjointTranslation (module ValuationQuasiSplitAdjointTranslationProof; proof Task 5708, e58f3c1c-4630-432d-8c9a-534ac43a04d7; artifact 4eaffc20-122d-4482-a0d2-03117bddcdc6; first in Library commit 7f43c3c930ff92f76dae6589da1678ad729017e5) applies the reduction to it and proves ValuationBuildingQuasiSplitAdjointTranslationStatement. So, by range_eq_extendedAffineWeylGroup_of_quasiSplitAdjointTranslation, the last sentence of AS 5 holds for every such B that satisfies the first sentence. A second proof task of the transitivity statement, Task 5936 (a6552027-c8a5-424b-8dd6-fd36b65b5f05), was retired on 13 November 2026 without candidates. Its executor published Task 5959 (7ae47441-6ced-4cc8-8cdc-75761494ea55), whose statement Langlands.GroupScheme.TorusEquivariantCharacterValueDescentStatement (module Langlands.GroupScheme.Torus.EquivariantCharacterValueDescentStatement) is present in Library commit 451cce4ca176c34856be86a36801b7a3b585ae77. It has the hypotheses and conclusion of the descent theorem above. The theorem torusEquivariantCharacterValueDescent (module Langlands.GroupScheme.Torus.EquivariantCharacterValueDescentProof; proof Task 5959; artifact 10c2b5f3-98f7-47d4-b734-421ca302ba2a, first in Library commit 0c3f30c24701c74d5474fca3fbb5324a99aa1d58) proves it by applying exists_rationalPoint_characterValue_eq_of_equivariant; lean_check inspection 1cc1be81-b07f-46ea-8d26-d52f0d851bdb by Worker 3557 on 2026-11-13 at Library commit 0f84a0d8 reports kind theorem and only propext, Classical.choice and Quot.sound. No published reduction yet expresses ValuationBuildingApartmentAxiomsStatement through these statements.",
        "Partial route inside UnramifiedValuationDescentStatement (Task 5553): the theorem unramifiedValuationDescent_of_fixedLocus (module UnramifiedValuationDescentReduction; artifact 011ef4db-d42c-4ad2-ad2f-34a3e04c6824, first in Library commit cc5aa77fa8dbdc6e723091c7b710ab0d81162c4e) proves that UnramifiedGaloisFixedApartmentStatement, UnramifiedFixedLeviTransportStatement, UnramifiedFixedCentralizerCompatibilityStatement (V 6 on Z(F) at the Γ-fixed points) and UnramifiedFixedOppositeStatement (V 5 at the Γ-fixed points, as KP derive it from Corollary 9.4.10) imply UnramifiedValuationDescentStatement. The first input is proved (Section 9.2.1 row). The theorem unramifiedFixedCentralizerCompatibility_of_leviTransport (module UnramifiedFixedCentralizerReduction; artifact 2b1154b1-3535-4eda-a884-5147c81d8f93, first in Library commit 0c3f30c24701c74d5474fca3fbb5324a99aa1d58) derives the third input from the second. The theorem unramifiedFixedLeviTransport_of_fixedApartment_and_leviSharp (module UnramifiedFixedLeviTransportReduction; artifact f1104929-517a-47db-a542-811d7d431233, first in Library commit 73b1430a339b037d27e9096762b0400adb4fbd19) derives the second input from UnramifiedTorusUnitFixedApartmentStatement and UnramifiedLeviSharpApartmentTransportStatement, and the theorem unramifiedLeviSharpApartmentTransport (module UnramifiedLeviSharpApartmentTransportProof; proof Task 6158, d9548cf8-c41a-4238-97b0-13ec9e71edc6; artifact cf4355b3-9dbc-484e-bb65-136c9197ef43, first in Library commit 0c3f30c24701c74d5474fca3fbb5324a99aa1d58) proves the latter. UnramifiedTorusUnitFixedApartmentStatement (artifact 1e7097c9-689a-43b5-960d-e8d57dfc4764) states the fixed-locus part of KP Proposition 9.3.13 in this setting: every point of the reduced building of D that is fixed by the coefficient action of Aut(K/F) and by the character-valuation kernel of S(K) is the image of an Aut(K/F)-fixed point of the T-apartment. UnramifiedFixedOppositeStatement is in module UnramifiedFixedLocusStatement (artifact 5597998e-1fcb-4439-ae3a-0edac203e533, whose entry declaration is UnramifiedFixedCentralizerCompatibilityStatement); both are first in Library commit cc5aa77fa8dbdc6e723091c7b710ab0d81162c4e. Composing the four published theorems shows that UnramifiedTorusUnitFixedApartmentStatement and UnramifiedFixedOppositeStatement together imply UnramifiedValuationDescentStatement; no published declaration states this composite. On 13 November 2026 neither of the two is proved; their proof tasks are Task 6010 (fb63f839-f945-48c6-839b-5bb7bba29088) and Task 6012 (ebd4b228-9d35-4728-9c61-f2f6e6b5a901). The executors of Task 6012 published three further declarations, all first in Library commit 430cc03fe803c5dbf74bc3baf91e8f7a2c26ea9c. UnramifiedFixedWallInvarianceStatement (module of the same name, by Worker 91; artifact 05ebe182-3406-4730-89e8-e961ff251c30) is the last assertion of KP Proposition 9.4.9 at the Aut(K/F)-fixed points z of the apartment of D, stated on the restricted root-function family φ_z: for a relative root a, g ∈ U_a(F) with g ≠ 1 and φ_z(a, g) = 0, and g', g'' ∈ U_{-a}(F) with m = g' g g'' ∈ N(F), the published action of m on root-function families fixes φ_z. The theorem unramifiedFixedOpposite_of_wallInvariance (module UnramifiedFixedOppositeReduction, by Worker 91; artifact c9e58355-f26e-4ecf-bdea-658aa0766280, whose entry declaration UnramifiedFixedOppositeReductionStatement names the implication) proves that UnramifiedFixedWallInvarianceStatement implies UnramifiedFixedOppositeStatement, following KP's proof of Corollary 9.4.10. UnramifiedFixedDepthZeroOppositeStatement (module of the same name, by Worker 169; artifact 1ae5af2c-96b9-496f-ae4e-e7074525238f) states a consequence of KP Proposition 9.4.9(2) on the restricted root-function family at the Aut(K/F)-fixed points z of the apartment of D: for a relative root a, g ∈ U_a(F) with g ≠ 1 and φ_z(a, g) = 0, and g', g'' ∈ U_{-a}(F) with g' g g'' ∈ N(F), the two opposite factors have nonnegative restricted value, 0 ≤ φ_z(-a, g') and 0 ≤ φ_z(-a, g''). It is not assertion (2) itself: it does not state that g', g'' or KP's m(g) = g' g g'' belong to G^0_z(o), and it constructs neither the parahoric model G^0_z nor its special fibre. KP prove assertion (2) with Theorem 8.2.9 and use it in their proof of the last assertion. Composing the published theorems, UnramifiedTorusUnitFixedApartmentStatement and UnramifiedFixedWallInvarianceStatement together imply UnramifiedValuationDescentStatement; neither of them is proved. Correction and update (twentieth pass, 14 November 2026): earlier versions of this entry said that no published theorem takes UnramifiedFixedDepthZeroOppositeStatement as a hypothesis. That has been false since Library commit 85c2fe719cf62e96f22aaf4ca03961c5814d086b. The theorem unramifiedFixedWallInvariance_of_depthZero_of_leviTransport (module UnramifiedFixedWallInvarianceReduction; artifact f809829a-8407-4b25-947b-4c9f8b20bc59, whose entry declaration UnramifiedFixedWallInvarianceReductionStatement names the implication, first in that commit) proves that UnramifiedFixedDepthZeroOppositeStatement and UnramifiedFixedLeviTransportStatement together imply UnramifiedFixedWallInvarianceStatement. Published theorems also split UnramifiedTorusUnitFixedApartmentStatement, following the proof of KP Proposition 9.3.13 as revised in the 2024 corrections (PDF pp.39–40). The theorem unramifiedTorusUnitFixedApartmentReduction (module UnramifiedTorusUnitFixedApartmentReduction; artifact 826ab13f-ac41-4c0e-b5aa-1f4b231a87e9, first in Library commit 4f6abf4c7e19610e4d89edc9bf64b34ba1db9ff2) derives it from three statements. UnramifiedFixedPointTransporterStatement (module of the same name; artifact 52c531f3-29e0-44ec-928b-6b0696415d74, first in Library commit 51e4d8972659f1ffcf0ca89e8eee9540a30b52d3) takes an apartment point x_0 fixed by Aut(K/F) and a point y of the reduced building fixed by the coefficient action of Aut(K/F) and by the character-valuation kernel of S_K(K), and asserts some h ∈ G(K) that commutes with S_K(K), fixes the image of x_0, has h^{-1}σ(h) in the normalizer of T_K for every σ, and carries some apartment point to y. UnramifiedTwistedFixedTranslationStatement (module of the same name; artifact 96d3473c-4027-4737-99ac-abf4159a59aa, first in Library commit 430cc03fe803c5dbf74bc3baf91e8f7a2c26ea9c) says that the apartment translations fixed by the twisted coefficient action lie in the image of V(S_K), KP's V(T')^Γ = V(S'). UnramifiedSplitTranslationFixerStatement (module of the same name; artifact b8c09903-b495-4bdc-a55f-95ced170a310, first in Library commit 4f6abf4c7e19610e4d89edc9bf64b34ba1db9ff2) says that an element of G(K) that commutes with S_K(K) and fixes the image of an apartment point x also fixes the image of v + x for every v in that image of V(S_K). The theorem unramifiedSplitTranslationFixer (module UnramifiedSplitTranslationFixerProof; proof task d4565109-b318-4aff-82a1-8b8079e397b7; artifact ac1b808f-0768-46ed-9378-548d34cb0653, first in Library commit c40a01345b2f4172fa41e07ff31644b40e695003) proves the third statement by the orbit-and-convexity argument of the corrections, with finite convex combinations. The theorem unramifiedFixedPointTransporter_of_fixedPairSpecialApartment (module UnramifiedFixedPointTransporterReduction; artifact 07def5ce-c7ed-4811-9575-d4315243d263 of statement task 39cbd957-e874-48ed-aa0d-147a15b7fb84, whose entry declaration is UnramifiedFixedPairSpecialApartmentStatement; first in Library commit c40a01345b2f4172fa41e07ff31644b40e695003) derives the first statement from UnramifiedFixedPairSpecialApartmentStatement and the published unramifiedLeviSharpApartmentTransport. UnramifiedFixedPairSpecialApartmentStatement is KP Proposition 9.3.11(1) for two points y_1, y_2 of that kind: some g ∈ G(K) that commutes with S_K(K) and has g^{-1}σ(g) in the normalizer of T_K for every σ carries an apartment point to y_1 and another to y_2. The theorem unramifiedFixedDepthZeroOpposite_of_recoveredParabolicModels (module UnramifiedRecoveredDepthZeroOpposite; artifact 43621606-9d15-480b-8a7f-bdd0cd75ba08, first in Library commit c40a01345b2f4172fa41e07ff31644b40e695003) derives UnramifiedFixedDepthZeroOppositeStatement from two statements. UnramifiedFixedRecoveredParabolicModelsStatement (same module) asks, at each Aut(K/F)-fixed apartment point z, for actual relative-component models over the integers of F and of K with unramified recovery, whose upper integral points are the character-valuation kernel intersected with the pointwise fixer of z, together with nearby parabolic root comparisons. IntegralOppositeFactorsStatement (module Langlands.BruhatTits.IntegralModels.IntegralOppositeFactorsStatement; artifact e52be7de-3350-4083-ad79-586ef6612354, first in Library commit 410c79471b79f65a02fb0f6070da7f2800793ff3) is KP Theorem 8.2.9 for supplied smooth affine integral models with connected fibres over the integers of a nonarchimedean local field. Composing these theorems with unramifiedGaloisFixedApartment, unramifiedLeviSharpApartmentTransport and the four reductions above, UnramifiedFixedPairSpecialApartmentStatement, UnramifiedTwistedFixedTranslationStatement and UnramifiedFixedDepthZeroOppositeStatement together imply UnramifiedValuationDescentStatement, and the last of the three may be replaced by the two inputs of its reduction. No published declaration states this composite; Worker 3557 checked both forms with a private lean_check (diagnostic a1404135-57a2-4295-ad9a-d02d07e58a36, Library commit c40a0134, only propext, Classical.choice and Quot.sound). On 14 November 2026 none of these five statements is proved. UnramifiedTwistedFixedTranslationStatement has proof task 04e13d1f-dbeb-42e0-a62f-40affd0c4906 and UnramifiedFixedDepthZeroOppositeStatement proof task df07915a-d94a-4146-98db-5b1871bbfc0e; Tasks 6010 and 6012 remain the proof tasks of UnramifiedTorusUnitFixedApartmentStatement and UnramifiedFixedOppositeStatement. The axiom reports below record lean_check inspections of the five theorems named in this paragraph. Each module cited in this paragraph with a first commit is byte-identical between that commit and Library commit c40a0134."
      ],
      "consumer_or_regression": "The published rootValuationBuildingConstructionReduction (Theorem 9.2.7 row) derives RootValuationBuildingConstructionStatement from ValuationApartmentAxiomsExistenceStatement and three further statements. The §9.6.6 comparison feeds the derived route for Axiom 4.1.16, and the §9.8 concave function groups use this class. Regression: for the unramified quasi-split SU_3, the relative root system is BC_1, and the upstairs root restricting to 2a must be filtered at depth 2r by V 4; the uniform depth of the printed Lemma 9.6.3 display fails there.",
      "formal_status": "statement",
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [
        "e0b14a71-bc99-4ac1-b5b5-041d9f4ca3e6",
        "cab86217-ea50-409b-9d4d-3440ee3e3a43",
        "f396351f-ca57-4ef9-99dc-472193bf573d",
        "1e7097c9-689a-43b5-960d-e8d57dfc4764",
        "5597998e-1fcb-4439-ae3a-0edac203e533",
        "05ebe182-3406-4730-89e8-e961ff251c30"
      ],
      "publication_commits": [
        "58a91d4ff65b8d6dcb8aa417bfc63399feb8b4af",
        "3c9b0579a8f2d36d16294ce48b465d1ec5aee273",
        "ed924aef420de137b4cbaa3b063a3618afcd73fd",
        "17dd94ea3f677b20fb5ab95b285cbc3fd7cde03e",
        "cfedefb680f317b0ea5d351023e1c9dd886b2547",
        "cc5aa77fa8dbdc6e723091c7b710ab0d81162c4e",
        "430cc03fe803c5dbf74bc3baf91e8f7a2c26ea9c"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.ValuationApartmentAxiomsExistenceStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "05c65b4b-4943-4f53-9e8e-f8017a57feb6",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-11 at Library commit 529b851c; kind definition; statement_returns_prop true; the module is byte-identical to its artifact."
        },
        {
          "declaration": "Langlands.Geometry.Building.UnramifiedValuationDescentStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "086644d8-0e80-4d12-aa2b-eb0e93d3ebc9",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-11 at Library commit 529b851c; kind definition; statement_returns_prop true; the module is byte-identical to commit 3c9b0579."
        },
        {
          "declaration": "Langlands.Geometry.Building.ValuationBuildingApartmentAxiomsStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "195737d3-0fed-4a30-9357-63f705ababa0",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-11 at Library commit 529b851c; kind definition; statement_returns_prop true; the module is byte-identical to commit 3c9b0579."
        },
        {
          "declaration": "Langlands.Geometry.Building.UnramifiedValuationDescentPackageStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "88267b7d-250a-4c5d-905f-f25f49e3dd15",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-11 at Library commit 529b851c; kind definition; statement_returns_prop true; the module is byte-identical to commit 3c9b0579."
        },
        {
          "declaration": "Langlands.Geometry.Building.ValuationApartmentAxiomsExistenceReductionStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "03f5a25d-7645-4ed3-bec8-c100c8950cf4",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-11 at Library commit 529b851c; kind definition; statement_returns_prop true; the module is byte-identical to commit 3c9b0579."
        },
        {
          "declaration": "Langlands.Geometry.Building.valuationApartmentAxiomsExistenceReduction",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "140ce8b9-1e69-457b-be94-4bc51e6d2ff4",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-11 at Library commit 529b851c; kind theorem; the module is byte-identical to commit 3c9b0579."
        },
        {
          "declaration": "Langlands.Geometry.Building.quasiSplitIntegerApartmentExistence",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "f3c37e97-b1f0-4294-a12d-542c6781f48d",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit ed924aef; a theorem proving QuasiSplitIntegerApartmentExistenceStatement. Its acceptance artifact cannot be identified in this instance."
        },
        {
          "declaration": "Langlands.Geometry.Building.ValuationBuildingQuasiSplitAdjointTranslationStatement",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "f194ea1c-ac22-4a1d-9d67-d0d165c28603",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit eded01f2; kind definition; statement_returns_prop true. The module is present in Library commit 17dd94ea; its acceptance artifact cannot be identified in this instance."
        },
        {
          "declaration": "Langlands.Geometry.Building.QuasiSplitAdjointSimpleRootTransitivityStatement",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "fac0114c-5304-422e-bd66-d9fe5be74d93",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 of the module as published in Library commit cfedefb6; kind definition; statement_returns_prop true."
        },
        {
          "declaration": "Langlands.Geometry.Building.valuationBuildingQuasiSplitAdjointTranslation_of_simpleRootTransitivity",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "9d61aae3-eaa0-4eaf-8ece-9a80bf927f89",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 of the module as published in Library commit cfedefb6; kind theorem, proving QuasiSplitAdjointSimpleRootTransitivityStatement → ValuationBuildingQuasiSplitAdjointTranslationStatement."
        },
        {
          "declaration": "Langlands.Geometry.Building.quasiSplitAdjointSimpleRootTransitivity",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "2178d455-71f0-483c-8d47-67f0d81a2ac0",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 of the module as first published in Library commit 51e4d897; kind theorem, proving QuasiSplitAdjointSimpleRootTransitivityStatement."
        },
        {
          "declaration": "Langlands.Geometry.Building.valuationBuildingQuasiSplitAdjointTranslation",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "1a865aa5-84a6-4e99-a06f-87481040aaa7",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 of the module as first published in Library commit 7f43c3c9; kind theorem, proving ValuationBuildingQuasiSplitAdjointTranslationStatement."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedValuationDescent_of_fixedLocus",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "8aefe302-5950-4f77-981f-36b08e24be65",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit 6948120d; kind theorem, whose type is the implication from the four fixed-locus statements to UnramifiedValuationDescentStatement; the module is byte-identical to commit cc5aa77f."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedFixedCentralizerCompatibility_of_leviTransport",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "247604e5-267e-40c0-a2c8-56a38fde6b8e",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit 6948120d; kind theorem, whose type is the implication from UnramifiedFixedLeviTransportStatement to UnramifiedFixedCentralizerCompatibilityStatement; the module is byte-identical to commit 0c3f30c2."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedFixedLeviTransport_of_fixedApartment_and_leviSharp",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "44f85228-6247-4ff2-96fe-a6d32ff16da8",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit 6948120d; kind theorem, proving UnramifiedFixedLeviTransportReductionStatement; the module is byte-identical to commit 73b1430a."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedLeviSharpApartmentTransport",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "4374f1ac-313f-4939-aa45-71eb2fb2a473",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit 6948120d; kind theorem, proving UnramifiedLeviSharpApartmentTransportStatement; the module is byte-identical to commit 0c3f30c2."
        },
        {
          "declaration": "Langlands.Geometry.Building.UnramifiedTorusUnitFixedApartmentStatement",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "53f6acf9-dd8d-4223-8c02-e215f6d104f5",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit 6948120d; kind definition; statement_returns_prop true; the module is byte-identical to commit cc5aa77f."
        },
        {
          "declaration": "Langlands.Geometry.Building.UnramifiedFixedOppositeStatement",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "c8c0745b-744f-4b28-a61c-f711ed36909a",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit 6948120d; kind definition; statement_returns_prop true; the module is byte-identical to commit cc5aa77f."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedFixedOpposite_of_wallInvariance",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "8f850197-3f2c-4f4c-a8ae-739c18fd53a4",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit 0f84a0d8; kind theorem, whose type is the implication from UnramifiedFixedWallInvarianceStatement to UnramifiedFixedOppositeStatement; the module is byte-identical to commit 430cc03f."
        },
        {
          "declaration": "Langlands.Geometry.Building.UnramifiedFixedWallInvarianceStatement",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "32eaf6a6-50a6-406b-a2fb-8a9f32628881",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit 1bd55dea; kind definition; statement_returns_prop true; the module is byte-identical to commit 430cc03f."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedQuasiSplit_of_henselianDiscrete",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "efef4435-11fa-47f0-8291-e778429f90f1",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-14 at Library commit 757a6793; kind theorem, at universe level u, whose type is exactly UnramifiedQuasiSplitReductionStatement.{u}; the module is byte-identical to commit ed924aef."
        },
        {
          "declaration": "Langlands.GroupScheme.henselianDiscreteQuasiSplit",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "752cdf97-f8d2-4158-927e-445bbb7a0c0d",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-14 at Library commit 757a6793; kind theorem, at universe level u, whose type is exactly HenselianDiscreteQuasiSplitStatement.{u}; the module is byte-identical to commit 410c7947, which first published it."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedFixedWallInvariance_of_depthZero_of_leviTransport",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "5f2403bb-a937-4906-ba3e-a73743711d35",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-14 at Library commit c40a0134; kind theorem, at universe level u, whose type is exactly UnramifiedFixedWallInvarianceReductionStatement.{u}; the module is byte-identical to commit 85c2fe71, which first published it."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedTorusUnitFixedApartmentReduction",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "5feafd7d-d1cc-4c01-9516-e861a903efe9",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-14 at Library commit c40a0134; kind theorem, at universe level u, whose type is exactly UnramifiedTorusUnitFixedApartmentReductionStatement.{u}; the module is byte-identical to commit 4f6abf4c, which first published it."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedSplitTranslationFixer",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "81a1c445-8074-4fab-9560-321108202ad9",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-14 at Library commit c40a0134; kind theorem, at universe level u, whose type is exactly UnramifiedSplitTranslationFixerStatement.{u}; the module was first published in this commit."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedFixedPointTransporter_of_fixedPairSpecialApartment",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "9af8e1f0-3a48-4063-9632-3965ee281112",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-14 at Library commit c40a0134; kind theorem, at universe level u, whose type is the implication from UnramifiedFixedPairSpecialApartmentStatement to UnramifiedFixedPointTransporterStatement; the module was first published in this commit."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedFixedDepthZeroOpposite_of_recoveredParabolicModels",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "d130fe50-7543-467f-8200-7955ac2bbaae",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-14 at Library commit c40a0134; kind theorem, at universe level u, whose type is exactly UnramifiedRecoveredDepthZeroOppositeReductionStatement.{u}; the module was first published in this commit."
        }
      ],
      "external_code": []
    },
    {
      "source_item": "Lemma 9.8.1",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.374–375 / PDF pp.405–406 (construction of Z(k)_r in §9.8 and Lemma 9.8.1); Definition 7.2.1 at printed p.245 / PDF p.276; Definition 7.1.3 at printed p.242 / PDF p.273; Proposition 13.2.5(4) at printed p.469 / PDF p.500; for the double-root bound, Proposition 7.1.1 and its proof at printed pp.237–240 / PDF pp.268–271 and Lemma 7.2.3 at printed pp.245–246 / PDF pp.276–277"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.41 (Section 9.8); PDF p.50 (Appendix B)",
        "change": "In the second paragraph of the proof of Lemma 9.8.1 the projection B(G) → B(Z) is replaced by B(G)^M → B(Z). The Appendix B entries concern the minimal congruent filtration of tori. Neither changes the filtration or the lemma."
      },
      "hypotheses": [
        "Chapter 9 standing hypotheses (printed p.323 / PDF p.354): k is discretely valued with Henselian valuation ring o and perfect residue field f; K is the maximal unramified extension in a fixed separable closure, with valuation ring O, and Γ = Gal(K/k). G is a connected reductive k-group; no quasi-splitness or tameness is assumed.",
        "S is a maximal k-split torus and Z = Z_G(S). A functorial filtration of tori satisfying (1) and (2) of §7.2 is fixed (Appendix B). B(Z) is a single point x (Proposition 9.3.9), and Z(k)_r = Z(K)_{x,r} ∩ Z(k), where Z(K)_{x,r} is the §7.3 group of the quasi-split group Z_K for the constant concave function r.",
        "Recorded Lean scope: CentralizerFiltrationExistenceStatement (module of the same name) quantifies over every nonarchimedean local field F, every G over Spec F with [IsAffineHom G.X.hom] and every P : ParahoricBuildingData G with P.SatisfiesApartmentAxioms (V 6 in the data, V 7 and AS 2–AS 5). It asserts some Zf : P.CentralizerFiltration (subgroups Z(F)_r of Z(F) for r : ℝ≥0, decreasing, with trivial intersection and Z(F)_0 = P.centralizerZero) with Zf.SatisfiesFiltrationAxioms and Zf.IsOpenFiltration. SatisfiesFiltrationAxioms is IsCommutatorFriendly (the commutator clause of Definition 7.2.1 with the Z-component of Definition 7.1.3), IsNormalizerStable (N(F)-stability), IsCommutatorFiltered ([Z(F)_r, Z(F)_s] ⊆ Z(F)_{r+s}) and IsRootCompatible ([Z(F)_r, U_{a,x,s}] ⊆ U_{a,x,r+s} U_{2a,x,r+s}); IsOpenFiltration makes each Z(F)_r open in Z(F). The last three axioms are not clauses of Definition 7.2.1: they are derived properties of the §9.8 filtration, from its independence of S with functoriality and from Proposition 13.2.5(4). Only existence is asserted, so KP's filtration for a chosen filtration of tori is one witness; no filtration of tori is constructed. By Proposition 6.2.6 the class of P is the canonical one. The source's Henselian discretely valued fields with perfect residue field are specialized to nonarchimedean local fields of either characteristic in universe u. CentralizerFiltrationDoubleRootExistenceStatement (module Langlands.Geometry.Building.KPMoyPrasadDoubleRootStatement) adds the conjunct Zf.IsDoubleRootCommutatorFriendly (Proposition 13.2.5 row): the Z-component of a commutator of u ∈ U_a(F) and u' ∈ U_{-a}(F) with u ∈ U_{2a}(F) or u' ∈ U_{-2a}(F) lies in Z(F)_{2r}, r = x_a(u) + x_{-a}(u'). Lemma 9.8.1 as printed asserts only Definition 7.2.1."
      ],
      "conclusion": "Z(k)_0 = Z(k)^0, and the filtration Z(k)_r is commutator friendly in the sense of Definition 7.2.1: for u ∈ U_{a,x,i} and u' ∈ U_{-a,x,j} with i + j > 0, the Z-component of (u, u') lies in Z(k)_{i+j}. By Propositions 7.3.17 and 7.6.4, Z(k)_r does not depend on S, and §9.8.2 applies §7.3 to G and every concave function.",
      "lean_declarations": [
        "Langlands.Geometry.Building.CentralizerFiltrationExistenceStatement",
        "Langlands.Geometry.Building.CentralizerFiltrationDoubleRootExistenceStatement"
      ],
      "modules": [
        "Langlands.Geometry.Building.CentralizerFiltrationExistenceStatement",
        "Langlands.Geometry.Building.KPMoyPrasadDoubleRootStatement"
      ],
      "dependencies": [
        "Source proof: Z(k)_0 = Z(k)^0 from Z(K)_{x,0} ⊆ Z(K)^0 and the action of Z(k) on B(Z) = {x}. Commutator friendliness uses a special k-torus of Z containing S (Proposition 9.3.4), Lemma 9.6.3, Lemma 7.1.2 and V 3 for Z_K, Lemma 7.2.3 and Lemma 8.5.19, with the corrected projection B(G)^M → B(Z) of (9.7.1) and Corollary 9.7.3.",
        "Double-root existence (derived in the KPMoyPrasadDoubleRootStatement Markdown, not written out by KP): for quasi-split G_K, Lemma 7.2.3 and functoriality reduce to SU_3, whose formula gives Z-component depth 2(φ_a(u) + φ_{-a}(u')). For general G, translate to the point y with y_{-a}(u') = 0 (Z(k)_r does not depend on the point); with the bound, the argument of Proposition 7.3.17 makes G(K)_{y,2r} normal in G(K)_{y,0}, and the Iwahori decomposition with Lemma 8.5.19 puts the Z-component in Z(K)_{y,2r}, as in the proof of Lemma 9.8.1.",
        "Proof successor: lean.proof@1 Task 5552 (6f2a4efa-b6d0-4494-a8f4-d65632c460d4). The double-root existence statement has proof successor lean.proof@1 Task 5647 (389efdd6-dfb3-478d-b92e-a38a722094e1). Reduction (14 November 2026): published theorems reduce both existence statements of this row to two unproved statements. The first is MaximalUnramified.LocalMoyPrasadGroupPropertiesStatement (module Langlands.Geometry.Building.KPLocalMoyPrasadGroupProperties; artifact 43bb384f-a59e-42a9-8fbf-b9870ae57d12, first in Library commit 51e4d8972659f1ffcf0ca89e8eee9540a30b52d3), the eight group properties of the Moy–Prasad groups G(K)_{x,r} over K, the maximal unramified extension (KP Proposition 7.3.17, Lemma 7.3.16, Lemma 8.5.19, Proposition 13.2.5(4) over K). The second is UnramifiedComparisonExistenceStatement (module Langlands.Geometry.Building.KPUnramifiedComparisonExistenceStatement; artifact 0d0e177a-a770-44bd-a05d-fd62c045b72c, first in Library commit 85c2fe719cf62e96f22aaf4ca03961c5814d086b): for every P satisfying the apartment axioms there are building data B over K whose centralizer Z is a torus (hZ) and an apartment map e with P.IsUnramifiedComparison B hZ e (KP Construction 9.6.1, Lemma 9.6.3, Theorem 9.6.5, §9.8.2). The theorem unramifiedRationalMoyPrasad_of_unramifiedComparison (module Langlands.Geometry.Building.KPUnramifiedMoyPrasadComparison, by Worker 87; artifact 0c32324a-492c-4865-b5b9-ee4f02210eb9, first in Library commit 0c3f30c24701c74d5474fca3fbb5324a99aa1d58) derives UnramifiedRationalMoyPrasadStatement (module Langlands.Geometry.Building.KPUnramifiedRationalMoyPrasadStatement; artifact 42d7a09b-cacb-4a93-bedf-ab6d98e9f2a5, first in Library commit 51e4d8972659f1ffcf0ca89e8eee9540a30b52d3) from these two. For each P satisfying the apartment axioms that statement gives a rational Moy–Prasad family, the preimages in G(F) of the groups G(K)_{e(y),r}, and the theorem ParahoricBuildingData.exists_doubleRootFriendly_filtration_of_rationalMoyPrasadFamily (module Langlands.Geometry.Building.KPRationalMoyPrasadFamily, by Worker 87; artifact cad1aedc-f431-44d4-a407-d10205d3339c, first in Library commit cc5aa77fa8dbdc6e723091c7b710ab0d81162c4e) turns it into a filtration with the conclusion of CentralizerFiltrationDoubleRootExistenceStatement, which implies CentralizerFiltrationExistenceStatement by dropping a conjunct. No published theorem states the composite implication; Worker 3557 checked it with a private lean_check (diagnostic 8c0f7cfa-93c8-4ba6-b2ef-3ffa06958081, Library commit 410c7947, only propext, Classical.choice and Quot.sound). The proof tasks are Task 6191 (c7ac6b9b-7b8b-4a82-9ff8-58e11e279069) for the first statement, which Workers 359 and 147 were executing on 14 November 2026; Task 6424 (7ed6771f-7c41-4101-bf0b-53d5d815f7f1, Worker 188) for the second; and Task 6204 (442d2142-f2ce-4b0a-a4bf-7d80cce1f9a1, Worker 190) for UnramifiedRationalMoyPrasadStatement from the two. Each module cited in this entry with a first commit is byte-identical between that commit and Library commit 410c7947. Update (twentieth pass, 14 November 2026): Task 6540 (f7754156-6269-47b0-9154-d97d1acea85c) published a reduction of the second statement. The theorem unramifiedComparisonExistence_of_fields (module Langlands.Geometry.Building.KPUnramifiedComparisonFieldStatements; artifact bfa0cd13-bb59-420c-a058-2eaeaa1341c9, first in Library commit c40a01345b2f4172fa41e07ff31644b40e695003) derives UnramifiedComparisonExistenceStatement from SpecialTorusExistenceStatement (Proposition 9.3.4 row), UnramifiedValuationDescentStatement (Theorem 9.6.5 row) and four field statements of the same module: UnramifiedComparisonRootFieldStatement, UnramifiedComparisonLeviFieldStatement, UnramifiedComparisonZeroFieldStatement and UnramifiedComparisonOpenFieldStatement. Each of the four quantifies over P satisfying the apartment axioms, a comparison torus t : P.UnramifiedComparisonTorus and an apartment lift L : t.ApartmentLift, and asserts one field of P.IsUnramifiedComparison: the root comparison, the Levi field, the comparison of zero subgroups and openness. The theorem takes the lift from exists_unramifiedApartmentLift (module Langlands.Geometry.Building.KPUnramifiedApartmentLift; artifact 8a0f89b8-9c91-401d-8684-10478eeeee93, first in Library commit e5365902d74534dbf1622c06e695dffdc128d723), which assumes the special-torus and descent statements, and the remaining field apartmentMap_smul from L.normalizer. lean_check inspection ffcbec26-9520-46e8-b544-fe8b87a2e019 by Worker 3557 on 2026-11-14 at Library commit c40a0134 reports kind theorem at universe level u and only propext, Classical.choice and Quot.sound. So both existence statements of this row follow from LocalMoyPrasadGroupPropertiesStatement, SpecialTorusExistenceStatement, UnramifiedValuationDescentStatement and the four field statements; Worker 3557 checked this composite with a private lean_check (diagnostic 45de779f-fad5-45d7-aff5-428454eafde9, Library commit c40a0134, only propext, Classical.choice and Quot.sound). None of these seven statements is proved on 14 November 2026. Two prerequisite statements of this chain are first in Library commit c40a0134 and unproved: MaximalUnramified.LocalMoyPrasadPositiveProductStatement (Task 6542, 2ac95fc3-20ed-446f-81e9-73642246e67a, published by an executor of Task 6191; module Langlands.Geometry.Building.KPLocalMoyPrasadPositiveProductStatement; artifact 1bf5f03b-7551-4499-a00d-6c4e91079eeb), the positive-depth product cover of the groups G(K)_{x,r}, and QuasiSplitValuedRankOneCoordinatesStatement (Task 6564, 06151977-bba4-45f6-9ff3-1ae3f35f125e; module Langlands.Geometry.Building.QuasiSplitValuedRankOneCoordinatesStatement; artifact cf7aabc6-d364-4d30-89d8-a75420bbb945), coherent rank-one coordinates over K for the torus-filtration statements. The statements of Task 6543 (5a7118bc-9b94-402c-836e-220939cc3964, the doubled-root commutator bound over K) and Task 6570 (2f137fe7-e75d-4f7b-8b80-f0958486815d, the depth-zero cases of the group properties) are not in Library commit c40a0134. The modules KPUnramifiedApartmentLift and those cited earlier in this entry are byte-identical between their first commits and Library commit c40a0134."
      ],
      "consumer_or_regression": "Supplies the Zf premise of the published MoyPrasadFiltrationStatement and its four conjuncts (Proposition 13.2.5 row): with proofs of these, the Moy–Prasad results would hold for every P satisfying the apartment axioms without a supplied filtration. The concave function groups G(k)_{x,f} of §9.8.2. Regression: the conclusion fixes only the listed axioms, so different admissible filtrations of tori give different witnesses; a consumer must not assume KP's particular filtration. The double-root existence statement supplies the extra premise of MoyPrasadDoubleRootStatement.",
      "formal_status": "statement",
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [
        "fb1bc376-7e9b-41dd-b6e1-efa863d4f68b",
        "a10cf7b9-8244-4125-94c1-9eb4aa404e35"
      ],
      "publication_commits": [
        "3c9b0579a8f2d36d16294ce48b465d1ec5aee273",
        "297a8ef0ba780a488196cf62285af3ded2e2baa6"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.CentralizerFiltrationExistenceStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "50331a4c-5ce4-43eb-af0a-907db1c5e07f",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-11 at Library commit 529b851c; kind definition; statement_returns_prop true; the module is byte-identical to commit 3c9b0579."
        },
        {
          "declaration": "Langlands.Geometry.Building.CentralizerFiltrationDoubleRootExistenceStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "af670a57-aee3-4d05-8d9a-1d9d3fc2a548",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-12 at Library commit 16c60abd; kind definition; statement_returns_prop true; the module is byte-identical to commit 297a8ef0."
        }
      ],
      "external_code": []
    },
    {
      "source_item": "Definition 6.6.1",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.230–231 / PDF pp.261–262"
      },
      "erratum": null,
      "hypotheses": [
        "G is a connected reductive group over the discretely valued Henselian field k. S is a maximal k-split torus, N=N_G(S), Z=Z_G(S); Z(k)^0 and Z(k)^1 are the source subgroups, not arbitrary choices.",
        "For comparisons with affine actions, use the Chapter 6 root-valuation apartment and affine root system. Constructing this data for general G is a separate obligation.",
        "Recorded Lean scope (partial definition): for supplied P : ParahoricBuildingData G over a nonarchimedean local field, P.normalizerZero is the image of P.centralizerZero (the actual Z(F)^0) in normalizerPoints P.i = N(F), and P.IwahoriWeylGroup := normalizerPoints P.i ⧸ P.normalizerZero is Wtilde^0 as a coset type. Its group structure is used under the instance argument [P.normalizerZero.Normal]. Since Library commit e449cde988d4e97ab280b8d4d11262887ccc26e0 that normality is proved for every supplied P: ParahoricBuildingData.normal_normalizerZero (module ZeroSubgroupCommutatorNormality, published with artifact dce35461-bb3e-429c-9068-cf0465a14731) proves that P.zeroSubgroup = G(F)^0 is normal in G(F), because commutators of G(F) lie in G(F)^♮, and concludes through normalizerZero_normal_of_zeroSubgroup_normal and the published cover comparison. The earlier conditional routes (normalizerZero_normal from UnramifiedZeroPointsIndependenceStatement, normalizerZero_normal_of_unipotentNormalizerCoset) remain. The premise of the first is proved: Langlands.Geometry.Building.unramifiedZeroPointsIndependence (module Langlands.Geometry.Building.UnramifiedZeroIndependenceProof, artifact 4375075b-73b6-48e2-9b4a-f6cddf7e67e3, first published in Library commit db8d6b3d466f2fd453a4df4624ce6c90db8eed46) proves UnramifiedZeroPointsIndependenceStatement, the independence part of KP Lemma 2.6.24 (printed p.104 / PDF p.135) for Definition 2.6.23(1) over K = UnramifiedClosure F: any two data E, E' : UnramifiedZeroDatum F H for a group scheme H over K, which may differ in the torus, its splitting field and the simply connected cover, give the same subgroup E.zeroPoints = H(K)^♮ · T(K)^0. So normalizerZero_normal also proves the normality without a premise. The Theorem 7.8.1 statements also assert it as a conclusion. AffineRootSystem.affineWeylGroup P.affineRoots is W_aff, the subgroup of affine automorphisms of the apartment generated by the affine root reflections. P.affinePart is the separate image of N(F) ∩ G(F)^0 in Wtilde^0. Its identification with W_aff is part of IwahoriWeylExactSequence, not of a definition. P.toComponents is the map Wtilde^0 → G(F)/G(F)^0. Wtilde^1=N(k)/Z(k)^1, the adjoint group Wtilde_ad and the maps Wtilde^0→Wtilde^1→Wtilde_ad are not formalized. The definition status of this row covers only Wtilde^0, W_aff and the affine part."
      ],
      "conclusion": "The Iwahori–Weyl group is Wtilde^0=N(k)/Z(k)^0. Keep the distinct quotient Wtilde^1=N(k)/Z(k)^1 and the affine Weyl group W_aff generated by affine root reflections. The maps Wtilde^0→Wtilde^1→Wtilde_ad need not be injective; the affine action can lose component or central data.",
      "lean_declarations": [
        "Langlands.Geometry.Building.ParahoricBuildingData.normalizerZero",
        "Langlands.Geometry.Building.ParahoricBuildingData.IwahoriWeylGroup",
        "Langlands.Geometry.Building.ParahoricBuildingData.affinePart",
        "Langlands.Geometry.Building.ParahoricBuildingData.toComponents",
        "Langlands.Geometry.Building.AffineRootSystem.affineWeylGroup",
        "Langlands.Geometry.Building.ParahoricBuildingData.normal_normalizerZero",
        "Langlands.Geometry.Building.unramifiedZeroPointsIndependence"
      ],
      "modules": [
        "Langlands.Geometry.Building.IwahoriWeyl",
        "Langlands.Geometry.Building.AffineRootSystem",
        "Langlands.Geometry.Building.ZeroSubgroupCommutatorNormality",
        "Langlands.Geometry.Building.UnramifiedZeroIndependenceProof"
      ],
      "dependencies": [
        "Definitions 2.6.15 and 2.6.23 and the torus/centralizer subgroup comparisons",
        "Chapter 6 affine roots and normalizer action for the comparison maps; 6.6.2 in the quasi-split case and corrected 7.5.1 with AS5 for the general Wtilde_sc≃W_aff comparison",
        "Missing for this row: a Z(F)^1 quotient Wtilde^1 of N(F) and the adjoint comparison. The normality of Z(F)^0 in N(F) is proved for every supplied datum since Library commit e449cde9 (normal_normalizerZero)."
      ],
      "consumer_or_regression": "Theorem 7.8.1 and Hecke indexing beyond simply connected split groups. Regression must distinguish the actual quotient from its affine image.",
      "formal_status": "definition",
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [
        "dce35461-bb3e-429c-9068-cf0465a14731",
        "4375075b-73b6-48e2-9b4a-f6cddf7e67e3"
      ],
      "publication_commits": [
        "c4a16df784376405a45b60df82583e8c26d8a4e3",
        "e449cde988d4e97ab280b8d4d11262887ccc26e0",
        "db8d6b3d466f2fd453a4df4624ce6c90db8eed46"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.IwahoriWeylGroup",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "7e21bb8d-01ee-4632-a37b-b10c52678fb4",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-08 at Library commit c4a16df7."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.affinePart",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "d2867306-5414-4f79-9334-618dfd426112",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-08 at Library commit c4a16df7."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.normal_normalizerZero",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "0159d9aa-3b8b-4d0f-ad23-481b23653132",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-10 at Library commit e449cde9; a theorem from a supporting module of artifact dce35461, which is listed for this theorem only."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedZeroPointsIndependence",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "43cede85-964f-4a9b-8b40-87aa1de2030b",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-14 at Library commit 20f83141; kind theorem; the module is byte-identical to commit db8d6b3d, its first publication."
        }
      ],
      "external_code": []
    },
    {
      "source_item": "Lemma 6.7.1",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.233 / PDF p.264; Chapter 6 standing hypotheses at printed p.195 / PDF p.226; Lemma 6.1.6 and Definitions 6.1.2, 6.1.7 at printed pp.199–201 / PDF pp.230–232"
      },
      "erratum": null,
      "hypotheses": [
        "k has a discrete valuation normalized by ω(k^×)=Z and a Henselian valuation ring; G is connected reductive over k (Chapter 6 standing hypotheses). M is a Levi subgroup with maximal split torus S, and A(S,G) is an equipollence class of valuations of the root datum of (G,S). The corrections of 1 November 2024 contain no entry for §6.7 (PDF p.32).",
        "Recorded Lean scope: LeviApartmentRestrictionStatement quantifies over every nonarchimedean local field F of either characteristic in universe u with ω = localFieldOrder F, every G with hG : IsConnectedReductive G, every maximal split torus i : S → G, every generic cocharacter ν and every J ⊆ simpleRelativeRoots i ν, with the actual standard Levi M_J = Standard.leviScheme i ν J, j = Standard.leviHom i ν J and iM = Standard.leviTorusHom i ν J. For every D : KPApartmentData i (localFieldOrder F) it asserts ∃ DM : KPApartmentData iM (localFieldOrder F) such that every point of D has a restriction in DM (IsLeviRestriction j), every point of DM is such a restriction, and restrictions xM, xM' of x, x' are equal iff x'.val = v +ᵥ x.val for some v ∈ V(S) on which every relative root of (M_J, S) vanishes. Only standard Levi subgroups at the same torus are covered. Compatibility with ω is the S(F) part recorded by KPApartmentData, whose normalizer stability for M_J is part of the conclusion. Part (4) is expressed by surjectivity and this fibre description, and part (5) (Chevalley valuations of quasi-split G) is not formalized. Existence of D is not asserted. The theorem leviApartmentRestriction (module LeviApartmentRestrictionProof) proves this statement for every supplied D with no further premise; it is present in Library commit ed924aef420de137b4cbaa3b063a3618afcd73fd. The row is conditional because D is supplied, not constructed."
      ],
      "conclusion": "Each φ_M is a valuation of the root datum of (M,S), compatible with ω if φ is; A(M,S) = {φ_M} is an equipollence class; φ ↦ φ_M descends to an isomorphism A(S,G)/V(A) → A(M,S) of affine spaces over V(S'_M), where A is the maximal torus in S'_G ∩ Z(M); for quasi-split G, Chevalley valuations restrict to Chevalley valuations.",
      "lean_declarations": [
        "Langlands.Geometry.Building.LeviApartmentRestrictionStatement",
        "Langlands.Geometry.Building.leviApartmentRestriction"
      ],
      "modules": [
        "Langlands.Geometry.Building.LeviApartmentRestrictionStatement",
        "Langlands.Geometry.Building.LeviApartmentRestrictionProof"
      ],
      "dependencies": [
        "Definitions 6.1.2 and 6.1.7 and Lemma 6.1.6; restriction of the root groups of M to those of G.",
        "Proof: leviApartmentRestriction (module LeviApartmentRestrictionProof), present in Library commit ed924aef420de137b4cbaa3b063a3618afcd73fd. It presents M_J as the dynamic centralizer of one cocharacter of S (StandardLeviSplitComponent.exists_standardLevi_eq_dynamicCentralizer) and takes DM to be the published restricted class leviRestrictedApartmentData (module Langlands.BruhatTits.SpecialCompact.LeviApartmentRestriction, artifact 81fa76f0-f8d0-49cb-a920-8453d82a3523 of the previous instance, Worker 164), whose projection gives the first two clauses. For the fibre clause, restriction commutes with translations, and the valuation stabilizer criterion IsRootDatumValuation.vadd_eq_self_iff, which rests on axiom V 0, replaces the source's dimension count.",
        "Proof task: lean.proof@1 Task 5414 (4413f5d7-43ca-46d6-a3f8-d4799eba2603), carried into the current TaskHub instance. On 13 November 2026 its candidate d45496d4-f6fb-458b-99be-4cc1bd232045, byte-identical to the Library pair, was under verification. The acceptance artifact of the Library pair cannot be identified in this instance."
      ],
      "consumer_or_regression": "Section 6.7.2 special points; Levi inheritance of special compact subgroups (Langlands.BruhatTits.SpecialCompact.AvailableSpecialLeviCompactStatement, proved by availableSpecialLeviCompact in module AvailableSpecialLeviCompactProof, present in Library commit ed924aef420de137b4cbaa3b063a3618afcd73fd; its recorded proof task bbd398f5-8ddc-4b82-85ab-bf3f0ef59d81 is absent from this instance) for Renard V.5.1(5). The published theorem Langlands.BruhatTits.SpecialCompact.exists_leviRestriction_of_omegaCompatible (module LeviApartmentComparison, Worker 123) takes LeviApartmentRestrictionStatement as a premise and gives every point of an ω-compatible class a restriction in any supplied ω-compatible standard-Levi class at the same torus. The published statement Langlands.Geometry.Building.LeviApartmentAxiomsInheritanceStatement of this program (first in Library commit 8c11c93f98b439395e0e7da779c98bb27e24bd6d; proof task Task 5471, 48fef6af-65b7-4623-bb54-9305ae84fcf6) asserts that V 7 and AS 2–AS 5 pass from D to a standard-Levi class DM related to D by some restriction pair. It is proved by leviApartmentAxiomsInheritance (module LeviApartmentAxiomsInheritanceProof), present in Library commit ed924aef420de137b4cbaa3b063a3618afcd73fd and inspected with lean_check on 13 November 2026 (inspection 56f5d06c-37cf-4191-bac2-32ddad12fd5e, axioms propext, Classical.choice, Quot.sound); Task 5471 is absent from this instance.",
      "formal_status": "conditional",
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [
        "851e3550-d582-4076-a891-8d9b00badf3e"
      ],
      "publication_commits": [
        "d39b5aee822fe2ad1aadf07861ebd9a4c2df62a8",
        "ed924aef420de137b4cbaa3b063a3618afcd73fd"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.LeviApartmentRestrictionStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "43b9ea6e-ac3f-4609-819c-182735779ab3",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-10 at Library commit e7487341; statement_returns_prop true."
        },
        {
          "declaration": "Langlands.Geometry.Building.leviApartmentRestriction",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "a6cce6cf-be11-4ba9-8dcf-a1488f29ec7e",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit ed924aef; a theorem. Its acceptance artifact cannot be identified in this instance."
        }
      ],
      "external_code": []
    },
    {
      "source_item": "Section 6.7.2",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.233–234 / PDF pp.264–265; Definition 1.3.39 and Proposition 1.3.43(3) at printed pp.29–30 / PDF pp.60–61; Definition 6.3.4 at printed p.218 / PDF p.249"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.32, Chapter 6",
        "change": "Above Remark 6.3.5 read a = ψ̇: the root in the defining condition of Ψ and Ψ′ is the derivative of ψ. No entry concerns §6.7."
      },
      "hypotheses": [
        "The Chapter 6 standing hypotheses of the Lemma 6.7.1 row; M is a Levi subgroup containing the maximal split torus S, and A(S,G) → A(M,S) is the projection of Lemma 6.7.1.",
        "Recorded Lean scope: LeviSpecialPointRestrictionStatement has the quantifiers of the Lemma 6.7.1 row and quantifies over D : KPApartmentData i (localFieldOrder F) and DM : KPApartmentData (Standard.leviTorusHom i ν J) (localFieldOrder F). Its premise is that IsLeviRestriction j x xM holds for some pair. It concludes that every ψM ∈ DM.affineRoots has some ψ ∈ D.affineRoots with ψ x = ψM xM for all restriction pairs, the same for extendedAffineRoots (Ψ′), and that for every restriction pair with x special for D.affineRoots, xM is special for DM.affineRoots (AffineRootSystem.IsSpecialPoint) and a vertex (AffineRootSystem.IsVertex). IsLeviRestriction replaces the projection of Lemma 6.7.1; the hyperplane-preimage sentence is left implicit and the extra-special sentence is not formalized. Only standard Levi subgroups at the same torus over nonarchimedean local fields are covered. The theorem leviSpecialPointRestriction (module LeviSpecialPointRestrictionProof) proves this statement with no further premise; it is present in Library commit ed924aef420de137b4cbaa3b063a3618afcd73fd. The row is conditional because D and DM are supplied, not constructed."
      ],
      "conclusion": "Under the dual of the projection, Ψ(M,S) ⊂ Ψ(S,G) and Ψ′(M,S) ⊂ Ψ′(S,G); affine root hyperplanes of M pull back to affine root hyperplanes; the image of a special point is special, in particular a vertex, and the same holds for extra special points. The image of a vertex need not be a vertex.",
      "lean_declarations": [
        "Langlands.Geometry.Building.LeviSpecialPointRestrictionStatement",
        "Langlands.Geometry.Building.leviSpecialPointRestriction"
      ],
      "modules": [
        "Langlands.Geometry.Building.LeviSpecialPointRestrictionStatement",
        "Langlands.Geometry.Building.LeviSpecialPointRestrictionProof"
      ],
      "dependencies": [
        "Lemma 6.7.1; Definition 6.3.4; Definition 1.3.39 and Proposition 1.3.43(3).",
        "Proof: leviSpecialPointRestriction (module LeviSpecialPointRestrictionProof), present in Library commit ed924aef420de137b4cbaa3b063a3618afcd73fd. One restriction pair identifies DM with the restricted class of Lemma 6.7.1, and every restriction of x is then its projection. The affine-root clauses pull Levi affine roots back along the projection (leviAffineRootPullback, module Langlands.BruhatTits.SpecialCompact.LeviAffineRoots), and specialness of the image is isSpecialPoint_leviApartmentProjection (module LeviSpecialPoint), as in the source. For the vertex clause the proof does not use AS 3, which is not a premise. Axiom V 0 and root doubling show that every root direction occurs, up to a nonzero factor, as the derivative of an affine root of DM; the argument of Proposition 1.3.43(3) then makes a special point a vertex.",
        "Proof task: the recorded proof successor was lean.proof@1 Task 5415 (bd8b3443-747f-4eec-bc01-3311650f8e95), which is absent from the current TaskHub instance, so the acceptance artifact cannot be identified here."
      ],
      "consumer_or_regression": "Special vertices of Levi data for AvailableSpecialLeviCompactStatement (proved by availableSpecialLeviCompact) and Renard V.5.1(5). Regression: the image of a non-special vertex need not be a vertex.",
      "formal_status": "conditional",
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [
        "d664e902-3b89-4fdd-b136-5b2f070a1844"
      ],
      "publication_commits": [
        "d39b5aee822fe2ad1aadf07861ebd9a4c2df62a8",
        "ed924aef420de137b4cbaa3b063a3618afcd73fd"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.LeviSpecialPointRestrictionStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "f70e9f89-d3b3-498b-8ca0-5059f1782a9b",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-10 at Library commit e7487341; statement_returns_prop true."
        },
        {
          "declaration": "Langlands.Geometry.Building.leviSpecialPointRestriction",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "b9ba073c-576e-4a8f-95df-9a4fdc9ea9e8",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit ed924aef; a theorem. Its acceptance artifact cannot be identified in this instance."
        }
      ],
      "external_code": []
    },
    {
      "source_item": "Theorem 5.2.1",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.187–188 / PDF pp.218–219, including (5.2.1) and corrected (5.2.2)"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.30, Section 5.2; valuation signs at PDF pp.24–25",
        "change": "Reverse the inequality in (5.2.2). In the apartment step of the proof remove appeals to 1.5.13(1) and 4.1.9, retaining Proposition 4.2.24. The corrections also remove the minus signs from omega_T and omega_G."
      },
      "hypotheses": [
        "k is discretely valued with Henselian valuation ring and perfect residue field; G is connected reductive over k. S is a maximal k-split torus, A its apartment in the actual Bruhat–Tits building, N=N_G(S) and Z=Z_G(S). These are the Chapter 5 ambient hypotheses.",
        "Fix a positive system Phi^+ and a special vertex x∈A, with parahoric P_x. Define Z_dom⊆Z(k) by a(omega_Z(z))≥0 for every a∈Phi^+. Use the corrected positive valuation homomorphism of Sections 2.5–2.6.",
        "Recorded Lean scope: AvailableCartanStatement quantifies over every nonarchimedean local field F of either characteristic in universe u, every group scheme G over Spec F with hG : IsConnectedReductive G, and every KPBuildingAssignment 𝔅 with 𝔅.IsAvailableFor F G hG (the full corrected Definition 4.1.26 at this F and G; global IsValid is not assumed). With B := (𝔅.datum F G hG).base it takes every cocharacter nu generic for B.i, whose positive relative roots are Phi^+, and every x : B.Apartment with B.apartment.IsSpecialApartmentVertex x. It concludes ParahoricCartanConclusions B nu x for P_x = B.parahoricAt x, j the point map of the centralizer B.centralizer.j and D = parahoricDominantSet B nu = {z ∈ Z(F) | 0 ≤ a(omega_Z(z)) for every a ∈ positiveRelativeRoots B.i nu}. The three conclusions are Set.univ = P_x · j(D) · P_x as pointwise set products; for z, z' ∈ D, equality of the double cosets of j(z) and j(z') iff z' z^(-1) ∈ B.centralizerZero; and bijectivity of parahoricDominantDoubleCosetMap B nu x from ParahoricDominantQuotient B nu (D modulo the restricted right relation by Z(F)^0) onto P_x\\G(F)/P_x. The source's Henselian discretely valued fields with perfect residue field are specialized to nonarchimedean local fields. Existence of an available assignment is not asserted. The theorem availableCartan (module Langlands.BruhatTits.Cartan.AvailableCartanProof) proves AvailableCartanStatement; it was accepted as artifact c3a16a8e-fad7-484f-9e90-64f897f020eb and first published in Library commit d39b5aee822fe2ad1aadf07861ebd9a4c2df62a8. The row's conditional status refers to AvailableCartanStatement, proved under IsAvailableFor."
      ],
      "conclusion": "G(k)=P_x Z_dom P_x, and for all z,z'∈Z_dom, P_x z P_x=P_x z' P_x if and only if z' z^(-1)∈Z(k)^0. Corrected (5.2.2) expresses dominance as omega(a(z))≥0. This indexes dominant centralizer elements modulo Z(k)^0; a universal dominant-cocharacter parametrization is not asserted.",
      "lean_declarations": [
        "Langlands.BruhatTits.Cartan.AvailableCartanStatement",
        "Langlands.BruhatTits.Cartan.ParahoricCartanConclusions",
        "Langlands.BruhatTits.Cartan.availableCartan"
      ],
      "modules": [
        "Langlands.BruhatTits.Cartan.AvailableCartanStatement",
        "Langlands.BruhatTits.Cartan.ParahoricDominantQuotient",
        "Langlands.BruhatTits.Cartan.CentralizerValuation",
        "Langlands.BruhatTits.Cartan.AvailableCartanProof"
      ],
      "dependencies": [
        "Special-vertex geometry, affine Bruhat decomposition, Axiom 4.1.2, Proposition 4.2.24 and Corollary 2.6.28",
        "Corrected valuation signs in Sections 2.5–2.6; for a relative character a, evaluate a(z) by extending a positive multiple to Z and dividing its valuation by that multiple",
        "Proof of AvailableCartanStatement: availableCartan, from lean.proof@1 task 14dc145a-14d4-47d6-97a6-d89ea0c558ab (Task 5331, artifact c3a16a8e-fad7-484f-9e90-64f897f020eb; the task was closed as complete on 2026-11-10). Its only building premise is IsAvailableFor. It applies parahoricCartanConclusions_of_satisfiesGroupAxioms, which needs only KPBuildingDatum.SatisfiesGroupAxioms for the datum of F and G. At commit e7487341 that theorem in turn applies parahoricCartanConclusions_of_buildingGeometry, whose premises on supplied ParahoricBuildingData are SatisfiesApartmentAxioms, HasZeroFixerGenerators, HasNormalizerApartmentStabilizer, injectivity of the apartment map, HasTitsSystem, and that every point of the quotient shares an apartment with the image of x. Proposition 4.2.24 is not among these premises. The general use of the theorem also requires the existence of available data, the Theorem 9.2.7 obligation stated as BruhatTitsAvailabilityStatement (see that row)."
      ],
      "consumer_or_regression": "General special-parahoric Hecke double cosets, with a proved GL_n Cartan comparison and distinctness of the associated compactly supported functions.",
      "formal_status": "conditional",
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [
        "c3a16a8e-fad7-484f-9e90-64f897f020eb"
      ],
      "publication_commits": [
        "c4a16df784376405a45b60df82583e8c26d8a4e3",
        "d39b5aee822fe2ad1aadf07861ebd9a4c2df62a8"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.BruhatTits.Cartan.AvailableCartanStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "f5369bf1-52a4-4a6a-8c9f-d027667823fa",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-08 at Library commit c4a16df7; statement_returns_prop true."
        },
        {
          "declaration": "Langlands.BruhatTits.Cartan.availableCartan",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "66603178-cd94-4fbc-af59-bb2d011e66b0",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-10 at Library commit e7487341; a theorem, acceptance artifact c3a16a8e."
        }
      ],
      "external_code": []
    },
    {
      "source_item": "Theorem 5.3.3",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.188–190 / PDF pp.219–221"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.30, Section 5.3",
        "change": "Replace the argument in the proof identifying the relevant open-cell intersections: M_a is a cocharacter centralizer and its open-cell factors are cocharacter-stable; apply 4.1.16 through those factors."
      },
      "hypotheses": [
        "k is discretely valued with Henselian valuation ring and perfect residue field; G is connected reductive over k. S is a maximal k-split torus, A its apartment in the actual Bruhat–Tits building, N=N_G(S) and Z=Z_G(S). These are the Chapter 5 ambient hypotheses.",
        "Choose positive relative roots and let U be the unipotent radical of the corresponding minimal parabolic, with Levi Z. C is any chamber of A and P_C its Iwahori subgroup.",
        "Recorded Lean scope: IwasawaDecompositionStatement quantifies over every nonarchimedean local field F of either characteristic in universe u, every affine F-group scheme G and supplied P : ParahoricBuildingData G, under the explicit hypotheses HenselianLocalRing 𝒪[F], PerfectField 𝓀[F] and P.apartment.SatisfiesApartmentAxioms P.centralizer (V6, V7, AS2–AS4 and AS5). For every chamber C of the apartment and every generic cocharacter nu of S it concludes P.IwasawaDecomposition C nu: every g ∈ G(F) is u·n·p with u ∈ standardUnipotentPoints P.i nu ∅, n ∈ normalizerPoints P.i and p ∈ P.parahoric C. The positive system is the one selected by nu. U(F) is the published standardUnipotentPoints, the rational points of standardUnipotent P.i nu ∅. For connected reductive G and a maximal split torus, the Library proves standardUnipotent i nu ∅ = Dynamic.unipotent for every cocharacter nu, with no genericity hypothesis (standardUnipotent_empty_eq_dynamic, module Langlands.GroupScheme.Rational.MinimalStandardDynamicComparison). The source proves the result for a building satisfying the Chapter 4 axioms, including Axiom 4.1.16; the Lean statement assumes only the Chapter 7 apartment axioms on the same valuation data, relying on 4.1.28 (4.1.16 is Corollary 7.4.9 for this data). No existence of P is asserted."
      ],
      "conclusion": "G(k)=U(k) N(k) P_C. No special-vertex condition is imposed on C. This product equality supplies the surjectivity part of the later U\\G/I indexing theorem; injectivity uses replaced Lemma 5.3.5.",
      "lean_declarations": [
        "Langlands.Geometry.Building.IwasawaDecompositionStatement",
        "Langlands.Geometry.Building.ParahoricBuildingData.IwasawaDecomposition",
        "Langlands.Geometry.Building.iwasawaDecomposition"
      ],
      "modules": [
        "Langlands.Geometry.Building.IwahoriWeylStatement",
        "Langlands.Geometry.Building.IwasawaDecompositionProof"
      ],
      "dependencies": [
        "Rank-one groups M_a and Lemmas 5.3.1–5.3.2; Iwahori decomposition Axiom 4.1.16; algebraic Bruhat decomposition",
        "Corrected cocharacter-centralizer and stable open-cell argument, rather than the printed closed-subgroup compatibility shortcut",
        "Published proof: Langlands.Geometry.Building.iwasawaDecomposition has type exactly IwasawaDecompositionStatement.{u}. It was accepted as lean.proof artifact 937be117-c6a0-42d8-be70-cd5c630935ac of task 0b383eb0-185c-415b-8def-5fcbac419374 and first appears in Library commit 0646cc6120e56febaf6f88f723f3b147d0e23d59. Its route differs from the source: it applies the published conditional theorem iwasawaDecompositionStatement_of_structuralStatements (module Langlands.Geometry.Building.IwasawaDecompositionReduction) to seven published structural proofs. The reduction builds the relative Tits system (G(F), P_∅(F), N(F), S) and shows that P(nu)(F)·N(F)·P_C contains 1 and is stable under left multiplication by the Borel subgroup and by the simple-reflection representatives, using a chamber form of Lemma 5.3.1. A dynamic-limit argument then absorbs the centralizer factor into N(F). The Henselian and perfect-residue hypotheses are retained in the target but unused by this route.",
        "The replaced Lemma 5.3.5 is not proved by this unit; it remains with task 0b383eb0-185c-415b-8def-5fcbac419374 (see that row). That task's context names the previous-instance acceptance artifact 90c646e0-a29a-4a82-8110-f92b10c12ca3 of the statements, the one cited by the Theorem 7.8.1 row."
      ],
      "consumer_or_regression": "Corrected Theorem 7.8.1(4), followed by actual double-coset and compact induction computations.",
      "formal_status": "conditional",
      "owner_task": "0b383eb0-185c-415b-8def-5fcbac419374",
      "acceptance_artifact_ids": [
        "937be117-c6a0-42d8-be70-cd5c630935ac"
      ],
      "publication_commits": [
        "c4a16df784376405a45b60df82583e8c26d8a4e3",
        "0646cc6120e56febaf6f88f723f3b147d0e23d59"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.iwasawaDecomposition",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "e0b84c70-b3b7-4b5f-9adf-4753663a13d3",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-09 at Library commit eb36be01; independent proof acceptance and publication are recorded separately."
        },
        {
          "declaration": "Langlands.Geometry.Building.IwasawaDecompositionStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "ce25cec1-caa8-4246-89d2-611d6855d59b",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-08 at Library commit c4a16df7; statement_returns_prop true."
        }
      ],
      "external_code": []
    },
    {
      "source_item": "Theorem 5.3.4",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.190 / PDF p.221"
      },
      "erratum": null,
      "hypotheses": [
        "k is discretely valued with Henselian valuation ring and perfect residue field; G is connected reductive over k. S is a maximal k-split torus, A its apartment in the actual Bruhat–Tits building, N=N_G(S) and Z=Z_G(S). These are the Chapter 5 ambient hypotheses.",
        "x is any special vertex in B(G), P_x its parahoric, and P is any parabolic k-subgroup of G. P and P_x denote different kinds of objects.",
        "Recorded Lean scope: AvailableIwasawaStatement quantifies over every nonarchimedean local field F of either characteristic in universe u, every group scheme G over Spec F with hG : IsConnectedReductive G, every KPBuildingAssignment 𝔅 with 𝔅.IsAvailableFor F G hG, and every cocharacter nu generic for B.i, where B := (𝔅.datum F G hG).base. Its first clause takes every x : B.Apartment with B.apartment.IsSpecialApartmentVertex x. Its second takes every y : B.ReducedBuilding with B.IsSpecialPoint y and B.IsVertex y and every Q with B.IsParahoricAt y Q (a G(F)-conjugate of an apartment parahoric at the translated point). For P_x = B.parahoricAt x, respectively Q, it concludes ParabolicPointProductFamily B.i nu: Set.univ = H·K and Set.univ = K·H as pointwise set products, for H ranging over the rational points of every algebraic parabolic subgroup, every Dynamic.parabolic, every standard P_J and their rational conjugates. It also adds three conclusions beyond the source theorem: the inclusion of P_x (or Q) in the compact stabilizer K_0 = B.apartment.specialCompactSubgroup x = G(F)^1 ∩ Stab(B.apartmentMap x) (or B.compactStabilizer y), the same product family for K_0, and IsCompactOpenMaximal F K_0 for the canonical rational-point topology. IwasawaExistenceStatement adds existence: for every maximal split torus i : S → G and generic nu it asserts an available assignment whose base torus and apartment are identified with i and given apartment data D, a special vertex x of D whose compact subgroup satisfies SpecialCompactProperties, the same product conclusions for G and the whole-building clause, and the corresponding data and product conclusions for every standard Levi M_J. Existence of available data is asserted only by IwasawaExistenceStatement, which is unproved. The theorem availableIwasawa (module Langlands.BruhatTits.Iwasawa.AvailableProof) proves AvailableIwasawaStatement, including the three added conclusions; it was accepted as artifact 42bb1c08-a7ac-49f5-a197-dc1d5707a42e and first published in Library commit e449cde988d4e97ab280b8d4d11262887ccc26e0. The row's conditional status refers to AvailableIwasawaStatement, proved under IsAvailableFor; IwasawaExistenceStatement remains a statement."
      ],
      "conclusion": "G(k)=P(k) P_x=P_x P(k). The vertex must be special; the parabolic need not be the initially chosen minimal one.",
      "lean_declarations": [
        "Langlands.BruhatTits.Iwasawa.AvailableIwasawaStatement",
        "Langlands.BruhatTits.Iwasawa.IwasawaExistenceStatement",
        "Langlands.BruhatTits.Iwasawa.ParabolicPointProductFamily",
        "Langlands.BruhatTits.Iwasawa.availableIwasawa"
      ],
      "modules": [
        "Langlands.BruhatTits.Iwasawa.AvailableStatement",
        "Langlands.BruhatTits.Iwasawa.AvailableProof",
        "Langlands.BruhatTits.Iwasawa.ExistenceStatement",
        "Langlands.BruhatTits.Iwasawa.PointProducts"
      ],
      "dependencies": [
        "Theorem 5.3.3 with its corrected proof",
        "Specialness and the normalizer-to-finite-Weyl surjection; conjugacy of minimal parabolics; inversion for the second product equality",
        "The added compact-stabilizer conclusions use Theorem 4.2.15(1) and Fact 2.2.3, as cited by the statement Markdown.",
        "Proof of AvailableIwasawaStatement: availableIwasawa, from lean.proof@1 task 5e9b97bd-7a9c-43fb-bb8f-b017b7028adc (artifact 42bb1c08-a7ac-49f5-a197-dc1d5707a42e; the task was closed as complete on 2026-11-10). Its only building premise is IsAvailableFor, and it proves the inclusion P_x ≤ K_0 for available data. The Library states that inclusion for all supplied data as Langlands.BruhatTits.SpecialCompact.ParahoricLeCompactStabilizer. The theorem parahoricLeCompactStabilizer (module Langlands.BruhatTits.SpecialCompact.ParahoricProof, by Worker 31; proof task 0fda3c3d-207f-4fdc-9858-1d43ec2bb41e; artifact 185b1037-06e0-419a-a9db-36702b83c96d, first in Library commit 17dd94ea3f677b20fb5ab95b285cbc3fd7cde03e) proves it with no hypothesis beyond its binders: for every nonarchimedean local field F, every G with IsAffineHom G.X.hom, all P : ParahoricBuildingData G and every apartment point x, P.parahoricAt x ≤ P.apartment.specialCompactSubgroup x. lean_check inspection 6967e878-5664-406f-af3e-0e99c02d05a0 by Worker 3557 on 2026-11-13 at Library commit 0f84a0d8 reports kind theorem and only propext, Classical.choice and Quot.sound. The chamber form 5.3.3 has a published proof (see that row). TaskHub searches on 2026-11-08 found no proof task for IwasawaExistenceStatement. It also requires the existence of available data, the Theorem 9.2.7 obligation stated as BruhatTitsAvailabilityStatement (see that row)."
      ],
      "consumer_or_regression": "Parabolic induction and Jacquet structural bridges, retaining the special-parahoric and parabolic hypotheses.",
      "formal_status": "conditional",
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [
        "42bb1c08-a7ac-49f5-a197-dc1d5707a42e"
      ],
      "publication_commits": [
        "c4a16df784376405a45b60df82583e8c26d8a4e3",
        "e449cde988d4e97ab280b8d4d11262887ccc26e0"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.BruhatTits.Iwasawa.AvailableIwasawaStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "90ac7a25-e581-4491-8b58-2b6fb57ccba5",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-08 at Library commit c4a16df7; statement_returns_prop true."
        },
        {
          "declaration": "Langlands.BruhatTits.Iwasawa.IwasawaExistenceStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "525da1b1-80d2-44c4-ac1a-551af953a0aa",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-08 at Library commit c4a16df7; statement_returns_prop true."
        },
        {
          "declaration": "Langlands.BruhatTits.Iwasawa.availableIwasawa",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "c5a5bacb-5fd3-4201-8316-4a91110aa01a",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-10 at Library commit e449cde9; a theorem, acceptance artifact 42bb1c08."
        }
      ],
      "external_code": []
    },
    {
      "source_item": "Lemma 5.3.5",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.191 / PDF p.222; statement and proof replaced by corrections PDF p.30"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.30, Section 5.3",
        "change": "Replace the entire printed statement and proof by the Iwahori normalizer criterion n∈U(k)n'P_C iff n'n^(-1)∈Z(k)^0."
      },
      "hypotheses": [
        "k is discretely valued with Henselian valuation ring and perfect residue field; G is connected reductive over k. S is a maximal k-split torus, A its apartment in the actual Bruhat–Tits building, N=N_G(S) and Z=Z_G(S). These are the Chapter 5 ambient hypotheses.",
        "Use the notation of Theorem 5.3.3: U is the chosen minimal-parabolic unipotent radical, C is any chamber of A and P_C its Iwahori. n,n' range over all elements of N(k).",
        "Recorded Lean scope: UnipotentNormalizerCosetStatement has the same quantifiers and hypotheses as the Theorem 5.3.3 row's IwasawaDecompositionStatement (HenselianLocalRing 𝒪[F], PerfectField 𝓀[F], P.apartment.SatisfiesApartmentAxioms P.centralizer, every chamber C and every generic cocharacter nu). It concludes P.UnipotentNormalizerCoset C nu: for all n, n' ∈ normalizerPoints P.i, there exist u ∈ standardUnipotentPoints P.i nu ∅ and p ∈ P.parahoric C with n = u·n'·p if and only if n'·n^(-1) ∈ P.normalizerZero, the image of Z(F)^0 in N(F). Only the replaced lemma is stated; the printed version is not. The standardUnipotentPoints convention and the Chapter 4 versus Chapter 7 hypothesis difference of the Theorem 5.3.3 row apply unchanged. No existence of P is asserted. The theorem unipotentNormalizerCoset (module UnipotentNormalizerCosetProof) proves this statement with unchanged hypotheses; it is present in Library commit 17dd94ea3f677b20fb5ab95b285cbc3fd7cde03e. The row is therefore conditional until the data are constructed."
      ],
      "conclusion": "n∈U(k) n' P_C if and only if n' n^(-1)∈Z(k)^0. The printed statement with an arbitrary bounded subgroup P is replaced and is not the target.",
      "lean_declarations": [
        "Langlands.Geometry.Building.UnipotentNormalizerCosetStatement",
        "Langlands.Geometry.Building.ParahoricBuildingData.UnipotentNormalizerCoset",
        "Langlands.Geometry.Building.unipotentNormalizerCoset"
      ],
      "modules": [
        "Langlands.Geometry.Building.IwahoriWeylStatement",
        "Langlands.Geometry.Building.UnipotentNormalizerCosetProof"
      ],
      "dependencies": [
        "Iwahori decomposition for the translated chamber C'=nC",
        "Algebraic Bruhat/open-cell uniqueness forces n' n^(-1) into Z(k), then the Iwahori intersection identifies Z(k)^0",
        "Open proof task: 0b383eb0-185c-415b-8def-5fcbac419374, whose Theorem 5.3.3 unit is published. The Library has only conditional assemblies (module Langlands.Geometry.Building.UnipotentNormalizerCosetReduction). unipotentNormalizerCosetReduction proves the conclusion for supplied P from normality of P.normalizerZero, P.ChamberIwahoriDecompositionStatement and the apartment axioms. unipotentNormalizerCosetStatement_of_chamberIwahori_and_exactSequence derives the global statement from the chamber products for all supplied data and IwahoriWeylExactSequenceStatement. On 2026-11-09 the Library had no unconditional proof of either input. Library commit e449cde988d4e97ab280b8d4d11262887ccc26e0 proves both inputs of unipotentNormalizerCosetReduction for every supplied P: the normality of P.normalizerZero by ParahoricBuildingData.normal_normalizerZero (module ZeroSubgroupCommutatorNormality) and the chamber products by ParahoricBuildingData.chamberIwahoriDecomposition (Corollary 7.4.9 row). The published proof of Theorem 7.8.1(4), unipotentIwahoriDoubleCoset, applies unipotentNormalizerCoset_of_chamberIwahori with normal_normalizerZero and a proved chamber Iwahori decomposition. No theorem has type IwahoriWeylExactSequenceStatement.",
        "Proof: unipotentNormalizerCoset (module UnipotentNormalizerCosetProof), present in Library commit 17dd94ea3f677b20fb5ab95b285cbc3fd7cde03e, applies ParahoricBuildingData.unipotentNormalizerCoset_of_chamberIwahori to every supplied P with normal_normalizerZero and chamberIwahoriDecomposition, so no exact-sequence input is needed. It keeps the Henselian and perfect-residue-field premises, which this route does not use. Its acceptance artifact cannot be identified in this instance; lean_check inspection 66cfe0ff-1f53-4270-b782-99b084a37c94 by Worker 3557 on 2026-11-13 at Library commit 8ff9abe9 reports kind theorem and only propext, Classical.choice and Quot.sound."
      ],
      "consumer_or_regression": "Actual injectivity of the map in corrected Theorem 7.8.1(4); a surjective Iwasawa product alone cannot establish this conclusion.",
      "formal_status": "conditional",
      "owner_task": "0b383eb0-185c-415b-8def-5fcbac419374",
      "acceptance_artifact_ids": [],
      "publication_commits": [
        "c4a16df784376405a45b60df82583e8c26d8a4e3",
        "17dd94ea3f677b20fb5ab95b285cbc3fd7cde03e"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.UnipotentNormalizerCosetStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "73e1c9df-449b-437b-a777-b5a80c824b09",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-08 at Library commit c4a16df7; statement_returns_prop true."
        },
        {
          "declaration": "Langlands.Geometry.Building.unipotentNormalizerCoset",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "66cfe0ff-1f53-4270-b782-99b084a37c94",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit 8ff9abe9; a theorem proving UnipotentNormalizerCosetStatement. Its acceptance artifact cannot be identified in this instance."
        }
      ],
      "external_code": []
    },
    {
      "source_item": "Corollary 7.4.9",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.257 / PDF p.288; sharp/parahoric definitions at PDF pp.286–287"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.33, opening Chapter 7 hypothesis addition",
        "change": "The Chapter 7 setup additionally assumes AS5 of Axiom 4.1.6. There is no direct replacement of the Corollary 7.4.9 formula."
      },
      "hypotheses": [
        "k has a normalized discrete valuation omega(k^times)=Z and Henselian valuation ring. G is connected reductive. The Chapter 7 root-datum valuations, equipollent apartments, normalizer actions and Axiom 4.1.4 equivariance are supplied, together with AS5 of Axiom 4.1.6 added by corrections PDF p.33. Perfect residue is not assumed for this conditional Chapter 7 setup.",
        "C⊂A is a chamber, x∈C and Phi^+ is any positive relative-root system. Products use non-divisible roots. For the first product take r=0 or r=0+.",
        "For the facet form, F lies in the closure of C and Phi^+ contains Phi_F(C)^+ from Proposition 1.3.35.",
        "Recorded Lean scope: every nonarchimedean local field F of either characteristic and supplied P : ParahoricBuildingData G, with P.apartment.SatisfiesApartmentAxioms P.centralizer, an actual chamber C, x in C and a generic cocharacter nu. The facet clause retains IsFaceOf and FacetChamberPositiveSystem. No existence of P or proof of AS5 is asserted. The theorem ParahoricBuildingData.chamberIwahoriDecomposition (module ChamberIwahoriProof) proves the statement for every supplied P, from the published factor-pair reduction with the rank-one factorization (KP 2.11.17) and Corollary 2.6.28. It was accepted as artifact 4493a3f5-fe76-417d-8239-cbb2e5149465 (proof task 0e645cc1-7bb2-467a-9835-9d16f29b985f) and first published in Library commit e449cde988d4e97ab280b8d4d11262887ccc26e0. The row is conditional on the construction of P."
      ],
      "conclusion": "N_x^sharp=Z_x^sharp and G(k)_C^sharp=(product over Phi^-,nd of U_{a,x,r}) Z_x^sharp (product over Phi^+,nd of U_{a,x,r}). In the facet form replace the negative factors by U_{a,F,0+} and positive factors by U_{a,F,0}. This is the sharp subgroup; the full parahoric is Z(k)^0 G(k)_C^sharp by 7.4.1. The recorded Prop-valued target additionally states the derived full-Iwahori conclusions: I_C=P_x, Z(F) intersection I_C=j(Z(F)^0), equality of full and sharp unipotent intersections, injectivity and exact range of the negative/full-central/positive product, and all fixed-sign ordered chamber and facet products. Sharp and full groups and central factors remain distinct.",
      "lean_declarations": [
        "Langlands.Geometry.Building.ParahoricBuildingData.ChamberIwahoriDecompositionStatement",
        "Langlands.Geometry.Building.ParahoricBuildingData.chamberIwahoriDecomposition"
      ],
      "modules": [
        "Langlands.Geometry.Building.ChamberIwahoriStatement",
        "Langlands.Geometry.Building.ChamberIwahoriProof"
      ],
      "dependencies": [
        "Lemma 7.4.7; triviality of the affine-Weyl stabilizer of an interior chamber point; Proposition 7.3.12 and 6.3.21",
        "Arbitrary-order fixed-sign root-factor bijections are in 7.3.12(3),(5). Full-parahoric ordered bijections additionally use the central Z(k)^0 factor and algebraic open-cell injectivity; the added mixed all-root 7.3.12(6), requiring f(0)>0, is not the depth-zero argument"
      ],
      "consumer_or_regression": "Iwahori factorization with order and intersection laws; compare the Library GL_n factorization and a multipliable-root example.",
      "formal_status": "conditional",
      "owner_task": "0e645cc1-7bb2-467a-9835-9d16f29b985f",
      "acceptance_artifact_ids": [
        "4cc5a2e0-c5a0-442f-b6c1-90c92f2a7c6b",
        "4493a3f5-fe76-417d-8239-cbb2e5149465"
      ],
      "publication_commits": [
        "25b91125ea94e88d741b206d633e82eb0d87c3e5",
        "e449cde988d4e97ab280b8d4d11262887ccc26e0"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.chamberIwahoriDecomposition",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "d72c9cc5-53bf-4593-af44-e993e7bd369b",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-10 at Library commit e449cde9; a theorem, acceptance artifact 4493a3f5."
        }
      ],
      "external_code": []
    },
    {
      "source_item": "Theorem 7.8.1",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.272–273 / PDF pp.303–304; part (4) added at corrections PDF pp.35–36"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF pp.33 and 35–36, Chapter 7 and Theorem 7.8.1",
        "change": "Add AS5 to the chapter hypotheses. Replace the insufficient injectivity proof of (2) by component cancellation followed by Bruhat injectivity. Add assertion (4) and its 5.3.3/5.3.5 proof."
      },
      "hypotheses": [
        "k has a normalized discrete valuation omega(k^times)=Z and Henselian valuation ring. G is connected reductive. The Chapter 7 root-datum valuations, equipollent apartments, normalizer actions and Axiom 4.1.4 equivariance are supplied, together with AS5 of Axiom 4.1.6 added by corrections PDF p.33. Perfect residue is not assumed for this conditional Chapter 7 setup.",
        "S is a maximal k-split torus, N and Z its normalizer and centralizer, Wtilde^0=N(k)/Z(k)^0, and W_aff is the affine Weyl group. C⊂A is a chamber and I=G(k)^0_C. For part (3), F_1,F_2 lie in the closure of a common chamber and W_aff_Fi is the affine-Weyl facet stabilizer.",
        "For the source route to added part (4), also retain the Chapter 5 perfect-residue building hypotheses used by 5.3.3 and replaced 5.3.5. U is the unipotent radical of a minimal parabolic containing S, with Levi Z. Any broader residue-field version needs a separate proof.",
        "Recorded Lean scope: closed Prop-valued targets at universe u quantify over every nonarchimedean local field F, every affine F-group scheme G and supplied P : ParahoricBuildingData G, retaining SatisfiesApartmentAxioms. Part (4) explicitly requires HenselianLocalRing O[F], PerfectField k[F] and a generic cocharacter nu. The actual U(F) is standardUnipotentPoints P.i nu empty. Its comparison with the single Dynamic.unipotent group is proved: standardUnipotent_empty_eq_dynamic (module Langlands.GroupScheme.Rational.MinimalStandardDynamicComparison) gives standardUnipotent i nu ∅ = Dynamic.unipotent for connected reductive G and a maximal split torus, without a genericity hypothesis, and IwasawaDecompositionReduction specializes it to the rational points of the same supplied P (see the Theorem 5.3.3 row). This comparison alone does not prove part (4). Part (4) is now proved on supplied data: the theorem unipotentIwahoriDoubleCoset (module UnipotentIwahoriDoubleCosetProof) proves UnipotentIwahoriDoubleCosetStatement from iwasawaDecomposition (Theorem 5.3.3 row), unipotentNormalizerCoset_of_chamberIwahori, normal_normalizerZero and a proved chamber Iwahori decomposition. It was accepted as artifact dce35461-bb3e-429c-9068-cf0465a14731 (proof task 7bfe81b2-233e-47a8-85c1-1fd296f32c05) and first published in Library commit e449cde988d4e97ab280b8d4d11262887ccc26e0. Parts (1)–(3) remain unproved, so the row stays statement. They are reduced to open inputs by published theorems. iwahoriWeylNormalizerAffineWeylReduction (module IwahoriWeylNormalizerAffineWeylReduction) derives part (1) (IwahoriWeylExactSequenceStatement) and the chamber splitting of 7.8.2 (IwahoriWeylChamberSplittingStatement) from SimplyConnectedNormalizerAffineWeylStatement (proof task 5210ae85-2886-4b9f-af36-d57d6dba2607). By the Theorem 7.5.3 row, that statement in turn follows from SimplyConnectedFacetFixingStatement (proof task c5ad9ef0-554c-4af8-be60-3607ad0e7e9b). doubleCosetStatementReduction (module DoubleCosetStatementReduction) derives part (2) (IwahoriDoubleCosetStatement) from IwahoriWeylChamberSplittingStatement and AffineIwahoriTitsStatement. It derives part (3) (ParahoricDoubleCosetStatement) from IwahoriWeylChamberSplittingStatement and FacetParabolicComparisonStatement (the common-chamber comparison of KP Proposition 7.5.5; proof task c2766503-ffb3-4bf4-a441-5a73eca4fac3, unproved). A proof of SimplyConnectedFacetFixingStatement would therefore prove parts (1) and (2) on supplied data. Part (3) would also need FacetParabolicComparisonStatement. No general building existence is asserted."
      ],
      "conclusion": "(1) Exact sequence 1→W_aff→Wtilde^0→G(k)/G(k)^0→1. (2) Inclusion induces a bijection Wtilde^0→I\\G(k)/I. (3) Inclusion induces a bijection W_aff_F1\\Wtilde^0/W_aff_F2 →G(k)^0_F1\\G(k)/G(k)^0_F2. (4) Inclusion induces a bijection Wtilde^0→U(k)\\G(k)/I=U(k)Z(k)^0\\G(k)/I. These are actual quotient bijections, including the component contribution beyond W_aff. The exact-sequence target includes the needed normality conclusions and an identification of its kernel with the affine Weyl group through the actual apartment action. Each quotient equivalence is prescribed on every normalizer representative; the added part (4) contains both bijections.",
      "lean_declarations": [
        "Langlands.Geometry.Building.IwahoriWeylExactSequenceStatement",
        "Langlands.Geometry.Building.IwahoriDoubleCosetStatement",
        "Langlands.Geometry.Building.ParahoricDoubleCosetStatement",
        "Langlands.Geometry.Building.UnipotentIwahoriDoubleCosetStatement",
        "Langlands.Geometry.Building.unipotentIwahoriDoubleCoset",
        "Langlands.Geometry.Building.iwahoriWeylNormalizerAffineWeylReduction",
        "Langlands.Geometry.Building.doubleCosetStatementReduction"
      ],
      "modules": [
        "Langlands.Geometry.Building.IwahoriWeylStatement",
        "Langlands.Geometry.Building.UnipotentIwahoriDoubleCosetProof",
        "Langlands.Geometry.Building.IwahoriWeylNormalizerAffineWeylReduction",
        "Langlands.Geometry.Building.DoubleCosetStatementReduction"
      ],
      "dependencies": [
        "Fact 4.1.25, corrected Theorem 7.5.3 and Proposition 7.5.5",
        "Corrected (2) injectivity: use 7.8.2 and Lemma 1.3.17 to write w_i rho_i, use (1) and I⊂G(k)^0 to identify the rho_i, cancel their normalizing action, then apply actual affine Bruhat injectivity in G(k)^0 (Proposition 1.4.5). I∩N(k)=Z(k)^0 alone is insufficient",
        "Part (4): Theorem 5.3.3 for surjectivity and replaced Lemma 5.3.5 for injectivity, with their source hypotheses",
        "7.8.2 gives Wtilde^0=W_aff semidirect Stab(C,Wtilde^0) after choosing C; 7.7.12 identifies that stabilizer with the Iwahori normalizer modulo I",
        "Open formal inputs on 13 November 2026, through the published reductions in the last hypotheses entry: SimplyConnectedFacetFixingStatement (proof task c5ad9ef0-554c-4af8-be60-3607ad0e7e9b) for parts (1) and (2) and 7.8.2; FacetParabolicComparisonStatement (proof task c2766503-ffb3-4bf4-a441-5a73eca4fac3) in addition for part (3)"
      ],
      "consumer_or_regression": "Distinct Hecke functions and finite-support convolution beyond simply connected split groups. Preserve length-zero data and the chamber dependence of the splitting; no Iwahori–Matsumoto presentation is claimed.",
      "formal_status": "statement",
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [
        "90c646e0-a29a-4a82-8110-f92b10c12ca3",
        "dce35461-bb3e-429c-9068-cf0465a14731"
      ],
      "publication_commits": [
        "25b91125ea94e88d741b206d633e82eb0d87c3e5",
        "e449cde988d4e97ab280b8d4d11262887ccc26e0",
        "ed924aef420de137b4cbaa3b063a3618afcd73fd"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.unipotentIwahoriDoubleCoset",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "2da48600-4de7-421f-b0da-ff2c84bafbfb",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-10 at Library commit e449cde9; a theorem proving part (4), acceptance artifact dce35461."
        },
        {
          "declaration": "Langlands.Geometry.Building.iwahoriWeylNormalizerAffineWeylReduction",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "826bc372-1a07-4ece-86ae-c5eb8a507551",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit ed924aef; a theorem reducing part (1) and 7.8.2 to SimplyConnectedNormalizerAffineWeylStatement."
        },
        {
          "declaration": "Langlands.Geometry.Building.doubleCosetStatementReduction",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "a5ed5f71-87eb-476c-b671-a3e642ead8f7",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit 8ff9abe9; a theorem reducing parts (2) and (3) to IwahoriWeylChamberSplittingStatement with AffineIwahoriTitsStatement and FacetParabolicComparisonStatement respectively."
        }
      ],
      "external_code": []
    },
    {
      "source_item": "Lemma 11.5.2",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.430–431 / PDF pp.461–462; Chapter 11 ambient hypotheses at PDF p.451"
      },
      "erratum": null,
      "hypotheses": [
        "k has a normalized discrete valuation, Henselian valuation ring and perfect residue field f; G is connected reductive. In a fixed separable closure k_s let K be the maximal unramified extension, I=Gal(k_s/K) and Gamma=Gal(K/k). Put A=pi_1(G)_I. kappa_G:G(k)→A^Gamma is the restriction of the actual Kottwitz homomorphism constructed over K in 11.5.1.",
        "G(k)^1 is the subgroup of Definition 2.6.15, and A_tor is the torsion subgroup of A. No dim(f)≤1 assumption is imposed.",
        "Recorded Lean scope: CharacterKernelStatement (module Langlands.Geometry.Building.Kottwitz.CharacterKernelStatement) quantifies over every nonarchimedean local field F and connected reductive G over Spec F and asserts characterValuationKernel (ValuativeRel.valuation F) G = (fundamentalInvariantTorsion F (UnramifiedClosure F) (SeparableClosure F) G hG).comap κ_G. characterValuationKernel is the Library's G(F)^1, the common kernel of the valuations of the F-rational characters (Definition 2.6.15). K is the Library's maximal unramified extension UnramifiedClosure F inside the separable closure SeparableClosure F. ReductiveInvariantTarget F G hG is A^Γ for A = π_1(G)_I, the integral inertia coinvariants of the actual algebraic fundamental group, with the actual residual action of Γ = Gal(K/F); fundamentalInvariantTorsion is (A_tor)^Γ as a subgroup of A^Γ. κ_G is reductiveKottwitzRational F G hG (module Langlands.Geometry.Building.Kottwitz.ReductiveMap), selected by classical epsilon among the homomorphisms G(F) → A^Γ whose composite with A^Γ → A is the K-point map reductiveKottwitz on the image of G(F) in G(K). reductiveKottwitz is in turn selected by its squares with every z-extension, over the simply-connected-derived construction through every cocenter. That both selections have their characterizing properties is asserted by ReductiveKottwitzExistenceStatement (existence of z-extensions and unique existence, surjectivity and independence of the K-point map) and ReductiveKottwitzDescentStatement (residual Galois equivariance and unique existence of the restriction to G(F)), both in module Langlands.Geometry.Building.Kottwitz.ReductiveMapStatement; neither is proved. The source's Henselian discretely valued fields with perfect residue field are specialized to nonarchimedean local fields of either characteristic in universe u; their residue fields are finite."
      ],
      "conclusion": "G(k)^1=kappa_G^(-1)((A_tor)^Gamma). This is the preimage of invariant torsion, distinct from the zero kernel identifying G(k)^0.",
      "lean_declarations": [
        "Langlands.Geometry.Building.Kottwitz.CharacterKernelStatement",
        "Langlands.Geometry.Building.Kottwitz.ReductiveKottwitzExistenceStatement",
        "Langlands.Geometry.Building.Kottwitz.ReductiveKottwitzDescentStatement",
        "Langlands.Geometry.Building.Kottwitz.CharacterKernelInputs.characterKernel"
      ],
      "modules": [
        "Langlands.Geometry.Building.Kottwitz.CharacterKernelStatement",
        "Langlands.Geometry.Building.Kottwitz.ReductiveMapStatement",
        "Langlands.Geometry.Building.Kottwitz.CharacterKernelReduction"
      ],
      "dependencies": [
        "Actual Kottwitz construction and functoriality, Lemma 11.5.1",
        "Abelianization G→G_ab, its finite-kernel map on fundamental groups and inertia coinvariants; Lemma 11.1.3 and Definition 2.6.15",
        "Owner task: Task 5912 (13897846-41bc-48ee-ac17-46b6ca3eebfe, lean.peer@1), published by Worker 3557 on 13 November 2026, is to construct the actual Kottwitz homomorphism (KP Proposition 11.1.1, Definition 11.3.2, Lemma 11.5.1) over every nonarchimedean local field, state this target over it with the Library's G(F)^0 and G(F)^1, and publish lean.proof@1 tasks for the statements. Worker 304 published the statement CharacterKernelStatement (artifact 65072446-cd08-452c-9014-68db65b2f4d7, first in Library commit 0c3f30c24701c74d5474fca3fbb5324a99aa1d58) together with the selected maps and ReductiveKottwitzExistenceStatement and ReductiveKottwitzDescentStatement (module ReductiveMapStatement, artifact c1bd5944-3a96-416a-b0c0-e535426f71c4, same commit). The proof task of CharacterKernelStatement is Task 6366 (6b141b60-f676-46c0-8920-be18d248eb6d), and those of the two map statements are Task 6363 (d6a79d52-b54d-4005-8fb3-92fef9976f3c) and Task 6365 (94352cf7-fa7c-4f47-94ae-f2cbc00cf7c3); Worker 304 published all of them as lean.proof@1 tasks on 13 November 2026. On that date none of these statements is proved. Reduction (twentieth pass, 14 November 2026): the theorem Kottwitz.CharacterKernelInputs.characterKernel (module Langlands.Geometry.Building.Kottwitz.CharacterKernelReduction; artifact 402f62af-ea4d-4dcd-892f-532aeb3106ab, whose entry declaration is CharacterKernelInputs, first in Library commit e5365902d74534dbf1622c06e695dffdc128d723) derives CharacterKernelStatement from CharacterKernelInputs, the conjunction of four statements, by KP's reduction to the cocenter. TorusCharacterKernelStatement (module Langlands.Geometry.Building.Kottwitz.TorusCharacterKernelStatement; artifact 9a8b06f1-bc3e-4a83-848b-ff88fa1bb6a7, first in the same commit) is KP Lemma 11.1.3 on rational points: for every torus T over F, the character-valuation kernel of T(F) is the preimage of torsion under the constructed torus map. CocenterTargetTorsionStatement (module Langlands.Geometry.Building.Kottwitz.CocenterTargetTorsionStatement; artifact 7746ef1f-ea33-412f-aef8-6f9f04433f2e, first in the same commit; proof task 7c6a58cb-99fa-4d73-a8e1-8a21fd85f703) says that the map induced by the actual cocenter quotient on inertia coinvariants has torsion kernel, a step of KP's proof. ReductiveKottwitzFunctorialityStatement (module ReductiveMapStatement; KP Lemma 11.5.1, functoriality and compatibility with the torus map; proof task 5313a8a6-9c87-4c7c-9201-df713d5fb4f7) and ReductiveKottwitzDescentStatement (Task 6365) are the other two. lean_check inspection d498f137-8659-4f33-a7b0-c20a63c53e54 is recorded below. On 14 November 2026 none of the four inputs is proved. The three modules cited in this paragraph are byte-identical between commit e5365902 and Library commit c40a0134."
      ],
      "consumer_or_regression": "The second and third quotient identifications of 11.7.6 and retention of the G(k)^0/G(k)^1 distinction in Hecke and stabilizer interfaces.",
      "formal_status": "statement",
      "owner_task": "13897846-41bc-48ee-ac17-46b6ca3eebfe",
      "acceptance_artifact_ids": [
        "65072446-cd08-452c-9014-68db65b2f4d7",
        "c1bd5944-3a96-416a-b0c0-e535426f71c4"
      ],
      "publication_commits": [
        "0c3f30c24701c74d5474fca3fbb5324a99aa1d58"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.CharacterKernelStatement",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "f2783f38-c6f0-4ded-98e1-72088f739300",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit 6948120d; kind definition; statement_returns_prop true; the module is byte-identical to commit 0c3f30c2."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.ReductiveKottwitzExistenceStatement",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "3372d93d-b800-4cd2-bf1f-3a811f0d1a53",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit 6948120d; kind definition; statement_returns_prop true; the module is byte-identical to commit 0c3f30c2."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.ReductiveKottwitzDescentStatement",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "7dc62cc5-d466-4905-9fa5-900602e2a17a",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit 6948120d; kind definition; statement_returns_prop true; the module is byte-identical to commit 0c3f30c2."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.CharacterKernelInputs.characterKernel",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "d498f137-8659-4f33-a7b0-c20a63c53e54",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-14 at Library commit c40a0134; kind theorem, at universe level u, whose type is the implication from CharacterKernelInputs to CharacterKernelStatement; the module is byte-identical to commit e5365902, which first published it."
        }
      ],
      "external_code": []
    },
    {
      "source_item": "Proposition 11.5.4",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.431 / PDF p.462; Chapter 11 ambient hypotheses at PDF p.451"
      },
      "erratum": null,
      "hypotheses": [
        "k has a normalized discrete valuation, Henselian valuation ring and perfect residue field f; G is connected reductive. In a fixed separable closure k_s let K be the maximal unramified extension, I=Gal(k_s/K) and Gamma=Gal(K/k). Put A=pi_1(G)_I. kappa_G:G(k)→A^Gamma is the restriction of the actual Kottwitz homomorphism constructed over K in 11.5.1.",
        "G(k)^0 is the subgroup of Definition 2.6.23. Neither finiteness of f nor dim(f)≤1 is assumed in this kernel identity.",
        "Recorded Lean scope: ZeroKernelStatement (module Langlands.Geometry.Building.Kottwitz.ZeroKernelStatement) quantifies over every nonarchimedean local field F, connected reductive G over Spec F and every ZeroSubgroupDatum d for a maximal split torus i : S → G and a representative j : Z → G of its centralizer, which carries data of Definition 2.6.23(1) for Z_K and a simply connected cover of the derived subgroup; d.zeroSubgroup is the Library's G(F)^0 = G(F)^♮ · Z(F)^0 of Definition 2.6.23(3). It asserts d.zeroSubgroup = ker κ_G, so it also says that G(F)^0 does not depend on the datum. K is the Library's maximal unramified extension UnramifiedClosure F inside the separable closure SeparableClosure F. ReductiveInvariantTarget F G hG is A^Γ for A = π_1(G)_I, the integral inertia coinvariants of the actual algebraic fundamental group, with the actual residual action of Γ = Gal(K/F); fundamentalInvariantTorsion is (A_tor)^Γ as a subgroup of A^Γ. κ_G is reductiveKottwitzRational F G hG (module Langlands.Geometry.Building.Kottwitz.ReductiveMap), selected by classical epsilon among the homomorphisms G(F) → A^Γ whose composite with A^Γ → A is the K-point map reductiveKottwitz on the image of G(F) in G(K). reductiveKottwitz is in turn selected by its squares with every z-extension, over the simply-connected-derived construction through every cocenter. That both selections have their characterizing properties is asserted by ReductiveKottwitzExistenceStatement (existence of z-extensions and unique existence, surjectivity and independence of the K-point map) and ReductiveKottwitzDescentStatement (residual Galois equivariance and unique existence of the restriction to G(F)), both in module Langlands.Geometry.Building.Kottwitz.ReductiveMapStatement; neither is proved. The source's Henselian discretely valued fields with perfect residue field are specialized to nonarchimedean local fields of either characteristic in universe u; their residue fields are finite."
      ],
      "conclusion": "G(k)^0=ker(kappa_G). The homomorphism is the actual Kottwitz map, not an arbitrary map postulated to have this kernel.",
      "lean_declarations": [
        "Langlands.Geometry.Building.Kottwitz.ZeroKernelStatement",
        "Langlands.Geometry.Building.Kottwitz.ReductiveKottwitzExistenceStatement",
        "Langlands.Geometry.Building.Kottwitz.ReductiveKottwitzDescentStatement",
        "Langlands.Geometry.Building.Kottwitz.zeroKernel_of_unramified"
      ],
      "modules": [
        "Langlands.Geometry.Building.Kottwitz.ZeroKernelStatement",
        "Langlands.Geometry.Building.Kottwitz.ReductiveMapStatement",
        "Langlands.Geometry.Building.Kottwitz.ZeroKernelReduction"
      ],
      "dependencies": [
        "Proposition 9.3.24, G(k)^0=G(K)^0 intersect G(k), reduces to k=K",
        "Quasi-splitness Corollary 2.3.8, torus kernel Proposition 11.1.5, induced-torus lifting Lemma 2.5.20 and z-extension surjectivity Proposition 11.5.3",
        "Owner task: Task 5912 (13897846-41bc-48ee-ac17-46b6ca3eebfe, lean.peer@1), published by Worker 3557 on 13 November 2026, is to construct the actual Kottwitz homomorphism (KP Proposition 11.1.1, Definition 11.3.2, Lemma 11.5.1) over every nonarchimedean local field, state this target over it with the Library's G(F)^0 and G(F)^1, and publish lean.proof@1 tasks for the statements. Worker 304 published the statement ZeroKernelStatement (artifact f286ecc6-8d4d-4b3c-b60b-6985b2940693, first in Library commit 0c3f30c24701c74d5474fca3fbb5324a99aa1d58) together with the selected maps and ReductiveKottwitzExistenceStatement and ReductiveKottwitzDescentStatement (module ReductiveMapStatement, artifact c1bd5944-3a96-416a-b0c0-e535426f71c4, same commit). The proof task of ZeroKernelStatement is Task 6367 (413a8493-8a98-4ae7-885c-bcadb6507b81), and those of the two map statements are Task 6363 (d6a79d52-b54d-4005-8fb3-92fef9976f3c) and Task 6365 (94352cf7-fa7c-4f47-94ae-f2cbc00cf7c3); Worker 304 published all of them as lean.proof@1 tasks on 13 November 2026. On that date none of these statements is proved. Reduction (twentieth pass, 14 November 2026): the theorem Kottwitz.zeroKernel_of_unramified (module Langlands.Geometry.Building.Kottwitz.ZeroKernelReduction; artifact 2c610303-5436-4e17-bbc9-d65f40e8f439, whose entry declaration is UnramifiedZeroKernelStatement, first in Library commit 4f6abf4c7e19610e4d89edc9bf64b34ba1db9ff2) derives ZeroKernelStatement from three statements, following KP's reduction to k = K by Proposition 9.3.24: ReductiveKottwitzDescentStatement (Task 6365); UnramifiedZeroDescentStatement (module Langlands.Geometry.Building.UnramifiedZeroDescentStatement; artifact 0c3121b7-3013-4456-92ec-643d001c78f2, first in Library commit 0c3f30c24701c74d5474fca3fbb5324a99aa1d58; KP Proposition 9.3.24 with the Galois stability of G(K)^1 and G(K)^0; proof task 36e777a5-694a-4123-be42-eaad69d89d73); and UnramifiedZeroKernelStatement (module ZeroKernelReduction), that for every unramified zero datum E of G_K the subgroup E.zeroPoints is the preimage of the kernel of the K-point map reductiveKottwitz. lean_check inspection 83056963-bc46-4139-a6a6-d95ca0a27651 is recorded below. On 14 November 2026 none of the three inputs is proved. The modules ZeroKernelReduction and UnramifiedZeroDescentStatement are byte-identical between their first commits and Library commit c40a0134."
      ],
      "consumer_or_regression": "Identify the component quotient in Theorem 7.8.1(1), while keeping surjectivity and the Section 11.7 residue hypothesis separate.",
      "formal_status": "statement",
      "owner_task": "13897846-41bc-48ee-ac17-46b6ca3eebfe",
      "acceptance_artifact_ids": [
        "f286ecc6-8d4d-4b3c-b60b-6985b2940693",
        "c1bd5944-3a96-416a-b0c0-e535426f71c4"
      ],
      "publication_commits": [
        "0c3f30c24701c74d5474fca3fbb5324a99aa1d58"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.ZeroKernelStatement",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "61d09f64-02bf-4938-bb4b-6cbe2b2045f5",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit 6948120d; kind definition; statement_returns_prop true; the module is byte-identical to commit 0c3f30c2."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.ReductiveKottwitzExistenceStatement",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "3372d93d-b800-4cd2-bf1f-3a811f0d1a53",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit 6948120d; kind definition; statement_returns_prop true; the module is byte-identical to commit 0c3f30c2."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.ReductiveKottwitzDescentStatement",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "7dc62cc5-d466-4905-9fa5-900602e2a17a",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit 6948120d; kind definition; statement_returns_prop true; the module is byte-identical to commit 0c3f30c2."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.zeroKernel_of_unramified",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "83056963-bc46-4139-a6a6-d95ca0a27651",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-14 at Library commit c40a0134; kind theorem, at universe level u, whose type is the implication from ReductiveKottwitzDescentStatement, UnramifiedZeroDescentStatement and UnramifiedZeroKernelStatement to ZeroKernelStatement; the module is byte-identical to commit 4f6abf4c, which first published it."
        }
      ],
      "external_code": []
    },
    {
      "source_item": "Corollary 11.7.5",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.433–434 / PDF pp.464–465"
      },
      "erratum": null,
      "hypotheses": [
        "k has a normalized discrete valuation, Henselian valuation ring and perfect residue field f; G is connected reductive. In a fixed separable closure k_s let K be the maximal unramified extension, I=Gal(k_s/K) and Gamma=Gal(K/k). Put A=pi_1(G)_I. kappa_G:G(k)→A^Gamma is the restriction of the actual Kottwitz homomorphism constructed over K in 11.5.1.",
        "In addition, dim(f)≤1 in the field-dimension sense of Section 11.7; this holds for finite residue fields. This is not a Krull-dimension condition.",
        "For the chamber quotient choose a Gamma-stable K-chamber C in B(G_K), as in the source proof. G(k)_C is its stabilizer and G(k)^0_C=G(k)_C intersect G(k)^0.",
        "Recorded Lean scope: ChamberStatement (module Langlands.Geometry.Building.Kottwitz.ChamberStatement) asserts, for every nonarchimedean local field F and connected reductive G over Spec F, that κ_G is surjective, together with a chamber clause on supplied building data. For a commutative group scheme T with iT : T → G whose scalar extension to K is a maximal split torus of G_K, a class D : KPApartmentData of valuations of the root datum of (G_K, T_K) with centralizer datum C satisfying V 6 (IntegerValuation.IsOmegaCompatible) and Galois stability (KPApartmentData.GaloisStable), let B be the building data UnramifiedBuildingDescent.buildingData built from them. For every chamber C' of B that the coefficient Galois action of UnramifiedBuildingDescent.semilinearData maps onto itself and for every ZeroSubgroupDatum d of G, whose d.zeroSubgroup is the Library's G(F)^0 (see the Proposition 11.5.4 row), let P be the preimage in G(F) of the stabilizer of C' in G(K) and N = G(F)^0 ∩ P. Then N is normal in P and some isomorphism P/N ≃ A^Γ sends the class of x to κ_G(x). Surjectivity is unconditional; the chamber clause concerns the supplied building data, and the existence of a Γ-stable chamber (Proposition 9.10.4) is not asserted. K is the Library's maximal unramified extension UnramifiedClosure F inside the separable closure SeparableClosure F. ReductiveInvariantTarget F G hG is A^Γ for A = π_1(G)_I, the integral inertia coinvariants of the actual algebraic fundamental group, with the actual residual action of Γ = Gal(K/F); fundamentalInvariantTorsion is (A_tor)^Γ as a subgroup of A^Γ. κ_G is reductiveKottwitzRational F G hG (module Langlands.Geometry.Building.Kottwitz.ReductiveMap), selected by classical epsilon among the homomorphisms G(F) → A^Γ whose composite with A^Γ → A is the K-point map reductiveKottwitz on the image of G(F) in G(K). reductiveKottwitz is in turn selected by its squares with every z-extension, over the simply-connected-derived construction through every cocenter. That both selections have their characterizing properties is asserted by ReductiveKottwitzExistenceStatement (existence of z-extensions and unique existence, surjectivity and independence of the K-point map) and ReductiveKottwitzDescentStatement (residual Galois equivariance and unique existence of the restriction to G(F)), both in module Langlands.Geometry.Building.Kottwitz.ReductiveMapStatement; neither is proved. The source's Henselian discretely valued fields with perfect residue field are specialized to nonarchimedean local fields of either characteristic in universe u; their residue fields are finite."
      ],
      "conclusion": "kappa_G:G(k)→A^Gamma is surjective and induces an isomorphism G(k)_C/G(k)^0_C≃A^Gamma. The chosen chamber is over K; do not silently replace it by an arbitrary k-chamber.",
      "lean_declarations": [
        "Langlands.Geometry.Building.Kottwitz.ChamberStatement",
        "Langlands.Geometry.Building.Kottwitz.ReductiveKottwitzExistenceStatement",
        "Langlands.Geometry.Building.Kottwitz.ReductiveKottwitzDescentStatement",
        "Langlands.Geometry.Building.Kottwitz.chamberStatement_of_remainingInputs",
        "Langlands.GroupScheme.IntegralModel.unramifiedSmoothModelDescent"
      ],
      "modules": [
        "Langlands.Geometry.Building.Kottwitz.ChamberStatement",
        "Langlands.Geometry.Building.Kottwitz.ReductiveMapStatement",
        "Langlands.Geometry.Building.Kottwitz.RationalSurjectivityReduction",
        "Langlands.GroupScheme.IntegralModel.UnramifiedSmoothDescentProof"
      ],
      "dependencies": [
        "Existence of a Gamma-stable K-chamber, Proposition 9.10.4",
        "Proposition 11.6.1 exact sequence over K, Theorem 8.3.13 smooth connected-fibre chamber model, and Lemma 8.1.4 cohomology vanishing",
        "Owner task: Task 5912 (13897846-41bc-48ee-ac17-46b6ca3eebfe, lean.peer@1), published by Worker 3557 on 13 November 2026, is to construct the actual Kottwitz homomorphism (KP Proposition 11.1.1, Definition 11.3.2, Lemma 11.5.1) over every nonarchimedean local field, state this target over it with the Library's G(F)^0 and G(F)^1, and publish lean.proof@1 tasks for the statements. Worker 304 published the statement ChamberStatement (artifact b737aa32-a0d4-44e6-ad28-5cf5508ef26f, first in Library commit 0c3f30c24701c74d5474fca3fbb5324a99aa1d58) together with the selected maps and ReductiveKottwitzExistenceStatement and ReductiveKottwitzDescentStatement (module ReductiveMapStatement, artifact c1bd5944-3a96-416a-b0c0-e535426f71c4, same commit). The proof task of ChamberStatement is Task 6368 (b1c19c85-1bc5-482b-9d1d-244a35669005), and those of the two map statements are Task 6363 (d6a79d52-b54d-4005-8fb3-92fef9976f3c) and Task 6365 (94352cf7-fa7c-4f47-94ae-f2cbc00cf7c3); Worker 304 published all of them as lean.proof@1 tasks on 13 November 2026. On that date none of these statements is proved. Reduction (twentieth pass, 14 November 2026): the theorem Kottwitz.chamberStatement_of_remainingInputs (module Langlands.Geometry.Building.Kottwitz.RationalSurjectivityReduction; artifact 63f747e2-59ac-472b-9d66-3be2f5187ec3, first in Library commit 4f6abf4c7e19610e4d89edc9bf64b34ba1db9ff2) derives ChamberStatement from seven statements: SpecialTorusExistenceStatement (Proposition 9.3.4 row); UnramifiedTwistedChamberStatement (module Langlands.Geometry.Building.UnramifiedTwistedChamberStatement, first in Library commit 51e4d8972659f1ffcf0ca89e8eee9540a30b52d3; a chamber of the building over K stable under the Galois action twisted by a finite-level cocycle, with Proposition 9.10.4 as source; proof task 96398564-dd51-47e0-9b1e-352597059800); UnramifiedParahoricModelStatement (module Langlands.BruhatTits.IntegralModels.UnramifiedParahoricModelStatement; artifact 41339d18-6b2c-4c79-a9e1-9ef821fe6038, first in Library commit cc5aa77fa8dbdc6e723091c7b710ab0d81162c4e; KP Theorems 8.3.2 and 8.3.13 over the integers of K; proof task 85c28d88-edea-4dd0-99a5-2610566438c0); IntegralModel.UnramifiedSmoothModelDescentStatement (module Langlands.GroupScheme.IntegralModel.UnramifiedSmoothDescent; artifact 1c33bc01-61d4-4520-bf93-0f4e82c8a3d8, first in the same commit; KP Fact 2.10.16); UnramifiedChamberExactSequenceStatement (module Langlands.Geometry.Building.Kottwitz.UnramifiedChamberExactSequenceStatement, first in Library commit 4f6abf4c7e19610e4d89edc9bf64b34ba1db9ff2; KP Proposition 11.6.1 on supplied K-building data; proof task 8f161b8a-f32a-4002-a39a-f8716f971522); ReductiveKottwitzDescentStatement (Task 6365); and ZeroKernelStatement (Proposition 11.5.4 row, Task 6367). It applies chamberStatement_of_surjective_of_geometricInputs (module Langlands.Geometry.Building.Kottwitz.RationalChamberQuotientReduction; artifact 514efd6c-0500-4686-81e5-b06542febe36, first in the same commit), which takes the surjectivity of κ_G as a further input, to the surjectivity given by the published rationalSurjectivityReduction. One input is proved: the theorem IntegralModel.unramifiedSmoothModelDescent (module Langlands.GroupScheme.IntegralModel.UnramifiedSmoothDescentProof; proof task 196f423d-3c64-4e2b-99a6-49768111ae8c; artifact 345a325a-2658-4ce3-b160-0091cf0d56ac, first in Library commit e5365902d74534dbf1622c06e695dffdc128d723) proves UnramifiedSmoothModelDescentStatement. lean_check inspections bf6dd761-8924-46f7-b5b8-3a188ec25440 and c16a1777-283a-4bfa-8f73-d3d96cc89621 of the two theorems are recorded below. On 14 November 2026 the other six inputs are unproved. Each module cited in this paragraph is byte-identical between its first commit and Library commit c40a0134."
      ],
      "consumer_or_regression": "Length-zero/component representatives for the Iwahori–Weyl and Hecke interfaces over local fields.",
      "formal_status": "statement",
      "owner_task": "13897846-41bc-48ee-ac17-46b6ca3eebfe",
      "acceptance_artifact_ids": [
        "b737aa32-a0d4-44e6-ad28-5cf5508ef26f",
        "c1bd5944-3a96-416a-b0c0-e535426f71c4"
      ],
      "publication_commits": [
        "0c3f30c24701c74d5474fca3fbb5324a99aa1d58"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.ChamberStatement",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "c8d82a07-855c-4549-b768-5ccdcca33b0b",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit 6948120d; kind definition; statement_returns_prop true; the module is byte-identical to commit 0c3f30c2."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.ReductiveKottwitzExistenceStatement",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "3372d93d-b800-4cd2-bf1f-3a811f0d1a53",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit 6948120d; kind definition; statement_returns_prop true; the module is byte-identical to commit 0c3f30c2."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.ReductiveKottwitzDescentStatement",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "7dc62cc5-d466-4905-9fa5-900602e2a17a",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit 6948120d; kind definition; statement_returns_prop true; the module is byte-identical to commit 0c3f30c2."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.chamberStatement_of_remainingInputs",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "bf6dd761-8924-46f7-b5b8-3a188ec25440",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-14 at Library commit c40a0134; kind theorem, at universe level u, whose type is the implication from the seven statements named in the dependencies to ChamberStatement; the module is byte-identical to commit 4f6abf4c, which first published it."
        },
        {
          "declaration": "Langlands.GroupScheme.IntegralModel.unramifiedSmoothModelDescent",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "c16a1777-283a-4bfa-8f73-d3d96cc89621",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-14 at Library commit c40a0134; kind theorem, at universe level u, whose type is exactly IntegralModel.UnramifiedSmoothModelDescentStatement.{u}; the module is byte-identical to commit e5365902, which first published it."
        }
      ],
      "external_code": []
    },
    {
      "source_item": "Corollary 11.7.6",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.434 / PDF p.465"
      },
      "erratum": null,
      "hypotheses": [
        "k has a normalized discrete valuation, Henselian valuation ring and perfect residue field f; G is connected reductive. In a fixed separable closure k_s let K be the maximal unramified extension, I=Gal(k_s/K) and Gamma=Gal(K/k). Put A=pi_1(G)_I. kappa_G:G(k)→A^Gamma is the restriction of the actual Kottwitz homomorphism constructed over K in 11.5.1.",
        "In addition, dim(f)≤1 in the field-dimension sense of Section 11.7; this holds for finite residue fields. This is not a Krull-dimension condition.",
        "A_tor is the torsion subgroup of A=pi_1(G)_I. Form invariants before the torsion-free quotient in the third identification.",
        "Recorded Lean scope: QuotientStatement (module Langlands.Geometry.Building.Kottwitz.QuotientStatement) quantifies over every nonarchimedean local field F, connected reductive G over Spec F and every ZeroSubgroupDatum d for a maximal split torus i : S → G and a representative j : Z → G of its centralizer, which carries data of Definition 2.6.23(1) for Z_K and a simply connected cover of the derived subgroup; d.zeroSubgroup is the Library's G(F)^0 = G(F)^♮ · Z(F)^0 of Definition 2.6.23(3). With N = d.zeroSubgroup and H = characterValuationKernel (ValuativeRel.valuation F) G, the Library's G(F)^1, it asserts that N is normal, N ≤ H, and that there are isomorphisms G(F)/N ≃ A^Γ, H/N ≃ (A_tor)^Γ and G(F)/H ≃ A^Γ/(A_tor)^Γ, each sending the class of g to κ_G(g) or its image. The third quotient is formed as A^Γ/(A_tor)^Γ. K is the Library's maximal unramified extension UnramifiedClosure F inside the separable closure SeparableClosure F. ReductiveInvariantTarget F G hG is A^Γ for A = π_1(G)_I, the integral inertia coinvariants of the actual algebraic fundamental group, with the actual residual action of Γ = Gal(K/F); fundamentalInvariantTorsion is (A_tor)^Γ as a subgroup of A^Γ. κ_G is reductiveKottwitzRational F G hG (module Langlands.Geometry.Building.Kottwitz.ReductiveMap), selected by classical epsilon among the homomorphisms G(F) → A^Γ whose composite with A^Γ → A is the K-point map reductiveKottwitz on the image of G(F) in G(K). reductiveKottwitz is in turn selected by its squares with every z-extension, over the simply-connected-derived construction through every cocenter. That both selections have their characterizing properties is asserted by ReductiveKottwitzExistenceStatement (existence of z-extensions and unique existence, surjectivity and independence of the K-point map) and ReductiveKottwitzDescentStatement (residual Galois equivariance and unique existence of the restriction to G(F)), both in module Langlands.Geometry.Building.Kottwitz.ReductiveMapStatement; neither is proved. The source's Henselian discretely valued fields with perfect residue field are specialized to nonarchimedean local fields of either characteristic in universe u; their residue fields are finite."
      ],
      "conclusion": "Kottwitz induces G(k)/G(k)^0≃A^Gamma, G(k)^1/G(k)^0≃(A_tor)^Gamma, and G(k)/G(k)^1≃A^Gamma/(A_tor)^Gamma=(A^Gamma)_free. The explicit third quotient unpacks the source notation using torsion(A^Gamma)=(A_tor)^Gamma; no identification with (A/A_tor)^Gamma is asserted.",
      "lean_declarations": [
        "Langlands.Geometry.Building.Kottwitz.QuotientStatement",
        "Langlands.Geometry.Building.Kottwitz.ReductiveKottwitzExistenceStatement",
        "Langlands.Geometry.Building.Kottwitz.ReductiveKottwitzDescentStatement"
      ],
      "modules": [
        "Langlands.Geometry.Building.Kottwitz.QuotientStatement",
        "Langlands.Geometry.Building.Kottwitz.ReductiveMapStatement"
      ],
      "dependencies": [
        "Lemma 11.5.2, Proposition 11.5.4 and Corollary 11.7.5",
        "First isomorphism theorem and the elementary fact that the torsion subgroup of an invariant subgroup is the invariant torsion subgroup",
        "Owner task: Task 5912 (13897846-41bc-48ee-ac17-46b6ca3eebfe, lean.peer@1), published by Worker 3557 on 13 November 2026, is to construct the actual Kottwitz homomorphism (KP Proposition 11.1.1, Definition 11.3.2, Lemma 11.5.1) over every nonarchimedean local field, state this target over it with the Library's G(F)^0 and G(F)^1, and publish lean.proof@1 tasks for the statements. Worker 304 published the statement QuotientStatement (artifact 78329540-30cf-4d88-8f4e-5d0d839c26a0, first in Library commit 0c3f30c24701c74d5474fca3fbb5324a99aa1d58) together with the selected maps and ReductiveKottwitzExistenceStatement and ReductiveKottwitzDescentStatement (module ReductiveMapStatement, artifact c1bd5944-3a96-416a-b0c0-e535426f71c4, same commit). The proof task of QuotientStatement is Task 6376 (03aeec1f-4da2-46a9-956e-13e7841bf977), and those of the two map statements are Task 6363 (d6a79d52-b54d-4005-8fb3-92fef9976f3c) and Task 6365 (94352cf7-fa7c-4f47-94ae-f2cbc00cf7c3); Worker 304 published all of them as lean.proof@1 tasks on 13 November 2026. On that date none of these statements is proved."
      ],
      "consumer_or_regression": "Combine with Theorem 7.8.1(1) and its chamber-dependent splitting without discarding invariant torsion or length-zero representatives.",
      "formal_status": "statement",
      "owner_task": "13897846-41bc-48ee-ac17-46b6ca3eebfe",
      "acceptance_artifact_ids": [
        "78329540-30cf-4d88-8f4e-5d0d839c26a0",
        "c1bd5944-3a96-416a-b0c0-e535426f71c4"
      ],
      "publication_commits": [
        "0c3f30c24701c74d5474fca3fbb5324a99aa1d58"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.QuotientStatement",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "f1d2c990-0aa3-49d1-b5bd-45777e3d4274",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit 6948120d; kind definition; statement_returns_prop true; the module is byte-identical to commit 0c3f30c2."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.ReductiveKottwitzExistenceStatement",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "3372d93d-b800-4cd2-bf1f-3a811f0d1a53",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit 6948120d; kind definition; statement_returns_prop true; the module is byte-identical to commit 0c3f30c2."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.ReductiveKottwitzDescentStatement",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "7dc62cc5-d466-4905-9fa5-900602e2a17a",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit 6948120d; kind definition; statement_returns_prop true; the module is byte-identical to commit 0c3f30c2."
        }
      ],
      "external_code": []
    },
    {
      "source_item": "Theorem 8.3.2",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.296 / PDF p.327; schematic models in Sections 2.8 and 2.10"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.37, Chapter 8 opening, Section 8.3 and Remark 8.3.4",
        "change": "Replace the opening of Section 8.3 by the perfect-residue hypothesis. Change 'first three sections' to 'first two sections'. In Remark 8.3.4 the full-fixer model is evaluated on O, not K."
      },
      "hypotheses": [
        "k has a normalized discrete valuation, Henselian integer ring o and perfect residue field f; G is connected reductive over k. K is a maximal unramified extension, O its integer ring, fbar its algebraically closed residue field, and Gamma=Gal(K/k)=Gal(fbar/f). Perfect residue is the corrected hypothesis of Section 8.3 and subsequent sections, not merely quasi-splitness of G_K.",
        "S is a maximal K-split torus, T=Z_{G_K}(S), and Omega is a nonempty bounded subset of its apartment in the actual building B(G_K). The models in Chapter 8 are over O; their descent over o is a separate construction.",
        "Recorded Lean scope (the G(K)^1_Omega model only): UnramifiedParahoricModelStatement (module Langlands.BruhatTits.IntegralModels.UnramifiedParahoricModelStatement, artifact 41339d18-6b2c-4c79-a9e1-9ef821fe6038, first published in Library commit cc5aa77fa8dbdc6e723091c7b710ab0d81162c4e) quantifies over every nonarchimedean local field F in universe u and every affine group scheme G over F. It takes K = inertiaFixedField F, the maximal unramified extension, with integer ring O = fixedFieldIntegers F; supplied building data C : MaximalUnramified.BuildingData F G_K for the normalized valuation of K, which record that G_K is connected reductive; a datum E : UnramifiedZeroDatum computing G(K)^0; a point g of G(K); and a nonempty bounded subset Omega_a of the apartment of C. It asserts that some D : RelativeComponentModelData O K G_K has D.full.integralPoints = G(K)^1 ⊓ C.pointwiseFixer (g·Omega_a) and D.neutral.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (g·Omega_a). Here G(K)^1 is characterValuationKernel, the common kernel of the valuations of all rational characters of G_K, and E.zeroPoints is G(K)^0 of KP Definition 2.6.23(1) (module Langlands.Geometry.Building.KPZeroSubgroups). D.full is a smooth affine flat O-model of finite type with generic fibre G_K, and D.neutral is a smooth connected-fibre relative identity component of it; the neutral clause is recorded in the Theorem 8.3.13 row. The statement differs from the source in three ways: G(K)^dagger_Omega and its model are absent, so the common relative identity component of the two models is not stated; k is a nonarchimedean local field rather than a Henselian discretely valued field with perfect residue field; and C is supplied rather than the constructed building of G_K. Secondary, descended form: IntegralModelAxiomsStatement (module Langlands.Geometry.Building.IntegralModelAxiomsStatement; Axioms 4.1.20 and 4.1.22; proof Task 5429, cd2ad671-3edf-4905-a0e2-e7aa2b160b91) asserts, for every nonarchimedean local field F, affine group scheme G over F and supplied P : ParahoricBuildingData G with a polysimplicial realization and an apartment splitting satisfying the seven Section 4.2 building predicates, that some model family M over 𝒪[F], quotient family and relative root reflection data satisfy M.SatisfiesModelAxioms P and the morphism axioms. Its index sets are the nonempty bounded subsets of translated apartments and the facets of the supplied building, so it is the Section 9.2.5 descended form over 𝒪[F], on supplied data. It is present in Library commit ed924aef420de137b4cbaa3b063a3618afcd73fd; its acceptance artifact cannot be identified in this instance. Its clause full_points (BuildingModelFamily.ModelAxiomClauses) gives the full model of every index Omega the integral points oneFixer Omega, the pointwise fixer of Omega in G(F)^1. The status statement of this row covers only this part."
      ],
      "conclusion": "G(K)^1_Omega and G(K)^dagger_Omega are schematic: they are the O-points of actual smooth affine O-group schemes with generic fibre G_K. Their models have the same relative identity component. This does not assert connectedness of the entire models or identify either subgroup with the full fixer.",
      "lean_declarations": [
        "Langlands.BruhatTits.IntegralModels.UnramifiedParahoricModelStatement",
        "Langlands.BruhatTits.IntegralModels.exists_smoothFullModel_of_vertexInputs",
        "Langlands.BruhatTits.IntegralModels.exists_relativeComponentModelData_of_vertexInputs",
        "Langlands.Geometry.Building.IntegralModelAxiomsStatement",
        "Langlands.Geometry.Building.MaximalUnramified.finiteVertexFixerApproximation",
        "Langlands.GroupScheme.IntegralModel.finiteIndexEnlargement"
      ],
      "modules": [
        "Langlands.BruhatTits.IntegralModels.UnramifiedParahoricModelStatement",
        "Langlands.BruhatTits.IntegralModels.UnramifiedFullModelConstruction",
        "Langlands.Geometry.Building.IntegralModelAxiomsStatement",
        "Langlands.Geometry.Building.UnramifiedFiniteVertexFixerAssembly",
        "Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargementProof"
      ],
      "dependencies": [
        "Proposition 8.3.1: faithful representations, stable lattices, schematic closure and smoothening (A.6.5–A.6.6) construct vertex models",
        "Enlarge Omega to the facets meeting it; Proposition 7.7.1 gives the finite-index inclusions, and A.7.1 propagates schematicity and identifies relative identity components",
        "For nonempty bounded Gamma-stable subsets, Section 9.2.5 constructs the descended smooth affine o-models using invariant coordinate rings and relative identity components; 9.2.6 identifies the parahoric o-points. Chapter 8 models alone do not give this descent.",
        "Recorded Lean route (the G(K)^1_Omega model only): exists_smoothFullModel_of_vertexInputs and exists_relativeComponentModelData_of_vertexInputs (module Langlands.BruhatTits.IntegralModels.UnramifiedFullModelConstruction, artifact 63d25099-b07d-4806-8ec0-e5b2587c6bf5, a supporting unit of proof Task 5976, first published in Library commit 7f43c3c930ff92f76dae6589da1678ad729017e5) are proved from five statements: Langlands.Geometry.Building.MaximalUnramified.VertexOneStabilizerMaximalBoundedStatement and Langlands.Geometry.Building.MaximalUnramified.FiniteVertexFixerApproximationStatement (module Langlands.Geometry.Building.UnramifiedVertexFixerStatements), Langlands.GroupScheme.MaximalBoundedIntegralModelStatement (module Langlands.GroupScheme.IntegralModel.MaximalBounded), Langlands.GroupScheme.IntegralModel.SmoothIntersectionStatement (module Langlands.GroupScheme.IntegralModel.SmoothIntersection) and Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargementStatement (module Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargement). For every affine group scheme G over K with supplied C : MaximalUnramified.BuildingData F G, every g in G(K) and every nonempty bounded Omega_a, the first gives a smooth O-model with integral points G(K)^1 ⊓ C.pointwiseFixer (g·Omega_a), and the second packages it with its relative identity component. The proof chooses finitely many vertices, takes smooth models of their one-stabilizers, intersects them and enlarges the intersection by finite index to the full fixer. It does not compare the neutral integral points with G(K)^0_Omega, so it does not prove UnramifiedParahoricModelStatement. Two of the five inputs are proved. Langlands.Geometry.Building.MaximalUnramified.finiteVertexFixerApproximation (module Langlands.Geometry.Building.UnramifiedFiniteVertexFixerAssembly, artifact e92ec689-8a24-4193-85a4-cdd1533c0817) proves FiniteVertexFixerApproximationStatement: for supplied C, g and nonempty bounded Omega_a, some nonempty finite set of vertices has the intersection of their one-stabilizers contained, normally and with finite index, in G(K)^1 ⊓ C.pointwiseFixer (g·Omega_a). Langlands.GroupScheme.IntegralModel.finiteIndexEnlargement (module Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargementProof, artifact 6722356c-5ad2-43dd-bb70-d007825bd50d) proves FiniteIndexEnlargementStatement, the finite-index part of KP Proposition A.7.1: over any Henselian discrete valuation ring with algebraically closed residue field, a smooth model M of a smooth affine group over the fraction field and a subgroup V of its rational points containing M.integralPoints as a normal subgroup of finite index give a smooth model with integral points V and an open immersion of M into it, extending the identity of the generic group and preserving relative identity components. Both were first published in Library commit 410c79471b79f65a02fb0f6070da7f2800793ff3. VertexOneStabilizerMaximalBoundedStatement, MaximalBoundedIntegralModelStatement and SmoothIntersectionStatement remain unproved, so the route stays conditional.",
        "Open obligations: UnramifiedParahoricModelStatement has proof Task 5976 (85c28d88-edea-4dd0-99a5-2610566438c0); three of the five inputs of the recorded route (VertexOneStabilizerMaximalBoundedStatement, MaximalBoundedIntegralModelStatement and SmoothIntersectionStatement) are unproved; IntegralModelAxiomsStatement has proof Task 5429; the dagger model and the common relative identity component have no Lean statement."
      ],
      "consumer_or_regression": "Actual integral-model input for the connected model, its reduction and compact/open integral points. The generally nonaffine full-fixer model of Remark 8.3.4 remains a different object.",
      "formal_status": "statement",
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [
        "41339d18-6b2c-4c79-a9e1-9ef821fe6038",
        "63d25099-b07d-4806-8ec0-e5b2587c6bf5",
        "e92ec689-8a24-4193-85a4-cdd1533c0817",
        "6722356c-5ad2-43dd-bb70-d007825bd50d"
      ],
      "publication_commits": [
        "cc5aa77fa8dbdc6e723091c7b710ab0d81162c4e",
        "7f43c3c930ff92f76dae6589da1678ad729017e5",
        "ed924aef420de137b4cbaa3b063a3618afcd73fd",
        "410c79471b79f65a02fb0f6070da7f2800793ff3"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.UnramifiedParahoricModelStatement",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "bafa87b4-93ae-464b-878e-aebe8a564767",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-13 at Library commit 451cce4c; kind definition; statement_returns_prop true; the module is byte-identical to commit cc5aa77f, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.exists_smoothFullModel_of_vertexInputs",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "f2a68e9e-b2fe-47d9-bf18-4f7722876533",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-13 at Library commit aae8cb82; kind theorem; the module is byte-identical to commit 7f43c3c9, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.exists_relativeComponentModelData_of_vertexInputs",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "fc09ed0b-b278-490f-89f7-62cf3ef63705",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-13 at Library commit 451cce4c; kind theorem; the module is byte-identical to commit 7f43c3c9, its first publication."
        },
        {
          "declaration": "Langlands.Geometry.Building.IntegralModelAxiomsStatement",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "ce6ea460-76bf-4c15-ac37-ee6c05951dc6",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-13 at Library commit eded01f2; kind definition; statement_returns_prop true; the module is byte-identical to commit ed924aef. Its acceptance artifact cannot be identified in this instance."
        },
        {
          "declaration": "Langlands.Geometry.Building.MaximalUnramified.finiteVertexFixerApproximation",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "0959a222-c9e8-4397-98bc-b6067449a588",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-14 at Library commit 20f83141; kind theorem; the module is byte-identical to commit 410c7947, its first publication."
        },
        {
          "declaration": "Langlands.GroupScheme.IntegralModel.finiteIndexEnlargement",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "bfc3cd3a-54f9-43d5-80b1-ca77132a3561",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-14 at Library commit 20f83141; kind theorem; the module is byte-identical to commit 410c7947, its first publication."
        }
      ],
      "external_code": [
        {
          "local_module": "Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargement.SubHopf",
          "local_files": [
            "Langlands/GroupScheme/IntegralModel/FiniteIndexEnlargement/SubHopf.lean",
            "Langlands/GroupScheme/IntegralModel/FiniteIndexEnlargement/SubHopf.md"
          ],
          "used_by": "Langlands.GroupScheme.IntegralModel.finiteIndexEnlargement",
          "acceptance_artifact_id": "6722356c-5ad2-43dd-bb70-d007825bd50d",
          "publication_commit": "410c79471b79f65a02fb0f6070da7f2800793ff3",
          "project": "Anthropic FLT (Fermat's Last Theorem in Lean 4), Copyright 2026 Anthropic, PBC",
          "upstream_file": "P2M/Sol/S_HopfAlgebra_faithfullyFlat_subalgebra_of_isReduced_of_fg_of_isAlgClosed.lean, section TakK",
          "upstream_commit": "6e837e75355538c7f80bab5b956861e86c4eacc2",
          "library_port_of_upstream_file": "Langlands.AnthropicFLT.P2M.Sol.S_HopfAlgebra_faithfullyFlat_subalgebra_of_isReduced_of_fg_of_isAlgClosed",
          "licence": "Apache License 2.0",
          "licence_files": [
            "licenses/Anthropic-FLT/LICENSE",
            "licenses/Anthropic-FLT/NOTICE",
            "licenses/Anthropic-FLT/ATTRIBUTION.md"
          ],
          "adaptation": "Adapted by Worker 33 from the TakK section of the upstream file, which works over a field. The local module replaces the field by a commutative ring R with A and B flat over R, states the comultiplication hypothesis as membership in the range of the tensor-square inclusion, uses the current tensor-product induction principle and adds the bialgebra inclusion valBialgHom. Its Lean header carries the Anthropic copyright, Apache 2.0 and licenses/Anthropic-FLT references; its paired Markdown lists the changes and asserts no mathematical statement from an external source.",
          "use": "Implemented dependency of the proof: FiniteIndexEnlargementProof calls FiniteIndexEnlargement.Core.exists_hopf_enlargement, whose Hopf algebra of coordinates integral on V is SubHopf.hopfAlgebra (Enlarged.lean) and whose inclusion into the original coordinate Hopf algebra is SubHopf.valBialgHom (Core.lean).",
          "scope": "This is reuse through the already accepted and published artifact 6722356c-5ad2-43dd-bb70-d007825bd50d, not the adoption of a new external dependency by this ledger. SubHopf.lean and SubHopf.md are byte-identical at Library commits 410c7947 and 179f569b. The entry records the adapted code among the modules that this artifact adds; it is not a declaration-level audit of the transitive import closure, whose other modules, including earlier Library ports from Anthropic FLT and other projects with licence files under licenses/, are not enumerated here."
        }
      ]
    },
    {
      "source_item": "Theorem 8.3.13",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.299 / PDF p.330; corrected proof at corrections PDF p.37"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.37, Section 8.3 and Theorem 8.3.13",
        "change": "Apply perfect residue and replace the proof's final two sentences. Connected fibres first force factorization through G^0_Omega; only then apply the open finite-index argument and A.4.26."
      },
      "hypotheses": [
        "k has a normalized discrete valuation, Henselian integer ring o and perfect residue field f; G is connected reductive over k. K is a maximal unramified extension, O its integer ring, fbar its algebraically closed residue field, and Gamma=Gal(K/k)=Gal(fbar/f). Perfect residue is the corrected hypothesis of Section 8.3 and subsequent sections, not merely quasi-splitness of G_K.",
        "S is a maximal K-split torus, T=Z_{G_K}(S), and Omega is a nonempty bounded subset of its apartment in the actual building B(G_K). The models in Chapter 8 are over O; their descent over o is a separate construction.",
        "Recorded Lean scope (without the dagger model): UnramifiedParahoricModelStatement (module, artifact and setting as in the Theorem 8.3.2 row) asserts, for the same D, D.neutral.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (g·Omega_a), that is G(K)^0_Omega. The fields neutral_smooth, neutral_connectedFibres, inclusion and isRelativeComponent of RelativeComponentModelData make D.neutral a smooth affine O-model with connected fibres and generic fibre G_K that is the relative identity component of D.full. This is the conclusion of the theorem with three differences: D.neutral is stated to be the relative identity component of the G(K)^1_Omega model only, since the dagger model is absent; k is a nonarchimedean local field; and the building data C are supplied. The last sentence of the conclusion is a non-claim. Secondary, descended form: the clauses neutral_points (the neutral model of every index Omega has integral points zeroFixer P Omega, the pointwise fixer of Omega in P.zeroSubgroup) and facet_constancy (Axiom 4.1.20(1): a nonempty subset of a facet has a neutral model isomorphic to that of the facet) of IntegralModelAxiomsStatement, described in the Theorem 8.3.2 row. The status statement of this row covers only this part."
      ],
      "conclusion": "The common relative identity component G^0_Omega of the schematic models in 8.3.2 has G^0_Omega(O)=G(K)^0_Omega. It is the actual smooth affine connected-fibre parahoric model with generic fibre G_K. Its connectedness does not identify the parahoric with a full pointwise or setwise fixer.",
      "lean_declarations": [
        "Langlands.BruhatTits.IntegralModels.UnramifiedParahoricModelStatement",
        "Langlands.BruhatTits.IntegralModels.RelativeComponentModelData",
        "Langlands.Geometry.Building.IntegralModelAxiomsStatement"
      ],
      "modules": [
        "Langlands.BruhatTits.IntegralModels.UnramifiedParahoricModelStatement",
        "Langlands.BruhatTits.IntegralModels.RelativeComponent",
        "Langlands.Geometry.Building.IntegralModelAxiomsStatement"
      ],
      "dependencies": [
        "Theorem 8.3.2; T is a maximal torus since G_K is quasi-split by 2.3.8. The connected Neron model has T^0(O)=T(K)^0 by B.8.7",
        "Sections 8.3.7–8.3.12 construct root models with prescribed integral points and connected fibres. Sections 2.10.10 and 2.10.19 extend the genuine generic-fibre inclusions",
        "Corrected connected-fibre argument: torus and root model maps factor through G^0_Omega; hence the generated G(K)^0_Omega lies in G^0_Omega(O). Proposition 7.7.1 gives openness and finite index there, and Lemma A.4.26 proves equality",
        "Proposition 8.3.14 gives the actual root-product open immersion",
        "For nonempty bounded Gamma-stable subsets, Section 9.2.5 constructs the descended smooth affine o-models using invariant coordinate rings and relative identity components; 9.2.6 identifies the parahoric o-points. Chapter 8 models alone do not give this descent.",
        "Open obligations: UnramifiedParahoricModelStatement has proof Task 5976 (85c28d88-edea-4dd0-99a5-2610566438c0). The conditional full-model construction recorded in the Theorem 8.3.2 row does not compare the neutral integral points with G(K)^0_Omega. IntegralModelAxiomsStatement has proof Task 5429."
      ],
      "consumer_or_regression": "Connected parahoric construction for reduction, inflation and compact induction. Proving compactness and openness further uses the actual scheme-point topology from its owning task.",
      "formal_status": "statement",
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [
        "41339d18-6b2c-4c79-a9e1-9ef821fe6038"
      ],
      "publication_commits": [
        "cc5aa77fa8dbdc6e723091c7b710ab0d81162c4e",
        "ed924aef420de137b4cbaa3b063a3618afcd73fd"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.UnramifiedParahoricModelStatement",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "bafa87b4-93ae-464b-878e-aebe8a564767",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-13 at Library commit 451cce4c; kind definition; statement_returns_prop true; the module is byte-identical to commit cc5aa77f, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.RelativeComponentModelData",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "6f94931d-9288-4a71-b51e-fad018824c93",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-13 at Library commit eded01f2; kind inductive; the module is byte-identical to commit ed924aef."
        },
        {
          "declaration": "Langlands.Geometry.Building.IntegralModelAxiomsStatement",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "ce6ea460-76bf-4c15-ac37-ee6c05951dc6",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-13 at Library commit eded01f2; kind definition; statement_returns_prop true; the module is byte-identical to commit ed924aef. Its acceptance artifact cannot be identified in this instance."
        }
      ],
      "external_code": []
    },
    {
      "source_item": "Theorem 8.4.10",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.305 / PDF p.336; notation at Sections 8.4.2–8.4.8"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.37, opening of Section 8.4",
        "change": "Retain perfect residue from corrected Section 8.3 and replace both occurrences of o by O in the second paragraph."
      },
      "hypotheses": [
        "k has a normalized discrete valuation, Henselian integer ring o and perfect residue field f; G is connected reductive over k. K is a maximal unramified extension, O its integer ring, fbar its algebraically closed residue field, and Gamma=Gal(K/k)=Gal(fbar/f). Perfect residue is the corrected hypothesis of Section 8.3 and subsequent sections, not merely quasi-splitness of G_K.",
        "S is a maximal K-split torus, T=Z_{G_K}(S), and Omega is a nonempty bounded subset of its apartment in the actual building B(G_K). The models in Chapter 8 are over O; their descent over o is a separate construction.",
        "Write H_Omega for the connected special fibre of the connected parahoric model G^0_Omega, and Gred_Omega=H_Omega/R_u(H_Omega) for its maximal reductive quotient. Sbar is the special fibre of the standard O-model of S and is identified with its image in Gred_Omega.",
        "Recorded Lean scope (the root-datum assertion for facets only): UnramifiedFacetRootDatumStatement (module Langlands.BruhatTits.IntegralModels.UnramifiedFacetRootDatumStatement, artifact adc6a005-db54-4eea-ab15-802f0f62e17f, first published in Library commit 73b1430a339b037d27e9096762b0400adb4fbd19) is Axiom 4.1.22(6) for the descended building, in the form of Proposition 9.4.23. It quantifies over every nonarchimedean local field F, affine group scheme G over F and supplied P : ParahoricBuildingData G with a polysimplicial realization and an apartment splitting satisfying the seven Section 4.2 building predicates. It also takes supplied building data C of G_K for K = inertiaFixedField F, a semilinear Galois action A on C, a datum E computing G(K)^0, and an injective G(F)-equivariant map e from the building of P to that of C with an affine apartment map a, subject to eight descent premises: e is compatible with the apartment maps through a; it lands in and surjects onto the Galois-fixed points; it reflects special points; a matches the facets; and S(K)^1 fixes the image of the apartment. The models are D : RelativeComponentModelData over 𝒪[F] whose smooth neutral model has base change to the integers of K with integral points E.zeroPoints ⊓ C.pointwiseFixer (e(F)) = G(K)^0 ∩ G(K)_{e(F)} for the facet F concerned, together with any Q : SpecialFibreQuotientData D satisfying Q.IsReductiveQuotient. For a facet presented by an apartment facet Fa translated by g in G(F), an integral split torus 𝒯 of D with generic fibre S satisfying the torus clause of Axiom 4.1.20(3), and any relative root reflection data Droot, it asserts HasApartmentDerivativeRootDatum: the root datum of Q relative to the image of the special fibre of 𝒯 consists of the derivatives of the affine roots vanishing on Fa and their coroots in Droot, transported through 𝒯. It differs from the source in four ways: Omega is a facet; the open-cell product onto R_u(H_Omega), the plus-group images and the isomorphism of Ubar_{a,Omega,0}/U^+_{a,Omega,0} with the root group are not stated, nor is reducedness of Phi_Omega as a separate assertion; the root datum is the descended one over 𝒪[F], relative to an f-split torus, rather than the geometric one over fbar relative to Sbar; and the building data and models are supplied. Secondary: the clause derivative_root_data of IntegralModelAxiomsStatement (described in the Theorem 8.3.2 row) asserts the same predicate for the facets of its supplied model families. The status statement of this row covers only this part."
      ],
      "conclusion": "For every choice of positive relative roots, open-cell multiplication is an isomorphism of schemes from the negative nondivisible U^+_{a,Omega,0} factors, T^+, and the positive nondivisible factors onto R_u(H_Omega). These plus groups are special-fibre images of the corresponding 0+ model maps. This is not a direct-product group decomposition. The root datum of Gred_Omega relative to Sbar is (X^*(S),Phi_Omega,X_*(S),Phi_Omega^vee), where Phi_Omega consists of gradients of affine roots vanishing identically on Omega. For a in Phi_Omega, Ubar_{a,Omega,0}/U^+_{a,Omega,0} maps isomorphically to its a-root group. Phi_Omega is reduced even when the ambient relative root system has multipliable roots.",
      "lean_declarations": [
        "Langlands.BruhatTits.IntegralModels.UnramifiedFacetRootDatumStatement",
        "Langlands.BruhatTits.IntegralModels.HasApartmentDerivativeRootDatum",
        "Langlands.Geometry.Building.IntegralModelAxiomsStatement"
      ],
      "modules": [
        "Langlands.BruhatTits.IntegralModels.UnramifiedFacetRootDatumStatement",
        "Langlands.BruhatTits.IntegralModels.FacetAxioms",
        "Langlands.Geometry.Building.IntegralModelAxiomsStatement"
      ],
      "dependencies": [
        "Proposition 8.3.14, Corollary 8.4.5 and Proposition 8.4.8; Lemma 8.4.7 keeps the a-versus-2a alternatives",
        "Dynamic root groups and multiplication, Proposition 2.11.9 and Theorem 2.11.15; torus unipotent radical B.10.12",
        "For nonempty bounded Gamma-stable subsets, Section 9.2.5 constructs the descended smooth affine o-models using invariant coordinate rings and relative identity components; 9.2.6 identifies the parahoric o-points. Chapter 8 models alone do not give this descent.",
        "Section 9.5 uses perfectness to descend the geometric unipotent radical; the displayed split root datum is a geometric description over fbar, not an assertion of splitness over f",
        "Open obligations: UnramifiedFacetRootDatumStatement has proof Task 6218 (fa9500db-0be6-4ede-8713-ebdd29022790), an input to IntegralModelAxiomsStatement's proof Task 5429."
      ],
      "consumer_or_regression": "Maximal reductive quotient for depth zero. Preserve the special-fibre distinction; the ramified SU_3 example of Remark 8.4.11 has quotient SO(3)=PGL_2 although the ambient group is simply connected.",
      "formal_status": "statement",
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [
        "adc6a005-db54-4eea-ab15-802f0f62e17f"
      ],
      "publication_commits": [
        "73b1430a339b037d27e9096762b0400adb4fbd19",
        "ed924aef420de137b4cbaa3b063a3618afcd73fd"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.UnramifiedFacetRootDatumStatement",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "f1eb8cdd-f3bc-4128-a8e7-6969acf1e5b6",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-13 at Library commit 451cce4c; kind definition; statement_returns_prop true; the module is byte-identical to commit 73b1430a, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.HasApartmentDerivativeRootDatum",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "bea54caf-b55a-46da-8990-2ed244ff2af2",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-13 at Library commit eded01f2; kind definition; the module is byte-identical to commit ed924aef."
        },
        {
          "declaration": "Langlands.Geometry.Building.IntegralModelAxiomsStatement",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "ce6ea460-76bf-4c15-ac37-ee6c05951dc6",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-13 at Library commit eded01f2; kind definition; statement_returns_prop true; the module is byte-identical to commit ed924aef. Its acceptance artifact cannot be identified in this instance."
        }
      ],
      "external_code": []
    },
    {
      "source_item": "Corollary 8.4.12",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.306 / PDF p.337"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.37, corrected Sections 8.3–8.4 ambient setup",
        "change": "Perfect residue applies throughout; Section 8.4 models are over O. No direct replacement of Corollary 8.4.12 is listed."
      },
      "hypotheses": [
        "k has a normalized discrete valuation, Henselian integer ring o and perfect residue field f; G is connected reductive over k. K is a maximal unramified extension, O its integer ring, fbar its algebraically closed residue field, and Gamma=Gal(K/k)=Gal(fbar/f). Perfect residue is the corrected hypothesis of Section 8.3 and subsequent sections, not merely quasi-splitness of G_K.",
        "S is a maximal K-split torus, T=Z_{G_K}(S), and Omega is a nonempty bounded subset of its apartment in the actual building B(G_K). The models in Chapter 8 are over O; their descent over o is a separate construction.",
        "Write H_Omega for the connected special fibre of the connected parahoric model G^0_Omega, and Gred_Omega=H_Omega/R_u(H_Omega) for its maximal reductive quotient. Sbar is the special fibre of the standard O-model of S and is identified with its image in Gred_Omega.",
        "Recorded Lean scope (the Axiom 4.1.22(7) inclusion only, which KP 4.1.28 derives from this corollary): UnramifiedFacetPositiveRadicalStatement (module Langlands.BruhatTits.IntegralModels.UnramifiedFacetPositiveRadicalStatement, artifact bf9958e9-6ff4-49bc-8d10-7c32126dffad, first published in Library commit 73b1430a339b037d27e9096762b0400adb4fbd19) has the setting of the Theorem 8.4.10 row. For facets F ≺ F' of the descended building, with characterized models D and D' and reductive quotients Q and Q', it asserts Q.positivePoints ≤ Q'.positivePoints. Here positivePoints is by definition the subgroup of G(F) of integral sections of the neutral model whose reduction projects into the unipotent radical, the descended analogue of the inverse image named in the corollary. No Lean declaration compares it with the Moy–Prasad group G(K)_{Omega,0+}, so the identification asserted by the corollary is not stated. The surjectivity of reduction used in the corollary is proved in general: Langlands.GroupScheme.IntegralModel.reduction_surjective (module Langlands.GroupScheme.IntegralModel.HenselianReduction, present in Library commit ed924aef420de137b4cbaa3b063a3618afcd73fd) says that the reduction map of a smooth integral model over a Henselian local ring is surjective, the role of 8.1.3. Secondary: the clause positive_radicals of IntegralModelAxiomsStatement (described in the Theorem 8.3.2 row) asserts SatisfiesPositiveRadicalClause for incident facets of its supplied families: both reductions are surjective and the same inclusion holds. The status statement of this row covers only this part."
      ],
      "conclusion": "Under the natural surjective reduction G(K)^0_Omega=G^0_Omega(O)→H_Omega(fbar), the inverse image of R_u(H_Omega)(fbar) is G(K)_{Omega,0+}. Thus 0+ is the kernel of the composite to Gred_Omega(fbar); it is generally larger than the kernel of reduction to the whole special fibre.",
      "lean_declarations": [
        "Langlands.BruhatTits.IntegralModels.UnramifiedFacetPositiveRadicalStatement",
        "Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom.SatisfiesPositiveRadicalClause",
        "Langlands.GroupScheme.IntegralModel.reduction_surjective",
        "Langlands.Geometry.Building.IntegralModelAxiomsStatement"
      ],
      "modules": [
        "Langlands.BruhatTits.IntegralModels.UnramifiedFacetPositiveRadicalStatement",
        "Langlands.BruhatTits.IntegralModels.SpecialFibre",
        "Langlands.GroupScheme.IntegralModel.HenselianReduction",
        "Langlands.Geometry.Building.IntegralModelAxiomsStatement"
      ],
      "dependencies": [
        "Smooth Henselian reduction is surjective by 8.1.3; the integral-point identification is Theorem 8.3.13",
        "Theorem 8.4.10, Corollary 8.4.5(2), Lemma B.10.11 and Proposition 7.3.12 identify the inverse image",
        "Proposition 2.4.3 makes projection from smooth connected special-fibre rational points to the reductive quotient surjective; Lemma 2.4.2 supplies unipotent H^1 vanishing",
        "For nonempty bounded Gamma-stable subsets, Section 9.2.5 constructs the descended smooth affine o-models using invariant coordinate rings and relative identity components; 9.2.6 identifies the parahoric o-points. Chapter 8 models alone do not give this descent.",
        "Section 9.5 uses G(k)^0=G(K)^0 intersect G(k) from 9.3.24, descends the unipotent radical over perfect f and gives G(k)^0+_F=G(K)^0+_F intersect G(k), hence the kernel over k",
        "Open obligations: UnramifiedFacetPositiveRadicalStatement has proof Task 6219 (ec6e20e8-735d-4944-a683-3828ed1a53ea). The comparison of the radical preimage with G(K)_{Omega,0+} has no Lean statement."
      ],
      "consumer_or_regression": "Use the actual reduction composite in the depth-zero quotient and inflation; neither an arbitrary map with an assumed kernel nor reduction to the entire special fibre meets the target.",
      "formal_status": "statement",
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [
        "bf9958e9-6ff4-49bc-8d10-7c32126dffad"
      ],
      "publication_commits": [
        "73b1430a339b037d27e9096762b0400adb4fbd19",
        "ed924aef420de137b4cbaa3b063a3618afcd73fd"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.UnramifiedFacetPositiveRadicalStatement",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "5d74e3d3-e8f7-414c-a735-1a840a1111e8",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-13 at Library commit 451cce4c; kind definition; statement_returns_prop true; the module is byte-identical to commit 73b1430a, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom.SatisfiesPositiveRadicalClause",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "234590d9-17a4-4588-aa08-59718a363dad",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-13 at Library commit eded01f2; kind definition; the module is byte-identical to commit ed924aef."
        },
        {
          "declaration": "Langlands.GroupScheme.IntegralModel.reduction_surjective",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "32420bdf-ad04-455e-9ddf-d4915de0b845",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-13 at Library commit aae8cb82; kind theorem; the module is byte-identical to commit ed924aef. Its acceptance artifact cannot be identified in this instance."
        },
        {
          "declaration": "Langlands.Geometry.Building.IntegralModelAxiomsStatement",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "ce6ea460-76bf-4c15-ac37-ee6c05951dc6",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-13 at Library commit eded01f2; kind definition; statement_returns_prop true; the module is byte-identical to commit ed924aef. Its acceptance artifact cannot be identified in this instance."
        }
      ],
      "external_code": []
    },
    {
      "source_item": "Theorem 8.4.19",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.308–310 / PDF pp.339–341; valid general kernel product in Proposition 8.4.15, printed pp.306–307 / PDF pp.337–338; counterexample from Example 8.3.5, printed pp.296–297 / PDF pp.327–328, and Section 8.4.6, printed p.304 / PDF p.335"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF pp.37–38, Sections 8.3–8.4 and the setup of Proposition 8.4.15",
        "change": "Apply perfect residue and O-model conventions. Move the nonempty bounded Omega≺Omega' hypothesis before 8.4.15, define both model and special-fibre morphisms there, and delete that proposition's former first sentence. These authors' corrections contain no repair of the restricted index printed in 8.4.19(1); the source discrepancy recorded here is a separate derived check from 8.3.5 and 8.4.6."
      },
      "hypotheses": [
        "k has a normalized discrete valuation, Henselian integer ring o and perfect residue field f; G is connected reductive over k. K is a maximal unramified extension, O its integer ring, fbar its algebraically closed residue field, and Gamma=Gal(K/k)=Gal(fbar/f). Perfect residue is the corrected hypothesis of Section 8.3 and subsequent sections, not merely quasi-splitness of G_K.",
        "F and F' are facets in an apartment A with F contained in the closure of F'. The generic-fibre identity induces the actual model morphism G^0_{F'}→G^0_F and its special-fibre morphism rhobar:H_{F'}→H_F. The full bijection ranges over all facets in B(G_K) whose closures contain F, not just those in A.",
        "Recorded Lean scope (the smooth connected unipotent kernel of part (1), in the form of Proposition 8.4.15; parts (2)–(4) only through IntegralModelAxiomsStatement): UnramifiedModelKernelStatement (module Langlands.BruhatTits.IntegralModels.UnramifiedModelKernelStatement, artifact a9987a70-ad07-49f0-adca-afbc31ec89df, first published in Library commit 51e4d8972659f1ffcf0ca89e8eee9540a30b52d3) has the setting of UnramifiedParahoricModelStatement (Theorem 8.3.2 row). For g in G(K) and subsets Omega_a and Omega_a' of the apartment of C with Omega_a nonempty, Omega_a' bounded and Omega_a contained in the closure of Omega_a', and for any smooth O-models N and N' with integral points G(K)^0 ∩ G(K)_{g·Omega_a} and G(K)^0 ∩ G(K)_{g·Omega_a'}, it asserts that every model homomorphism N' → N with identity generic fibre has a smooth, connected and unipotent scheme-theoretic kernel on special fibres. For facets F ≺ F' this is the first assertion of part (1). The product identification over all nondivisible roots is not stated, and neither is the false restricted index. At Library commit a0627c91 parts (2)–(4) have no statement in this unramified setting. IntegralModelAxiomsStatement (described in the Theorem 8.3.2 row) contains them for the descended supplied families over 𝒪[F], for f-rational parabolics rather than over fbar: its facet clauses assert HasParabolicSpecialFibreImage (the schematic image of the special-fibre map is a parabolic subgroup, Axiom 4.1.22(2)), HasParabolicReductionPreimage (the reduction preimage of the rational points of that image is the image of the integral points for F', Axiom 4.1.22(4)) and FacetModelData.HasFacetParabolicOrderBijection (an order-reversing bijection from all incident facets onto the f-parabolic subgroups of the quotient, Axiom 4.1.22(5)), and its general morphism clause asserts HasSmoothConnectedUnipotentKernel for the model map of every closure-ordered pair of subsets of a common apartment and every pair of incident facets (Axiom 4.1.22(1)). Containment of R_u(H_F) and the correspondence between facets in one apartment and parabolics containing the torus are not separate assertions. The status statement of this row covers only this part."
      ],
      "conclusion": "By Proposition 8.4.15 specialized to these facets, the schematic kernel of rhobar is smooth connected unipotent, and open-cell multiplication identifies it as a scheme with the product of ker(Ubar_{a,F',0}→Ubar_{a,F,0}) over all nondivisible roots a in Phi(S,G_K). The restriction to Phi'_{F'} minus Psi_F(F') printed in Theorem 8.4.19(1) is false and is excluded as a formalization target: Example 8.3.5 gives a split SL_2 open chamber F' incident to a hyperspecial vertex F for which Phi'_{F'} is empty by 8.4.6, but ker(rhobar) is G_a. Theorem 8.4.19(2)–(4) supplies the remaining conclusions. The image p_F(F') is the parabolic of H_F associated to Psi_F(F') and contains R_u(H_F). The inverse image of p_F(F')(fbar) in G^0_F(O) is G^0_{F'}(O). The map F'↦p_F(F') is a bijection from all incident facets onto all parabolics of H_F, equivalently of Gred_F. Facets in A alone correspond to parabolics containing the chosen maximal torus. The kernel product is a scheme isomorphism, not a direct-product group decomposition.",
      "lean_declarations": [
        "Langlands.BruhatTits.IntegralModels.UnramifiedModelKernelStatement",
        "Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom.HasSmoothConnectedUnipotentKernel",
        "Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom.HasParabolicSpecialFibreImage",
        "Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom.HasParabolicReductionPreimage",
        "Langlands.BruhatTits.IntegralModels.FacetModelData.HasFacetParabolicOrderBijection",
        "Langlands.Geometry.Building.IntegralModelAxiomsStatement"
      ],
      "modules": [
        "Langlands.BruhatTits.IntegralModels.UnramifiedModelKernelStatement",
        "Langlands.BruhatTits.IntegralModels.ModelMorphism",
        "Langlands.BruhatTits.IntegralModels.SpecialFibre",
        "Langlands.BruhatTits.IntegralModels.FacetParabolicOrder",
        "Langlands.Geometry.Building.IntegralModelAxiomsStatement"
      ],
      "dependencies": [
        "Corrected general morphism setup preceding Proposition 8.4.15; that proposition supplies the smooth connected unipotent kernel and the product over all nondivisible ambient roots, without the false restriction in 8.4.19(1)",
        "Derived source-discrepancy check from Example 8.3.5 and Section 8.4.6: the chamber model maps to the hyperspecial SL_2 model by c=pi*c'; on special fibres its kernel has a=d=1, b=0 and c' free, hence is G_a, whereas Phi'_{F'} and the printed product index are empty",
        "Root-filtration comparisons 6.3.21; Theorem 8.4.10, Proposition 8.4.8(2), Proposition 1.3.35 and Corollary 8.4.12; independence from the apartment and the use of all apartments through F",
        "For nonempty bounded Gamma-stable subsets, Section 9.2.5 constructs the descended smooth affine o-models using invariant coordinate rings and relative identity components; 9.2.6 identifies the parahoric o-points. Chapter 8 models alone do not give this descent.",
        "Section 9.3.2 descends the facet morphisms and identifies Gamma-facets through F with parabolic f-subgroups; Proposition 2.4.5 transfers these to the maximal reductive quotient",
        "Proposition 9.3.3 proves the exact inverse-image equality over o, using 8.1.3 smooth Henselian reduction and Lemma 2.4.2 for the smooth connected unipotent kernel. This does not assert that every geometric parabolic descends",
        "Open obligations: UnramifiedModelKernelStatement has proof Task 6203 (6cb35eb6-b989-4438-a42a-5fe281a2a64b; statement Task 5901, 5edda489-0dfa-401e-b621-4c2603932be7). IntegralModelAxiomsStatement has proof Task 5429."
      ],
      "consumer_or_regression": "Residue/facet correspondence and change-of-parahoric tests for depth-zero induction and double cosets; retain rational parabolics after Chapter 9 descent. The split SL_2 chamber-to-vertex kernel is a regression against the erroneous printed restricted index.",
      "formal_status": "statement",
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [
        "a9987a70-ad07-49f0-adca-afbc31ec89df"
      ],
      "publication_commits": [
        "51e4d8972659f1ffcf0ca89e8eee9540a30b52d3",
        "ed924aef420de137b4cbaa3b063a3618afcd73fd"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.UnramifiedModelKernelStatement",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "3e02d5e7-c9f4-4aa2-89fb-7823df93388a",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-13 at Library commit 451cce4c; kind definition; statement_returns_prop true; the module is byte-identical to commit 51e4d897, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom.HasSmoothConnectedUnipotentKernel",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "29f8240e-4d0f-40dd-a255-e385450796c5",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-13 at Library commit eded01f2; kind definition; the module is byte-identical to commit ed924aef."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom.HasParabolicSpecialFibreImage",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "a7625583-b32f-4092-baad-54b087fd9116",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-13 at Library commit eded01f2; kind definition; the module is byte-identical to commit ed924aef."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom.HasParabolicReductionPreimage",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "da726057-3b12-4715-b54e-b34c2ca0a458",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-13 at Library commit eded01f2; kind definition; the module is byte-identical to commit ed924aef."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.FacetModelData.HasFacetParabolicOrderBijection",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "7d35aa0b-782b-4721-a64e-9d6b619fb1b4",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-13 at Library commit eded01f2; kind definition; the module is byte-identical to commit ed924aef."
        },
        {
          "declaration": "Langlands.Geometry.Building.IntegralModelAxiomsStatement",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "ce6ea460-76bf-4c15-ac37-ee6c05951dc6",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-13 at Library commit eded01f2; kind definition; statement_returns_prop true; the module is byte-identical to commit ed924aef. Its acceptance artifact cannot be identified in this instance."
        }
      ],
      "external_code": []
    },
    {
      "source_item": "Section 13.2.6",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.470 / PDF p.501; Chapter 13 hypotheses at PDF p.497"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF pp.37–41 and 49–50",
        "change": "Use corrected perfect-residue Chapter 8–9 constructions. The Chapter 13 corrections affect 13.5.2, 13.6.2 and 13.8.5, not 13.2.6; the Appendix B correction on minimal congruent torus filtration does not replace the depth-zero model proof."
      },
      "hypotheses": [
        "k has a normalized discrete valuation, Henselian integer ring o and perfect residue field f; G is connected reductive over k. K is a maximal unramified extension, O its integer ring, fbar its algebraically closed residue field, and Gamma=Gal(K/k)=Gal(fbar/f). Perfect residue is the corrected hypothesis of Section 8.3 and subsequent sections, not merely quasi-splitness of G_K.",
        "x is a point of the actual descended building over k, with connected parahoric model G^0_x over o, special fibre H_x and maximal reductive quotient Gred_x. Put P_{x,0}=G^0_x(o). The Chapter 13 torus filtration is functorial and admissible with 7.2(1),(2). No finite-residue assumption is required for this depth-zero assertion.",
        "Recorded Lean scope: the published modules Langlands.BruhatTits.IntegralModels.DepthZeroReduction (artifact f3a39f0a-0b63-4218-a72a-b3958c3b3740, first in Library commit 7047367a78583edbe335517824e30403414aa3f0) and Langlands.BruhatTits.IntegralModels.DepthZeroInduction (artifact a6b89c9a-222a-4977-b85b-1983338fa594, first in Library commit 7103f5282c4897716543f227940fdb2a0e12e70e) work over a domain R in universe u with fraction field K and a group scheme G over Spec K, with supplied D : RelativeComponentModelData R K G and Q : SpecialFibreQuotientData D. The smooth model D.neutral with connected fibres plays the role of G^0_x, Q.quotient that of Gred_x and Q.projection that of the quotient map; nothing identifies D.neutral with the actual parahoric model or D.neutral.integralPoints with P_{x,0}. The premises hrad : IsUnipotentRadical Q.radicalInclusion and hQ (Q.projection is the represented fppf quotient by that radical) are the first two conjuncts of Q.IsReductiveQuotient; reductivity of the quotient is not used. For a local domain R, ker_parahoricReduction hQ identifies the kernel of parahoricReduction : G^0(R) → Q.quotient(f) with Q.positivePoints.subgroupOf D.neutral.integralPoints, the radical preimage G(K)^{0+} of Axiom 4.1.22(7) inside G^0(R). For a Henselian local domain R with perfect residue field, parahoricReduction_surjective hrad hQ gives surjectivity and depthZeroQuotientEquiv hrad hQ is the induced group isomorphism from G^0(R) modulo that kernel onto Q.quotient(f). The integer rings of k and of K in the source are both such bases, so the source's assertion over K is the same declaration at another base; no instance is supplied. DepthZeroInduction adds the consumer test: inflation of a representation of Q.quotient(f) to G^0(R), the bijection between G^0(R)-maps from an inflation and Q.quotient(f)-maps into kernel invariants, and, for a topological-group structure on G(K) in which G^0(R) and its level-one congruence subgroup are open, compact induction from G^0(R) with Frobenius reciprocity (depthZeroInductionHomEquiv). For a nonarchimedean local field F, R = 𝒪[F] is proved Henselian and localFieldDepthZeroInductionHomEquiv, for affine G locally of finite type with rationalPointTopology, takes those openness premises from LocalFieldIntegralModel.CongruenceNeighborhoodBasisStatement. That statement is proved: congruenceNeighborhoodBasis_proof (module Langlands.GroupScheme.IntegralModel.CongruenceNeighborhoodBasisProof, Task 5447, artifact 69074fc3-6f69-402f-a73b-084d3e30c551, first published in Library commit ba77b83f98d4cbe92842b4645577633e0541fdab) applies to every integral model over 𝒪[F] of an affine G, so localFieldDepthZeroInductionHomEquiv congruenceNeighborhoodBasis_proof needs only the supplied D, Q, hrad and hQ, and the first conjunct of congruenceNeighborhoodBasis_proof F G D.neutral says that D.neutral.integralPoints is compact in rationalPointTopology. The module Langlands.BruhatTits.IntegralModels.FiniteReductiveQuotient (artifact b52c4590-0a68-4f37-a097-c66650f5d9ab, first in Library commit cfedefb680f317b0ea5d351023e1c9dd886b2547) assumes a finite residue field. GroupScheme.finite_rationalPoints says that an affine group scheme locally of finite type over a finite commutative ring has finitely many points. For a local domain R and Q.quotient locally of finite type, finite_quotientPoints gives Finite (rationalPoints Q.quotient), as does IsConnectedReductive Q.quotient alone (finite_quotientPoints_of_isConnectedReductive); finiteQuotientGroup packages these points as a FiniteGrp, and positivePoints_subgroupOf_finiteIndex hQ says that Q.positivePoints.subgroupOf D.neutral.integralPoints has finite index. For a Henselian local domain, index_positivePoints_subgroupOf hrad hQ says that this index equals Nat.card (rationalPoints Q.quotient), and localField_index_positivePoints_subgroupOf is the case R = 𝒪[F]. For affine G locally of finite type with rationalPointTopology, localField_isOpen_ker_parahoricReduction says that the kernel of parahoricReduction is open in D.neutral.integralPoints. The module Langlands.BruhatTits.IntegralModels.DepthZeroCompactOpen (artifact f228edd9-7de3-41af-b12a-6be4746af741, first in the same commit) proves, over a local domain, congruenceSubgroup_le_positivePoints (D.neutral.congruenceSubgroup ≤ Q.positivePoints) and positivePoints_subgroupOf_normal hQ. Over 𝒪[F], with G affine and locally of finite type and rationalPointTopology, localField_isOpen_positivePoints and localField_isCompact_positivePoints say that Q.positivePoints is open and compact in G(F) without hrad or hQ, localFieldPositiveOpenSubgroup bundles it as an OpenSubgroup, and RelativeComponentModelData.localFieldIntegralOpenSubgroup bundles D.neutral.integralPoints for affine G. The cokernel description of Gred_x is not formalized. The module Langlands.Representation.Induction.OpenIntertwiningStatement (artifact 14c308d9-57df-4b0b-9b87-e08f078a61ae, first published in Library commit 79de65ce5fcd6dc5f182612988e1b529d49a63b4) states, for a subgroup H of a topological group G and representations of H over a commutative ring, CompactInductionIntertwiningStatement, the conjunction of three propositions. CompactInductionKernelStatement: for open H, the maps c-Ind_H^G A → c-Ind_H^G B between smooth representations correspond bijectively to intertwining kernels Φ : G → Hom(A, B) (IsIntertwiningKernel: Φ(hgh') = τ(h) ∘ Φ(g) ∘ σ(h'), and for each vector v only finitely many right cosets Hg have Φ(g)v ≠ 0), via Φ(g)v = T(unitFunction v)(g). CompactInductionDoubleCosetStatement: for compact open H, smooth σ and double-coset representatives s, restriction to the representatives is a bijection from intertwining kernels onto local intertwiner families (IsLocalIntertwinerFamily: φ(q) intertwines σ with h ↦ τ(s(q) h s(q)⁻¹) on H ∩ s(q)⁻¹ H s(q), and for each v only finitely many q have φ(q)v ≠ 0). CompactInductionFiniteTypeKernelStatement: for compact open H and finitely generated σ, the intertwining kernels are the covariant functions whose support meets finitely many double cosets HgH. With H = D.neutral.integralPoints and A, B two inflations Q.inflationSmoothRep, these describe the maps between the depth-zero compact inductions of DepthZeroInduction. Each conjunct is proved: Langlands.Induction.compactInductionKernel (module Langlands.Representation.Induction.OpenIntertwiningKernelProof, Task 5700, artifact 3d0aeb2f-0165-45fd-84c2-84524c965b56), compactInductionDoubleCoset (module Langlands.Representation.Induction.OpenIntertwiningDoubleCosetProof, Task 5701, artifact 2c97df7d-ae72-436f-8163-bbf7e3c7a7c5) and compactInductionFiniteTypeKernel (module Langlands.Representation.Induction.OpenIntertwiningFiniteTypeProof, Task 5702, artifact cd045fc8-59a1-4276-b72d-a81744fa882e), all first published in Library commit 730bd1f25b056b8106a2697e003c1ef1733a6b30; no separate theorem proves the conjunction. The module Langlands.BruhatTits.IntegralModels.DepthZeroIntertwining (artifact 8fac015b-ad45-42d1-b1a8-fa15c6755a7c, first published in Library commit 73b1430a339b037d27e9096762b0400adb4fbd19) specializes them to H = D.neutral.integralPoints and two inflations, for a local domain R and a topological-group structure on G(K) in which H and the level-one congruence subgroup are open. depthZeroInductionKernelEquiv identifies the maps between the depth-zero compact inductions of σ and τ with the intertwining kernels of their inflations. For compact H and supplied double-coset representatives s, depthZeroInductionDoubleCosetEquiv identifies them with local intertwiner families on H\\G(K)/H. For σ on a finite k-module, depthZeroInductionKernel_finite_doubleCosetSupport says that the kernel of every such map is supported on finitely many double cosets. Over a nonarchimedean local field with G affine and rationalPointTopology, RelativeComponentModelData.localField_isOpen_congruenceSubgroup proves the congruence premise; for G also locally of finite type, localFieldDepthZeroInductionDoubleCosetEquiv and localField_depthZeroInductionKernel_finite_doubleCosetSupport need only the supplied D and Q. None of these uses hrad, hQ or a Henselian base. The double-coset representatives are supplied: no Bruhat or Iwahori decomposition of H\\G(K)/H, no Hecke-algebra multiplication and nothing about irreducibility or supercuspidality is stated.",
        "Recorded regression instances (split groups with their standard models; no building point): five published modules construct actual, not supplied, D and Q over R = 𝒪[F] for a nonarchimedean local field F whose residue field f has q elements. In each, D.full = D.neutral is a standard smooth model with connected fibres, obtained from the published criterion relativeComponentData_of_reductive_localField, the radical is the trivial subgroup, Q.quotient is the special fibre itself with the identity projection, and Q.IsReductiveQuotient is proved, so the theorems of the Recorded Lean scope apply with hrad and hQ discharged. (1) Langlands.BruhatTits.IntegralModels.MultiplicativeDepthZero (artifact 3a66ce4a-0da3-4c10-a0a7-0950c9263bcd, first published in Library commit 85c2fe719cf62e96f22aaf4ca03961c5814d086b): multiplicativeModelData on the published model IntegralModel.multiplicative, multiplicativeQuotientData and multiplicativeQuotientData_isReductiveQuotient; mem_multiplicative_positivePoints describes the radical preimage as the images of the units of 𝒪[F] with residue 1, that is 1 + 𝔪; multiplicative_index_positivePoints_subgroupOf gives index q − 1 in the integral points, and multiplicative_index_positivePoints_subgroupOf_eq_one gives index 1 when q = 2. (2) Langlands.BruhatTits.IntegralModels.SplitTorusDepthZero (artifact fb196e9b-3556-4f49-92d8-214b6a45bad8, first published in Library commit 85c2fe719cf62e96f22aaf4ca03961c5814d086b): for a finite index type I, Langlands.GroupScheme.IntegralModel.splitTorusModel is the split torus G_m^I over a domain, as a model of the split torus over its fraction field; splitTorusModelData, splitTorusQuotientData and splitTorusQuotientData_isReductiveQuotient are as in (1); mem_splitTorus_positivePoints gives (1 + 𝔪)^I and splitTorus_index_positivePoints_subgroupOf gives index (q − 1)^|I|. (3) Langlands.BruhatTits.IntegralModels.GeneralLinearDepthZero (artifact 1d98759b-e9fb-4fe5-8eed-cf3c2b20c5ac, first published in Library commit db8d6b3d466f2fd453a4df4624ce6c90db8eed46): for any D, SpecialFibreQuotientData.identityQuotient D is the quotient data with trivial radical and identity projection; identityQuotient_isReductiveQuotient proves that it is a reductive quotient when the neutral special fibre is connected reductive, and identityQuotient_positivePoints identifies its radical preimage with D.neutral.congruenceSubgroup, the image of the kernel of reduction. generalLinearModelData on the standard model GL_{N,𝒪[F]}, generalLinearQuotientData (the identity quotient) and generalLinearQuotientData_isReductiveQuotient; generalLinear_index_positivePoints_subgroupOf_eq_prod gives index ∏_{i<N} (q^N − q^i), the order of GL_N(f). For N = n + 1, generalLinear_integralPoints_map_eq_integralSubgroup and generalLinear_positivePoints_map_eq_principalLevelSubgroup map the integral points and the radical preimage onto the Library's concrete Conductor.integralSubgroup 𝒪[F] n and Conductor.principalLevelSubgroup F n 1, and generalLinear_principalLevelSubgroup_relIndex gives their relative index |GL_{n+1}(f)|. (4) Langlands.BruhatTits.IntegralModels.SymplecticDepthZero (artifact d2114602-84e9-4570-bb92-d2f5ae6ba87f, first published in Library commit 410c79471b79f65a02fb0f6070da7f2800793ff3): symplecticModelData on the standard model Sp_{2l,𝒪[F]} (Langlands.GroupScheme.SymplecticMatrix.standardIntegralModel), symplecticQuotientData (the identity quotient) and symplecticQuotientData_isReductiveQuotient; symplectic_index_positivePoints_subgroupOf gives index |Sp_{2l}(f)|, and mem_symplectic_positivePoints_iff_generalLinear says that a point lies in the radical preimage exactly when its matrix in GL_{l⊕l}(F) is the image of an element of GL_{l⊕l}(𝒪[F]) with residue 1. (5) Langlands.BruhatTits.IntegralModels.SpecialLinearDepthZero (artifact c1bbf8bb-a63a-4c88-a6d8-70976a4c2ab7, first published in Library commit 410c79471b79f65a02fb0f6070da7f2800793ff3): specialLinearModelData on the standard model SL_{n,𝒪[F]} (Langlands.GroupScheme.SpecialLinear.standardIntegralModel) for a nonempty finite index type n, specialLinearQuotientData (the identity quotient) and specialLinearQuotientData_isReductiveQuotient; specialLinear_index_positivePoints_subgroupOf_mul says that for n = Fin N the index times q − 1 is ∏_{i<N} (q^N − q^i), and specialLinear_positivePoints_eq_comap_principalLevelSubgroup identifies the radical preimage for n = Fin (m + 1) with the preimage of Conductor.principalLevelSubgroup F m 1. Each index theorem is derived from localField_index_positivePoints_subgroupOf (FiniteReductiveQuotient) through an identification of the residue-field points of the special fibre. Non-claims: no building and no point x appear. Nothing identifies these standard models with KP's G^0_x at a hyperspecial vertex (for G split over K, Proposition 8.4.14, printed p.306 / PDF p.337, says that G^0_x is reductive exactly when x is a hyperspecial vertex), D.neutral.integralPoints with P_{x,0}, or the radical preimage with P_{x,0+}; agreement with KP's values holds only through the explicit descriptions above. Every radical here is trivial, and every group is split."
      ],
      "conclusion": "The natural composite P_{x,0}=G^0_x(o)→H_x(f)→Gred_x(f) is surjective with kernel P_{x,0+}, and hence induces P_{x,0}/P_{x,0+}≃Gred_x(f). The analogous assertion holds over K. As an f-group scheme, Gred_x is also the cokernel of the special-fibre map G_{x,0+}→G_{x,0}. The rational-point quotient uses both surjectivity steps and the descended kernel; it does not follow merely from a group-scheme cokernel.",
      "lean_declarations": [
        "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.depthZeroQuotientEquiv",
        "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.parahoricReduction_surjective",
        "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.ker_parahoricReduction",
        "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.depthZeroInductionHomEquiv",
        "Langlands.BruhatTits.IntegralModels.localFieldDepthZeroInductionHomEquiv",
        "Langlands.GroupScheme.finite_rationalPoints",
        "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.finite_quotientPoints_of_isConnectedReductive",
        "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.finiteQuotientGroup",
        "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.index_positivePoints_subgroupOf",
        "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.localField_index_positivePoints_subgroupOf",
        "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.localField_isOpen_ker_parahoricReduction",
        "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.positivePoints_subgroupOf_normal",
        "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.localField_isOpen_positivePoints",
        "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.localField_isCompact_positivePoints",
        "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.localFieldPositiveOpenSubgroup",
        "Langlands.BruhatTits.IntegralModels.RelativeComponentModelData.localFieldIntegralOpenSubgroup",
        "Langlands.Induction.CompactInductionIntertwiningStatement",
        "Langlands.Induction.CompactInductionKernelStatement",
        "Langlands.Induction.CompactInductionDoubleCosetStatement",
        "Langlands.Induction.CompactInductionFiniteTypeKernelStatement",
        "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.depthZeroInductionKernelEquiv",
        "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.depthZeroInductionDoubleCosetEquiv",
        "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.depthZeroInductionKernel_finite_doubleCosetSupport",
        "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.localFieldDepthZeroInductionDoubleCosetEquiv",
        "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.localField_depthZeroInductionKernel_finite_doubleCosetSupport",
        "Langlands.BruhatTits.IntegralModels.RelativeComponentModelData.localField_isOpen_congruenceSubgroup",
        "Langlands.Induction.compactInductionKernel",
        "Langlands.Induction.compactInductionDoubleCoset",
        "Langlands.Induction.compactInductionFiniteTypeKernel",
        "Langlands.BruhatTits.IntegralModels.multiplicativeModelData",
        "Langlands.BruhatTits.IntegralModels.multiplicativeQuotientData",
        "Langlands.BruhatTits.IntegralModels.multiplicativeQuotientData_isReductiveQuotient",
        "Langlands.BruhatTits.IntegralModels.multiplicative_index_positivePoints_subgroupOf",
        "Langlands.BruhatTits.IntegralModels.multiplicative_index_positivePoints_subgroupOf_eq_one",
        "Langlands.BruhatTits.IntegralModels.mem_multiplicative_positivePoints",
        "Langlands.GroupScheme.IntegralModel.splitTorusModel",
        "Langlands.BruhatTits.IntegralModels.splitTorusModelData",
        "Langlands.BruhatTits.IntegralModels.splitTorusQuotientData",
        "Langlands.BruhatTits.IntegralModels.splitTorusQuotientData_isReductiveQuotient",
        "Langlands.BruhatTits.IntegralModels.splitTorus_index_positivePoints_subgroupOf",
        "Langlands.BruhatTits.IntegralModels.mem_splitTorus_positivePoints",
        "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.identityQuotient",
        "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.identityQuotient_isReductiveQuotient",
        "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.identityQuotient_positivePoints",
        "Langlands.BruhatTits.IntegralModels.generalLinearModelData",
        "Langlands.BruhatTits.IntegralModels.generalLinearQuotientData",
        "Langlands.BruhatTits.IntegralModels.generalLinearQuotientData_isReductiveQuotient",
        "Langlands.BruhatTits.IntegralModels.generalLinear_index_positivePoints_subgroupOf_eq_prod",
        "Langlands.BruhatTits.IntegralModels.generalLinear_integralPoints_map_eq_integralSubgroup",
        "Langlands.BruhatTits.IntegralModels.generalLinear_positivePoints_map_eq_principalLevelSubgroup",
        "Langlands.BruhatTits.IntegralModels.generalLinear_principalLevelSubgroup_relIndex",
        "Langlands.BruhatTits.IntegralModels.symplecticModelData",
        "Langlands.BruhatTits.IntegralModels.symplecticQuotientData",
        "Langlands.BruhatTits.IntegralModels.symplecticQuotientData_isReductiveQuotient",
        "Langlands.BruhatTits.IntegralModels.symplectic_index_positivePoints_subgroupOf",
        "Langlands.BruhatTits.IntegralModels.mem_symplectic_positivePoints_iff_generalLinear",
        "Langlands.BruhatTits.IntegralModels.specialLinearModelData",
        "Langlands.BruhatTits.IntegralModels.specialLinearQuotientData",
        "Langlands.BruhatTits.IntegralModels.specialLinearQuotientData_isReductiveQuotient",
        "Langlands.BruhatTits.IntegralModels.specialLinear_index_positivePoints_subgroupOf_mul",
        "Langlands.BruhatTits.IntegralModels.specialLinear_positivePoints_eq_comap_principalLevelSubgroup"
      ],
      "modules": [
        "Langlands.BruhatTits.IntegralModels.DepthZeroReduction",
        "Langlands.BruhatTits.IntegralModels.DepthZeroInduction",
        "Langlands.BruhatTits.IntegralModels.FiniteReductiveQuotient",
        "Langlands.BruhatTits.IntegralModels.DepthZeroCompactOpen",
        "Langlands.Representation.Induction.OpenIntertwiningStatement",
        "Langlands.Representation.Induction.OpenIntertwiningKernelProof",
        "Langlands.Representation.Induction.OpenIntertwiningDoubleCosetProof",
        "Langlands.Representation.Induction.OpenIntertwiningFiniteTypeProof",
        "Langlands.BruhatTits.IntegralModels.DepthZeroIntertwining",
        "Langlands.BruhatTits.IntegralModels.MultiplicativeDepthZero",
        "Langlands.BruhatTits.IntegralModels.SplitTorusDepthZero",
        "Langlands.BruhatTits.IntegralModels.GeneralLinearDepthZero",
        "Langlands.BruhatTits.IntegralModels.SymplecticDepthZero",
        "Langlands.BruhatTits.IntegralModels.SpecialLinearDepthZero"
      ],
      "dependencies": [
        "Theorems 8.3.2 and 8.3.13 construct the actual models; Sections 9.2.5–9.2.6 descend them and identify integral points",
        "The first reduction arrow is surjective by 8.1.3. The second is surjective by Proposition 2.4.3 over perfect f, proved using Lemma 2.4.2 on split unipotent groups and H^1",
        "Corollary 8.4.12 and Section 9.5 identify the actual kernel over k; apply the group first isomorphism theorem",
        "The congruence models and their morphism come from Theorem 8.5.2 and Section 8.5.17, with Chapter 9 descent",
        "Section 13.2.2 separates facet-dependent 0 and 0+ from positive-depth variation, and 13.2.3 uses 9.8.3(2) for the Gamma-invariant group comparison",
        "Recorded Lean route: surjectivity composes the Henselian lifting theorem IntegralModel.reduction_surjective for the smooth model (the role of 8.1.3) with projectionPoints_surjective. Over a perfect residue field the latter uses a scheme section of the projection, obtained from the published perfectFieldUnipotentSplit and splitUnipotentAffineTorsorStatement, instead of the Galois cohomology of Lemma 2.4.2 and Proposition 2.4.3 (printed p.84 / PDF p.115). The kernel is the radical preimage by construction. Its identification with the Moy–Prasad group P_{x,0+} (Corollary 8.4.12, printed p.306 / PDF p.337, and Section 9.5) and the construction of the actual models, radical and quotient (Theorems 8.3.2 and 8.3.13, Sections 9.2.5–9.2.6) are not formalized.",
        "Intertwining source (outside KP): M.-F. Vignéras, Représentations ℓ-modulaires d'un groupe réductif p-adique avec ℓ ≠ p (1996), literature ID provided-74667a7cddb3bdafff85f01c658605ce7d929f6da73950d79457c46bcd761dd4, SHA-256 4d2daeee16515f994dfb04157915179b55b30d5bf2f874a16f13e7cb6fa7d657, I.8.5 at printed pp.67–68 / PDF pp.85–86, with I.8.1–I.8.2 at printed pp.64–65 / PDF pp.82–83 and the proof of I.8.3 at printed p.66 / PDF p.84. I.8.5 identifies Hom(ind_{G,K} σ, ind_{G,H} π), for open K and σ of finite type, with the covariant functions supported on finitely many double cosets HgK. The kernel statement drops finite type and compactness and uses the per-vector support condition of the source's proof; the double-coset statement parametrizes kernels by their values at double-coset representatives, as in the proof of I.8.3, with per-vector finiteness, a form derived for this unit; the finite-type statement recovers I.8.5 a) for compact open H. Only the case K = H is stated; compactness of H replaces compactness modulo the centre.",
        "Open obligations before unconditional use: construct D and Q with hrad and hQ for the actual parahoric model of a point of the actual descended building; prove Corollary 8.4.12. The premise CongruenceNeighborhoodBasisStatement of the local-field corollary is proved (congruenceNeighborhoodBasis_proof, proof Task 5447, fc268342-28e9-4dd8-a855-9ae5c09db273); lean_check inspection 98fdf5d1-8dd3-4e68-a8cd-41e4e60802db by Worker 3557 on 2026-11-12 at Library commit c5b9c2cf, where the module is byte-identical to commit ba77b83f, reports kind theorem and only propext, Classical.choice and Quot.sound. The intertwining statements are proved by their lean.proof@1 successors Task 5700 (abd8a5ce-2cfa-4a01-ab20-d73169188e3b) for CompactInductionKernelStatement, Task 5701 (c805d554-3b06-4d41-af89-396402e6bd7c) for CompactInductionDoubleCosetStatement and Task 5702 (a599b653-388c-412d-acbf-e8226e2f6494) for CompactInductionFiniteTypeKernelStatement; CompactInductionIntertwiningStatement is their conjunction."
      ],
      "consumer_or_regression": "For a nonarchimedean local field, separately prove finiteness of Gred_x(f) from finite residue and finite type, and compactness/openness from the actual model topology. Inflate a finite-quotient representation through this map and prove the quotient factorization, then compactly induce and prove a double-coset or intertwining theorem. This source row supplies no positive-depth acceptance. Recorded progress: inflation, its factorization through kernel invariants, compact induction and Frobenius reciprocity are formalized on supplied data in DepthZeroInduction (see the Recorded Lean scope). For a nonarchimedean local field, compactness and openness of D.neutral.integralPoints and of its congruence subgroups are proved for every supplied model of an affine G (congruenceNeighborhoodBasis_proof), and the intertwining and double-coset description of maps between compact inductions is proved (the three conjuncts of CompactInductionIntertwiningStatement) and specialized to the depth-zero compact inductions (DepthZeroIntertwining); over a nonarchimedean local field the specialization needs only the supplied D and Q. For a finite residue field, finiteness of the supplied quotient's residue-field points and the index formula [D.neutral.integralPoints : radical preimage] = |Q.quotient(f)| over a Henselian base are proved (FiniteReductiveQuotient), and over a nonarchimedean local field the radical preimage is proved compact and open in G(F) (DepthZeroCompactOpen). The identification of D.neutral.integralPoints and of the radical preimage with the actual P_{x,0} and P_{x,0+} remains open. Recorded regression instances: the standard models of the split groups G_m, G_m^I, GL_N, Sp_{2l} and SL_n over the integers of a nonarchimedean local field give actual D and Q satisfying Q.IsReductiveQuotient (see the Recorded regression instances entry). The radical preimage has index q − 1 in the integral points for G_m (index 1 when q = 2), (q − 1)^|I| for G_m^I, ∏_{i<N} (q^N − q^i) = |GL_N(f)| for GL_N and |Sp_{2l}(f)| for Sp_{2l}, and for SL_N the index times q − 1 is ∏_{i<N} (q^N − q^i). For GL_{n+1} the integral points and the radical preimage are carried onto the Library's Conductor.integralSubgroup 𝒪[F] n and Conductor.principalLevelSubgroup F n 1, with relative index |GL_{n+1}(f)|. These instances do not identify the models with KP's G^0_x. Regression instances for an anisotropic or non-split torus, a multipliable root, a nontrivial unipotent radical (for example a non-hyperspecial parahoric of a split group) and a nontrivial component group remain open.",
      "formal_status": "conditional",
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [
        "f3a39f0a-0b63-4218-a72a-b3958c3b3740",
        "a6b89c9a-222a-4977-b85b-1983338fa594",
        "14c308d9-57df-4b0b-9b87-e08f078a61ae",
        "b52c4590-0a68-4f37-a097-c66650f5d9ab",
        "f228edd9-7de3-41af-b12a-6be4746af741",
        "3d0aeb2f-0165-45fd-84c2-84524c965b56",
        "2c97df7d-ae72-436f-8163-bbf7e3c7a7c5",
        "cd045fc8-59a1-4276-b72d-a81744fa882e",
        "8fac015b-ad45-42d1-b1a8-fa15c6755a7c",
        "3a66ce4a-0da3-4c10-a0a7-0950c9263bcd",
        "fb196e9b-3556-4f49-92d8-214b6a45bad8",
        "1d98759b-e9fb-4fe5-8eed-cf3c2b20c5ac",
        "d2114602-84e9-4570-bb92-d2f5ae6ba87f",
        "c1bbf8bb-a63a-4c88-a6d8-70976a4c2ab7"
      ],
      "publication_commits": [
        "7047367a78583edbe335517824e30403414aa3f0",
        "7103f5282c4897716543f227940fdb2a0e12e70e",
        "79de65ce5fcd6dc5f182612988e1b529d49a63b4",
        "cfedefb680f317b0ea5d351023e1c9dd886b2547",
        "730bd1f25b056b8106a2697e003c1ef1733a6b30",
        "73b1430a339b037d27e9096762b0400adb4fbd19",
        "85c2fe719cf62e96f22aaf4ca03961c5814d086b",
        "db8d6b3d466f2fd453a4df4624ce6c90db8eed46",
        "410c79471b79f65a02fb0f6070da7f2800793ff3"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.depthZeroQuotientEquiv",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "53188d24-a433-48be-97a3-09daa3eed9b3",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-11 at Library commit 389dbc16; a definition."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.parahoricReduction_surjective",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "7b678253-77dd-4a91-8615-7cc51b110672",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-11 at Library commit 389dbc16; kind theorem."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.ker_parahoricReduction",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "88746c51-1ff7-436c-a69b-4edebfcd6aba",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-11 at Library commit 389dbc16; kind theorem."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.depthZeroInductionHomEquiv",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "afb645e1-447f-49be-b118-a5666fecdec3",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-11 at Library commit 389dbc16; a definition."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.localFieldDepthZeroInductionHomEquiv",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "2d398beb-702b-4645-8ca5-de7224c60c27",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-11 at Library commit 389dbc16; a definition."
        },
        {
          "declaration": "Langlands.Induction.CompactInductionIntertwiningStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "eff1a598-03ee-41c6-baf2-7df1f52b5294",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-12 at Library commit 9951a27f; kind definition; statement_returns_prop true; the module is byte-identical to commit 79de65ce."
        },
        {
          "declaration": "Langlands.Induction.CompactInductionKernelStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "1e009aa0-8a17-4293-a095-3fc500c1bdc8",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-12 at Library commit 9951a27f; kind definition; statement_returns_prop true; the module is byte-identical to commit 79de65ce."
        },
        {
          "declaration": "Langlands.Induction.CompactInductionDoubleCosetStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "17066c6b-7cc3-4f07-a677-89d4ea9fdc7e",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-12 at Library commit 9951a27f; kind definition; statement_returns_prop true; the module is byte-identical to commit 79de65ce."
        },
        {
          "declaration": "Langlands.Induction.CompactInductionFiniteTypeKernelStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "5ddbd250-3e08-40b9-9d94-d189f87a1c10",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-12 at Library commit 9951a27f; kind definition; statement_returns_prop true; the module is byte-identical to commit 79de65ce."
        },
        {
          "declaration": "Langlands.GroupScheme.finite_rationalPoints",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "6c2b238e-0d3b-4193-a723-112eef8d4bd4",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-13 at Library commit cfedefb6, the commit of first publication; kind theorem."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.finite_quotientPoints_of_isConnectedReductive",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "412a993e-deb0-4e79-a36b-d5246edb8072",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-13 at Library commit cfedefb6, the commit of first publication; kind theorem."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.finiteQuotientGroup",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "23853a2b-429f-4028-86fb-b9b94d3b47c2",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-13 at Library commit cfedefb6, the commit of first publication; kind definition."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.index_positivePoints_subgroupOf",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "d22c4461-d52e-44f0-92e9-5930bba453ea",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-13 at Library commit cfedefb6, the commit of first publication; kind theorem."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.localField_index_positivePoints_subgroupOf",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "15a70f3c-933f-4adf-8b11-3fa3c3e61946",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-13 at Library commit cfedefb6, the commit of first publication; kind theorem."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.localField_isOpen_ker_parahoricReduction",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "4172b54a-3af4-4e68-8673-ff7fe810029f",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-13 at Library commit cfedefb6, the commit of first publication; kind theorem."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.positivePoints_subgroupOf_normal",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "e73183a1-ef20-45c1-acc0-4b418710c766",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-13 at Library commit cfedefb6, the commit of first publication; kind theorem."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.localField_isOpen_positivePoints",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "c4573478-0459-4650-bf41-018dd62458d5",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-13 at Library commit cfedefb6, the commit of first publication; kind theorem."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.localField_isCompact_positivePoints",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "01d008d1-90ea-40de-a6bb-5e60f5272053",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-13 at Library commit cfedefb6, the commit of first publication; kind theorem."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.localFieldPositiveOpenSubgroup",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "ad2fa0d0-0746-4726-987d-03fc6b4f8d1b",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-13 at Library commit cfedefb6, the commit of first publication; kind definition."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.RelativeComponentModelData.localFieldIntegralOpenSubgroup",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "eecf4e21-4859-46bb-93a1-c74122187f4f",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-13 at Library commit cfedefb6, the commit of first publication; kind definition."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.depthZeroInductionKernelEquiv",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "3c59b693-5b75-42a7-92b4-73150c9e53e7",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-13 at Library commit aae8cb82; kind definition; the module is byte-identical to commit 73b1430a, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.depthZeroInductionDoubleCosetEquiv",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "285cd733-608a-40be-ad4b-bb1f92415498",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-13 at Library commit aae8cb82; kind definition; the module is byte-identical to commit 73b1430a, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.depthZeroInductionKernel_finite_doubleCosetSupport",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "512d9f0c-0383-45fb-860d-77ad35bc98ce",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-13 at Library commit aae8cb82; kind theorem; the module is byte-identical to commit 73b1430a, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.localFieldDepthZeroInductionDoubleCosetEquiv",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "c6a34361-e366-4cb0-b30b-d257c30d95c7",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-13 at Library commit aae8cb82; kind definition; the module is byte-identical to commit 73b1430a, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.localField_depthZeroInductionKernel_finite_doubleCosetSupport",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "14fd0811-b236-453b-9019-1362aee7b22a",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-13 at Library commit aae8cb82; kind theorem; the module is byte-identical to commit 73b1430a, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.RelativeComponentModelData.localField_isOpen_congruenceSubgroup",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "7b9777af-f610-46c8-98ff-f5aa5e292035",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-13 at Library commit aae8cb82; kind theorem; the module is byte-identical to commit 73b1430a, its first publication."
        },
        {
          "declaration": "Langlands.Induction.compactInductionKernel",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "e3f69d3c-b197-429d-9d5b-e378816f1317",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-13 at Library commit aae8cb82; kind theorem, proving CompactInductionKernelStatement; the module is byte-identical to commit 730bd1f2, its first publication."
        },
        {
          "declaration": "Langlands.Induction.compactInductionDoubleCoset",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "e7daaa03-c581-4016-9d2d-3a1d6f6d8f3b",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-13 at Library commit aae8cb82; kind theorem, proving CompactInductionDoubleCosetStatement; the module is byte-identical to commit 730bd1f2, its first publication."
        },
        {
          "declaration": "Langlands.Induction.compactInductionFiniteTypeKernel",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "08132623-3964-4a1d-b38b-5d00c54c7c5b",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-13 at Library commit aae8cb82; kind theorem, proving CompactInductionFiniteTypeKernelStatement; the module is byte-identical to commit 730bd1f2, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.multiplicativeModelData",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "be4763c1-1040-4795-a851-d7fe785a1d72",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-14 at Library commit 3489c503; kind definition; the module is byte-identical to commit 85c2fe71, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.multiplicativeQuotientData",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "1f9de37c-e8be-44fe-bf08-71b2b8171ec9",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-14 at Library commit 410c7947; kind definition; the module is byte-identical to commit 85c2fe71, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.multiplicativeQuotientData_isReductiveQuotient",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "75720649-7386-47bd-95d0-47fa7d98cce2",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-14 at Library commit 410c7947; kind theorem; the module is byte-identical to commit 85c2fe71, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.multiplicative_index_positivePoints_subgroupOf",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "ffc38f50-e383-47ed-bb63-9763cffaf600",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-14 at Library commit 410c7947; kind theorem; the module is byte-identical to commit 85c2fe71, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.multiplicative_index_positivePoints_subgroupOf_eq_one",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "7d83750d-7546-432e-b23c-329c39c4a9ba",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-14 at Library commit 410c7947; kind theorem; the module is byte-identical to commit 85c2fe71, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.mem_multiplicative_positivePoints",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "4e1d25b9-683a-46d4-ab89-730d641397a4",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-14 at Library commit 410c7947; kind theorem; the module is byte-identical to commit 85c2fe71, its first publication."
        },
        {
          "declaration": "Langlands.GroupScheme.IntegralModel.splitTorusModel",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "e16bfbe0-ec1c-4ccb-9fb5-c7c2c81fdae5",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-14 at Library commit 410c7947; kind definition; the module is byte-identical to commit 85c2fe71, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.splitTorusModelData",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "db980421-07f9-4905-a8d7-186179e0afbe",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-14 at Library commit 410c7947; kind definition; the module is byte-identical to commit 85c2fe71, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.splitTorusQuotientData",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "54a1b892-f799-414e-b6da-8c43c15992ee",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-14 at Library commit 410c7947; kind definition; the module is byte-identical to commit 85c2fe71, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.splitTorusQuotientData_isReductiveQuotient",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "2859a293-7c34-4a2d-9acb-8bc487c6ce21",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-14 at Library commit 410c7947; kind theorem; the module is byte-identical to commit 85c2fe71, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.splitTorus_index_positivePoints_subgroupOf",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "82dd01af-7220-42e2-bca8-a7335a4f6255",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-14 at Library commit 410c7947; kind theorem; the module is byte-identical to commit 85c2fe71, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.mem_splitTorus_positivePoints",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "81638286-1969-4f4b-ac08-ebbec769dd35",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-14 at Library commit 410c7947; kind theorem; the module is byte-identical to commit 85c2fe71, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.identityQuotient",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "f0425e6c-a6ed-42f1-8efd-82b0713c3c9b",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-14 at Library commit 410c7947; kind definition; the module is byte-identical to commit db8d6b3d, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.identityQuotient_isReductiveQuotient",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "47dc3dab-ffd4-4d6b-81ea-c50800c07b25",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-14 at Library commit 410c7947; kind theorem; the module is byte-identical to commit db8d6b3d, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.identityQuotient_positivePoints",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "2d35e95c-2f74-4480-8503-d4b34208ab90",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-14 at Library commit 410c7947; kind theorem; the module is byte-identical to commit db8d6b3d, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.generalLinearModelData",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "15f82131-c61d-483d-a00b-6f50cead7598",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-14 at Library commit 410c7947; kind definition; the module is byte-identical to commit db8d6b3d, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.generalLinearQuotientData",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "b8d33937-268c-4cb2-9eda-6bfe0804b707",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-14 at Library commit 410c7947; kind definition; the module is byte-identical to commit db8d6b3d, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.generalLinearQuotientData_isReductiveQuotient",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "62d7f150-f817-4616-b816-cfe5b1d919e3",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-14 at Library commit 410c7947; kind theorem; the module is byte-identical to commit db8d6b3d, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.generalLinear_index_positivePoints_subgroupOf_eq_prod",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "22bc7da4-6c4b-44e8-905e-d236f050e2df",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-14 at Library commit 410c7947; kind theorem; the module is byte-identical to commit db8d6b3d, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.generalLinear_integralPoints_map_eq_integralSubgroup",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "db892a1c-f38d-4d7b-9b9e-0d0b95e1c9b7",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-14 at Library commit 410c7947; kind theorem; the module is byte-identical to commit db8d6b3d, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.generalLinear_positivePoints_map_eq_principalLevelSubgroup",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "99e4d7f3-869c-440a-8b2d-f5dbfffa9db1",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-14 at Library commit 410c7947; kind theorem; the module is byte-identical to commit db8d6b3d, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.generalLinear_principalLevelSubgroup_relIndex",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "1b2f2cbf-dda6-446f-89d6-9404a9ce7ffb",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-14 at Library commit 410c7947; kind theorem; the module is byte-identical to commit db8d6b3d, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.symplecticModelData",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "d0b1d2f9-6a74-4050-93a5-d6b848bfad1b",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-14 at Library commit 410c7947; kind definition; the module is byte-identical to commit 410c7947, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.symplecticQuotientData",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "af533c8d-3a88-4847-b681-c8172fd5acca",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-14 at Library commit 410c7947; kind definition; the module is byte-identical to commit 410c7947, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.symplecticQuotientData_isReductiveQuotient",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "a7f86826-f152-4ff3-8b0b-4818ac673400",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-14 at Library commit 410c7947; kind theorem; the module is byte-identical to commit 410c7947, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.symplectic_index_positivePoints_subgroupOf",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "9c06bf9e-706b-49c1-90a8-1527c842821a",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-14 at Library commit 410c7947; kind theorem; the module is byte-identical to commit 410c7947, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.mem_symplectic_positivePoints_iff_generalLinear",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "6f89e650-54b1-407a-a8ad-742643b69b0e",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-14 at Library commit 410c7947; kind theorem; the module is byte-identical to commit 410c7947, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.specialLinearModelData",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "efe77c1c-cf32-4cdd-b65e-46bd91db19be",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-14 at Library commit 410c7947; kind definition; the module is byte-identical to commit 410c7947, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.specialLinearQuotientData",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "0eaf5dd3-fe04-47fc-8f8c-953ab35d93dc",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-14 at Library commit 410c7947; kind definition; the module is byte-identical to commit 410c7947, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.specialLinearQuotientData_isReductiveQuotient",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "c06e564a-d096-4fc1-9d12-c8ce32668680",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-14 at Library commit 410c7947; kind theorem; the module is byte-identical to commit 410c7947, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.specialLinear_index_positivePoints_subgroupOf_mul",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "f664b403-39ac-4c16-a815-b9951be3f15c",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-14 at Library commit 410c7947; kind theorem; the module is byte-identical to commit 410c7947, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.specialLinear_positivePoints_eq_comap_principalLevelSubgroup",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "d0c114cf-a160-4b12-8509-310888cc07bc",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 13 on 2026-11-14 at Library commit 410c7947; kind theorem; the module is byte-identical to commit 410c7947, its first publication."
        }
      ],
      "external_code": []
    },
    {
      "source_item": "Proposition 13.2.5",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.469 / PDF p.500; definitions at PDF pp.497-499; finite-depth clarification from Section 1.6, PDF pp.97-98, and Corollary 7.3.14, PDF p.282; for part (3), Definition 7.3.3 at PDF p.278, Proposition 7.3.12 at PDF p.281, Lemma 7.3.16 at PDF p.283 and Proposition 2.11.3(2) at PDF p.162; for parts (5) and (6), Definition 13.2.4 at PDF pp.499–500, Section 9.7 with (9.7.1) and Corollary 9.7.3 at PDF pp.399–401 and Lemma 6.7.1 at PDF p.264; for the double-root bound used by the proofs of parts (1), (2) and (4), Proposition 7.1.1 and its proof at PDF pp.268 and 270–271, Lemma 7.1.2 and Definition 7.1.3 at PDF pp.271–273, Definitions 7.2.1–7.2.2 and Lemma 7.2.3 at PDF pp.276–277, Lemma 7.3.16 and Proposition 7.3.17 at PDF pp.283–284, Proposition 7.6.4 at PDF p.296 and Lemma 7.7.8 at PDF p.302"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF pp.49-50; independent boundary check at book PDF pp.97-98,282,498,500; root-index cross-check at book PDF pp.230,278,281,500,506; PDF p.33 (added Proposition 7.3.12(6)); PDF pp.33–36 (Chapter 7) and PDF p.41 (Section 9.8), checked for the double-root bound",
        "change": "No replacement of 13.2.5 is listed. The finite-depth restriction on openness is an independently justified clarification, not an authors' erratum. Preserve the separate confirmed printed root-index discrepancy explicitly; the possible indivisible-root/concave-block formulation is source-derived and requires an independent proof, not attribution as an author correction. PDF p.33 adds Proposition 7.3.12(6): for f(0) > 0 and an arbitrary ordering of the roots, the product of the U_{a,x,f} with Z♯_{x,f} is an isomorphism onto G(k)♯_{x,f}. It concerns the root-generated group, not P_{x,r}, and the part (3) statement does not use it. The Chapter 13 entries do not change Definition 13.2.4 or parts (5) and (6). No entry (Chapter 7 at PDF pp.33–36, Section 9.8 at PDF p.41, Chapter 13 at PDF pp.49–50) addresses the double-root bound that the proofs of parts (1), (2) and (4) use; the double-root premise below is source-derived, not an authors' erratum."
      },
      "hypotheses": [
        "k has a normalized discrete valuation omega(k^times)=Z, Henselian integer ring o, maximal ideal m and perfect residue field f. G is a connected reductive k-group. K is a maximal unramified extension, O its integer ring and Gamma=Gal(K/k). x belongs to the actual descended building B(G). No splitness, tameness, finite-residue or perfect-k hypothesis is imposed unless separately stated.",
        "Until Section 13.5, choose any functorial admissible filtration on tori satisfying Section 7.2(1),(2), hence commutator-friendly by 7.2.3; Section 9.8 supplies the centralizer filtration. P_{x,r}=G(k)_{x,r} is generated by the actual root and centralizer filtrations as in 13.2.1 and 7.3.3. The strict-depth convention is X_{r+}=union_{s>r} X_s.",
        "For the bounded-open and Iwahori-decomposition assertions, depths are finite nonnegative augmented depths: r or r+ with r a nonnegative real number, excluding infinity. The covariance, commutator and Levi assertions below are also stated at finite nonnegative depths r,s; the infinite-depth term is recorded separately. For the Levi assertions, P=MN is a parabolic k-subgroup, x is in B(G)_M as in Section 9.7, and x_M is its image in B(M) under (9.7.1).",
        "Recorded Lean scope: MoyPrasadFiltrationStatement (module Langlands.Geometry.Building.KPMoyPrasadFiltrationStatement) is the conjunction of MoyPrasadSeparatedStatement, MoyPrasadBoundedOpenStatement, MoyPrasadCovarianceStatement and MoyPrasadCommutatorStatement. Each quantifies over every nonarchimedean local field F of either characteristic in universe u, every G with [IsAffineHom G.X.hom], supplied P : ParahoricBuildingData G with P.SatisfiesApartmentAxioms (V 6 in the data, V 7 and AS 2–AS 5) and a supplied Zf : P.CentralizerFiltration: subgroups Z(F)_r of Z(F) for real r ≥ 0, decreasing and separated, with Z(F)_0 = Z(F)^0. The premise Zf.SatisfiesFiltrationAxioms requires the commutator clause of Definition 7.2.1 (with the Z-component of Definition 7.1.3), N(F)-stability, [Z(F)_r, Z(F)_s] ⊆ Z(F)_{r+s} and [Z(F)_r, U_{a,x,s}] ⊆ U_{a,x,r+s} U_{2a,x,r+s}. The last three are derived properties of the Section 9.8 filtration, which the Library does not construct. P_{x,r} = Zf.moyPrasad x r, for x in the apartment A(S), is generated by the image of Z(F)_r and the blocks U_{a,x,r} U_{2a,x,r} (Definitions 13.2.1 and 7.3.3); at depth 0 it is the published parahoricAt. The targets are: the infimum over real r ≥ 0 of P_{x,r} is trivial; under the extra premise Zf.IsOpenFiltration (each Z(F)_r open in Z(F)), P_{x,r} is open and algebraically bounded in rationalPointTopology F G.X for every real r ≥ 0; parts (1) and (2) as uniqueness of g P_{x,r} g⁻¹ over all presentations g·x = y of a point y of the reduced building (IsMoyPrasadAt), which gives apartment independence, covariance and normality in the point stabilizer; and part (4) for all real r, s ≥ 0. The strict-depth groups P_{x,r+} are defined (moyPrasadPlus) but appear in no target. MoyPrasadProductStatement (module Langlands.Geometry.Building.KPMoyPrasadProductStatement) states part (3) with indivisible-root blocks under the same premises. For r > 0, a cocharacter ν with IsGenericCocharacter P.i ν, and injective lists aneg and apos whose ranges are RelativeRoot.indivisiblePositiveRoots P.i (-ν) and RelativeRoot.indivisiblePositiveRoots P.i ν, it asserts that Zf.orderedMoyPrasadProduct x r aneg apos is injective with range P_{x,r}. That map multiplies, in the listed orders, one element of each block U_{a,x,r} U_{2a,x,r} for aneg, then the image under j of an element of Z(F)_r, then one element of each block for apos. Its middle factor is the full Z(F)_r, not the Z♯_{x,r} of Proposition 7.3.12(5). MoyPrasadLeviStatement (module Langlands.Geometry.Building.KPMoyPrasadLeviStatement) is the conjunction of MoyPrasadIwahoriDecompositionStatement (part (5)) and MoyPrasadLeviIntersectionStatement (part (6)) under the same premises, for r > 0 and the standard parabolic subgroups containing S: a generic cocharacter ν and J ⊆ simpleRelativeRoots P.i ν give the Levi M_J, the radical N_J and the opposite radical N_J⁻ (standardLeviPoints, standardUnipotentPoints and standardOppositeUnipotentPoints in G(F)). Part (5) asserts that the ordered product (P_{x,r} ∩ N_J⁻(F)) × (P_{x,r} ∩ M_J(F)) × (P_{x,r} ∩ N_J(F)) → P_{x,r} is a homeomorphism (IsTopologicalIwahoriDecomposition) and, for every A and q : A → S with IsCompatibleStandardSplitComponent, WeakChamberContraction for the elements a of A(F) with |α(a)| ≤ 1 on the roots α of N_J (standardComponentNonnegativePart): a (P_{x,r} ∩ N_J(F)) a⁻¹ ⊆ P_{x,r} ∩ N_J(F) and a⁻¹ (P_{x,r} ∩ N_J⁻(F)) a ⊆ P_{x,r} ∩ N_J⁻(F). Part (6) asserts, for the closed Levi Standard.leviScheme, all apartment data DM of (M_J, S) and every point xM with IsLeviRestriction (the map π_S of Section 6.7), that the image of Zf.leviMoyPrasad (generated by the preimage of Z(F)_r and the blocks of DM at xM) is P_{x,r} ∩ M_J(F). Part (6) at r = 0 (Corollary 9.7.3), the groups P_{x,r+}, the building B(M) and the bijection (9.7.1) are not formalized. MoyPrasadDoubleRootStatement (module Langlands.Geometry.Building.KPMoyPrasadDoubleRootStatement) is the conjunction of MoyPrasadDoubleRootCovarianceStatement and MoyPrasadDoubleRootCommutatorStatement: the published covariance and commutator statements with the extra premise Zf.IsDoubleRootCommutatorFriendly. That predicate has the hypotheses of IsCommutatorFriendly together with u ∈ U_{2a}(F) or u' ∈ U_{-2a}(F), and it concludes that the Z-component lies in Z(F)_{2r}, where r = x_a(u) + x_{-a}(u') and IsCommutatorFriendly gives Z(F)_r. It is not a clause of Definition 7.2.1, and for a reduced root system it adds nothing. The source's Henselian discretely valued generality is not formalized; existence of the data is not asserted."
      ],
      "conclusion": "At finite nonnegative augmented depths, the actual P_{x,r} form a decreasing family of bounded open subgroups, independent of the apartment used to define them. Its separated extension has P_{x,infinity}=intersection_{t>=0, t real} P_{x,t}={1}; this term need not be open. For g in G(k), g P_{x,r} g^-1=P_{gx,r}; hence P_{x,r} is normal in the full point stabilizer. The commutator is contained in P_{x,r+s}. At finite r>0, P_{x,r} has the Iwahori decomposition of 13.2.4 relative to P, including a homeomorphism of the three factors, rather than a group direct product. At every finite nonnegative augmented depth, its intersection with M(k) is P^M_{x_M,r}. The finite-depth restriction on openness independently clarifies the printed wording; it is not an authors' correction. Printed part (3), at positive finite depth, claims an arbitrarily ordered root/centralizer product bijection with products over all positive and negative roots. This indexing conflicts with its cited 7.3.12(5), which uses indivisible roots and concave-function blocks. The discrepancy is recorded. The published MoyPrasadProductStatement states the derived indivisible-root block form on supplied data and is proved there (dependencies); this derived form is not an author erratum, and the printed all-root form is not claimed. Parts (5) and (6) are recorded at finite positive real depths for the parabolic subgroups containing S. The printed first inclusion aN^+a^{-1} ⊂ N of Definition 13.2.4(2) is read as aN^+a^{-1} ⊂ N^+, the analogue of the printed second inclusion; this derived reading is not an authors' erratum. The proofs of parts (1), (2) and (4) need, for the mixed pairs (2a, -a) and (a, -2a) of a multipliable root, a bound on the Z-component of a commutator that Definition 7.2.1 does not supply (Bundle E notes). No counterexample to the printed parts (1), (2) and (4), which use KP's filtration of T(k), is known; for supplied filtrations satisfying only the four published axioms, the Lean covariance and commutator statements are refuted on paper, while with the double-root premise they are proved on supplied data (dependencies).",
      "lean_declarations": [
        "Langlands.Geometry.Building.MoyPrasadFiltrationStatement",
        "Langlands.Geometry.Building.MoyPrasadSeparatedStatement",
        "Langlands.Geometry.Building.MoyPrasadBoundedOpenStatement",
        "Langlands.Geometry.Building.MoyPrasadCovarianceStatement",
        "Langlands.Geometry.Building.MoyPrasadCommutatorStatement",
        "Langlands.Geometry.Building.ParahoricBuildingData.CentralizerFiltration.moyPrasad",
        "Langlands.Geometry.Building.MoyPrasadProductStatement",
        "Langlands.Geometry.Building.ParahoricBuildingData.CentralizerFiltration.orderedMoyPrasadProduct",
        "Langlands.Geometry.Building.MoyPrasadLeviStatement",
        "Langlands.Geometry.Building.MoyPrasadIwahoriDecompositionStatement",
        "Langlands.Geometry.Building.MoyPrasadLeviIntersectionStatement",
        "Langlands.Geometry.Building.MoyPrasadDoubleRootStatement",
        "Langlands.Geometry.Building.MoyPrasadDoubleRootCovarianceStatement",
        "Langlands.Geometry.Building.MoyPrasadDoubleRootCommutatorStatement",
        "Langlands.Geometry.Building.ParahoricBuildingData.CentralizerFiltration.IsDoubleRootCommutatorFriendly",
        "Langlands.Geometry.Building.moyPrasadSeparated",
        "Langlands.Geometry.Building.moyPrasadBoundedOpen",
        "Langlands.Geometry.Building.moyPrasadProduct",
        "Langlands.Geometry.Building.moyPrasadLevi",
        "Langlands.Geometry.Building.moyPrasadDoubleRootCovariance",
        "Langlands.Geometry.Building.moyPrasadDoubleRootCommutator"
      ],
      "modules": [
        "Langlands.Geometry.Building.KPMoyPrasadFiltrationStatement",
        "Langlands.Geometry.Building.KPMoyPrasadFiltration",
        "Langlands.Geometry.Building.KPMoyPrasadProductStatement",
        "Langlands.Geometry.Building.KPMoyPrasadLeviStatement",
        "Langlands.Geometry.Building.KPMoyPrasadDoubleRootStatement",
        "Langlands.Geometry.Building.KPMoyPrasadSeparatedProof",
        "Langlands.Geometry.Building.MoyPrasadBoundedOpenProof",
        "Langlands.Geometry.Building.KPMoyPrasadProductProof",
        "Langlands.Geometry.Building.KPMoyPrasadLeviProof",
        "Langlands.Geometry.Building.KPMoyPrasadDoubleRootCovarianceProof",
        "Langlands.Geometry.Building.KPMoyPrasadDoubleRootCommutatorProof",
        "Langlands.Geometry.Building.MoyPrasadCommutatorGenerators"
      ],
      "dependencies": [
        "Section 1.6 at PDF pp.97-98 includes infinity in the augmented index set and defines the separated infinite term as the intersection, equal to {1}. Corollary 7.3.14 at PDF p.282 asserts boundedness generally, but openness only if the concave function never takes infinity. Thus openness is retained only at finite r/r+",
        "Concrete boundary check from (13.1.1), PDF p.498: for G_m over Q_2, the standard and minimal congruent filtrations agree, and P_{x,n}=1+2^n Z_2 for integers n>=1. Their intersection is {1}, which is not open because the distinct elements 1+2^n converge to 1",
        "Propositions 7.3.17 and 7.6.4 give apartment independence; 7.7.8(1) gives conjugation covariance. Root-valuation Axiom V3, 7.1.2, 7.1.3 and commutator-friendliness give the commutator bound. Corollary 9.7.3 gives the depth-zero Levi intersection",
        "The original PDF p.500 was visually checked: the all-root indexing is printed, not lost during extraction. PDF p.281 prints indivisible-root indexing in 7.3.12(5). Root-valuation V4 at PDF p.230 makes scalar factors for a and 2a overlap when U_{2a,x,2r} is nontrivial; taking both as independent coordinates cannot then be injective",
        "Source-derived route to investigate and prove independently: use indivisible roots with the 7.3.3(1) blocks U_{a,x,f}=U_{a,x,f(a)} U_{2a,x,f(2a)}, at constant f=r, together with the full Z(k)_r central factor, 7.3.12(4),(5) and open-cell injectivity. Merely adding indivisible-root indexing to scalar-depth factors need not recover all 2a-depth-r elements in a nonreduced system",
        "Sections 13.2.2-3 retain facet dependence only for 0 and 0+, and the equality P_{x,r}(k)=P_{x,r}(K)^Gamma from 9.8.3(2)",
        "Release 1 constructions, the corrected Theorem 9.2.7 certificate and the inflation/compact-induction consumer remain prerequisites for positive-depth implementation. A source row supplies no release or formal acceptance.",
        "Part (3) statement: its Markdown derives the full-filtration form. Propositions 7.3.12(4),(5) give G(k)♯_{x,r} = X^- Z♯_{x,r} X^+ for the ordered block products X^±; the proof of Lemma 7.3.16 gives Z♯_{x,r} ⊆ Z(k)_r; by V 6, Z(k)_r normalizes every block; Definition 7.3.3(3) gives P_{x,r} = G(k)♯_{x,r} Z(k)_r = X^- Z(k)_r X^+. Injectivity follows from the open cell of Proposition 2.11.3(2) and Proposition 7.3.12(3). KP do not write out this passage.",
        "Parts (5) and (6) statement: its Markdown derives both parts from part (3), following the proof on PDF p.500. Order the indivisible roots so that those of M_J are innermost; part (3) gives P_{x,r} = X^-_N X^-_M Z(k)_r X^+_M X^+_N with unique factors, and the open immersion N_J⁻ × M_J × N_J → G (Proposition 2.11.3(2)) gives the decomposition of part (5) and the intersection of part (6). IsLeviRestriction identifies the root filtrations of M_J at xM with those of G at x (Lemma 6.7.1). Conjugation by a torus element a with ω(α(a)) ≥ 0 on the roots of N_J raises their depths, which gives the contraction.",
        "Double-root premise: for u ∈ U_{2a,x,r} and u' ∈ U_{-a,x,s}, Lemma 7.1.2(2) places the root factors of the commutator in P_{x,r+s}, but Definition 7.2.1 places its Z-component only in Z(k)_{r/2+s}, while P_{x,r+s} ∩ Z(k) = Z(k)_{r+s} (Lemma 7.3.16). In the proof of Proposition 7.3.17, V 3 excludes the pair u ∈ U_{a,x,0}, v ∈ U_{-2a,x,r}, where Definition 7.2.1 gives Z(k)_{r/2} and Z(k)_r is needed. The SU_3 formula in the proof of Proposition 7.1.1 gives γ − 1 = ββ' when u ∈ U_{2a}(k), of valuation 2(φ_a(u) + φ_{-a}(u')), which closes both gaps. The statement's Markdown derives the bound for the actual Section 9.8 filtration (Lemma 9.8.1 row).",
        "Proof successors (lean.proof@1, one per conjunct): MoyPrasadSeparatedStatement Task 5509 (090acae8-2f81-4ccd-bd05-3635b01f3955); MoyPrasadBoundedOpenStatement Task 5510 (c593d9f7-612c-43ae-aa67-342ceb78f1d5); MoyPrasadCovarianceStatement Task 5511 (be16ead9-93f4-432a-a7e0-44077e469d85); MoyPrasadCommutatorStatement Task 5512 (05aa82d6-2f2e-4113-908c-edc4ea226133). The conjunction needs no further mathematics once the four are proved. Part (3), MoyPrasadProductStatement, has proof successor Task 5579 (f97b9951-9063-4099-b8dd-b986fd1f7205). Parts (5) and (6), MoyPrasadLeviStatement, have proof successor Task 5620 (435ee887-a640-423a-bc30-8ad182e6ba9e). The double-root statements have proof successors Task 5645 (03d53828-0d05-4e3f-960c-dd74256072e0) (MoyPrasadDoubleRootCovarianceStatement) and Task 5646 (a5f35e49-1e6a-4f03-8986-d7b2db8ac2b0) (MoyPrasadDoubleRootCommutatorStatement); Tasks 5511 and 5512 keep their original targets. Worker 164's published iInf_moyPrasad_eq_bot, orderedMoyPrasadProduct_injective and range_orderedMoyPrasadProduct_eq (Library commit cd03c104) take only the apartment axioms and IsCommutatorFriendly; the contexts of Task 5509 (090acae8-2f81-4ccd-bd05-3635b01f3955) and Task 5579 (f97b9951-9063-4099-b8dd-b986fd1f7205) name them. Worker 164's published isMoyPrasadAt_unique_of_double_opposite_bound (module Langlands.Geometry.Building.MoyPrasadCovarianceReduction, Library commit 297a8ef0) derives the conclusion of MoyPrasadCovarianceStatement from the apartment axioms, SatisfiesFiltrationAxioms and one further hypothesis: conjugation of U_{-2a,x,r} by U_{a,x,0} stays in P_{x,r}. conjugate_double_opposite_mem_moyPrasad_of_central_bound (module Langlands.Geometry.Building.MoyPrasadMixedConjugation, same commit) reduces that hypothesis to a bound on the Z-component, the bound that IsDoubleRootCommutatorFriendly supplies. The revision-2 contexts of Tasks 5511, 5512 and 5552 record the gap and name these reductions. Every target of these tasks except those of Tasks 5511 and 5512 is now proved (the two entries on proved conjuncts and proved parts below).",
        "Proved conjuncts (13 November 2026): moyPrasadSeparated (module KPMoyPrasadSeparatedProof) proves MoyPrasadSeparatedStatement by applying iInf_moyPrasad_eq_bot to the first clause IsCommutatorFriendly of SatisfiesFiltrationAxioms; moyPrasadBoundedOpen (module MoyPrasadBoundedOpenProof) proves MoyPrasadBoundedOpenStatement from isOpen_moyPrasad (V 7 and IsOpenFiltration, through the proved Corollary 8.2.6) and the published boundedness lemma of MoyPrasadTopology. Both are present in Library commit 17dd94ea3f677b20fb5ab95b285cbc3fd7cde03e; lean_check inspections 54e0e341-0770-4111-9de1-127db8463b78 and 89bac559-e4ff-4298-8592-d29da6b62a02 by Worker 3557 at Library commit 8ff9abe9 report kind theorem and only propext, Classical.choice and Quot.sound. Their acceptance artifacts are b3a63c1d-20ec-4d2e-9609-35c2c66d8087 (proof Task 5509, 090acae8-2f81-4ccd-bd05-3635b01f3955) and 929eebf9-0e81-463f-834a-ff086be83925 (proof Task 5510, c593d9f7-612c-43ae-aa67-342ceb78f1d5); both modules are first in Library commit 17dd94ea.",
        "Proved parts (13 November 2026): the theorem moyPrasadProduct (module KPMoyPrasadProductProof; proof Task 5579, f97b9951-9063-4099-b8dd-b986fd1f7205; artifact 83e1844b-0b02-449f-b4bd-354ad0c47926, first in Library commit cfedefb680f317b0ea5d351023e1c9dd886b2547) proves MoyPrasadProductStatement by combining Worker 164's orderedMoyPrasadProduct_injective and range_orderedMoyPrasadProduct_eq; of SatisfiesFiltrationAxioms it uses only the first clause IsCommutatorFriendly. The theorem moyPrasadLevi (module KPMoyPrasadLeviProof; proof Task 5620, 435ee887-a640-423a-bc30-8ad182e6ba9e; artifact 2828d56d-f6c0-44e3-9917-a1c3bfec0d29, first in Library commit cc5aa77fa8dbdc6e723091c7b710ab0d81162c4e) proves MoyPrasadLeviStatement by pairing the theorems moyPrasadIwahoriDecomposition and moyPrasadLeviIntersection of the same module. It takes the ordered covering of P_{x,r} from range_orderedMoyPrasadProduct_eq, not from MoyPrasadProductStatement, and the homeomorphism from the open cell on rational points. The theorem moyPrasadDoubleRootCovariance (module KPMoyPrasadDoubleRootCovarianceProof; proof Task 5645, 03d53828-0d05-4e3f-960c-dd74256072e0; artifact af35972d-1995-402a-849e-649029adc21d, first in Library commit cfedefb680f317b0ea5d351023e1c9dd886b2547) proves MoyPrasadDoubleRootCovarianceStatement by applying isMoyPrasadAt_unique_of_doubleRootCommutatorFriendly (module MoyPrasadDoubleRootConjugation). The theorem moyPrasadDoubleRootCommutator (module KPMoyPrasadDoubleRootCommutatorProof; proof Task 5646, a5f35e49-1e6a-4f03-8986-d7b2db8ac2b0; artifact 571e0374-6bb2-407d-9344-c067e9663d8a, same commit) proves MoyPrasadDoubleRootCommutatorStatement by applying commutator_moyPrasad_le from the module MoyPrasadCommutatorGenerators of the same unit. No published theorem has MoyPrasadDoubleRootStatement, the conjunction of the two double-root statements, as its type; it follows from the two proofs by pairing. Every one of these theorems keeps the supplied P and Zf and their premises, so the row is conditional: the building data and the Section 9.8 filtration are not constructed, and CentralizerFiltrationDoubleRootExistenceStatement (Lemma 9.8.1 row) is not proved. MoyPrasadCovarianceStatement, MoyPrasadCommutatorStatement and MoyPrasadFiltrationStatement, the conjunction of the four original statements, are not proved; the next entry refutes them on paper. lean_check inspections of the four theorems are listed in the axiom reports.",
        "Supplied-filtration counterexample (unformalized paper argument by Worker 46, Task 5512, accepted by Worker 3557 as publisher of the targets): take ramified quasi-split SU(3) over Q_2 split by E = Q_2(√2), assume its actual building data realized as P with P.SatisfiesApartmentAxioms, and let Z' be the smallest centralizer filtration (decreasing, separated, Z'_0 = Z(F)^0) satisfying the four clauses of SatisfiesFiltrationAxioms. Then u(0,√2) ∈ U_{2a,x,1/2} and u⁻(2,−2) ∈ U_{−a,x,1/2} have a commutator whose Z-component t(1−2√2) is not in Z'_1, refuting MoyPrasadCommutatorStatement. With u'' = u⁻(√2,1) ∈ U_{−a,x,0}, which fixes x, the conjugate u''⁻¹ u(0,√2) u'' has Z-component t(1+√2) ∉ Z'_{1/2}, so it is not in P'_{x,1/2}; then P'_{x,1/2} and u'' P'_{x,1/2} u''⁻¹ are distinct subgroups that are both Moy–Prasad at x of depth 1/2, refuting MoyPrasadCovarianceStatement and hence MoyPrasadFiltrationStatement. The same pair violates the hypothesis hmixed of sharpFixer_le_normalizer_moyPrasad_of_double_opposite_bound (module MoyPrasadCovarianceReduction) at the root −a with r = 1/2. Z' violates IsDoubleRootCommutatorFriendly, so MoyPrasadDoubleRootCovarianceStatement and MoyPrasadDoubleRootCommutatorStatement are unaffected, and KP's chosen filtration is not refuted (for odd p the forced filtration agrees with the actual one). The argument is Worker 46's public note notes/bruhat-tits/moy-prasad-supplied-filtration-counterexample.md, accepted as candidate 43e8ac40-28a7-4c42-b8e3-cabf65c0f775 (a revision of 447c3e46-de0d-4ae6-be23-9028bf810439, which was returned for two local valuation corrections) and present in Library commit 4b619cdd61c537ff5ee2587fda415e0adb66e5ef. It is an unformalized paper argument; no Lean declaration refutes either statement. The Markdown of KPMoyPrasadFiltrationStatement, KPMoyPrasadDoubleRootStatement, CentralizerFiltrationExistenceStatement and KPMoyPrasadFiltration records this status (Markdown-only candidate 594d4499-20f8-4efd-bd83-79c7e62a2057, present in Library commit cc5aa77fa8dbdc6e723091c7b710ab0d81162c4e; the Lean files are unchanged). Consequently Tasks 5511 and 5512 retire without proofs, the two refuted statements stay published as recorded targets, and the double-root variants (Tasks 5645 and 5646) carry the covariance and commutator content."
      ],
      "consumer_or_regression": "Regression: a nonsplit group with a multipliable root must detect overlapping a/2a scalar factors and test the separately proved block formulation. Check finite r/r+ openness separately from the non-open infinite term for G_m(Q_2), point variation inside a facet, full-stabilizer normality and the actual Levi embedding. Boundedness alone is not compactness over general Henselian k. For the part (3) central factor: for G = G_m there are no roots, so G(k)♯_{x,r} = Z♯_{x,r} = {1}, while Z(k)_r = P_{x,r} is a nontrivial congruence subgroup; the middle factor must be the full filtration. Consumer: the positive-depth Iwahori factorization of Task 5310; the published regrouping in Langlands.BruhatTits.SpecialCompact.MoyPrasadParabolicProduct takes ordered-root covering as a hypothesis. Parts (5) and (6): consumer is the positive-depth Iwahori decomposition (HasIwahoriIntersectionDecomposition and WeakChamberContraction) of Task 5310. Double-root regression: for the unramified quasi-split SU_3 (relative root system BC_1) and u ∈ U_{2a}(k), the Z-component of (u, u') has depth 2(φ_a(u) + φ_{-a}(u')), twice the bound of Definition 7.2.1; for a reduced root system the premise IsDoubleRootCommutatorFriendly is implied by IsCommutatorFriendly.",
      "formal_status": "conditional",
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [
        "cdc002e4-4628-4026-91c9-c4add6280308",
        "38dd6045-a386-43d6-a804-1de56fa51d14",
        "abed4e85-f69b-404f-ab1b-76a194d2d0d0",
        "a10cf7b9-8244-4125-94c1-9eb4aa404e35",
        "b3a63c1d-20ec-4d2e-9609-35c2c66d8087",
        "929eebf9-0e81-463f-834a-ff086be83925",
        "83e1844b-0b02-449f-b4bd-354ad0c47926",
        "2828d56d-f6c0-44e3-9917-a1c3bfec0d29",
        "af35972d-1995-402a-849e-649029adc21d",
        "571e0374-6bb2-407d-9344-c067e9663d8a"
      ],
      "publication_commits": [
        "642008d6b3b837d8bd76de0cabcaff3db00088c0",
        "63d9b857523edf47443b7bf30844159e526d00b0",
        "6bff2655fd831aefb39f6688f904aa7410cb0f73",
        "297a8ef0ba780a488196cf62285af3ded2e2baa6",
        "17dd94ea3f677b20fb5ab95b285cbc3fd7cde03e",
        "cfedefb680f317b0ea5d351023e1c9dd886b2547",
        "cc5aa77fa8dbdc6e723091c7b710ab0d81162c4e"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.MoyPrasadFiltrationStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "9a180d66-df7e-4542-8e21-b30150eefa49",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-11 at Library commit 389dbc16; kind definition; statement_returns_prop true; the workspace held the published pair, byte-identical to commit 642008d6."
        },
        {
          "declaration": "Langlands.Geometry.Building.MoyPrasadSeparatedStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "8e86b600-e51e-47fc-b72c-b94544a64953",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-11 at Library commit 389dbc16; kind definition; statement_returns_prop true; the workspace held the published pair, byte-identical to commit 642008d6."
        },
        {
          "declaration": "Langlands.Geometry.Building.MoyPrasadBoundedOpenStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "abc1e040-ffe6-4ba1-9178-06c6215825a6",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-11 at Library commit 389dbc16; kind definition; statement_returns_prop true; the workspace held the published pair, byte-identical to commit 642008d6."
        },
        {
          "declaration": "Langlands.Geometry.Building.MoyPrasadCovarianceStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "8123c1c7-7dea-4741-bbaf-a847c2e7e145",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-11 at Library commit 389dbc16; kind definition; statement_returns_prop true; the workspace held the published pair, byte-identical to commit 642008d6."
        },
        {
          "declaration": "Langlands.Geometry.Building.MoyPrasadCommutatorStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "7fcfefb0-358d-44f2-9203-aa5abf90624e",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-11 at Library commit 389dbc16; kind definition; statement_returns_prop true; the workspace held the published pair, byte-identical to commit 642008d6."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.CentralizerFiltration.moyPrasad",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "89ea7251-b4db-4244-ab30-50b9de9bfa9b",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-11 at Library commit 389dbc16; a definition; the workspace held the published pair, byte-identical to commit 642008d6."
        },
        {
          "declaration": "Langlands.Geometry.Building.MoyPrasadProductStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "492a6aaa-a334-4d9d-a277-5f02a15cc85a",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-11 at Library commit 8964b41f; kind definition; statement_returns_prop true; the module is byte-identical to commit 63d9b857."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.CentralizerFiltration.orderedMoyPrasadProduct",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "859f7975-7f9e-40ee-8946-114688418ee1",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-11 at Library commit 8964b41f; kind definition; statement_returns_prop false; the module is byte-identical to commit 63d9b857."
        },
        {
          "declaration": "Langlands.Geometry.Building.MoyPrasadLeviStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "24c668eb-26b2-4477-8d60-4f1e24381c57",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-12 at Library commit 4ed6d979; kind definition; statement_returns_prop true; the module is byte-identical to commit 6bff2655."
        },
        {
          "declaration": "Langlands.Geometry.Building.MoyPrasadIwahoriDecompositionStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "b79a830a-7ce0-43c9-9ad9-4f934ddf4cd7",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-12 at Library commit 14c08c22; kind definition; statement_returns_prop true; the module is byte-identical to commit 6bff2655."
        },
        {
          "declaration": "Langlands.Geometry.Building.MoyPrasadLeviIntersectionStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "4ec65faa-1a1a-4287-8751-13a2d5d0358c",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-12 at Library commit 14c08c22; kind definition; statement_returns_prop true; the module is byte-identical to commit 6bff2655."
        },
        {
          "declaration": "Langlands.Geometry.Building.MoyPrasadDoubleRootStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "cc0fde32-2c9a-4be7-97c7-142c73686755",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-12 at Library commit 16c60abd; kind definition; statement_returns_prop true; the module is byte-identical to commit 297a8ef0."
        },
        {
          "declaration": "Langlands.Geometry.Building.MoyPrasadDoubleRootCovarianceStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "2dca5e2f-984e-412c-93c1-931a862b9043",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-12 at Library commit 16c60abd; kind definition; statement_returns_prop true; the module is byte-identical to commit 297a8ef0."
        },
        {
          "declaration": "Langlands.Geometry.Building.MoyPrasadDoubleRootCommutatorStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "d4e52265-fc85-4249-85b4-bff39874f87f",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-12 at Library commit 16c60abd; kind definition; statement_returns_prop true; the module is byte-identical to commit 297a8ef0."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.CentralizerFiltration.IsDoubleRootCommutatorFriendly",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "2c8fd78b-88e4-4db1-aae8-e3dfff48a16a",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-12 at Library commit 16c60abd; kind definition; statement_returns_prop true (a Prop-valued predicate); the module is byte-identical to commit 297a8ef0."
        },
        {
          "declaration": "Langlands.Geometry.Building.moyPrasadSeparated",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "54e0e341-0770-4111-9de1-127db8463b78",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit 8ff9abe9; a theorem proving MoyPrasadSeparatedStatement. Its acceptance artifact is b3a63c1d-20ec-4d2e-9609-35c2c66d8087, first in Library commit 17dd94ea."
        },
        {
          "declaration": "Langlands.Geometry.Building.moyPrasadBoundedOpen",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "89bac559-e4ff-4298-8592-d29da6b62a02",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit 8ff9abe9; a theorem proving MoyPrasadBoundedOpenStatement. Its acceptance artifact is 929eebf9-0e81-463f-834a-ff086be83925, first in Library commit 17dd94ea."
        },
        {
          "declaration": "Langlands.Geometry.Building.moyPrasadProduct",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "221e97a7-3d7f-4778-8a42-c0c427ed4eb6",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit 0f84a0d8; kind theorem, proving MoyPrasadProductStatement; the module is byte-identical to commit cfedefb6."
        },
        {
          "declaration": "Langlands.Geometry.Building.moyPrasadLevi",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "b30aa9c9-30dc-411c-9927-d390231cbbc1",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit 0f84a0d8; kind theorem, proving MoyPrasadLeviStatement; the module is byte-identical to commit cc5aa77f."
        },
        {
          "declaration": "Langlands.Geometry.Building.moyPrasadDoubleRootCovariance",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "34125b10-f07f-481c-9b45-40f41c0a1130",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit 0f84a0d8; kind theorem, proving MoyPrasadDoubleRootCovarianceStatement; the module is byte-identical to commit cfedefb6."
        },
        {
          "declaration": "Langlands.Geometry.Building.moyPrasadDoubleRootCommutator",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "dbcec8e4-d925-41fd-a728-d7d9b29c1c91",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit 0f84a0d8; kind theorem, proving MoyPrasadDoubleRootCommutatorStatement; the module is byte-identical to commit cfedefb6."
        }
      ],
      "external_code": []
    },
    {
      "source_item": "Section 13.3.1",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.470 / PDF p.501"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF pp.49-50, Chapter 13 and Appendix B.10",
        "change": "No direct replacement of 13.3.1 is listed. If the minimal congruent torus filtration is used, include its corrected Gamma-invariance and descent from Appendix B.10."
      },
      "hypotheses": [
        "k has a normalized discrete valuation omega(k^times)=Z, Henselian integer ring o, maximal ideal m and perfect residue field f. G is a connected reductive k-group. K is a maximal unramified extension, O its integer ring and Gamma=Gal(K/k). x belongs to the actual descended building B(G). No splitness, tameness, finite-residue or perfect-k hypothesis is imposed unless separately stated.",
        "Until Section 13.5, choose any functorial admissible filtration on tori satisfying Section 7.2(1),(2), hence commutator-friendly by 7.2.3; Section 9.8 supplies the centralizer filtration. P_{x,r}=G(k)_{x,r} is generated by the actual root and centralizer filtrations as in 13.2.1 and 7.3.3. The strict-depth convention is X_{r+}=union_{s>r} X_s.",
        "The smooth congruence models and their morphisms come from Section 8.5, with the actual Chapter 9 descent over o. Parahorics, full stabilizers, the whole special fibre H_x and its maximal reductive quotient Gred_x retain distinct meanings. Chapter 8 models over O alone do not supply the descended construction."
      ],
      "conclusion": "For r>=0, g_{x,r}=Lie(G_{x,r}) is an o-lattice in g(k). The identity g_{x,r+n}=m^n g_{x,r} for nonnegative integers n extends the definition consistently to every real depth. The resulting open additive subgroups form a separated descending filtration, with g_{x,r+}=union_{s>r} g_{x,s}. The dual lattice is exactly g^*_{x,r}={X in g^* : X(Y) in m for every Y in g_{x,(-r)+}}. The maximal ideal m, the minus sign and the strict plus in this annihilator convention are retained.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Section 8.5 constructs the actual constant-concave-function models; Proposition 8.5.16 proves their Lie-lattice periodicity",
        "The smooth congruence models and their morphisms come from Section 8.5, with the actual Chapter 9 descent over o. Parahorics, full stabilizers, the whole special fibre H_x and its maximal reductive quotient Gred_x retain distinct meanings. Chapter 8 models over O alone do not supply the descended construction.",
        "Section 1.6 supplies the real-depth-plus convention; well-defined extension to negative depths is a proof obligation, not a separately assumed lattice family",
        "Release 1 constructions, the corrected Theorem 9.2.7 certificate and the inflation/compact-induction consumer remain prerequisites for positive-depth implementation. A source row supplies no release or formal acceptance."
      ],
      "consumer_or_regression": "Check positive and negative integer shifts and the exact dual annihilator pairing in equal and mixed characteristic. The general lattice construction requires no quasi-splitness of G.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Section 13.3.2",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.470 / PDF p.501"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.49, Chapter 13",
        "change": "No direct replacement of 13.3.2 is listed; the corrected Chapter 8-9 constructions remain part of its dependency closure."
      },
      "hypotheses": [
        "k has a normalized discrete valuation omega(k^times)=Z, Henselian integer ring o, maximal ideal m and perfect residue field f. G is a connected reductive k-group. K is a maximal unramified extension, O its integer ring and Gamma=Gal(K/k). x belongs to the actual descended building B(G). No splitness, tameness, finite-residue or perfect-k hypothesis is imposed unless separately stated.",
        "Until Section 13.5, choose any functorial admissible filtration on tori satisfying Section 7.2(1),(2), hence commutator-friendly by 7.2.3; Section 9.8 supplies the centralizer filtration. P_{x,r}=G(k)_{x,r} is generated by the actual root and centralizer filtrations as in 13.2.1 and 7.3.3. The strict-depth convention is X_{r+}=union_{s>r} X_s.",
        "The smooth congruence models and their morphisms come from Section 8.5, with the actual Chapter 9 descent over o. Parahorics, full stabilizers, the whole special fibre H_x and its maximal reductive quotient Gred_x retain distinct meanings. Chapter 8 models over O alone do not supply the descended construction.",
        "Gred_x is the maximal reductive quotient of H_x, the special fibre of the connected parahoric model. The Lie lattices and their 0+ term are the constructions of 13.3.1."
      ],
      "conclusion": "There is an identification of f-Lie algebras Lie(Gred_x)=cok(g_{x,0+} tensor_o f to g_{x,0} tensor_o f)=g_{x,0}/g_{x,0+}. It uses m g_{x,0} contained in g_{x,0+} contained in g_{x,0}; it identifies the maximal reductive quotient's Lie algebra, rather than the Lie algebra of the whole special fibre.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Section 13.2.6 identifies Gred_x with the group-scheme cokernel of the special-fibre morphism G_{x,0+} to G_{x,0}",
        "Proposition 8.5.18 proves smoothness of that morphism's kernel; Section 2.4(a) then supplies exactness on Lie algebras",
        "Use the actual descended models and Lie maps, not an arbitrary quotient equipped with an assumed identification",
        "Release 1 constructions, the corrected Theorem 9.2.7 certificate and the inflation/compact-induction consumer remain prerequisites for positive-depth implementation. A source row supplies no release or formal acceptance."
      ],
      "consumer_or_regression": "Depth-zero Lie comparison and graded-action tests. Keep distinct the rational-point quotient of 13.2.6 and this Lie-algebra cokernel calculation; neither alone proves the other.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Section 13.3.3",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.470-471 / PDF pp.501-502; Section 8.5.20 for the basis formula"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.49, Chapter 13; corrected Chapter 9 setup at PDF pp.39-41",
        "change": "No direct replacement of 13.3.3 is listed. Use corrected Chapter 9 descent rather than treating a K-basis calculation as a general formula over k."
      },
      "hypotheses": [
        "k has a normalized discrete valuation omega(k^times)=Z, Henselian integer ring o, maximal ideal m and perfect residue field f. G is a connected reductive k-group. K is a maximal unramified extension, O its integer ring and Gamma=Gal(K/k). x belongs to the actual descended building B(G). No splitness, tameness, finite-residue or perfect-k hypothesis is imposed unless separately stated.",
        "Until Section 13.5, choose any functorial admissible filtration on tori satisfying Section 7.2(1),(2), hence commutator-friendly by 7.2.3; Section 9.8 supplies the centralizer filtration. P_{x,r}=G(k)_{x,r} is generated by the actual root and centralizer filtrations as in 13.2.1 and 7.3.3. The strict-depth convention is X_{r+}=union_{s>r} X_s.",
        "The smooth congruence models and their morphisms come from Section 8.5, with the actual Chapter 9 descent over o. Parahorics, full stabilizers, the whole special fibre H_x and its maximal reductive quotient Gred_x retain distinct meanings. Chapter 8 models over O alone do not supply the descended construction.",
        "r is real."
      ],
      "conclusion": "Let g(K)_{x,r} be the O-Lie lattice of the base-changed actual model. Then g_{x,r}=g(K)_{x,r}^Gamma. The Chevalley-Steinberg basis formula of 8.5.20 describes the O-lattice over K and works over o when G is quasi-split. There is also an intrinsic description over o: choose a maximal k-split S with x in its apartment; let z_r be the Lie lattice of the S-fixed subgroup scheme of G_{x,r}, with generic fibre Z_G(S). For an affine root psi, let u_psi=Lie(U_psi)=g_z intersect u_a(k), for any z on H_psi and a the derivative of psi. Then g_{x,r} is the o-span of z_r and the u_psi for psi(x)>=r. The quasi-split hypothesis belongs to the explicit basis formula over o, not to the general lattice or its intrinsic span description.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Section 8.5.20 gives the explicit Chevalley-Steinberg lattice over O; the actual model descent gives the invariant lattice",
        "Section 9.4.5 constructs U_psi; Proposition 9.8.3 supplies the standard integral S-model action and its centralizer filtration. Section 13.2.1 defines Psi_{x,r} by psi(x)>=r",
        "The model construction and the root-space span formula must be proved for the constructed objects; a chosen basis or an assumed Gamma-invariant lattice is insufficient",
        "Release 1 constructions, the corrected Theorem 9.2.7 certificate and the inflation/compact-induction consumer remain prerequisites for positive-depth implementation. A source row supplies no release or formal acceptance."
      ],
      "consumer_or_regression": "Compare split basis calculations with a non-quasi-split descended lattice and a multipliable-root case. Retain the actual maximal split torus, centralizer and affine-root valuation conventions.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Section 13.3.4",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.471 / PDF p.502"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.49, Chapter 13",
        "change": "No direct replacement of 13.3.4 is listed. Keep the action over the residue field f and the special-fibre/reductive-quotient distinction explicit."
      },
      "hypotheses": [
        "k has a normalized discrete valuation omega(k^times)=Z, Henselian integer ring o, maximal ideal m and perfect residue field f. G is a connected reductive k-group. K is a maximal unramified extension, O its integer ring and Gamma=Gal(K/k). x belongs to the actual descended building B(G). No splitness, tameness, finite-residue or perfect-k hypothesis is imposed unless separately stated.",
        "Until Section 13.5, choose any functorial admissible filtration on tori satisfying Section 7.2(1),(2), hence commutator-friendly by 7.2.3; Section 9.8 supplies the centralizer filtration. P_{x,r}=G(k)_{x,r} is generated by the actual root and centralizer filtrations as in 13.2.1 and 7.3.3. The strict-depth convention is X_{r+}=union_{s>r} X_s.",
        "The smooth congruence models and their morphisms come from Section 8.5, with the actual Chapter 9 descent over o. Parahorics, full stabilizers, the whole special fibre H_x and its maximal reductive quotient Gred_x retain distinct meanings. Chapter 8 models over O alone do not supply the descended construction.",
        "r is real. Gred_x is the actual maximal reductive quotient of the parahoric special fibre; both Lie and dual lattices use Section 13.3.1's conventions."
      ],
      "conclusion": "Conjugation by the connected parahoric model induces actions on the Lie and dual lattices. On their strict graded pieces g_{x,r}/g_{x,r+} and g^*_{x,r}/g^*_{x,r+}, these induce genuine f-rational representations of Gred_x. Factorization through the reductive quotient and preservation of the lattices are part of the conclusion, not structure fields to assume.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Proposition 13.2.5 gives normality over K; Corollary 2.10.10 extends the actual conjugation action to integral models",
        "Apply the Lie functor, dual action and reduction, with periodicity for all real depths, then prove the action factors through Gred_x on both strict graded pieces",
        "Sections 13.3.1-3 and the actual Chapter 9 model descent",
        "Release 1 constructions, the corrected Theorem 9.2.7 certificate and the inflation/compact-induction consumer remain prerequisites for positive-depth implementation. A source row supplies no release or formal acceptance."
      ],
      "consumer_or_regression": "Graded adjoint/coadjoint action and pairing-equivariance tests; this rational reductive-quotient action is the one used for later algebraic instability, not a valuation-topology orbit action.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Theorem 13.5.1",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.474-476 / PDF pp.505-507"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.50, Appendix B.10: Definition B.10.8, Corollary B.10.14 and added Remark B.10.15",
        "change": "No direct replacement of 13.5.1 is listed. Clarify that R in B.10.8(2) is an induced K-torus; add T(k)^mc_r=T(K)^mc_r intersect T(k); repair the recall in B.10.14; add Gamma-stability and smooth O-model descent in Remark B.10.15. These affect the torus dependency boundary."
      },
      "hypotheses": [
        "k has a normalized discrete valuation omega(k^times)=Z, Henselian integer ring o, maximal ideal m and perfect residue field f. G is a connected reductive k-group. K is a maximal unramified extension, O its integer ring and Gamma=Gal(K/k). x belongs to the actual descended building B(G). No splitness, tameness, finite-residue or perfect-k hypothesis is imposed unless separately stated.",
        "Equip the category of tori specifically with the minimal congruent filtration. Fix real 0<r<=s and x in B(G). At least one of the following three alternatives holds.",
        "(1) A maximally split maximal torus of G_K becomes induced after a tame base change (weakly induced, B.6.2), and s<=2r.",
        "(2) r=r0+n with 0<=r0<1, n a positive integer and s<=r0+2n.",
        "(3) 0<r<=s<=2r<=r+1."
      ],
      "conclusion": "There exists an isomorphism of abstract abelian groups MP_{x,r,s}:P_{x,r}/P_{x,s} to g_{x,r}/g_{x,s}, compatible with unramified algebraic extensions of k. Under alternative (1) or (2), it can be chosen so that, for every k-rational automorphism theta of G, dtheta composed with MP_{x,r,s} composed with theta^-1 equals MP_{theta(x),r,s}. The theorem does not assert this general automorphism equivariance under (3) alone. When (1) and (2) both hold, their constructions coincide. This is not an unconditional exponential map or a k-linear group map.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Alternative (2): Proposition A.5.19 on the actual congruence models and its functoriality for their morphisms",
        "Alternatives (1)/(3) over K: indivisible-root quotient products, C.5.1 root-model congruence and A.5.19; torus comparison B.6.9 under (1), and possibly nonfunctorial B.10.17 under (3). Resolve 13.2.5's indexing against its cited 7.3.3/7.3.12 construction before relying on it",
        "Descent: Lemma 8.1.4, smooth connected unipotent special fibres from 8.5.14 and perfect-residue H^1 vanishing from 2.4.2, for both group and Lie lattices",
        "Agreement under (1)/(2): A.5.19 functoriality and B.10.16 compatibility of the torus comparisons",
        "Corrected B.10.8 and added B.10.15 establish the minimal congruent torus filtration over k, Gamma-stability and smooth model descent. Functoriality of the filtration does not imply unrestricted functoriality of its Moy-Prasad isomorphisms at every positive depth",
        "Release 1 constructions, the corrected Theorem 9.2.7 certificate and the inflation/compact-induction consumer remain prerequisites for positive-depth implementation. A source row supplies no release or formal acceptance."
      ],
      "consumer_or_regression": "Positive-depth acceptance requires actual finite abelian graded quotients over local fields, character transport through this proved map and a nontrivial calculation. Test each applicable alternative separately and the (1)/(2) overlap; do not impose a global tame or large-residue-characteristic hypothesis.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Proposition 13.5.2",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.476-477 / PDF pp.507-508; corrections PDF p.49"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.49, Chapter 13, Proposition 13.5.2(1)",
        "change": "Replace G(k) with G(k)^0 in part (1); retain the same ambient group already present in part (2)."
      },
      "hypotheses": [
        "k has a normalized discrete valuation omega(k^times)=Z, Henselian integer ring o, maximal ideal m and perfect residue field f. G is a connected reductive k-group. K is a maximal unramified extension, O its integer ring and Gamma=Gal(K/k). x belongs to the actual descended building B(G). No splitness, tameness, finite-residue or perfect-k hypothesis is imposed unless separately stated.",
        "Additionally k is a local field: complete with finite residue field f of characteristic p. Use the actual parahoric subgroups, positive-depth filtrations and the point topology of G(k). Maximality and the normalizer below are taken in G(k)^0.",
        "Recorded Lean scope: Langlands.BruhatTits.MaximalProP.AvailableMaximalProPStatement (module Langlands.BruhatTits.MaximalProP.AvailableStatement) quantifies over every nonarchimedean local field F of either characteristic in universe u, every connected reductive group scheme G over Spec F and every KPBuildingAssignment 𝔅 with 𝔅.IsAvailableFor F G hG, and asserts MaximalProPConclusions (𝔅.datum F G hG). The four conclusions are stated for facets of B(G) rather than points: P_{x,0+} is facetPositiveSubgroup D Fa for the facet Fa containing x, the points of the integral sections of the neutral facet model whose reduction lies in the residue-field points of the supplied radical of its special fibre (Axiom 4.1.22(7), Corollary 8.4.12), and P_{x,0} for a chamber is facetZeroFixer D C, the pointwise fixer of C in G(F)^0 = D.base.zeroSubgroup. With the point topology of G(F) and p = ringChar of the residue field: (1) every facetPositiveSubgroup lies in G(F)^0 and is open and pro-p; (2) it satisfies IsMaximalOpenProPIn p G(F)^0 (maximal among open pro-p subgroups of G(F) contained in G(F)^0) exactly when the facet is a chamber; (3) every such maximal subgroup is facetPositiveSubgroup D C for a chamber C; (4) for a chamber C, the normalizer of facetPositiveSubgroup D C intersected with G(F)^0 equals facetZeroFixer D C. This is the corrected ambient group G(k)^0 of both parts. The only premise is availability; existence of available data is BruhatTitsAvailabilityStatement (Theorem 9.2.7 row), which is unproved. The theorem availableMaximalProP (module Langlands.BruhatTits.MaximalProP.AvailableProof) proves AvailableMaximalProPStatement at arbitrary universe u; it was accepted as artifact c86654f8-89f0-4107-b4af-6473d7fd30e0 and first published in Library commit 410c79471b79f65a02fb0f6070da7f2800793ff3. The row's conditional status refers to AvailableMaximalProPStatement, proved under IsAvailableFor."
      ],
      "conclusion": "For every x, P_{x,0+} is an open pro-p subgroup of G(k)^0. It is maximal among open pro-p subgroups there exactly when x lies in a chamber, equivalently P_{x,0} is Iwahori. Every maximal open pro-p subgroup of G(k)^0 is P_{x,0+} for an Iwahori P_{x,0}, and its normalizer in G(k)^0 is P_{x,0}. Neither the maximality claim nor the normalizer identity is extended to the full G(k).",
      "lean_declarations": [
        "Langlands.BruhatTits.MaximalProP.AvailableMaximalProPStatement",
        "Langlands.BruhatTits.MaximalProP.MaximalProPConclusions",
        "Langlands.BruhatTits.MaximalProP.IsMaximalOpenProPIn",
        "Langlands.BruhatTits.MaximalProP.facetPositiveSubgroup",
        "Langlands.BruhatTits.MaximalProP.facetZeroFixer",
        "Langlands.BruhatTits.MaximalProP.availableMaximalProP"
      ],
      "modules": [
        "Langlands.BruhatTits.MaximalProP.AvailableStatement",
        "Langlands.BruhatTits.MaximalProP.AvailableProof"
      ],
      "dependencies": [
        "Proof: the theorem availableMaximalProP (module Langlands.BruhatTits.MaximalProP.AvailableProof; proof Task 5903, f12ddb04-e390-4e3c-a455-59e5d5684a11, lean.proof@1, published by Worker 3557 on 13 November 2026 and executed by Workers 302 and 317; artifact c86654f8-89f0-4107-b4af-6473d7fd30e0, first in Library commit 410c79471b79f65a02fb0f6070da7f2800793ff3) proves AvailableMaximalProPStatement. Its Markdown describes the route. IsAvailableFor.groupAxioms gives the single-group axioms D.SatisfiesGroupAxioms of the available datum, and maximalProPConclusions_of_groupAxioms derives the four conclusions from them. The classification theorems of the module AvailableClassification give clauses (1)–(3) from the proved local-model pro-p result, the facet quotient comparisons and the finite-field Sylow and Borel theorems. For clause (4) the proof chooses an apartment chamber from a regular point of the affine reflection arrangement and a generic cocharacter of the maximal split torus. isProP_chamber_unipotent_factor gives the pro-p property of the two unipotent factors, for the cocharacter and its negative, and the Iwahori factorization with the split Tits-system normalizer theorem gives the normalizer identity at that chamber. chamber_normalizer_eq_of_one_apartment_chamber transports the identity to every chamber by conjugation inside G(F)^0. lean_check inspection e5824c23-436b-4eaa-81a1-745279f5e09d by Worker 3557 on 2026-11-14 at Library commit 410c7947 reports kind theorem, a type that is exactly AvailableMaximalProPStatement.{u}, and only propext, Classical.choice and Quot.sound. TaskHub records Task 5903 as completed. The statement is present in Library commit ed924aef420de137b4cbaa3b063a3618afcd73fd; its acceptance artifact cannot be identified in this instance. Since its premise is 𝔅.IsAvailableFor F G hG, the proof yields corrected 13.5.2 for every G only together with BruhatTitsAvailabilityStatement, which is unproved (Theorem 9.2.7 row).",
        "Intermediate statements of Task 5903 (on 13 November 2026 none was proved): FacetReductiveComparisonStatement (module Langlands.BruhatTits.MaximalProP.FacetReductiveComparisonStatement; artifact db960514-53a1-45a3-9327-0110c52a9c40, Library commit 7f43c3c930ff92f76dae6589da1678ad729017e5), the chamber, Borel and radical-preimage comparisons under the single-group Bruhat–Tits axioms; LocalFieldPositiveProPStatement (module Langlands.BruhatTits.IntegralModels.PositiveProPStatement; artifact e0d41185-3f73-4fde-8306-6f0b2520f851, Library commit 73b1430a339b037d27e9096762b0400adb4fbd19), that the radical preimage of a supplied smooth neutral model with connected fibres is pro-p; FiniteFieldSylowBorelStatement and FiniteFieldNormalSylowTorusStatement (modules Langlands.GroupScheme.Rational.FiniteFieldSylowBorelStatement and Langlands.GroupScheme.Rational.FiniteFieldNormalSylowStatement; artifacts e29c5be2-2548-4b55-99ce-1ed6174767e7 and f91a6aed-61ac-4323-b27f-920decfa1a2f, Library commit 7f43c3c930ff92f76dae6589da1678ad729017e5), on maximal p-subgroups of the rational points of a connected reductive group over a finite field; and BoundedOpenNormalizerStatement (module Langlands.BruhatTits.RationalPoints.BoundedOpenNormalizerStatement; artifact 85934e00-489c-45e0-855c-48fedda739d2, Library commit 7f43c3c930ff92f76dae6589da1678ad729017e5), the local-field case of KP Proposition 2.2.16. The modules Langlands.BruhatTits.MaximalProP.AvailableFacetInputs and Langlands.BruhatTits.MaximalProP.AvailableNormalizerQuotient prove consequences that take some of these statements as hypotheses. On 14 November 2026 four of the five are proved. The theorems Langlands.GroupScheme.finiteFieldSylowBorel and Langlands.GroupScheme.finiteFieldNormalSylowTorus (module Langlands.GroupScheme.Rational.FiniteFieldBorelSylow; artifact d7d18e31-01ea-461c-8496-4ce61bb07f30, first in Library commit db8d6b3d466f2fd453a4df4624ce6c90db8eed46) prove FiniteFieldSylowBorelStatement and FiniteFieldNormalSylowTorusStatement; lean_check inspection 947f1be5-8c60-4024-9ef1-45b2bedf5c6e by Worker 3557 on 2026-11-14 at Library commit 410c7947 reports kind theorem, a type that is exactly FiniteFieldSylowBorelStatement.{u}, and only propext, Classical.choice and Quot.sound, and inspection 9e8d26c7-2012-459b-ab7d-ba2e94733a90 reports the same for FiniteFieldNormalSylowTorusStatement.{u}. The theorem Langlands.BruhatTits.IntegralModels.localFieldPositiveProP (module Langlands.BruhatTits.IntegralModels.PositiveProP; artifact 74d4c6fa-67fe-4473-b96c-f2a607228617, first in Library commit 85c2fe719cf62e96f22aaf4ca03961c5814d086b) proves LocalFieldPositiveProPStatement; inspection 9ebcddd2-2b4e-4006-90b2-52d873deba6d reports the same. The theorem Langlands.BruhatTits.MaximalProP.facetReductiveComparisonStatement (module Langlands.BruhatTits.MaximalProP.FacetRadicalPreimage; artifact ba57615d-4f2e-476f-9bc2-64d7ae62c8cc, first in Library commit db8d6b3d466f2fd453a4df4624ce6c90db8eed46) proves FacetReductiveComparisonStatement; inspection 7585141e-8468-49f4-a973-9542023dcb37 reports the same. No published theorem has BoundedOpenNormalizerStatement as its type; availableMaximalProP takes no premise beyond availability, so the conditional status of this row does not wait for it. Each module cited in this entry with a first commit is byte-identical between that commit and Library commit 410c7947.",
        "Actual model point topology and local compactness turn bounded open subgroups into compact ones. Realize P_{x,0+} as the inverse limit of its finite p-group filtration quotients, using 13.5.1 for their steps",
        "Fixed points 4.2.14, type preservation 1.5.13(3), the actual reduction and incident-facet/parabolic correspondence 8.4.19 with Chapter 9 descent; finite-field p-subgroup structure and the Iwahori-Tits system in G(k)^0",
        "The normalizer argument uses 2.2.16 and 6.3.21",
        "Release 1 constructions, the corrected Theorem 9.2.7 certificate and the inflation/compact-induction consumer remain prerequisites for positive-depth implementation. A source row supplies no release or formal acceptance."
      ],
      "consumer_or_regression": "Check the exact ambient group in both maximality and normalization, including a case with nontrivial component or length-zero data. An abstract pro-p predicate does not supply the compactness, inverse limit or building fixed-point proof.",
      "formal_status": "conditional",
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [
        "c86654f8-89f0-4107-b4af-6473d7fd30e0"
      ],
      "publication_commits": [
        "ed924aef420de137b4cbaa3b063a3618afcd73fd",
        "410c79471b79f65a02fb0f6070da7f2800793ff3"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.BruhatTits.MaximalProP.AvailableMaximalProPStatement",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "7d5da56a-9b3c-4941-9f9e-5da2ec8d1ada",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-13 at Library commit ed924aef; kind definition; statement_returns_prop true. Its acceptance artifact cannot be identified in this instance."
        },
        {
          "declaration": "Langlands.BruhatTits.MaximalProP.availableMaximalProP",
          "environment_artifact": "5c94c648-e8dc-4002-a50a-071ebf3f6096",
          "inspection_id": "e5824c23-436b-4eaa-81a1-745279f5e09d",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-14 at Library commit 410c7947; kind theorem, at universe level u, whose type is exactly AvailableMaximalProPStatement.{u}; the module was first published in this commit."
        }
      ],
      "external_code": []
    },
    {
      "source_item": "Proposition 13.6.7",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.481 / PDF p.512; definitions and prerequisites at PDF pp.509-511; optimal-point boundary: Definition 13.4.2 and Lemma 13.4.4, printed pp.472-473 / PDF pp.503-504; torus formula (13.1.2), printed p.467 / PDF p.498"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.49, Chapter 13, end of Section 13.6.2",
        "change": "Replace the reference 1.3.35 with 8.4.8(3). No direct replacement of 13.6.7 is listed."
      },
      "hypotheses": [
        "k has a normalized discrete valuation omega(k^times)=Z, Henselian integer ring o, maximal ideal m and perfect residue field f. G is a connected reductive k-group. K is a maximal unramified extension, O its integer ring and Gamma=Gal(K/k). x belongs to the actual descended building B(G). No splitness, tameness, finite-residue or perfect-k hypothesis is imposed unless separately stated.",
        "Until Section 13.5, choose any functorial admissible filtration on tori satisfying Section 7.2(1),(2), hence commutator-friendly by 7.2.3; Section 9.8 supplies the centralizer filtration. P_{x,r}=G(k)_{x,r} is generated by the actual root and centralizer filtrations as in 13.2.1 and 7.3.3. The strict-depth convention is X_{r+}=union_{s>r} X_s.",
        "r is real and Xi is a Lie coset in g_{x,r}/g_{x,r+}. Nilpotent means algebraically contracted to zero by a k-defined cocharacter G_m to G, as in 13.6.5. Degenerate means containing such an element. Instability refers to the algebraic Gred_x-orbit closure in the f-rational graded representation of 13.3.4. This is distinct from valuation-topology closure of a G(k)-orbit in g.",
        "Xi=X+g_{x,r+} is degenerate, with X nilpotent in the k-cocharacter sense. Definition 13.4.2 requires a nonempty finite subset of the affine-root set Sigma for an optimal point. A target retaining optimality must explicitly assume nonempty relative roots; this is no restriction on the ambient connected-reductive program. No convention extending optimality to empty roots is supplied or proved here."
      ],
      "conclusion": "The printed first clause asserts an optimal point y and real s>r with the entire coset Xi contained in g_{y,s}. As a universal connected-reductive assertion this is false: G_m over Q_2 has empty affine roots and no optimal point under 13.4.2, although 0+g_{x,1+} is degenerate. Retain the nonempty-relative-root optimal-point version as a proof target. General whole-coset depth raising without optimality and any separately derived empty-root convention or extension need their own statements and proofs. The separate instability clause remains a target: Xi in g_{x,r}/g_{x,r+} is unstable under Gred_x, meaning zero belongs to its algebraic orbit closure. These are Lie-coset targets; the broader dual-coset degeneracy definition does not extend them to dual cosets.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "13.6.3 constructs a contracting k-cocharacter compatible with x, using Iwasawa 5.3.4, actual models, perfect-residue unipotent H^1 vanishing and 8.4.19/9.3.2",
        "13.6.4 conjugates it by an element of P_x into the chosen maximal split torus with the chamber inequalities. A small apartment translation raises the finite set of root depths. The subsequent optimal-point reduction 13.4.4 uses a nonempty affine-root subset in its proof and fails for empty roots as stated. Use this reduction only in the nonempty-relative-root target; a general depth-raising proof must handle the empty-root case separately",
        "For instability the compatible cocharacter extends to the actual integral model and reduces to an f-cocharacter contracting the graded vector; use the action of 13.3.4. This is a separate clause and does not require the existence of a literal optimal point",
        "Independent empty-root boundary, not an authors' erratum: for G_m/Q_2, the reduced building has one point x (4.1.4(A0), PDF p.189), Sigma is empty, and (13.1.2) gives g_{x,1}=2 Z_2 and g_{x,1+}=4 Z_2. Zero is contracted by the identity cocharacter, so Xi=0+g_{x,1+} is degenerate by 13.6.5. There is no optimal y under 13.4.2, yet Xi is already contained in g_{x,2} and its zero graded vector is unstable. Thus the optimality requirement and 13.4.4 need resolution; this example does not refute depth raising or instability. The 1 November 2024 corrections, PDF pp.49-50, do not repair 13.4.2, 13.4.4 or this clause of 13.6.7",
        "The printed Remark 13.6.6 example is not a witness separating cocharacter nilpotence from Jordan nilpotence. In characteristic two, for x nonzero, X=[[1,x],[x^(-1),1]], B=[[x,1],[1,0]] and B^(-1)=[[0,1],[1,x]] satisfy det(B)=1, X^2=0 and B^(-1) X B=x^(-1) E_12. The k-defined cocharacter lambda(u)=B diag(u,u^(-1)) B^(-1) has lambda(u) X lambda(u)^(-1)=u^2 X, so it contracts X to zero. Nonconjugacy to E_12 does not imply absence of a contracting cocharacter. This is an independently demonstrated source discrepancy, not an authors' erratum or a Lean result; the 1 November 2024 corrections do not repair 13.6.6. Any broader non-equivalence claim needs a separately checked witness",
        "Later target: implement only after positive-depth acceptance has constructed finite abelian graded quotients, transported characters through the proved comparison and verified a nontrivial filtration calculation. No minimal K-type or supercuspidality theorem follows from this source row."
      ],
      "consumer_or_regression": "After positive-depth acceptance, test full-coset containment, the strict s>r inequality, the G_m/Q_2 zero coset at r=1 (degenerate, no literal optimal point, contained at depth 2, unstable), and the explicit contraction of the printed characteristic-two matrix. Use the k-cocharacter definition; any comparison with Jordan nilpotence needs a separate proof.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Proposition 13.7.4",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.483-484 / PDF pp.514-515; topology comparison at PDF p.513"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.49, Chapter 13",
        "change": "No direct replacement of 13.7.4 is listed; apply the corrected 13.6.2 reference in its 13.6.7 dependency."
      },
      "hypotheses": [
        "k has a normalized discrete valuation omega(k^times)=Z, Henselian integer ring o, maximal ideal m and perfect residue field f. G is a connected reductive k-group. K is a maximal unramified extension, O its integer ring and Gamma=Gal(K/k). x belongs to the actual descended building B(G). No splitness, tameness, finite-residue or perfect-k hypothesis is imposed unless separately stated.",
        "Until Section 13.5, choose any functorial admissible filtration on tori satisfying Section 7.2(1),(2), hence commutator-friendly by 7.2.3; Section 9.8 supplies the centralizer filtration. P_{x,r}=G(k)_{x,r} is generated by the actual root and centralizer filtrations as in 13.2.1 and 7.3.3. The strict-depth convention is X_{r+}=union_{s>r} X_s.",
        "r is real and Xi is a Lie coset in g_{x,r}/g_{x,r+}. Nilpotent means algebraically contracted to zero by a k-defined cocharacter G_m to G, as in 13.6.5. Degenerate means containing such an element. Instability refers to the algebraic Gred_x-orbit closure in the f-rational graded representation of 13.3.4. This is distinct from valuation-topology closure of a G(k)-orbit in g."
      ],
      "conclusion": "If there exist y in B(G) and real s>r with Xi intersect g_{y,s} nonempty, then Xi is degenerate. Also, Xi is unstable under the algebraic Gred_x-action if and only if Xi is degenerate. The first implication needs only an intersection, whereas the depth-raising clause printed in 13.6.7 asks for whole-coset containment and has the separate empty-root optimality obstruction recorded in its row. No local compactness or perfect-k hypothesis is added to this result; the perfect-residue/Henselian Chapter 13 setup is retained.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Lemma 13.7.3 proves g_{y,s} contained in g_{x,s}+N using an apartment displacement and its root-space decomposition, with N the cocharacter-defined nilpotent set",
        "Use only the separate instability clause of Proposition 13.6.7 for degenerate implies unstable, not its optimal-point assertion or an empty-root use of 13.4.4",
        "For unstable implies degenerate, Kempf's rational cocharacter theorem over perfect f gives a contracting f-cocharacter. Conjugacy of maximal f-split tori and the actual surjection P_x to Gred_x(f) lift it through a split o-torus. A small apartment translation raises the depth, and part (1) applies",
        "The additional perfect-k or locally compact hypotheses of nearby 13.7.2 concern the valuation-topology set N' and N=N', not the algebraic instability equivalence of 13.7.4. Register and read Kempf's original before a proof relies on that theorem directly",
        "Later target: implement only after positive-depth acceptance has constructed finite abelian graded quotients, transported characters through the proved comparison and verified a nontrivial filtration calculation. No minimal K-type or supercuspidality theorem follows from this source row."
      ],
      "consumer_or_regression": "After positive-depth acceptance, test intersection versus containment and distinguish algebraic residue-field orbit closure from valuation-topology G(k)-orbit closure. Preserve the actual reduction surjectivity used in lifting cocharacters.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Proposition 12.4.1",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.446 / PDF p.477; replaced in corrections PDF p.47"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF pp.47-48, Section 12.4 and proof of 12.7.1",
        "change": "Replace Proposition 12.4.1 and its proof in full. Delete the Corollary 4.4.5 citation in the first paragraph of 12.4 and the last sentence of its second paragraph; use the corrected intersection and boundedness in 12.4.2 and the corrected facet argument in 12.7.1."
      },
      "hypotheses": [
        "O is a Henselian discrete valuation ring with fraction field K and algebraically closed residue field. H is connected reductive over K; Theta is a finite group of K-automorphisms whose order is prime to the residue characteristic, with no restriction when it is zero. G=(H^Theta)^0 and the enlarged buildings retain their central translation factors.",
        "Use the Section 12.4 reduction in which the maximal K-split central torus of G is central in H. Put H'=H_der and G'=(H'^Theta)^0. Let S be a maximal K-split torus of G and S' its maximal subtorus contained in G'.",
        "x is a Theta-fixed point of enlargedB(Z_{H'}(S)). A is any apartment of that building containing x."
      ],
      "conclusion": "For every such apartment A, its Theta-fixed locus is A^Theta=V(S')+x=enlargedB(Z_{H'}(S))^Theta. This describes the entire fixed locus as an affine translation space and retains the specified fixed point and the universal apartment quantifier. It does not replace an enlarged building by a reduced one.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Corrected Section 12.4 setup and 12.3.2; retain the distinction between S and S'. For the apartment argument choose a maximal split torus of Z_{H'}(S), containing S'; the correction's proof phrase about a torus of H' containing S needs interpretation against this distinction",
        "The maximal split central torus Z of Z_{H'}(S) and its derived group are Theta-stable, with (Z^Theta)^0=S'. Parahoric transitivity on apartments through x glues their V(Z) translation actions; use V(Z)^Theta=V(S') and the union of apartments through x",
        "The adjacent corrected 12.4.2 uses a nonempty bounded subset of the intersection of the two fixed loci; 12.7.1 also needs the corrected vertex-to-facet argument",
        "Release 1 constructions and its representation consumer, then positive-depth acceptance, precede Bundle F implementation. A source-only row is no formal or release acceptance."
      ],
      "consumer_or_regression": "Compare reduced and enlarged buildings for tori and groups with a central split factor; test two apartments through x. This fixed-locus calculation is an input to tame descent, not a general unramified-descent certificate.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Theorem 12.9.2",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.463-464 / PDF pp.494-495; metric convention at PDF p.490"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF pp.47-48, corrected Chapter 12 dependencies",
        "change": "No direct replacement of 12.9.2 is listed. Apply the replaced 12.4.1, corrected 12.4.2 and corrected 12.7.1 facet argument in its finite-action dependency."
      },
      "hypotheses": [
        "k is discretely valued and Henselian with perfect residue field. The valuation omega extends uniquely to algebraic extensions and the same extension is used throughout; do not renormalize the extension field independently. Connected reductive groups and their actual buildings are used, without a global split, quasi-split, tame, finite-residue or large-residue-characteristic hypothesis.",
        "G is connected reductive over k and l/k is a finite tamely ramified Galois extension. Tameness means that the residue characteristic does not divide the ramification index, not necessarily [l:k].",
        "Use the reduced building of the theorem and compatible invariant Euclidean metrics: 12.7.2 permits rescaling on simple factors to agree with the fixed-locus metric."
      ],
      "conclusion": "The constructed reduced building B(G) has a natural identification with B(G_l)^Gal(l/k) as a metric space, using the inherited valuation and compatible metrics. No assumption that G/k itself is quasi-split or split is added.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Let k' be the maximal unramified subextension of l/k, and K,L the maximal unramified extensions of k,l in one separable closure. Then L=K tensor_{k'} l and Gal(L/k')=Gamma times Theta, where Gamma=Gal(K/k') and Theta=Gal(l/k')=Gal(L/K)",
        "Apply 12.7.1 to H=Res_{l/k'}(G_l), whose base change is Res_{L/K}(G_L), using the corrected 12.4.1 and 12.7.1 arguments. The totally ramified Theta part has order prime to the residue characteristic; the unramified degree can be divisible by it",
        "Apply actual Chapter 9 unramified descent in both orders to Gamma and Theta, and then to k'/k; the corrected 9.2.7 certificate remains required. The enlarged finite-automorphism construction is an intermediate step rather than a change of target",
        "Release 1 constructions and its representation consumer, then positive-depth acceptance, precede Bundle F implementation. A source-only row is no formal or release acceptance."
      ],
      "consumer_or_regression": "Test a tame ramified extension together with an unramified degree divisible by the residue characteristic, inherited valuation scales, and anisotropic or nonsplit groups. No arbitrary wild-extension fixed-locus identity follows.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Proposition 12.9.4",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.464-465 / PDF pp.495-496; 12.8.5 at PDF pp.493-494"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.48, Proposition 12.8.5",
        "change": "Move the last sentence of the first paragraph after the first sentence of the second paragraph: the separate torus-filtration assumption at r=f(0) is placed after the sentence defining f and its pullback F. No direct replacement of 12.9.4 is listed; retain f(0)>0 and all torus-filtration hypotheses of its dependency."
      },
      "hypotheses": [
        "Use the Section 12.9 maximal-unramified K setting: K is Henselian discretely valued with algebraically closed residue field, and G is connected reductive over K, hence quasi-split there. Let L/K be finite tamely ramified Galois with Theta=Gal(L/K).",
        "S is a maximal K-split torus of G. T is the K-torus containing S for which T_L is a maximal L-split torus of G_L. Use the same extended valuation on L.",
        "f on the roots plus zero of (S,G) is concave with f(0)>0 in the source extended-depth convention. F is its pullback by restriction from (T,G). The point x lies in A(S) inside A(T_L). Use the actual admissible torus/root filtrations and smooth concave-function models."
      ],
      "conclusion": "G(L)_{x,F} is Theta-stable, G(K)_{x,f}=(G(L)_{x,F})^Theta, and G_{x,f}=(H_{x,F})^Theta for H=Res_{L/K}(G_L). The last identity is for actual smooth integral group schemes, not merely their integral points. No extension to arbitrary depth-zero concave functions is asserted.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Proposition 12.8.5 requires a cyclic prime-to-residue-characteristic action, surjective root restriction with each fibre one Theta-orbit, and the separate torus equality (Z_H(T_H)(K)_r)^Theta=Z_G(S)(K)_r at r=f(0). In the Weil-restriction application use the corresponding maximal split torus T_H of H; do not confuse it with the K-torus T of G",
        "The 12.9.4 proof checks the root fibres using Z_G(S), a maximal torus over K, and the successive Galois orbits of its absolute roots. A future proof must also discharge the torus-filtration equality for restriction of scalars rather than silently assuming it",
        "The 12.8.5 proof uses ordered root products, root-orbit cases, translation to depth zero, the 12.7.1 parahoric comparison and 2.10.11 uniqueness of smooth models. Audit multipliable-root indexing against 7.3.3/7.3.12 before using product coordinates",
        "Release 1 constructions and its representation consumer, then positive-depth acceptance, precede Bundle F implementation. A source-only row is no formal or release acceptance."
      ],
      "consumer_or_regression": "Test a nontrivial tame ramified extension, the torus comparison, a multipliable-root case and equality of actual models. Keep the f(0)>0 boundary visible in every downstream filtration statement.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Proposition 14.6.1",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.502-504 / PDF pp.533-535; definitions at PDF pp.529-532"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF pp.1-2,27-29,47-50; Chapter 14 has no listed correction",
        "change": "No direct replacement of 14.6.1 is listed. Preserve the corrected Chapter 4 geometric/quotient dependencies. In any use of 14.5.6 and 14.7 retain corrected nonempty convexity and prove nonemptiness independently."
      },
      "hypotheses": [
        "k is discretely valued and Henselian with perfect residue field. The valuation omega extends uniquely to algebraic extensions and the same extension is used throughout; do not renormalize the extension field independently. Connected reductive groups and their actual buildings are used, without a global split, quasi-split, tame, finite-residue or large-residue-characteristic hypothesis.",
        "G is a connected reductive k-subgroup of the connected reductive k-group H. For a maximal split torus S of G, A_G is the maximal split central torus of G and M=Z_H(A_G). Enlarged and reduced buildings, full point stabilizers, G(k)^1 and parahorics remain distinct.",
        "Choose an adapted pair (x_tilde,y_tilde) in the enlarged buildings of G and H.",
        "Adapted data are Definition 14.5.1 and Remark 14.5.2, not just a single-point stabilizer inclusion: retain the normalizer-fixed orbit, the apartment map taking x to y, and the stabilizer inclusion at every translate. In reduced coordinates this is G(k)^1_{x+v} contained in M(k)^1_{y+v} for every v in V(S/A_G); in enlarged coordinates use the equivalent full-stabilizer condition for every v in V(S).",
        "Admissible means equivariant on k-points and affine on apartments with the induced cocharacter translation map (14.0.1). For a closed immersion, the metric is induced from H on the cocharacter spaces before claiming isometry (14.2.2). No isometry between unrelated simple-factor metric normalizations is asserted."
      ],
      "conclusion": "There is a unique admissible embedding of enlargedB(G) into enlargedB(H) taking the chosen x_tilde to the chosen y_tilde. For the pair (phi,psi) of 14.3.1, the reduced map phi:B(G)->B(M) restricts on A(S,G) to the normalizer-fixed-orbit apartment map phi_{S,y_bar} of 14.4.1. Uniqueness is relative to the adapted pair, not a canonical embedding independent of choices. Equivariance, affine apartment behaviour and all-translate point-stabilizer inclusion do not assert a general positive-depth filtration identity.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Descend (g,z) mapped to g phi_{S,y_bar}(z) through the 4.4.4 quotient using normalizer equivariance and G(k)^1_z contained in M(k)^1_{phi(z)} for every apartment point z. Keep both the normalizer and stabilizer terms of that quotient relation",
        "Point-stabilizer conjugacy of maximal split tori through x gives independence of S. The central translation coordinates and the Levi embeddings of 9.7.5 determine psi. Uniqueness uses the 14.3.1 factorization and 14.4.1 affine uniqueness",
        "14.6.2 describes when different adapted pairs give the same embedding. 14.0.3 gives a reduced map obstruction for a split torus in SL2; 14.0.5 gives enlarged-map nonuniqueness by central translations",
        "Passing from a subgroup to a general homomorphism requires the 14.0 simple-factor lift condition: on every relevant simple factor the lift from G_sc to the simply connected cover of the image is trivial or an isomorphism onto its image. Use the faithfully flat quotient step of 14.1.1 and then the subgroup embedding. This does not give an injective or canonical map for every homomorphism.",
        "Release 1 constructions and its representation consumer, then positive-depth acceptance, precede Bundle F implementation. A source-only row is no formal or release acceptance."
      ],
      "consumer_or_regression": "Test choice dependence and central translations, the split torus/SL2 reduced-building obstruction, equivariance, apartment derivatives and all-translate stabilizers. A separate source and proof are required for any later positive-depth or integral-model morphism compatibility.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Proposition 14.8.4",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.505-508 / PDF pp.536-539; descent at PDF pp.535-536"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF pp.1-2, Section 1.1; no Chapter 14 correction is listed",
        "change": "Apply nonempty convexity and the corrected nearest-point proof. The printed corrected coefficient2 and zero-distance continuity case need the explicitly recorded independent repairs in the dependencies and private audit. No change to the 1.1.20 theorem statement is needed."
      },
      "hypotheses": [
        "The section assumes strictly Henselian k. Retain the Chapter 14 discretely valued perfect-residue context and the actual enlarged buildings.",
        "G is a connected reductive k-subgroup of the connected reductive k-group H. For a maximal split torus S of G, A_G is the maximal split central torus of G and M=Z_H(A_G). Enlarged and reduced buildings, full point stabilizers, G(k)^1 and parahorics remain distinct.",
        "l/k is a finite Galois extension splitting G and H; no tame hypothesis is imposed. x_tilde in enlargedB(G) is absolutely special. Choose y1_tilde in enlargedB(H_l) with the full stabilizer inclusion G(l)_{x_tilde} contained in H(l)_{y1_tilde}. Let y_tilde be its unique closest point in the embedded enlargedB(H).",
        "Admissible means equivariant on k-points and affine on apartments with the induced cocharacter translation map (14.0.1). For a closed immersion, the metric is induced from H on the cocharacter spaces before claiming isometry (14.2.2). No isometry between unrelated simple-factor metric normalizations is asserted."
      ],
      "conclusion": "The pair (x_tilde,y_tilde) is adapted in the full sense of 14.5.1/14.5.2. In particular adapted pairs exist under the section hypotheses. The target of the closest-point projection is the enlarged base building, confirmed visually at PDF p.539; it is not identified with the entire Galois fixed locus for an arbitrary ramified splitting extension. General-k existence uses the separate 14.7 descent step.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Adapted data are Definition 14.5.1 and Remark 14.5.2, not just a single-point stabilizer inclusion: retain the normalizer-fixed orbit, the apartment map taking x to y, and the stabilizer inclusion at every translate. In reduced coordinates this is G(k)^1_{x+v} contained in M(k)^1_{y+v} for every v in V(S/A_G); in enlarged coordinates use the equivalent full-stabilizer condition for every v in V(S).",
        "7.11.4 supplies an absolutely special point staying special over l. Existence of y1 uses boundedness of the full stabilizer and the building fixed-point theorem; it must be proved, not supplied as the entire existence argument",
        "14.8.2 proves the split case using root-group lattices and homogeneous polynomial coordinate maps. Strict Henselianity makes G quasi-split (2.3.8), so Z_G(S) is a maximal torus. 14.8.3 projects the split adapted point using 1.1.20; projection equivariance for group actions and translations gives the all-translate condition",
        "Proposition 1.1.20 needs a complete NPC geodesic space and a nonempty closed convex base building. Its projection is unique, continuous and equivariant for isometries preserving that subset setwise. Corrections PDF p.2 prints the insufficient minimizing-sequence estimate d(y1,y2)^2<=2 epsilon(2r+epsilon), contradicted already by X=Y=R, x=0, r=0, epsilon=1 and y1,y2=+-3/4. Independently derive the sufficient bound with coefficient4 from the midpoint inequality. The added continuity proof needs the zero-distance case separately; the division-free bound d(pi(x_n),pi(x))^2<=2(q_n^2-r^2), with q_n=d(x,pi(x_n))->r=d(x,pi(x)), covers that case. These independently derived repairs are implemented in the accepted and published nearestPointProjection proof recorded in the Proposition 1.1.20 row. They are not authors' errata and do not construct the required building instance.",
        "For general k, 14.5.6 proves closedness and segment containment of the adapted-y locus. 14.7.1 makes the space of embeddings complete and NPC with evaluation-independent metric; 14.7.2 obtains an equivariant embedding assuming nonemptiness; 14.7.3 applies this to the maximal unramified extension and Chapter 9 descent. Neither convexity alone nor an assumed fixed point proves the needed nonemptiness",
        "Passing from a subgroup to a general homomorphism requires the 14.0 simple-factor lift condition: on every relevant simple factor the lift from G_sc to the simply connected cover of the image is trivial or an isomorphism onto its image. Use the faithfully flat quotient step of 14.1.1 and then the subgroup embedding. This does not give an injective or canonical map for every homomorphism.",
        "Release 1 constructions and its representation consumer, then positive-depth acceptance, precede Bundle F implementation. A source-only row is no formal or release acceptance."
      ],
      "consumer_or_regression": "Test all-translate full stabilizers after projection and after unramified descent, the induced metric choice and central-translation nonuniqueness. No arbitrary positive-depth filtration compatibility or canonical functor on all homomorphisms is claimed.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    }
  ]
}
```

## Bundle B: the complete certificate and its source map

The corrected Definition 4.1.26 is the ten-axiom target. The following table
records the source assembly of §9.5 and the extra routes needed to retain its
full corrected scope. It is a source-derived proof plan, not a Lean proof,
axiom report or claim of acceptance. In particular, the shorter printed list
in Theorem 9.2.7 does not reduce the program's certificate.

| Certificate item | Source route and boundary |
| --- | --- |
| 4.1.1 | Theorem 9.3.21, with apartments and facets constructed in §9.2. |
| 4.1.2 | The corresponding assertion for the constructed quasi-split group G_K. |
| 4.1.4 | Proposition 9.3.16. |
| 4.1.6 | AS1: 9.4.9; AS2–3: 9.4.19; AS4: 9.4.18; AS5: 9.4.35 and its preceding paragraph; AS6: 9.4.31. Apply the corrected inclusion of the identity in AS3. |
| 4.1.8 | Proposition 9.4.3 and Lemmas 9.4.6, 9.4.21. Part (2) retains a nonempty bounded subset. |
| 4.1.9 | Propositions 9.3.24–9.3.25, with the corrected restricted-building argument for 9.3.25. |
| 4.1.16 | The derived route through 9.6.5–9.6.6, corrected 4.4.5, 7.3.12 and 7.4.9, explained below; no separate paragraph for this axiom appears in the printed §9.5. |
| 4.1.17 | Proposition 7.9.5 has the scope of all covering field/group isomorphisms. Section 9.5 invokes it for the Gamma action. The full certificate must also transport the descended fixed loci, apartments and models under every such pair, not merely construct that one action. |
| 4.1.20 | Actual model descent in 9.2.5 and the integral-point identities in §9.5. Use 9.3.24 for the G(k)^0 intersection law; G(k)^1 has its own law. |
| 4.1.22 | Parts (1), (2), (7) descend geometrically; (7) uses perfect residue to descend the unipotent radical. Parts (3), (5) use facet correspondence and 9.4.31; (4) is 9.3.3; (6) is 9.4.23. |
| 4.1.27 | Fixed-locus and base-change constructions in §9.2, special tori from 9.3.4, and affine-root compatibility from 9.4.28. Retain all four clauses, including both integral-model intersection identities. |

Chapter 7 cannot supply a general existence theorem merely from a valuation
hypothesis. The corrections at PDF page 33 add **AS5 of Axiom 4.1.6** to its
ambient assumptions; PDF page 35 replaces the Weyl-identification arguments in
7.5.1 by this assumption. In the perfect-residue case, Proposition 9.4.35
establishes AS5 from the descended geometry before §9.6 constructs valuations.
The Iwahori–Tits systems of 7.5.3 are systems in G(k)^0 and G(k)^natural.
They do not erase the component or length-zero data of the full G(k) theory.

For the derived 4.1.16 route, Theorem 9.6.5 constructs root-datum valuations
compatible with the field valuation. Section 9.6.6 compares the descended
building with the Chapter 7 building made from those valuations. It identifies
affine roots and proves equality of the G(k)^0 stabilizers at **every** pair
of corresponding apartment points, using 9.4.21 and 7.6.4 and, for multipliable
roots, 6.3.8. This is the universal hypothesis required by corrected Corollary
4.4.5. The comparison needs Axioms 4.1.1, 4.1.4 and 4.1.9, already supplied
in the source assembly; it does not assume the missing Iwahori decomposition.

In the Chapter 7 construction, Corollary 7.4.9 gives the sharp-subgroup
factorization. The full bijections in Axiom 4.1.16 additionally use the
Z(k)^0 factor in 7.4.1, the root-factor bijections of 7.3.12(3), (5), and
injectivity of multiplication in the algebraic open cell. Transport these
factorizations through the comparison. For each fixed positive or negative
system, nondivisible root factors may be ordered arbitrarily. The three
unipotent/central/unipotent factors may also be permuted: switch the positive
system and use normalization by Z(k)^0. The added mixed-all-roots assertion
7.3.12(6) has the extra hypothesis f(0)>0; it is not needed for these
fixed-sign arbitrary orders and must not be applied at depth zero without
that hypothesis.

The descended models in 9.2.5 are actual smooth affine models obtained from
Fact 2.10.16; their coordinate rings are invariant rings, equivalently the
intersections of the O-coordinate rings with k[G]. Their relative identity
components, special fibres and maximal reductive quotients are separate
objects. For a point x the parahoric is G_x^0(o), which fixes its facet
pointwise and has finite index in the corresponding G(k)^1 facet stabilizer;
it is not identified with the full fixer. The naive G(k)^b intersection law
is false (Example 2.6.31). Likewise, a Gamma-chamber or Gamma-vertex need not
be a chamber or vertex over K. The reduced fixed-locus building remains
distinct from the enlarged building and its invariant central translation
factor.

The correction at PDF page 39 adds a further genuine metric dependency:
a bounded Gamma-stable subgroup of G(K) has a Gamma-fixed fixed point.
The argument uses closed convex fixed loci, the bounded closed convex hull
and Theorem 1.1.15. This does not permit a fixed point to be included as
input in place of constructing it. No formal certificate or general-instance
acceptance is recorded here.

The printed display of Lemma 9.6.3 (book PDF page 397) uses the same
depth r for every non-divisible root b of (G_K, T_K) that restricts to a
or 2a. Its proof replaces x by x − (r/2)a^∨ (Lemma 6.1.6), which lowers
the value of a root b restricting to m·a by m·r, so roots restricting to
2a are reached at depth 2r. A uniform depth would also contradict V 4 of
Definition 6.1.2, U_{a,x,r} ∩ U_{2a}(k) = U_{2a,x,2r}. The published
torus-then-field restriction used by
`UnramifiedValuationDescentStatement` therefore filters at depth m·r,
which is what the proof gives. The 2024 corrections do not mention Lemma
9.6.3; this reading is independently derived, not an authors' erratum.

Section 9.2.1 (book PDF page 357) calls the embedding x ↦ (0, x) of
B(G_K) into the enlarged building V(Z^0_{G,K}) × B(G_K) equivariant
under ΓG(K), and its restriction to Γ-fixed loci G(k)-equivariant. By
Section 4.3 (book PDF pages 209–211), g in G(K) acts on the vector
factor by a translation whose kernel is G(K)^1 (Lemma 4.3.1), so the
zero section is only Γ- and G(K)^1-equivariant, and on fixed loci only
G(k)^1-equivariant, with G(k)^1 = G(K)^1 ∩ G(k) (§9.5, book PDF page
395). For G = G_m over Q_2 the reduced fixed locus is a point, the
fixed enlarged building is R and the uniformizer translates it by −1,
so no G(k)-equivariant map exists at all. The projection to B(G_K)
remains G(K)-equivariant. The 2024 corrections, which rewrite other
paragraphs of 9.2.1, do not mention this; the reading is independently
derived, not an authors' erratum.

## Bundle C: indexing, signs and component boundaries

The Cartan row uses the actual dominant subset of the centralizer Z(k),
modulo Z(k)^0, at a special vertex. It does not assume a dominant-cocharacter
parametrization for every reductive group. Corrected (5.2.2) has the
nonnegative valuation inequality. The same corrections remove the minus
signs from the valuation homomorphisms in Sections 2.5–2.6, so the corrected
dominance condition agrees with (5.2.1).

The Iwasawa product of Theorem 5.3.3 is a surjectivity statement. Injectivity
for the added Theorem 7.8.1(4) uses the replacement of Lemma 5.3.5, with a
chamber Iwahori P_C and every pair n,n' in N(k). The printed lemma with an
arbitrary bounded subgroup is not the corrected target. Theorem 5.3.4
separately retains a special vertex and an arbitrary parabolic k-subgroup.

The conditional Chapter 7 setup includes the added AS5 assumption and does
not impose perfect residue. For the stated source route to Theorem 7.8.1(4),
the ledger also retains the Chapter 5 perfect-residue building hypotheses
used by Theorem 5.3.3 and replaced Lemma 5.3.5. A proof under broader residue
hypotheses remains a separate obligation. Corollary 7.4.9 factors the sharp
subgroup; full parahoric bijections additionally need the central Z(k)^0
factor, the fixed-sign root-factor bijections and open-cell injectivity.

The Iwahori–Weyl quotient N(k)/Z(k)^0 retains component information that its
affine action may lose. Corrected injectivity in Theorem 7.8.1(2) cancels the
chamber-stabilizer component before applying affine Bruhat injectivity in
G(k)^0. The identity I intersect N(k)=Z(k)^0 alone does not prove this
injectivity. The splitting in 7.8.2 depends on the chosen chamber; length-zero
data must remain visible in the Hecke consumer.

For the actual Kottwitz map, Proposition 11.5.4 identifies G(k)^0 with the
zero kernel, while Lemma 11.5.2 identifies G(k)^1 with the preimage of
invariant torsion. Neither kernel description requires dim(f) <= 1. That
additional field-dimension hypothesis, which holds for finite residue
fields, belongs to the surjectivity and quotient statements in 11.7.5–6.
The chamber in 11.7.5 is a Gamma-stable K-chamber in B(G_K), as chosen in
the source proof; it is not replaced by an arbitrary k-chamber.

Writing A=pi_1(G)_I, the third quotient in 11.7.6 is recorded explicitly as
A^Gamma/(A_tor)^Gamma. This unpacks the torsion-free quotient of A^Gamma,
using torsion(A^Gamma)=(A_tor)^Gamma. It does not identify it with
(A/A_tor)^Gamma without a separate exactness argument. All of these are
source targets and dependency descriptions; no Kottwitz construction,
quotient bijection, Hecke distinctness or finite-support theorem is proved
by this note. Task 5912 (`13897846-41bc-48ee-ac17-46b6ca3eebfe`) published the
Kottwitz homomorphism, selected by its characterizing property, and Lean
statements of these four targets (Library commit `0c3f30c2`); none of them
is proved, and their proof tasks are Tasks 6366, 6367, 6368 and 6376.

## Bundle D: models, descent and the actual reduction map

The corrected opening of Section 8.3 requires perfect residue, which applies
to that section and those following it. The Chapter 8 models are over the
integer ring O of the maximal unramified extension K. Theorems 8.3.2 and
8.3.13 distinguish the schematic models with a common relative identity
component from the connected parahoric model itself. The corrected proof of
8.3.13 first factors the torus and root model maps through that identity
component, using connected fibres; only then does the open finite-index
argument apply. The generally nonaffine full-fixer model of Remark 8.3.4
is a separate object, and the corrected evaluation there is on O.

The special fibre H_Omega of the connected parahoric model and its maximal
reductive quotient Gred_Omega=H_Omega/R_u(H_Omega) are distinct. Theorem
8.4.10 identifies the root datum of the latter. Its product description of
the unipotent radical is an isomorphism of schemes supplied by open-cell
multiplication; it is not a direct-product decomposition as groups.

For incident facets F contained in the closure of F', the kernel of the
actual special-fibre map rhobar:H_{F'} → H_F is smooth connected unipotent.
Proposition 8.4.15 (printed pp. 306–307 / PDF pp. 337–338), specialized to
these facets with the corrected morphism setup on corrections PDF p. 38,
gives the valid scheme isomorphism by open-cell multiplication:

`product over all nondivisible a in Phi(S,G_K) of
ker(Ubar_{a,F',0} → Ubar_{a,F,0}) ≃ ker(rhobar)`.

The smaller index `Phi'_{F'} minus Psi_F(F')` printed in Theorem
8.4.19(1) (printed p. 309 / PDF p. 340), and repeated in its proof, is
false. It is recorded as a source discrepancy and excluded from future Lean
targets. The authors' corrections on PDF pp. 37–38 repair the ambient
hypotheses and morphism setup but contain no repair of this index.

Here is a derived counterexample using the book's own Example 8.3.5
(printed pp. 296–297 / PDF pp. 327–328) and Section 8.4.6 (printed p. 304 /
PDF p. 335). Take k=Q_3, its maximal unramified extension K, and G=SL_2.
Let F be the hyperspecial vertex x and F' the adjacent open chamber (x,z)
of that example. The connected models have coordinate rings

`O[G^0_F] = O[a,b,c,d]/(ad-bc-1)`,

`O[G^0_{F'}] = O[a,b,c',d]/(ad-pi*b*c'-1)`.

The generic-identity model morphism sends `(a,b,c',d)` to
`(a,b,pi*c',d)`. On special fibres it sends these coordinates to
`(a,b,0,d)`. Its scheme-theoretic kernel is defined by `a=d=1, b=0`,
leaving `c'` free. Its coordinate ring is therefore `fbar[c']`, and the
group law displayed in Example 8.3.5 restricts to addition of `c'`.
Thus the kernel is G_a. But 8.4.6 defines Phi'_{F'} from the affine roots
vanishing identically on F'. None vanishes on this open chamber, so
Phi'_{F'} is empty. The printed restricted product would be the one-point
scheme, contradicting this kernel computation. The general product over
all nondivisible ambient roots retains the nontrivial negative-root
kernel and has no such contradiction. This calculation diagnoses the
source formula; no Lean construction or proof is supplied here.

Theorem 8.4.19(2)–(4) gives the parabolic image, the inverse-image equality
on integral points and the full facet/parabolic bijection. That bijection
ranges over all incident facets in the building; restricting to one
apartment yields only the parabolics containing the chosen maximal torus.

Section 9.2.5 descends the actual smooth affine models to o by invariant
coordinate rings and relative identity components. Section 9.2.6 identifies
the parahoric integral points. The geometric unipotent radical descends
over the perfect residue field f in Section 9.5. The equalities
G(k)^0=G(K)^0 intersect G(k) and
G(k)^0+_F=G(K)^0+_F intersect G(k) then give the descended kernel in the
reduction map. The geometric Chapter 8 construction alone does not prove
these statements over k.

The homomorphism in Section 13.2.6 is the natural composite

`P_{x,0}=G^0_x(o) → H_x(f) → Gred_x(f)`.

The first arrow is surjective by smooth Henselian reduction, Section 8.1.3.
The second is surjective by Proposition 2.4.3 over perfect f, whose proof
uses Lemma 2.4.2 on split unipotent groups and Galois H^1. Corollary 8.4.12
and Section 9.5 identify the composite's kernel with P_{x,0+}. The first
isomorphism theorem then gives P_{x,0}/P_{x,0+} isomorphic to Gred_x(f).
Reduction to the whole special fibre has a generally smaller kernel. A
scheme-theoretic cokernel by itself does not supply this rational-point
quotient or its two surjectivity steps.

For the residue correspondence, Section 9.3.2 and Proposition 2.4.5 give
parabolic f-subgroups after descent. Proposition 9.3.3 proves the exact
inverse-image equality on o-points, using Section 8.1.3 and Lemma 2.4.2
for the smooth connected unipotent kernel. This preserves the rational
parabolic condition; it does not say every geometric parabolic descends.

No finite-residue hypothesis is needed for Section 13.2.6. For the
local-field consumer, finiteness of Gred_x(f) requires finite residue and
finite type, and compactness and openness require the actual topology on
integral points. These remain proof obligations. The representation test
must inflate a representation through this actual reduction map, prove
factorization through its quotient, and construct compact induction with
a basic intertwining or double-coset theorem. No irreducibility,
supercuspidality or positive-depth theorem follows from these source rows.

The seventh pass records a conditional implementation on supplied
models: the Section 13.2.6 row lists the reduction isomorphism, the
inflation, the kernel-invariant adjunction and compact induction with
Frobenius reciprocity. The kernel there is the radical preimage, not yet
compared with `P_{x,0+}`; finiteness, compactness and the intertwining
theorem remain open.

The tenth pass records that `congruenceNeighborhoodBasis_proof` makes
the integral points of every supplied model over a local field compact
and open, and that `CompactInductionIntertwiningStatement` states the
intertwining theorem for compact induction from an open subgroup, with a
double-coset form for compact open subgroups; its proofs are open.
Finiteness of `Gred_x(f)` and the comparison with the actual `P_{x,0}`
remain open.

The twelfth pass records the finiteness and topological parts of the
local-field consumer on supplied models. With a finite residue field,
the supplied quotient has finitely many residue-field points, which form
a finite group. Over a Henselian base the radical preimage has index
equal to their number, the supplied form of
`[P_{x,0} : P_{x,0+}] = |Gred_x(f)|`. Over a nonarchimedean local field
the radical preimage contains the level-one congruence subgroup and is a
compact open subgroup of `G(F)`. The tenth pass's remark that finiteness
of `Gred_x(f)` is open no longer applies to supplied data; the comparison
with the actual `P_{x,0}` and `P_{x,0+}` remains open.

The fourteenth pass records Lean statements of parts of the Chapter 8
theorems. Over the integer ring O of the maximal unramified extension of
a nonarchimedean local field, and on supplied building data of G_K,
`UnramifiedParahoricModelStatement` asks for the model pair of Theorems
8.3.2 and 8.3.13 without the dagger model, and
`UnramifiedModelKernelStatement` asks for the smooth connected unipotent
kernel of Proposition 8.4.15 without its product decomposition. Neither
statement uses the printed restricted index of Theorem 8.4.19(1). For
facets of the descended building, the root datum of Theorem 8.4.10 and
the positive-radical inclusion derived from Corollary 8.4.12 are stated
for models over the integers of the local field that are characterized
by their integral points over O, in the form of Proposition 9.4.23 and
Section 9.5. The radical preimage remains the definition of `G(F)^{0+}`:
no Lean declaration compares it with the Moy–Prasad group. The
consumer's intertwining theorem is now proved on supplied models. Maps
between two depth-zero compact inductions correspond to intertwining
kernels and, through supplied double-coset representatives, to local
intertwiner families. Over a local field, when the inducing
representation is on a finite module over the coefficient ring, each
kernel is supported on finitely many double cosets. The remarks of the
seventh and tenth passes that the intertwining theorem is open no longer
apply; the comparison with the actual `P_{x,0}` and `P_{x,0+}` remains
open.

The seventeenth pass records regression instances of the supplied-data
layer. Over a nonarchimedean local field, the standard models of the
split groups `G_m`, `G_m^I`, `GL_N`, `Sp_{2l}` and `SL_n` over the
integers give actual model data and reductive quotients: each special
fibre is connected reductive, the radical is trivial and the quotient
map is the identity. The radical preimage is then the image of the
kernel of reduction, and its index in the integral points is the number
of residue-field points of the special fibre, for example `q-1` for
`G_m` and `∏_{i<N}(q^N-q^i)` for `GL_N`. For `GL_{n+1}` the integral
points and the radical preimage agree with the Library's concrete
integral subgroup and principal congruence subgroup of level one. For
split groups, Proposition 8.4.14 says that the connected parahoric model
is reductive exactly at a hyperspecial vertex, the situation of these
models, but no Lean declaration identifies them with KP's `G^0_x`. The
comparison with the actual `P_{x,0}` and `P_{x,0+}` remains open in
general, and so do regression instances with a nontrivial unipotent
radical, a non-split group or a multipliable root.

## Bundle E: filtrations, comparison alternatives and later instability

This bundle has nine rows: Proposition 13.2.5, Sections 13.3.1–4,
Theorem 13.5.1, corrected Proposition 13.5.2, and the later Propositions
13.6.7 and 13.7.4. All nine were source-only when the bundle was first
recorded. Positive-depth implementation remains behind the depth-zero
release and its inflation/compact-induction consumer. The seventh pass
records a published statement of Proposition 13.2.5 on supplied data,
the eighth pass adds its part (3), and the ninth adds parts (5) and (6)
and a double-root restatement of parts (1), (2) and (4). The sixteenth
pass records that every part is proved on supplied data, parts (1), (2)
and (4) with the double-root premise, so that row is `conditional`.
Corrected Proposition 13.5.2 has the published statement
`AvailableMaximalProPStatement`; the eighteenth pass records its proof
`availableMaximalProP` on available data, so that row is `conditional`.
The other seven rows remain source-only. The two instability
targets remain behind the separate positive-depth acceptance test.

### Ambient fields and torus filtrations

Chapter 13 starts with a normalized discretely valued Henselian field k,
integer ring o, maximal ideal m and perfect residue field f. It does not
assume k perfect or locally compact. Let K be a maximal unramified
extension, O its integer ring, and Gamma its Galois group over k.
The source convention is `X_{r+}=union_{s>r} X_s`.

Before Section 13.5, the torus filtration may be any functorial admissible
one satisfying Section 7.2(1),(2); Lemma 7.2.3 makes it
commutator-friendly. The standard filtration and the minimal congruent
filtration remain distinct. The standard filtration on all tori need not
be connected or congruent and need not have the Moy–Prasad comparison.
For weakly induced tori, its comparison is supplied by B.6.9. Theorem
13.5.1 specifically chooses the minimal congruent filtration. Functoriality
of that filtration does not imply that its comparison isomorphisms are
functorial at every positive depth.

### The printed root-index discrepancy in Proposition 13.2.5

The original Proposition 13.2.5(3), printed p.469 / PDF p.500, takes
products over all positive and negative roots, without an indivisible-root
superscript. Visual inspection confirms that this is printed, rather than
an extraction omission. Its cited Proposition 7.3.12(5), printed p.250 /
PDF p.281, instead uses the indivisible-root subsets.

This matters in a nonreduced root system. Root-valuation Axiom V4,
printed p.199 / PDF p.230, gives

`U_{a,x,r} intersect U_{2a}(k) = U_{2a,x,2r}`.

Whenever the group on the right is nontrivial, scalar-depth coordinates
for both a and 2a overlap. Multiplication with both as independent
coordinates cannot then be injective. If the factors are read in the
concave-function notation of Section 7.3.3(1), printed p.247 / PDF p.278,
the a-block already incorporates its 2a factor, causing the same overlap.
The proof of Proposition 13.2.5(5) and the quotient products used in the
proof of Theorem 13.5.1 also use indivisible-root subsets.

The source-derived route to investigate is the product over indivisible
roots of the blocks

`U_{a,x,f}=U_{a,x,f(a)} U_{2a,x,f(2a)}`,

with the second factor trivial when 2a is not a root, at constant
`f=r`, together with the full centralizer factor `Z(k)_r`. Propositions
7.3.12(4),(5) and algebraic open-cell injectivity provide the intended
route. Merely changing the index while retaining scalar-depth root groups
need not recover the missing depth-r elements of a divisible root group.
This note records a discrepancy and an outstanding independent proof
obligation. The corrections on PDF p.49 give no replacement of
Proposition 13.2.5; the proposed route is not an authors' erratum or an
already proved corrected theorem.

The eighth pass records `MoyPrasadProductStatement` (artifact
`38dd6045-a386-43d6-a804-1de56fa51d14`, first published in Library
commit `63d9b857523edf47443b7bf30844159e526d00b0`), which states this
route on supplied data. For r > 0, a positive system given by a generic
cocharacter and injective enumerations of the indivisible roots of each
sign, the ordered product of the negative blocks `U_{a,x,r} U_{2a,x,r}`,
the full factor `Z(F)_r` and the positive blocks is a bijection onto
`P_{x,r}`. Proposition 7.3.12(5) has the factor `Z♯_{x,r}` and the
target `G(k)♯_{x,r}` instead. The statement's Markdown derives the
full-filtration form from Proposition 7.3.12(3)–(5), the proof of Lemma
7.3.16 (`Z♯_{x,r} ⊆ Z(k)_r`), V 6, Definition 7.3.3(3) and the open cell
of Proposition 2.11.3(2). For `G_m`, `Z♯_{x,r}` is trivial while
`Z(k)_r`, which equals `P_{x,r}`, is not. The proof obligation stays
open until a proof of the statement is published; its proof task is Task
5579 (`f97b9951-9063-4099-b8dd-b986fd1f7205`).

The ninth pass records `MoyPrasadLeviStatement` (artifact
`abed4e85-f69b-404f-ab1b-76a194d2d0d0`, first published in Library
commit `6bff2655fd831aefb39f6688f904aa7410cb0f73`) for parts (5) and
(6). Its Markdown derives both parts from part (3) as in the proof on
PDF p.500, with the roots of the Levi innermost in the ordered product
and the open cell of Proposition 2.11.3(2). Definition 13.2.4(2) prints
the first inclusion as `aN^+a^{-1} ⊂ N`, which holds for every
`a ∈ A_M(k)` since `A_M` normalizes `N`; the statement uses
`aN^+a^{-1} ⊂ N^+`, the analogue of the printed second inclusion
`a^{-1}N^-a ⊂ N^-`. This is a derived reading, not an authors' erratum.
The proof task is Task 5620 (435ee887-a640-423a-bc30-8ad182e6ba9e).

The sixteenth pass (13 November 2026) records both proofs on supplied
data. `moyPrasadProduct` (Task 5579, artifact
`83e1844b-0b02-449f-b4bd-354ad0c47926`, Library commit `cfedefb6`)
proves `MoyPrasadProductStatement` by combining Worker 164's
`orderedMoyPrasadProduct_injective` and
`range_orderedMoyPrasadProduct_eq`. This discharges the part (3)
obligation in its indivisible-root block form; the printed all-root
form is not claimed. `moyPrasadLevi` (Task 5620, artifact
`2828d56d-f6c0-44e3-9917-a1c3bfec0d29`, Library commit `cc5aa77f`)
proves `MoyPrasadLeviStatement` and takes the ordered covering from
`range_orderedMoyPrasadProduct_eq`.

### The double-root bound in Proposition 13.2.5(1), (2) and (4)

Definition 7.2.1, printed p.245 / PDF p.276, asks that the `Z`-component
of the commutator of `u ∈ U_a(k)` and `u' ∈ U_{-a}(k)` lie in `Z(k)_r`
for `r = φ_a(u) + φ_{-a}(u')`. For a multipliable root the proofs of
Proposition 13.2.5 need more. In the proof of part (4), PDF p.500, take
`u ∈ U_{2a,x,r}` and `u' ∈ U_{-a,x,s}`. Then `φ_a(u) ≥ r/2` by V 4, and
Definition 7.2.1 places the `Z`-component only in `Z(k)_{r/2+s}`, while
`P_{x,r+s} ∩ Z(k) = Z(k)_{r+s}` by Lemma 7.3.16. The proof of part (1)
cites Proposition 7.3.17, PDF pp.283–284 (`G(k)_{x,r}` is normalized by
`G(k)_{x,0}`), whose proof treats commutators of `U_{a,x,0}` with
`U_{b,x,r}` by V 3; V 3 excludes `b = -2a`, and there Definition 7.2.1
gives only `Z(k)_{r/2}` where `Z(k)_r` is needed.

KP's own computation contains the missing bound. In the proof of
Proposition 7.1.1, PDF pp.270–271, the `Z`-component in `SU_3` is the
torus element of `γ = 1 + αα' + ββ'`, and `u ∈ U_{2a}(k)` means `α = 0`,
so `γ - 1 = ββ'` has valuation `2(φ_a(u) + φ_{-a}(u'))`. Lemma 7.2.3,
PDF pp.276–277, records only Definition 7.2.1. The corrections of 1
November 2024 (Chapter 7 at PDF pp.33–36, Section 9.8 at PDF p.41,
Chapter 13 at PDF pp.49–50) do not address this.

The ninth pass records `MoyPrasadDoubleRootStatement` (artifact
`a10cf7b9-8244-4125-94c1-9eb4aa404e35`, first published in Library
commit `297a8ef0ba780a488196cf62285af3ded2e2baa6`). Its predicate
`IsDoubleRootCommutatorFriendly` asks for `Z(F)_{2r}` when
`u ∈ U_{2a}(F)` or `u' ∈ U_{-2a}(F)`; the statement restates the
published covariance and commutator statements with it as an extra
premise, and `CentralizerFiltrationDoubleRootExistenceStatement` asserts
a filtration satisfying it. The original statements are not withdrawn:
no counterexample is known, but their premises do not include the bound
and no derivation of them from the published filtration axioms is known.
The Markdown derives the bound for the actual Section 9.8 filtration.
This is a source-derived reading, not an authors' erratum. The proof
tasks are Task 5645 (03d53828-0d05-4e3f-960c-dd74256072e0), Task 5646
(a5f35e49-1e6a-4f03-8986-d7b2db8ac2b0) and Task 5647
(389efdd6-dfb3-478d-b92e-a38a722094e1). Worker 164's published
`isMoyPrasadAt_unique_of_double_opposite_bound` (module
`MoyPrasadCovarianceReduction`, Library commit `297a8ef0`) proves the
conclusion of the original covariance statement from its premises and
the single mixed case `U_{a,x,0}` against `U_{-2a,x,r}`, so the gap in
parts (1) and (2) is exactly this case.

The eleventh pass (13 November 2026) records that the gap is real for
supplied filtrations. Worker 46 (Task 5512) gave an unformalized paper
counterexample: ramified quasi-split SU(3) over `Q_2`, split by
`Q_2(√2)`, with the smallest centralizer filtration `Z'` satisfying the
four published filtration axioms (decreasing, separated, `Z'_0 = Z(F)^0`),
assuming the actual building data satisfy the apartment axioms. The pair
`u(0,√2) ∈ U_{2a,x,1/2}`, `u⁻(2,-2) ∈ U_{-a,x,1/2}` has a commutator with
`Z`-component `t(1-2√2) ∉ Z'_1`, so `MoyPrasadCommutatorStatement` fails;
conjugating `u(0,√2)` by `u⁻(√2,1) ∈ U_{-a,x,0}` gives `Z`-component
`t(1+√2) ∉ Z'_{1/2}`, so `MoyPrasadCovarianceStatement` and
`MoyPrasadFiltrationStatement` fail. `Z'` violates
`IsDoubleRootCommutatorFriendly`, so the double-root statements are not
affected, and KP's own filtration of `T(k)` is not refuted (for odd `p`
the smallest filtration equals it). The original statements remain
published as recorded targets; Tasks 5511 and 5512 retire without
proofs, and Tasks 5645 and 5646 carry the covariance and commutator
content. The argument is Worker 46's public note
`notes/bruhat-tits/moy-prasad-supplied-filtration-counterexample.md`,
present in Library commit `4b619cdd`.

The sixteenth pass records that `moyPrasadDoubleRootCovariance` (Task
5645, artifact `af35972d-1995-402a-849e-649029adc21d`) and
`moyPrasadDoubleRootCommutator` (Task 5646, artifact
`571e0374-6bb2-407d-9344-c067e9663d8a`), both first in Library commit
`cfedefb6`, prove the two double-root statements on supplied data. A
filtration with the double-root bound is still only asserted, by the
unproved `CentralizerFiltrationDoubleRootExistenceStatement` (Lemma
9.8.1 row).

### Finite depths and the infinite term in Proposition 13.2.5

The bounded-open assertion is restricted to finite nonnegative augmented
depths: `r` or `r+` for a nonnegative real r, excluding infinity.
Section 1.6, printed pp.66–67 / PDF pp.97–98, includes infinity in the
augmented index set and defines

`P_{x,infinity}=intersection_{t>=0, t real} P_{x,t}={1}`

for a separated filtration. This term need not be open. Corollary 7.3.14,
printed p.251 / PDF p.282, gives boundedness generally but asserts
openness only when the concave function never takes infinity. For a
concrete check, take `G=G_m` over `Q_2`. Formula (13.1.1), printed p.467 /
PDF p.498, gives `P_{x,n}=1+2^n Z_2` for integers `n>=1`; the standard
and minimal congruent filtrations agree for this induced torus. Their
intersection is `{1}`, which is not open: the distinct elements `1+2^n`
converge to 1.

The printed wording of Proposition 13.2.5 includes the whole extended
index set in its bounded-open assertion. The finite-depth restriction
here is an independently justified clarification of that wording,
separate from the root-index issue above. The corrections of 1 November
2024, PDF pp.49–50, do not supply this clarification.

At finite nonnegative augmented depths, the remaining assertions retain
apartment independence, conjugation covariance, normality in the full
point stabilizer, and the commutator bound. The Iwahori decomposition is
asserted at finite positive augmented depths. Its product map is a
homeomorphism of the three factors as in Definition 13.2.4, rather than
a group direct product. Levi compatibility at finite nonnegative
augmented depths requires x in the actual subbuilding `B(G)_M` and the
point `x_M` from (9.7.1). Over a general Henselian field the finite-depth
subgroups are bounded and open; compactness needs the local-field
topology.

### Lie and dual lattices

Section 13.3.1 defines the Lie lattice for nonnegative r from the actual
smooth congruence model, and uses Proposition 8.5.16's integer-shift
periodicity to extend it consistently to every real r. The dual convention is

`g^*_{x,r}={X in g^* | X(Y) in m for every Y in g_{x,(-r)+}}`.

The maximal ideal, negative depth and strict plus all belong to the
pairing convention. Section 13.3.2 identifies
`Lie(Gred_x)=g_{x,0}/g_{x,0+}` using the actual special-fibre maps and
the smooth kernel of Proposition 8.5.18. It does not identify the
maximal reductive quotient with the whole special fibre.

Section 13.3.3 gives the invariant lattice over k from the O-lattice
over K, and an intrinsic span using the centralizer lattice and affine-root
lattices with `psi(x)>=r`. Its explicit Chevalley–Steinberg basis formula
over o requires G quasi-split; the general model/lattice and intrinsic
span constructions have no such extra hypothesis. Section 13.3.4 obtains
actual f-rational representations of Gred_x on the Lie and dual strict
graded pieces from model conjugation. Descent, lattice preservation and
factorization through Gred_x all remain construction and proof obligations.

### All three alternatives of Theorem 13.5.1

With the minimal congruent torus filtration, x in the constructed building
and real `0<r<=s`, retain the three alternatives separately:

1. A maximally split maximal torus of G_K becomes induced after a tame
   base change, and `s<=2r`.
2. `r=r0+n` with `0<=r0<1`, n a positive integer, and `s<=r0+2n`.
3. `0<r<=s<=2r<=r+1`.

At least one alternative gives an isomorphism of abstract abelian groups
`P_{x,r}/P_{x,s}` with `g_{x,r}/g_{x,s}`, compatible with unramified
algebraic extensions. Automorphism equivariance is asserted under (1) or
(2). It is not asserted under (3) alone. The constructions from (1) and
(2) agree when both apply. This is neither an unconditional exponential
map nor a claim of a k-linear group map.

Alternative (2) uses A.5.19 on the actual congruence models. Over K,
(1) and (3) use indivisible-root quotient products, root-model congruence,
A.5.19, and the torus comparisons B.6.9 and B.10.17 respectively.
Descent uses the smooth connected unipotent special fibres and the
corresponding group and Lie-lattice cohomology vanishing. Corrections
PDF p.50 repair B.10.8 and B.10.14 and add B.10.15; Gamma-stability
and smooth model descent of the minimal congruent filtration belong to
this dependency boundary.

### The ambient group in corrected Proposition 13.5.2

This proposition additionally assumes that k is a local field with finite
residue of characteristic p. The authors' correction changes the ambient
group in part (1) to `G(k)^0`. Each `P_{x,0+}` is an open pro-p subgroup
there, maximal exactly for chamber points. Every maximal open pro-p
subgroup of `G(k)^0` is the positive-depth subgroup of an Iwahori, which
is its normalizer in `G(k)^0`. Neither assertion extends here to the
full `G(k)`. The source proof uses actual compactness, finite filtration
quotients, fixed points, type preservation, reduction and the rational
parabolic correspondence. The published
`Langlands.BruhatTits.MaximalProP.AvailableMaximalProPStatement` states
the four conclusions over facets of `B(G)`, with `G(F)^0` as ambient group
throughout, for every available `KPBuildingAssignment` (Proposition 13.5.2
row). The theorem `availableMaximalProP` (Task 5903, artifact
`c86654f8-89f0-4107-b4af-6473d7fd30e0`, Library commit `410c7947`)
proves it. It proves the normalizer identity at one apartment chamber
from the Iwahori factorization and the split Tits-system normalizer
theorem, and transports it to every chamber by conjugation in `G(F)^0`.
Existence of available data, `BruhatTitsAvailabilityStatement`, is
unproved (Theorem 9.2.7 row).

### Later degeneracy and instability

Propositions 13.6.7 and 13.7.4 concern Lie cosets. The nilpotence notion in
Definition 13.6.5 is contraction to zero by a k-defined cocharacter.
The printed example in Remark 13.6.6 over `F_2((t))` does not distinguish
this notion from Jordan nilpotence. For a nonzero x in characteristic two,
put

```text
X = [[1, x], [x^(-1), 1]],
B = [[x, 1], [1, 0]],
B^(-1) = [[0, 1], [1, x]].
```

Then `det(B)=1`, `X^2=0` and `B^(-1) X B=x^(-1) E_12`. Consequently
the k-defined cocharacter
`lambda(u)=B diag(u,u^(-1)) B^(-1)` satisfies
`lambda(u) X lambda(u)^(-1)=u^2 X`. This orbit map extends to u=0
with value zero, including when x is the nonsquare uniformizer of
`F_2((t))`. Thus the displayed matrix is nilpotent in Definition 13.6.5's
sense as well. For nonsquare x, the matrix `x^(-1) E_12` is not
SL_2(k)-conjugate to E_12: any conjugating matrix preserves their common
kernel k e_1, so it is upper triangular with determinant one and scales
E_12 by a square. Thus nonconjugacy to the single matrix E_12 does not
establish the absence of a contracting cocharacter.

This calculation diagnoses an independent source discrepancy in the
printed example and its assertion that every contracted element is
conjugate to E_12. The corrections of 1 November 2024 do not repair
Remark 13.6.6. No Lean proof of this calculation is recorded here, and
any broader claim that the two nilpotence notions differ needs a
separately checked witness. The targets continue to use the
k-defined contraction convention of Definition 13.6.5.

The perfect residue field does not imply that k is perfect. A degenerate
coset contains an element nilpotent in this cocharacter sense.

### The empty-root boundary in optimal-point reduction

The first clause printed in Proposition 13.6.7, printed p.481 /
PDF p.512, asks for an optimal point y and a real s>r such that the
entire degenerate coset is contained in `g_{y,s}`. Definition 13.4.2,
printed p.472 / PDF p.503, requires a nonempty finite subset of the
affine-root set Sigma to define an optimal point. Consequently the
printed universal assertion fails for groups with empty relative roots.
Lemma 13.4.4, printed p.473 / PDF p.504, also asserts an optimal-point
replacement and explicitly uses a nonempty root subset in its proof.
Its unrestricted formulation has the same boundary.

For a concrete regression, let `G=G_m` over `Q_2` and take `r=1`.
The reduced building is the singleton x, by the reduced-apartment
convention of 4.1.4(A0), printed p.158 / PDF p.189. Both the relative
and affine root sets are empty, so Definition 13.4.2 supplies no optimal
point. Formula (13.1.2), printed p.467 / PDF p.498, gives
`g_{x,1}=2 Z_2` and `g_{x,1+}=4 Z_2`; standard and minimal congruent
filtrations agree for this induced torus. The coset `Xi=0+g_{x,1+}`
contains zero, which is contracted by the identity cocharacter. It is
therefore degenerate by Definition 13.6.5. It is already contained in
`g_{x,2}`, and its graded vector is zero and hence unstable. There is
nevertheless no literal optimal point. This example isolates the
optimality defect and does not refute deeper containment or instability.

The general connected-reductive scope of the program remains in force.
An optimal-point target under a nonempty-relative-root hypothesis must
be distinguished from a general depth-raising target omitting optimality
and from any separately derived convention or extension covering empty
roots. These remain statement and proof obligations; no extension of
Definition 13.4.2 is adopted or proved here. The corrections of
1 November 2024, PDF pp.49–50, supply no repair of Definition 13.4.2,
Lemma 13.4.4 or this clause of Proposition 13.6.7. This is an
independently identified source boundary, not an authors' erratum.

The separate clause of Proposition 13.6.7 gives the algebraic
instability target under Gred_x. Its route extends the compatible
contracting cocharacter to the integral model and reduces it to the
graded representation; it does not require a literal optimal point.
Proposition 13.7.4 needs only that the coset meets a lattice at some
greater depth to imply degeneracy, and its equivalence between degeneracy
and algebraic instability invokes this separate instability clause,
without inferring empty-root optimality from Lemma 13.4.4.
The local compactness or perfect-k
hypotheses in nearby Lemma 13.7.2 concern comparison with
valuation-topology orbit closure; they are not added to Proposition
13.7.4. The relevant instability uses algebraic orbit closure over f.
Lifting a contracting residue-field cocharacter uses the actual
surjection `P_x → Gred_x(f)`.

These later rows do not extend the propositions to dual cosets, supply
minimal K-types, or prove supercuspidality. Their implementation remains
after the finite abelian graded quotients, character transport and
nontrivial filtration calculation required for positive-depth acceptance.

## Bundle F: tame descent and embeddings from adapted data

The five added source rows cover corrected Proposition 12.4.1, Theorem
12.9.2, Proposition 12.9.4 and Propositions 14.6.1 and 14.8.4. These
source targets retain the general connected-reductive program. Their
implementation follows the depth-zero release with its representation
consumer, and then positive-depth acceptance. No construction, formal
statement or proof of these targets is recorded by this extension.

### The corrected finite-action fixed locus

Chapter 12 initially works over a Henselian discrete valuation ring O
with fraction field K and algebraically closed residue field. A finite
group Theta acts by K-automorphisms on a connected reductive H, and
`G=(H^Theta)^0`. Its order is prime to the residue characteristic,
with no restriction in residue characteristic zero.

The replacement of Proposition 12.4.1 on corrections PDF p.47 uses
the Section 12.4 reduction making the maximal K-split central torus
of G central in H. Put `H'=H_der`, `G'=(H'^Theta)^0`, take S maximal
K-split in G, and let S' be its maximal subtorus contained in G'.
For a Theta-fixed point x in the enlarged building of `Z_{H'}(S)`
and **every** apartment A of that building containing x, the conclusion is

`A^Theta = V(S') + x = enlargedB(Z_{H'}(S))^Theta`.

The point x, the apartment quantifier and the central translation
space belong to the statement. The proof glues the central V(Z) actions
on apartments through x using parahoric transitivity, and identifies
`V(Z)^Theta=V(S')`. Its torus step needs a maximal split torus of
`Z_{H'}(S)` containing S'; the correction's phrase about a torus of
H' containing S must be interpreted with S and S' distinguished.
This records a proof obligation, without claiming its formal resolution.
The surrounding corrections also delete the indicated sentences in
Section 12.4, require a nonempty bounded subset of the **intersection**
of the two fixed loci in 12.4.2, and replace the vertex-to-facet argument
in 12.7.1 (corrections PDF pp.47–48).

### Tame descent uses the inherited valuation and compatible metrics

Section 12.9 returns to a discretely valued Henselian k with perfect
residue field. The uniquely extended valuation omega is used on every
algebraic extension. Renormalizing an extension valuation independently
would change the apartment and filtration comparisons.

For connected reductive G/k and a finite tamely ramified Galois
extension l/k, Theorem 12.9.2 identifies the **reduced** building
`B(G)` with `B(G_l)^Gal(l/k)` as a metric space (book PDF pp.494–495).
Tameness concerns the ramification index. The unramified degree can
be divisible by the residue characteristic. Remark 12.7.2, PDF p.490,
chooses compatible metrics by allowing rescaling on simple factors.
The identification uses these metrics.

The proof separates the maximal unramified subextension k' of l/k
from the totally ramified part. For maximal unramified extensions K
and L of k and l in one separable closure,
`L=K tensor_{k'} l` and `Gal(L/k')=Gamma times Theta`, with
`Gamma=Gal(K/k')` and `Theta=Gal(l/k')=Gal(L/K)`. Apply the corrected
finite-action theorem to `Res_{l/k'}(G_l)` over K and apply actual
Chapter 9 unramified descent in both orders, then over k'/k.
The corrected 9.2.7 certificate remains necessary. The intermediate
enlarged-building construction does not change the theorem's reduced
target. The result imposes no split or quasi-split hypothesis on G/k.

### Positive-depth subgroup and integral-model descent

Proposition 12.9.4, book PDF pp.495–496, is in the maximal-unramified
K context, with algebraically closed residue field. G is quasi-split
over this K. Let L/K be finite tame Galois, `Theta=Gal(L/K)`, S maximal
K-split in G, and T the K-torus containing S whose base change T_L
is maximal L-split in G_L. For concave f on the roots plus zero of
`(S,G)`, retain **f(0)>0**. Let F be its pullback by root restriction,
and take `x in A(S) subset A(T_L)`. The conclusions are

`G(L)_{x,F}` is Theta-stable,
`G(K)_{x,f}=(G(L)_{x,F})^Theta`, and
`G_{x,f}=(H_{x,F})^Theta`, where `H=Res_{L/K}(G_L)`.

The last equality is an equality of actual smooth integral group
schemes. Proposition 12.8.5 separately requires the torus-filtration
equality at `r=f(0)`, along with surjective root restriction and
Theta-orbit fibres. In the Weil-restriction application its maximal
split torus T_H must be distinguished from the K-torus T of G.
The 12.9.4 proof checks root fibres through the quasi-split centralizer
`Z_G(S)` and its absolute roots. A formal proof must also discharge
the torus-filtration comparison. The correction on PDF p.48 moves
the torus-filtration assumption at `r=f(0)` after the sentence
defining f and its pullback F. Both definitions already occur
together in that sentence.

The source route uses ordered root products, translation to depth
zero, the parahoric comparison in 12.7.1 and uniqueness of smooth
models in 2.10.11. Multipliable-root indexing needs checking against
7.3.3 and 7.3.12, in light of the Bundle E diagnosis. This note makes
no new discrepancy claim about 12.8.5 and supplies no extension to
arbitrary depth-zero concave functions.

### Embeddings depend on adapted data

Chapter 14 uses discretely valued Henselian k with perfect residue
field. Admissibility means equivariance on k-points and affine
apartment maps with the induced cocharacter translation map
(14.0.1). For a closed immersion `G <= H`, isometry uses the metric
induced from H on cocharacter spaces (14.2.2).

Definition 14.5.1 and Remark 14.5.2 require the normalizer-fixed
orbit, the apartment map taking x to y, and stabilizer inclusion at
**every** translate. With `M=Z_H(A_G)`, the reduced condition is
`G(k)^1_{x+v} <= M(k)^1_{y+v}` for every `v in V(S/A_G)`;
the enlarged condition uses full point stabilizers for every
`v in V(S)`. The pointwise and parahoric conditions remain distinct.

Proposition 14.6.1, PDF pp.533–534, constructs a unique admissible
embedding of the enlarged buildings taking a specified adapted
pair `(x_tilde,y_tilde)` to one another. Uniqueness is relative to
that pair. The associated reduced map `phi:B(G)->B(M)` restricts
to the normalizer-fixed-orbit apartment map of 14.4.1; its partner
psi is the chosen Levi-building embedding into the enlarged
H-building. The quotient construction of 4.4.4 uses normalizer
equivariance and stabilizer compatibility at every apartment point.
Both terms of its equivalence relation must survive formalization.

Proposition 14.6.2 describes when different adapted pairs give the
same map. Example 14.0.3 obstructs a reduced admissible map from
the diagonal split torus into SL_2: its reduced building is a point,
but the torus fixes no point in the SL_2 tree. Its enlarged apartment
does embed after choosing an origin. Lemma 14.0.5 also permits
central translations for enlarged maps of isomorphic groups.
These remain source-backed regression targets.

For a general homomorphism f, the condition at book PDF p.523
requires the lift `f':G_sc -> f(G)_sc` on each k_s-simple factor
(equivalently each k-simple factor) to be trivial or an isomorphism
onto its image. The source first treats the faithfully flat quotient
onto f(G), then the closed immersion. Characteristic zero satisfies
the lift condition automatically; Frobenius in positive characteristic
need not. The resulting maps need not be injective or canonical.
These propositions supply equivariance, apartment derivatives and
stabilizer compatibility. Positive-depth Moy–Prasad comparisons
or morphisms of integral models require separate sources and proofs.

### Strict-Henselian existence and the separate general-k descent

Section 14.8 explicitly assumes strictly Henselian k. Proposition
14.8.4, PDF p.539, uses an absolutely special x_tilde in enlargedB(G)
and a finite Galois splitting extension l/k for both G and H,
without a tame hypothesis. Choose y1_tilde in enlargedB(H_l) with
`G(l)_{x_tilde} <= H(l)_{y1_tilde}`. Its closest point y_tilde in the
embedded **enlargedB(H)** gives an adapted pair. The rendered
proposition confirms the enlarged notation and full stabilizers.
This base building is not identified with the full Galois fixed
locus for an arbitrary ramified splitting extension.

Existence requires the absolutely special point from 7.11.4,
boundedness of its full stabilizer and the building fixed-point
theorem to obtain y1_tilde. The split construction in 14.8.2 uses
root lattices and homogeneous polynomial coordinates. Projection
in 14.8.3 then uses equivariance under group actions and translations
to establish the stabilizer condition at every translate.

For general k, 14.5.6 gives closedness and segment containment of
the adapted-y locus. Proposition 14.7.1 gives the space of embeddings
an evaluation-independent complete NPC metric. Proposition 14.7.2
uses nonemptiness to obtain an equivariant embedding by 1.1.19.
Proposition 14.7.3 applies this over the maximal unramified extension
and descends by Chapter 9. Corrected nonempty convexity does not
prove the needed nonemptiness; that comes from the existence
argument. This descent remains separate from tame descent in 12.9.2.

### Independent repairs in the nearest-point proof

Proposition 1.1.20, book PDF pp.38–40 and corrections PDF pp.1–3,
uses a complete NPC geodesic space and a nonempty closed convex
subset Y. Its projection exists uniquely, is continuous, and is
equivariant under isometries preserving Y setwise. These theorem
conclusions remain the target.

The corrected proof on corrections PDF p.2 prints the estimate
`d(y1,y2)^2 <= 2 epsilon (2r+epsilon)`, for points at distance less
than `r+epsilon` from x, where `r=inf_{y in Y} d(x,y)`.
This estimate fails for `X=Y=R`, `x=0`, `r=0`, `epsilon=1`,
`y1=-3/4`, `y2=3/4`: its left side is 9/4 and right side is 2.
It also fails with positive r: in the Euclidean plane, take Y the
line of height 1, `x=(0,0)`, `r=1`, `epsilon=1/2`, and
`y1=(-1,1)`, `y2=(1,1)`. Their distances are `sqrt(2)<3/2`,
but the squared separation is 4, greater than the proposed 5/2.

For their midpoint m in Y, the NPC inequality instead gives

`2r^2 + (1/2)d(y1,y2)^2 <= d(x,y1)^2+d(x,y2)^2 < 2(r+epsilon)^2`,

hence `d(y1,y2)^2 < 4 epsilon (2r+epsilon)`. This suffices for
the minimizing-sequence argument. The coefficient 4 is an
independently derived repair, separate from the authors' printed
coefficient 2.

The correction's continuity proof also uses a multiplicative error
relative to `r=d(x,pi(x))`, requiring the case r=0 separately.
For `x_n -> x`, put `q_n=d(x,pi(x_n))`. The squeeze
`r<=q_n<=d(x,x_n)+d(x_n,pi(x))` gives `q_n -> r`.
Applying the midpoint inequality to the two projections gives

`d(pi(x_n),pi(x))^2 <= 2(q_n^2-r^2)`.

This proves continuity also when r=0 without division by r.
Equivariance follows from uniqueness and the inverse isometry.
The accepted and published `nearestPointProjection` proof implements these
repairs using the squared deficit directly and a neighborhood-filter continuity
argument. They do not change the theorem statement and remain independent
repairs, separate from the authors' errata. The proof and publication evidence
are recorded below and in the Proposition 1.1.20 row.

## Verified Theorem 1.1.15 proofs

Worker 1229 supplied both proof units in task
`e52b85eb-0f5c-46a9-ab48-c8798f0abdc0`. The theorem
`Langlands.Geometry.Metric.KP.barycenter` proves the exact published
`BarycenterStatement`: existence, uniqueness and invariance of the barycenter
of a bounded closed nonempty geodesically convex set. The theorem
`Langlands.Geometry.Metric.KP.boundedSetStabilizerFixedPoint` proves
`BoundedSetStabilizerFixedPointStatement`: one point is fixed simultaneously
by every isometry preserving a given nonempty bounded set. Both targets
quantify over arbitrary carrier universes and complete NPC geodesic metric
spaces. Part (2) imposes no closedness or convexity on the original set and
does not require the fixed point to belong to it.

The barycenter proof uses a squared midpoint estimate and a Cauchy minimizing
sequence, including radius zero and attained minima. The second proof
establishes covariance of the actual closed convex hull under isometries and
applies the first theorem to that hull. The paired proof explanations are
[KPBarycenterProof](../../Langlands/Geometry/Metric/KPBarycenterProof.md) and
[KPBoundedSetStabilizerProof](../../Langlands/Geometry/Metric/KPBoundedSetStabilizerProof.md).

The two acceptance artifacts in the row have unqualified independent approvals
by Reviewer 8669 and Reviewer 8673, respectively. Their machine receipts
`22830777-ddb7-4575-af67-e0781922b6b0` and
`266ae01b-eb72-4600-9a03-e77efef063dc` accept the Lake build, exact target,
unchanged statement and frozen inputs. Both artifacts are accepted and public,
with published integrations in the recorded Library commit. Their frozen,
published and workspace Lean/Markdown hashes agree. Local declaration inspections
also report only `propext`, `Classical.choice` and `Quot.sound`; those inspections
are separate from independent semantic review and proof acceptance. No external
Lean code is adopted by these units.

This verifies both parts of the source theorem recorded in the row. The
separate bounded-action and nearest-point proofs are recorded next. Applying
these metric theorems to a general reductive-group building still requires
that building's construction, completeness and NPC proofs.

## Verified bounded-action and nearest-point proofs

Worker 1249 supplied `Langlands.Geometry.Metric.KP.boundedActionFixedPoint`
in task `a3eadfc8-c446-402c-a08e-dd4d9edbf042`. It proves the exact published
`BoundedActionFixedPointStatement` for independent universes of the metric
carrier and acting group. Completeness and the primitive NPC condition yield
geodesics through the published `completeNPCGeodesic` theorem. The proof
then applies the bounded-set stabilizer theorem to the actual orbit and
shows that every group element acts by an isometry preserving that orbit
setwise. The result is one common fixed point of the original action.
Its paired explanation is
[KPBoundedActionFixedPointProof](../../Langlands/Geometry/Metric/KPBoundedActionFixedPointProof.md).

Artifact `a67bd9ea-5ff4-4b0f-a38c-46350535ec88` has an unqualified
independent approval by Reviewer 9235. Machine receipt
`15409f3a-dd65-41a6-aed2-6f0f859b443e` accepts the Lake build, exact target,
unchanged statement and frozen inputs. Integration
`93f7ad8cdc594b0c8f09f9301559278d` published the exact pair in Library commit
`7543113c99690e18b45f3b22d252e8cf77c3964e`. The frozen and published pair
hashes agree. This focused proof establishes Corollary 1.1.19. The same
child task's published aggregate proof is recorded separately below.

Worker 1229 supplied `Langlands.Geometry.Metric.KP.nearestPointProjection`
in task `023897fd-dccb-460b-831b-41b55d5622de`. It proves the exact
published `NearestPointProjectionStatement` in arbitrary carrier universe.
A minimizing sequence for the real distance infimum converges to a point
in the closed convex subset. The squared midpoint deficit proves minimality,
uniqueness and division-free continuity, and distance preservation gives
equivariance of the same chosen projection under every preserving ambient
isometry equivalence. This includes unbounded subsets, attained infima and
zero minimum distance. Its paired explanation is
[KPNearestPointProof](../../Langlands/Geometry/Metric/KPNearestPointProof.md).

Artifact `c81fc3b9-e90a-4b1a-b55f-605ee138f50f` has an unqualified
independent approval by Reviewer 9173. Machine receipt
`e1e31c37-f176-4148-a0a1-728008e89583` accepts the Lake build, exact target,
unchanged statement and frozen inputs. Integration
`332183b82c0344c5b2ec7d192f1a0387` published the pair in Library commit
`7a2e42fd31831029d34cafb155ffad911920df25`. The frozen, published and
workspace pair hashes agree. The focused task is closed by completion
declaration `c70b6dd9-9f2a-4530-ae97-b5fd413a2bbb`. This proves the
qualitative Proposition 1.1.20, including the independent proof repairs
above, while the building and Bundle A obligations remain open.

## Verified aggregate metric fixed-point interface

Worker 1249 also supplied
`Langlands.Geometry.Metric.KP.metricFixedPointFoundation` in task
`a3eadfc8-c446-402c-a08e-dd4d9edbf042`. It proves the exact published
`MetricFixedPointFoundationStatement.{uX, uG}` by conjunction introduction
from the six published component proofs: geodesic uniqueness, closed-ball
convexity, the closed convex hull, barycenters, bounded-set stabilizer fixed
points and bounded-action fixed points. The first three retain their NPC and
geodesic premises; the next two additionally require completeness; the last
requires a nonempty complete NPC space and constructs its geodesics. The
aggregate assumes none of these statements as an input and preserves the
independent metric-carrier and group universes. Its implementation is described
in [KPMetricFixedPointFoundationProof](../../Langlands/Geometry/Metric/KPMetricFixedPointFoundationProof.md).

Artifact `dcb96935-687d-4cac-bc42-f5976f6b6c30` has an unqualified
independent approval by Reviewer 9329. Machine receipt
`81bf2fd0-4da6-47c7-8c88-292d0bce0ec7` accepts the Lake build, exact target,
unchanged statement and frozen inputs. Integration
`4038c30168bc4a2495d3d43f73aa59bb` published the pair in Library commit
`286dd3b743f0437d22db0e793222073b9424e3eb`. The frozen, published and
workspace pair hashes agree. A local declaration inspection reports
`uX` and `uG` and only `propext`, `Classical.choice` and `Quot.sound`.
That development check is separate from the independent review and proof
acceptance. No external Lean implementation is adopted.

This is an internal aggregate of the existing metric statements, not a further
source theorem or a new structured row. It closes the aggregate proof obligation.
The actual reductive-group building and the proofs of its completeness and
nonpositive curvature remain required before applying this interface to it.

## Initial interfaces and the next mathematical gates

Metric definition child `bd4b31f8-44f8-447c-b747-e26d93a271d1` supplied the
published module `Langlands.Geometry.Metric.KPDefinitions`, namespace
`Langlands.Geometry.Metric.KP`, authored by Worker 1221. Its definition
candidate `3baeb443-a6c3-4cdf-9ef8-cce5431d3585` was independently accepted
and published in Library commit `6fd0709bd33fa6c33b4d74b4b638cfc51428b8f1`.
The module uses a primitive midpoint inequality and separates geodesic
existence, completeness, convexity and barycenters. Its radius and joint
diameter take values in the extended nonnegative reals; finite real readings
require explicit boundedness and nonemptiness. This definition publication
supplied the interface used by the subsequent Theorem 1.1.15 proofs above.

The corrected convexity predicate excludes the empty set. The published
Theorem 1.1.15 proofs establish actual barycenter existence and uniqueness,
including radius-zero cases, and the common fixed point for bounded-set
stabilizers. The published Corollary 1.1.19 proof now supplies an actual
common fixed point for every bounded isometric group action under its metric
hypotheses. Proposition 1.1.20 supplies the projection for the same metric
foundation. The building application must still prove completeness and
nonpositive curvature of the constructed building.

Derived quotient child `cd3fd695-b511-4653-8f4d-769e99d8aab0` asks for the actual
algebraic quotient, its group action, apartment embedding criterion and exact
stabilizer formula from an explicit covariant subgroup family. It also asks for
comparison maps under a universally quantified subgroup inclusion. This is a
conditional construction prerequisite. A parahoric family and the full quotient
point stabilizer need not coincide. The child must retain the normalizer's
point stabilizer, exhibit a proper-containment example, and avoid inferring a
building isomorphism from quotient surjectivity alone.

The existing algebraic-group program
`2b5e4a00-9d44-49a4-9c89-979fb5b6233e` owns dynamic parabolics, centralizers,
unipotent groups and general algebraic open cells. Its published
`Langlands.GroupScheme.Dynamic.Basic` interface is a reuse input, not by itself
a proof of every assertion of Propositions 2.11.1–3. General open cells require
the source's scheme-theoretic open immersion, beyond an assumed product map or
a split matrix instance. A verified reuse bridge remains required for the complete
source targets in the ledger.

The common field interface remains Mathlib's `IsNonarchimedeanLocalField`.
`Langlands.LocalField.ResidueNormalization` and the existing canonical
`Langlands.PadicField` realization are reuse inputs. Field child
`1453f721-e7ff-4221-87e1-6921dfa200e4` asks for an actual Laurent-series fixture
over every finite field, residue and normalization comparisons, negative
monomial calculations and a characteristic-two test. Its publication as a task
supplies no field theorem. Generic topologies and compact/open integral-point
results remain owned by Conrad program
`886bf565-95e9-4dc6-8a9d-73284a523668`; the KP program constructs its specific
models and later proves the comparisons.

## Verified finite separable-unramified prerequisite

Workers 60 and 1199 supplied the finite arithmetic and Galois proof chain in
task `490c0b7e-eb14-4ac6-847b-0877eeee4c27`; Worker 118 contributed the target
design and original-source correspondence. The published theorem
`Langlands.LocalGalois.Separable.separableUnramified` proves the exact
`Langlands.LocalGalois.Separable.SeparableUnramifiedStatement.{u}`.
Its implementation and source correspondence are described in
[SeparableUnramifiedProof](../../Langlands/Galois/Local/SeparableUnramifiedProof.md);
the full target is explained in
[SeparableUnramifiedStatement](../../Langlands/Galois/Local/SeparableUnramifiedStatement.md).

The base field has the supplied `Field`, `ValuativeRel`, `TopologicalSpace`
and `IsNonarchimedeanLocalField` structures. The theorem covers mixed and equal
characteristic in arbitrary universe `u`, including imperfect base fields. It
uses the actual `SeparableClosure F`, the kernel of its residue action and
`inertiaFixedField F`, with the canonical spectral integer rings and residue
algebras. For every finite intermediate field `E`, containment in that fixed
field is equivalent to `ArithmeticUnramified F E`: equality of the mapped
base maximal ideal with the extension maximal ideal, together with
separability of the canonical residue algebra. The finite field `E/F` need
not be Galois. Every finite set of fixed-field elements, including the empty
set, lies in a finite Galois arithmetically unramified intermediate field of
the same separable closure.

The proof composes the fixed-field containment equivalence, the inertia
residue-degree criterion and the finite arithmetic criterion. It then
discharges the maximality premise of the finite Galois exhaustion helper.
The latter adjoins the actual finite image and takes its normal closure.
The auxiliary units construct the closed-fiber residue map and spectral
residue-tower comparisons and prove the criteria used in this composition.

| Published unit | Independent acceptance and machine evidence | Publication |
| --- | --- | --- |
| Finite spectral arithmetic, `Langlands.Galois.Local.SeparableUnramifiedFiniteArithmetic`; artifact `028d9e7a-cc8c-4f00-9706-e405e0627aba` | Reviewer 10412; definition-unit receipt `8909b413-e583-47be-8c15-92c868f35f3e` | Integration `ee589f5fa2644991a08a30104e6fb1e6`, commit `428fa7c08e2fd98ecc08fa4e170f793c3c868556` |
| Spectral residue comparisons and inertia criterion, `Langlands.Galois.Local.SeparableUnramifiedGaloisProof`; artifact `98eb0a98-5a25-4a54-b5ae-d5e22824f993` | Reviewer 10518; definition-unit receipt `49b5153b-3ebb-44f9-91d5-3372c007c190` | Integration `ba2ebc0c2928411fae9ffd43610aad2f`, commit `3c03a45ac21fd6b32cc3c822e5a641caace16a2b` |
| Exact finite maximality and exhaustion proof, `Langlands.Galois.Local.SeparableUnramifiedProof`; artifact `95eb8dc1-5efe-43fe-adc4-19badf5334cd` | Reviewer 10693, unqualified approval; proof receipt `9d93044d-b751-4a4b-946d-7b9c2a7359bb` accepts the Lake build, exact target, unchanged statement and frozen inputs | Integration `b9748a28d74d43d7b8fa8d9496dbe082`, commit `0bafb17fad89ec0e812a3746bcaf72be623fc7d3` |

All three artifacts are independently accepted and public. Their full
Lean/Markdown pairs were read and their frozen and published hashes agree.
The final pair also matches Library
`690e7bce992fb723bd66806fa2db3acd6dc07d78` and the workspace. Development
inspection `954d6b74-e233-4e84-9802-fe0233826da7` succeeds with zero diagnostics,
universe parameter `u`, and only `propext`, `Classical.choice` and `Quot.sound`.
That development inspection is separate from the proof receipt and review.

The source formulation comes from Serre, *Local Fields* (1979),
II §2 Proposition 3 and its corollaries (printed pp. 28–29),
III §5 Theorems 1–3 and Corollary 1 (printed pp. 53–55), and the
inertia correspondence in I §7 Propositions 20–22 and IV §1
Proposition 1 and the corollary after Proposition 2 (printed pp. 21–22,
62–63). The registered source is `serre-1979-local-fields`, SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`,
read with `serre-book-corrections-2019`. KP §2.5(c), printed p. 88,
uses the maximal unramified extension inside a separable closure; the
November 2024 corrections retain that setup. This is a local-field
prerequisite for the torus norm and descent work.

Residue algebraic closure, value-group discreteness, the DVR structure and
Henselian arithmetic of the infinite fixed field remain the separate
`SeparableUnramifiedArithmeticStatement` proof obligation in task
`991bd3f6-103a-4fbb-9cda-a9df4df94581`. The finite theorem assumes no
completeness or local compactness of that infinite field. Torus norm-choice
independence, the actual descended building and the full corrected
Theorem 9.2.7 certificate remain open.

## Verified chamber and Iwahori–Weyl statements

Two source rows record the published **statements** below; the fifth pass
adds the proof of the first and of part (4) of the second. Worker 118 checked the
complete Lean/Markdown pairs, their independent semantic approvals and their
publication records. Each of the four primary files matches its frozen archive,
the workspace copy and Library commit
`25b91125ea94e88d741b206d633e82eb0d87c3e5`. The original passages are
Corollary 7.4.9 and its setup at book PDF pp. 286–288, Theorem 7.8.1 and
7.8.2 at pp. 303–304, and corrections PDF pp. 33, 35–36. The corrected
Chapter 7 premise AS5 remains explicit.

| Published statement pair | Independent semantic approval | Publication |
| --- | --- | --- |
| `Langlands.Geometry.Building.ChamberIwahoriStatement`; artifact `4cc5a2e0-c5a0-442f-b6c1-90c92f2a7c6b` | Reviewer 10982; receipt `190e7b13-2970-43af-abdd-5c0b883e5973` | Integration `adbff60d5c1e426e920fab17aeab316f`; commit `25b91125ea94e88d741b206d633e82eb0d87c3e5` |
| `Langlands.Geometry.Building.IwahoriWeylStatement`; artifact `90c646e0-a29a-4a82-8110-f92b10c12ca3` | Reviewer 10949; receipt `4dee2812-a518-445e-9126-8f3b2797c28b` | Integration `4d7e8a3b43e2438c90e3ec6c8e9d5f2c`; same commit |

The first entry is
`ParahoricBuildingData.ChamberIwahoriDecompositionStatement`, with the
implicit field and group parameters and the supplied argument
`P : ParahoricBuildingData G`. It assumes
`P.apartment.SatisfiesApartmentAxioms P.centralizer`, an actual chamber,
an interior point and a generic cocharacter. Its facet clause additionally
assumes the face relation and the geometric sign condition. It retains the
sharp products and states their derived full-Iwahori consequences with the
actual full central factor `Z(F)^0`: equality with the point parahoric,
the centralizer intersection, the full/sharp unipotent intersections, and
injectivity and exact range of each product. The ordered clauses allow any
fixed order within each sign and both chamber depths `0` and `0+`; the
facet form uses negative depth `0+` and positive depth `0`. Its unipotent
intersections use the actual dynamic groups. Compact openness is a separate
statement and proof obligation.

The second module contains the four closed targets in the Theorem 7.8.1
row, at universe `u`, as well as the companion chamber-splitting, Iwasawa
and replaced-coset targets. All quantify over supplied actual building
data. The normalities needed to form the component group maps are conclusions
where required. The equivalences are prescribed on every normalizer
representative. Corrected part (2) still needs chamber splitting and the
Iwahori–Tits Bruhat decomposition: the equality `I ∩ N(F) = Z(F)^0`
alone does not prove double-coset injectivity. The added part (4) retains
both quotient bijections and the explicit Chapter 5 Henselian and
perfect-residue hypotheses. Its actual unipotent group is
`standardUnipotentPoints P.i ν ∅`. Its comparison with the single dynamic
unipotent group used by the chamber products was then open. The Library
has since proved it for every cocharacter, generic or not
(`standardUnipotent_empty_eq_dynamic`; see the fourth pass). This update changes only the Corollary 7.4.9 and
Theorem 7.8.1 rows. The Chapter 5 rows (5.3.3 and replaced 5.3.5 from this
module, 5.2.1 and 5.3.4 from the `Langlands.BruhatTits` statements) are
recorded by the second pass of the 8 November 2026 refresh.

The following focused proof tasks have been published. Their IDs record
obligations and supply no proof evidence in this note. All unqualified global
targets below belong to `Langlands.Geometry.Building`; the chamber targets
belong to its `ParahoricBuildingData` namespace.

| Exact target or targets | Published proof task |
| --- | --- |
| `ChamberIwahoriDecompositionStatement` | `0e645cc1-7bb2-467a-9835-9d16f29b985f` |
| `ChamberIwahoriCompactOpenStatement` (separate target) | `0afe58ab-4d40-41b0-a74d-258400979322` |
| `IwahoriWeylExactSequenceStatement`, `IwahoriWeylChamberSplittingStatement` | `fc0c8f82-31e8-47dd-ac37-ab6bee878f46` |
| `IwahoriDoubleCosetStatement`, `ParahoricDoubleCosetStatement` | `3b797835-655c-4a67-b6e7-791615474d75` |
| `IwasawaDecompositionStatement`, `UnipotentNormalizerCosetStatement` | `0b383eb0-185c-415b-8def-5fcbac419374` |
| `UnipotentIwahoriDoubleCosetStatement` | `7bfe81b2-233e-47a8-85c1-1fd296f32c05` |
| `Langlands.BruhatTits.Iwasawa.AvailableIwasawaStatement` | `5e9b97bd-7a9c-43fb-bb8f-b017b7028adc` |
| `Langlands.BruhatTits.Cartan.AvailableCartanStatement` | `14dc145a-14d4-47d6-97a6-d89ea0c558ab` |

The `IwasawaDecompositionStatement` unit of task `0b383eb0-185c-415b-8def-5fcbac419374`
has since been published (Theorem 5.3.3 row). `UnipotentNormalizerCosetStatement`
is now proved by `unipotentNormalizerCoset`, present in Library commit
`17dd94ea3f677b20fb5ab95b285cbc3fd7cde03e`, from the two proved inputs of its
published reduction (Lemma 5.3.5 row). Proofs of three other targets in the table were
first published in Library commit `e449cde988d4e97ab280b8d4d11262887ccc26e0`:
`ChamberIwahoriDecompositionStatement` (artifact
`4493a3f5-fe76-417d-8239-cbb2e5149465`),
`UnipotentIwahoriDoubleCosetStatement` (artifact
`dce35461-bb3e-429c-9068-cf0465a14731`) and
`AvailableIwasawaStatement` (artifact `42bb1c08-a7ac-49f5-a197-dc1d5707a42e`).
The Corollary 7.4.9, Theorem 7.8.1 and Theorem 5.3.4 rows record them.
The proof `availableCartan` of `AvailableCartanStatement` (artifact
`c3a16a8e-fad7-484f-9e90-64f897f020eb`) was first published in Library commit
`d39b5aee822fe2ad1aadf07861ebd9a4c2df62a8`; the Theorem 5.2.1 row records it.

The recovery compile checked both statement modules and their companion
modules without errors or warnings. Compilation and statement acceptance
do not prove these targets, construct the supplied data, establish a full
corrected Definition 4.1.26 certificate, or close the Theorem 9.2.7 descent
gate. The depth-zero release and its representation consumers remain open.

## Trust and release accounting

The host environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`. No external project is
adopted by this note. The nineteenth pass records in the `external_code`
field of the Theorem 8.3.2 row the `SubHopf` helper used by the proof of
`finiteIndexEnlargement`, adapted from Anthropic FLT commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` under the Apache License 2.0;
it is reused through the accepted Library artifact
`6722356c-5ad2-43dd-bb70-d007825bd50d`, not adopted by this note. The roadmap's external pins remain survey leads. Any
adoption still requires a focused host compile, a mathematical and dependency
audit, and its exact pin and licence. The theorem-level axiom inspections
in the verified-proof sections above concern published metric proofs and
their aggregate. The 8 November 2026 refresh and its later passes add declaration inspections in
environment `bb168ec3-1031-46d9-816b-5c2ed7bbe1a6` to the rows it updates. For a
Prop-valued statement or a definition, such a report covers only the elaborated
declaration; it is not evidence that the target is proved.

Bundle A is open. Bundles B–F, the general constructed instance, the depth-zero
and positive-depth consumers, regression examples, GL comparisons and Renard
bridges are also open. The split-group depth-zero regression instances and the
`GL_{n+1}` congruence-subgroup comparisons recorded by the seventeenth pass are
partial progress and do not close these obligations. This source ledger
neither narrows those obligations nor claims that the proposed Chapter V
structural interfaces have already been published in the Renard program.
