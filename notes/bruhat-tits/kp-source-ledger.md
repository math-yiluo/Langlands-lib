# KP Bundles A–F: source ledger and construction boundaries

This source ledger covers Bundle A, initial Bundle B targets and Bundles C–F of the standing KP program
`f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703`. It records mathematical source targets
and their verified formal status. Both parts of Theorem 1.1.15, Corollary
1.1.19 and Proposition 1.1.20 have independently accepted, published proofs,
recorded below in three of the
fifty-two rows. The separately verified metric fixed-point aggregate assembles
six published component proofs and adds no source row. The separately verified
finite separable-unramified prerequisite is recorded below without adding a KP
source row. Propositions 4.2.7 and 4.4.4, both assertions of Theorem
4.2.10, Corollary 4.2.14, corrected Corollary 4.4.5, Theorem 5.3.3 and
Corollary 7.4.9 have published conditional formalizations: they are proved
on supplied building data, whose general construction is open. Theorem
5.2.1 with corrected (5.2.2) and Theorem 5.3.4 are proved on available
Bruhat–Tits data in the sense of corrected Definition 4.1.26, which is
equally conditional. Section 13.2.6 is proved for supplied integral models
and reductive quotients, together with its inflation and compact-induction
consumer. Corrected Theorem 7.8.1
and the `G(F)^0` branch of Theorem 7.5.3 have independently accepted,
published statements on supplied building data, and part (4) of Theorem
7.8.1 is proved. Replaced Lemma 5.3.5, Proposition 4.2.24, Lemma 6.7.1
and Section 6.7.2 have published statements. Proposition 13.2.5 has a
published statement of its opening sentence at finite depths and of parts
(1)–(6) on supplied data, part (3) with indivisible-root blocks and parts
(5) and (6) at positive depth for the parabolic subgroups containing the
split torus; parts (1), (2) and (4) are also stated with an extra
double-root premise that their source proofs use.
Section 9.2.1 (a Galois-fixed point
of a stable apartment), Proposition 9.3.4, Theorem 9.6.5 and Lemma 9.8.1
have published statements, and Theorem 9.6.5 also a proved reduction to
five statements. Corrected Definition 4.1.26 has a
published definition, the corrected Definition 4.1.26 part of Theorem 9.2.7
a published existence statement, and Definition 6.6.1 a partial published
definition. The other twenty-five rows retain empty formal-status and
evidence fields. The remaining Bundle B
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
  "coverage": "Bundle A named targets, Bundle B targets (corrected Definition 4.1.26, Theorem 7.5.3, Theorem 9.2.7 and the Chapter 9 descent inputs Section 9.2.1, Proposition 9.3.4, Theorem 9.6.5 and Lemma 9.8.1), Bundle C decompositions and narrow component/Kottwitz interfaces, Bundle D parahoric models, maximal reductive quotients and depth-zero reduction with Chapter 9 descent, Bundle E group/Lie/dual filtrations, all three comparison alternatives, corrected pro-p ambient group and later degeneracy/instability targets, and Bundle F corrected finite-action fixed loci, tame building and integral-model descent, and embeddings from adapted data with their strict-Henselian and general-k existence boundaries. Remaining Bundle B items still need public rows. Both parts of Theorem 1.1.15, Corollary 1.1.19 and Proposition 1.1.20 have verified published proofs; Propositions 4.2.7 and 4.4.4, both assertions of Theorem 4.2.10, Corollary 4.2.14, corrected Corollary 4.4.5, Theorem 5.3.3 and Corollary 7.4.9 have published conditional formalizations on supplied building data, Theorems 5.2.1 and 5.3.4 have them on available data, and Section 13.2.6 on supplied integral models and reductive quotients; corrected Theorem 7.8.1, whose part (4) is proved, and the G(F)^0 branch of Theorem 7.5.3 have published statements on supplied building data; corrected Definition 4.1.26 has a published definition; replaced Lemma 5.3.5, Proposition 4.2.24, Lemma 6.7.1, Section 6.7.2, Section 9.2.1, Proposition 9.3.4, Theorem 9.6.5 (with a proved reduction to five statements) and Lemma 9.8.1 have published statements, Proposition 13.2.5 a published statement of its opening sentence at finite depths and of parts (1)–(6) on supplied data, part (3) with indivisible-root blocks, parts (5) and (6) at positive depth for parabolics containing the split torus, and parts (1), (2) and (4) also with a double-root premise, the corrected Definition 4.1.26 part of Theorem 9.2.7 a published existence statement and Definition 6.6.1 a partial published definition; the other twenty-five rows remain source-only. The building construction and release gates remain open.",
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
        "Recorded Lean scope: ApartmentConjugacyFixingIntersectionStatement quantifies over every nonarchimedean local field F of either characteristic in universe u, every group scheme G over Spec F with [IsAffineHom G.X.hom], and supplied P : ParahoricBuildingData G with a polysimplicial realization R and an apartment splitting T. Its premises are the seven Library predicates of the Corollary 4.2.14 row: SatisfiesBuildingAxiom R (Axiom 4.1.1 for G alone), HasBoundedOpenStabilizers (4.1.2), SatisfiesAffineApartmentAxiom T (4.1.4), HasRootReflections, SatisfiesApartmentAxioms and HasCompatibleApartmentFacets (4.1.6, including V 7) and HasTitsSystem (4.1.9). For all A1 A2 : Set P.toValuationBuildingData.ReducedBuilding with P.IsApartment A1 and P.IsApartment A2 (G(F)-translates of the image of A(S)) it concludes ∃ g ∈ P.zeroSubgroup, g • A1 = A2 ∧ ∀ y ∈ A1 ∩ A2, g • y = y, where P.zeroSubgroup is G(F)^0. The comparisons of Axiom 4.1.1 between groups are not premises. The source's Henselian discretely valued fields with perfect residue field are specialized to nonarchimedean local fields. KPBuildingAssignment.IsAvailableFor supplies all seven premises. Existence of the data or of the axiom witnesses is not asserted."
      ],
      "conclusion": "There is g ∈ G(k)^0 with gA1 = A2 and gx = x for every x ∈ A1 ∩ A2.",
      "lean_declarations": [
        "Langlands.Geometry.Building.ApartmentConjugacyFixingIntersectionStatement"
      ],
      "modules": [
        "Langlands.Geometry.Building.ApartmentConjugacyFixingIntersectionStatement"
      ],
      "dependencies": [
        "Proposition 1.5.13(1) for the Tits system of Axiom 4.1.9; the Section 4.2 metric and segments (Propositions 4.2.1 and 4.2.3, Definition 4.2.4); A1 ∩ A2 is closed, convex and a union of facets.",
        "The source proof does not treat an empty intersection; that case is the transitivity of G(k)^0 on apartments, used in the corrected proof of Proposition 4.2.1.",
        "Proof successor: lean.proof@1 Task 5413 (4e839bbd-8290-40d8-9add-333c46e63847)."
      ],
      "consumer_or_regression": "Corollaries 4.2.25 and 4.2.26, and the corrected source proof of Theorem 5.2.1. The published formal proof availableCartan (task 14dc145a-14d4-47d6-97a6-d89ea0c558ab) uses the sharp fixer and a two-facet Tits transport instead.",
      "formal_status": "statement",
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [
        "8a396dca-5fc1-4680-94bb-f07abc3a4749"
      ],
      "publication_commits": [
        "d39b5aee822fe2ad1aadf07861ebd9a4c2df62a8"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.ApartmentConjugacyFixingIntersectionStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "0bcd437a-6578-4912-bcb4-baef39b1dc03",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-10 at Library commit e7487341; statement_returns_prop true."
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
        "Recorded Lean scope: AffineIwahoriTitsStatement states only the G(F)^0 branch of 7.5.3(1),(2), for every nonarchimedean local field F, affine F-group scheme G and supplied P : ParahoricBuildingData G with P.apartment.SatisfiesApartmentAxioms P.centralizer and every chamber C of A(S): normality of P.normalizerZero and P.zeroSubgroup, and P.AffineIwahoriTits C (a multiplicative equivalence of the affine part of N(F) ∩ G(F)^0 with the affine Weyl group W(Ψ) realizing the actual apartment action, the published IsTitsSystem for G(F)^0, the generated parahoric of C, N(F) ∩ G(F)^0 and the chamber-simple reflections, and the corrected saturation as an intersection of conjugates). The G(F)^natural branch and the conjugacy of choices are not stated. affineIwahoriTits_of_inputs derives P.AffineIwahoriTits C from normality of P.normalizerZero, an action comparison and the eight fields of AffineIwahoriTitsInputs C, which are explicit hypotheses of that lemma. At c4a16df7 three fields are proved under the apartment axioms: closure_chamberSimpleReflections (closure_chamberSimpleReflections_affineRoots, KP Proposition 1.3.22(1)), parahoric_le_zeroSubgroup (from ApartmentRootCover) and zeroSubgroup_le_sup (chamberParahoricGeneration : ChamberParahoricGenerationStatement). affineIwahoriTitsStatement_of_inputStatements derives AffineIwahoriTitsStatement from IwahoriWeylExactSequenceStatement (KP 7.8.1(1), which supplies both normalities and the comparison), AffineRankOneTwoCellStatement (KP Lemma 7.1.5(3)) and the five statements of AffineIwahoriTitsInputStatements. Of these seven, only ChamberParahoricGenerationStatement has a published proof; ChamberParahoricNormalizerStatement, RootGroupParahoricFiltrationStatement, ChamberConjugateIntersectionStatement and AffineRankOneTwoCellStatement have none, and ChamberSimpleFactorizationStatement and IwahoriWeylExactSequenceStatement have only conditional reductions (chamberSimpleFactorizationPrerequisiteReduction and iwahoriWeylExactSequenceStatement_of_prerequisites)."
      ],
      "conclusion": "The two tuples (G(k)^0,I,N(k) intersect G(k)^0,R) and (G(k)^natural,I^natural,N(k) intersect G(k)^natural,R) are saturated Tits systems. Their Weyl groups identify with the affine Weyl group of Psi through the apartment action. Choices of torus and chamber give systems conjugate under G(k)^natural. This statement does not replace either ambient group by full G(k).",
      "lean_declarations": [
        "Langlands.Geometry.Building.AffineIwahoriTitsStatement",
        "Langlands.Geometry.Building.ParahoricBuildingData.affineIwahoriTits_of_inputs",
        "Langlands.Geometry.Building.ParahoricBuildingData.affineIwahoriTitsInputs_of_statements",
        "Langlands.Geometry.Building.affineIwahoriTitsStatement_of_inputStatements",
        "Langlands.Geometry.Building.chamberParahoricGeneration"
      ],
      "modules": [
        "Langlands.Geometry.Building.AffineIwahoriTits",
        "Langlands.Geometry.Building.AffineIwahoriTitsStatement",
        "Langlands.Geometry.Building.AffineIwahoriTitsInputStatements",
        "Langlands.Geometry.Building.AffineIwahoriTitsAssembly",
        "Langlands.Geometry.Building.ChamberParahoricGenerationProof"
      ],
      "dependencies": [
        "Chapter 6 affine roots, valuation and normalizer action; corrected AS5 assumption",
        "Theorem 7.5.1, Lemma 7.5.2 and Lemma 1.4.12; Section 7.4 parahoric construction and Corollary 7.4.9",
        "For the general perfect-residue construction: Proposition 9.4.35, Theorem 9.6.5 and the every-point comparison in 9.6.6",
        "Open proof tasks: 20fbe465-f4ae-4fe9-9846-2201f1c31d28 (AffineIwahoriTitsStatement) and 5210ae85-2886-4b9f-af36-d57d6dba2607 (range part of 7.5.3(2))"
      ],
      "consumer_or_regression": "Restricted building construction 7.6.1 and the affine part of later double-coset decompositions. A nontrivial length-zero/component example must retain the full Iwahori–Weyl data separately.",
      "formal_status": "statement",
      "owner_task": "20fbe465-f4ae-4fe9-9846-2201f1c31d28",
      "acceptance_artifact_ids": [],
      "publication_commits": [
        "c4a16df784376405a45b60df82583e8c26d8a4e3"
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
        "Langlands.Geometry.Building.BruhatTitsAvailabilityStatement"
      ],
      "modules": [
        "Langlands.Geometry.Building.BruhatTitsAvailabilityStatement",
        "Langlands.Geometry.Building.FullValidity.Assignment"
      ],
      "dependencies": [
        "Quasi-split Chapter 6–8 building and actual integral models; Corollary 2.3.8; descent Fact 2.10.16; special k-tori Proposition 9.3.4",
        "Complete NPC fixed-point theory (Theorem 1.1.15), corrected 9.2.1; geometry and restricted-building arguments of Sections 9.3–9.4, including corrected 9.3.25 and AS5 Proposition 9.4.35",
        "Axiom-by-axiom source map in Section 9.5, expanded below; for 4.1.16 use Sections 9.6 and 7.3–7.4 with corrected every-point Corollary 4.4.5",
        "For 4.1.17, Proposition 7.9.5 and transport of the descended construction under all covering field/group isomorphisms; a Gamma action alone is not the full axiom",
        "G(k)^0=G(K)^0 intersect G(k) (9.3.24) and the G(k)^1 intersection identity; model base change and root compatibility for Axiom 4.1.27",
        "Published partial target, not the certificate: Langlands.Geometry.Building.RootValuationBuildingConstructionStatement (module of the same name) asks, for every nonarchimedean local field F and connected reductive G/F, for constructed P : ParahoricBuildingData G, realization and splitting with only the five Section 4.2 axiom witnesses (one-group 4.1.1, 4.1.2, 4.1.4, 4.1.6, 4.1.9) on the existing valuation quotient. Its proof task is 00b6788c-23c3-4b22-88f5-41fdbc6d3654. Together with metricRealization it would make the Proposition 4.2.7 and Theorem 4.2.10 rows unconditional; it does not supply 4.1.8, 4.1.16, 4.1.17, 4.1.20, 4.1.22, 4.1.27 or the 4.1.1 comparison clauses.",
        "Open proof obligation: BruhatTitsAvailabilityStatement has no proof task. Its proof belongs to this program and is split into the focused statements of the next entry; task 00b6788c-23c3-4b22-88f5-41fdbc6d3654 covers only the five Section 4.2 axioms above. Published statements with the hypothesis 𝔅.IsAvailableFor F G hG or 𝔅.IsValid are conditional on it. Among them are AvailableCartanStatement (Theorem 5.2.1 row, proved by availableCartan, artifact c3a16a8e-fad7-484f-9e90-64f897f020eb) and AvailableIwasawaStatement (Theorem 5.3.4 row, proved by availableIwasawa, artifact 42bb1c08-a7ac-49f5-a197-dc1d5707a42e), and two Renard-sourced statements whose proof tasks belong to proof task 8c39faa0-2a70-4fc4-a027-914987aba924: Langlands.Plancherel.RenardCartan.AvailableRenardCartanStatement (task be989fac-448d-4a56-ad1b-663853caf8cd) and Langlands.BruhatTits.SpecialCompact.AvailableSimultaneousStandardBasisStatement (task 8d4643b8-dcf9-476e-a86f-04b62b8d738f). Task 7dc04fe2-f965-4f59-b63c-75f5012b3f64 published three more statements in Langlands.BruhatTits.SpecialCompact, first in Library commit e449cde988d4e97ab280b8d4d11262887ccc26e0: ValidAssignmentTorusRebasingStatement and AvailableSpecialLeviCompactStatement assume 𝔅.IsValid, and AvailableSpecialVertexExistenceStatement assumes 𝔅.IsAvailableFor F G hG. Their proof tasks are 9ec91e66-99df-4afa-be5c-3e5c59207196, bbd398f5-8ddc-4b82-85ab-bf3f0ef59d81 and 8ecbd7c3-bf60-4c93-a0ef-afa198caf8b3. None of these tasks proves that available data exist.",
        "Decomposition (KP 4.1.28 assigns the axioms to Chapters 6–8). Six published statements of this program, first in Library commit 58a91d4ff65b8d6dcb8aa417bfc63399feb8b4af, split availability. KPBuildingAssignment.isAvailableFor_iff separates IsAvailableFor into KPBuildingDatum.SatisfiesGroupAxioms, the comparison clauses of Axiom 4.1.1 and Axiom 4.1.17. Accordingly GroupAxiomsExistenceStatement (every connected reductive G over every nonarchimedean local field has some KPBuildingDatum satisfying the clauses of the ten axioms that concern G alone), BuildingComparisonAxiomStatement (the comparison clauses of Axiom 4.1.1 for all supplied valuation-building data; proof task Task 5427, 45fca8a2-fdf4-4530-98eb-a6307a31f6cf) and IsomorphismCompatibilityAxiomStatement (Axiom 4.1.17 for all supplied data; proof task Task 5428, fa830bf4-4cc7-4e50-9b79-c65dfb6110c4) are intended to give BruhatTitsAvailabilityStatement. GroupAxiomsExistenceStatement is in turn intended to follow from RootValuationBuildingConstructionStatement together with RootGroupActionAxiomStatement (Axiom 4.1.8(2),(3); Task 5425, 7aba1f84-72ba-4b7d-b839-5e1bb849fcf2), IwahoriDecompositionAxiomStatement (Axiom 4.1.16; Task 5426, 96685786-b196-4cbf-83bc-4bdee7ffb004) and IntegralModelAxiomsStatement (Axioms 4.1.20 and 4.1.22; Task 5429, cd2ad671-3edf-4905-a0e2-e7aa2b160b91). These two implications are not published; the assembly proof tasks will be published once their inputs are proved. The published reduction rootValuationBuildingConstructionReduction (module RootValuationBuildingConstructionReduction, Task 4749) derives RootValuationBuildingConstructionStatement from ValuationApartmentAxiomsExistenceStatement (KP Theorem 9.6.5; proof task 17c6d83c-1e02-4345-b9d6-0a8f711e778b), ActualApartmentSplittingStatement (Task 5439, 4d8b4782-7726-4ab3-bb88-fc3df18693fc), AffineIwahoriTitsStatement (task 20fbe465-f4ae-4fe9-9846-2201f1c31d28) and AffineIwahoriTitsBuildingStatement (Task 5440, 81a85d8b-3e8d-454c-97f4-d9b0a3c7e748). Through ParahoricBuildingData.fiveAxioms_of_statements the last three also give ChapterSevenBuildingAxiomsStatement (published by this program, first in Library commit 8c11c93f98b439395e0e7da779c98bb27e24bd6d; proof task Task 5470, 4aa6902d-5c5f-4ca6-9502-061842714858): for supplied ParahoricBuildingData satisfying V 7 and AS 2–AS 5, a polysimplicial realization and a splitting with the other six predicates of the corrected opening of Section 4.2. Two of the four inputs of rootValuationBuildingConstructionReduction are proved: actualApartmentSplitting (module Langlands.Geometry.Building.ActualApartmentSplittingProof, artifact 94af3c4e-b313-44ad-adce-6b6383233dc9, first published in Library commit 8401ccd1f8b9caa18ded91cbfb9c1a31f423ecfd) proves ActualApartmentSplittingStatement (Task 5439), and affineIwahoriTitsBuilding (module Langlands.Geometry.Building.AffineIwahoriTitsBuildingProof, artifact 75baba4f-16d0-4518-87d3-e7e88493aaa9, first published in Library commit cd03c1042f631409e39a0b2a833ed70c0ad78d55) proves AffineIwahoriTitsBuildingStatement (Task 5440). lean_check inspections 3edd4041-7f28-44e5-b70b-7a648f7aeb04 and f2116893-5218-4bcf-9fe1-b6edbb684aa2 by Worker 3557 on 2026-11-12 at Library commit 14c08c22 report kind theorem and only propext, Classical.choice and Quot.sound. ValuationApartmentAxiomsExistenceStatement and AffineIwahoriTitsStatement remain unproved, so RootValuationBuildingConstructionStatement and ChapterSevenBuildingAxiomsStatement remain open.",
        "Chapter 9 descent rows: Section 9.2.1, Proposition 9.3.4 and Theorem 9.6.5 record the published statements of the unramified-descent route to ValuationApartmentAxiomsExistenceStatement, including the proved reduction valuationApartmentAxiomsExistenceReduction; Lemma 9.8.1 records the existence statement for the §9.8 filtration of Z(k)."
      ],
      "consumer_or_regression": "Release 1 general-instance certificate, then actual parahoric reduction, inflation and compact induction. Check anisotropic and torus reduced/enlarged factors, a multipliable root and a nontrivial component example. A Gamma-chamber or Gamma-vertex need not be a K-chamber or K-vertex.",
      "formal_status": "statement",
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [
        "f81d0fe7-8c61-4e05-bfcc-e7d6b14a3f04"
      ],
      "publication_commits": [
        "230ec08a058832bd6941fa887c30897e4826429b"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.BruhatTitsAvailabilityStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "f84d7d5e-94fd-4deb-b771-14d57bcf1815",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-10 at Library commit 230ec08a; statement_returns_prop true."
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
        "Langlands.Geometry.Building.UnramifiedGaloisFixedApartmentStatement"
      ],
      "modules": [
        "Langlands.Geometry.Building.UnramifiedSpecialApartmentStatement"
      ],
      "dependencies": [
        "Proposition 7.9.5; Proposition 4.4.3 and H^1(Gal(K/k'), V) = 0 for the pointwise fixation; Corollary 4.2.12; for the equivariance of the zero section, the central action of Section 4.3 (printed pp.178–180 / PDF pp.209–211), whose kernel is G(K)^1 by Lemma 4.3.1; for the corrected addition, Corollary 4.2.14, Proposition 4.2.18, Proposition 4.2.7, Lemma 1.1.11 and Theorem 1.1.15.",
        "Library inputs named by the statement's Markdown: KPApartmentData.exists_galoisFixed (the analogue for finite extensions K/k), the affine subspace galoisFixedApartment with mem_galoisFixedApartment_iff, under which the conclusion says that galoisFixedApartment is nonempty, and IntegerValuation.IsOmegaCompatible.galoisStable.",
        "Proof successor: lean.proof@1 Task 5513 (a23aef86-8894-44b0-b1c9-b76314d0865f)."
      ],
      "consumer_or_regression": "The apartments A^Γ of §9.2.3 and Construction 9.6.1. The fixed-point set of UnramifiedValuationDescentStatement (Theorem 9.6.5 row) is nonempty only by this statement. Regression: for the norm-one torus T of the unramified quadratic extension in SL_2, T_K is a maximal K-split torus, Frobenius acts on V(T_K) by −1 and the Γ-fixed part of A_T is a single point; T is not special, which the Lean statement allows. Regression for the zero section: for k = Q_2 and G = G_m, B(G_K)^Γ is a single point and the Γ-fixed enlarged building is R, on which 2 ∈ G(k) (normalized valuation 1) acts by t ↦ t − 1; no G(k)-equivariant map from the point exists, while G(k)^1 = Z_2^× acts trivially on R.",
      "formal_status": "statement",
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [
        "528e1be2-9d8b-452b-ad68-e956bf9179ee"
      ],
      "publication_commits": [
        "9bc92c384fa84da7ce5811a5979d408fb69d40b0"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.UnramifiedGaloisFixedApartmentStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "d1da49d0-bde2-4462-b14a-ec1c5c1f8046",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-11 at Library commit 529b851c; kind definition; statement_returns_prop true; the module is byte-identical to commit 9bc92c38."
        }
      ],
      "external_code": []
    },
    {
      "source_item": "Proposition 9.3.4",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.332 / PDF p.363; special k-tori in §9.2.2 at printed p.326 / PDF p.357"
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
        "Recorded Lean scope: SpecialTorusExistenceStatement (module Langlands.Geometry.Building.UnramifiedSpecialApartmentStatement) quantifies over every nonarchimedean local field F, every connected reductive G over Spec F and every maximal split torus iS : S.toGrp ⟶ G (IsMaximalSplitTorus). K is the Library's maximal unramified extension inertiaFixedField F (definitionally UnramifiedClosure F) with its F-algebra structure, and scalar extension is base change along algebraBaseMap F K. It asserts a commutative group scheme T with iT : T.toGrp ⟶ G and f : S ⟶ T such that CommGroupScheme.groupHom f ≫ iT = iS, iT is a closed subgroup (IsClosedSubgroup), and the scalar extension iT_K is a maximal split torus of G_K. That T is an F-torus follows from the last condition and is not stated separately. The source's Henselian discretely valued fields with perfect residue field are specialized to nonarchimedean local fields of either characteristic in universe u."
      ],
      "conclusion": "Every maximal k-split torus S of G is contained in a special k-torus.",
      "lean_declarations": [
        "Langlands.Geometry.Building.SpecialTorusExistenceStatement"
      ],
      "modules": [
        "Langlands.Geometry.Building.UnramifiedSpecialApartmentStatement"
      ],
      "dependencies": [
        "Source proof: S(K)^1 is Γ-stable and acts boundedly on B(G_K) (Proposition 4.2.13); with the finite-quotient action of corrected 9.2.1, Theorem 1.1.15 gives a point x fixed by Γ and S(K)^1. The schematic closure of S in the descended model G^1_x of 9.2.5 is a torus (Proposition B.2.4); Proposition 8.2.1(1) gives a closed o-torus containing it whose special fibre is a maximal f-torus of the special fibre, and its generic fibre is the special torus.",
        "Proof successor: lean.proof@1 Task 5514 (632bdfae-d1a6-4680-acf6-e5c1d32a17d8)."
      ],
      "consumer_or_regression": "Special k-apartments (§9.2.2–9.2.3); Axiom 4.1.27 in §9.5; the proof of Lemma 9.8.1; the published reduction valuationApartmentAxiomsExistenceReduction (Theorem 9.6.5 row), which takes SpecialTorusExistenceStatement as an input. Regression: for anisotropic G the maximal split torus is trivial, and the statement asserts a k-torus that is maximally split over K.",
      "formal_status": "statement",
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [
        "528e1be2-9d8b-452b-ad68-e956bf9179ee"
      ],
      "publication_commits": [
        "9bc92c384fa84da7ce5811a5979d408fb69d40b0"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.SpecialTorusExistenceStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "8ffb183d-c0ab-46a7-9a9f-4234b0c5f135",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-11 at Library commit 3c9b0579; kind definition; statement_returns_prop true; the module is byte-identical to commit 9bc92c38."
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
        "Langlands.Geometry.Building.valuationApartmentAxiomsExistenceReduction"
      ],
      "modules": [
        "Langlands.Geometry.Building.ValuationApartmentAxiomsExistenceStatement",
        "Langlands.Geometry.Building.UnramifiedValuationDescentStatement"
      ],
      "dependencies": [
        "Source proof: V 0 and V 1 from Construction 9.6.1 and Proposition 9.4.3; equivariance from Lemma 9.4.15; V 2 from the same computation; V 6 from Proposition 9.3.16; V 3 from Proposition 9.4.8 and Remark 9.6.4; V 4 and V 5 from Corollary 9.4.10. Lemma 9.6.3 (Lemma 9.4.21, Propositions 7.3.12 and 9.3.24) compares U_{a,x,r} with the upstairs filtrations.",
        "Recorded Lean route: valuationApartmentAxiomsExistenceReduction takes a maximal split torus from exists_maximalSplitTorus and a special torus T ⊇ S from SpecialTorusExistenceStatement (Proposition 9.3.4 row). It makes G_K connected reductive by connectedReductiveFieldExtensionStatement and quasi-split by UnramifiedQuasiSplitStatement. QuasiSplitIntegerApartmentExistenceStatement, applied to K with MaximalUnramified.valuation_surjective and valuationSubring_isHenselian, gives the upstairs class with V 6. rootRankOneFactorization gives hE. UnramifiedValuationDescentStatement descends the class, and ValuationBuildingApartmentAxiomsStatement supplies the apartment axioms.",
        "Proof obligations: ValuationApartmentAxiomsExistenceStatement has proof task Task 5441 (17c6d83c-1e02-4345-b9d6-0a8f711e778b), which the reduction reduces to its five inputs. UnramifiedValuationDescentStatement has proof task Task 5553 (4401e3df-51b5-4132-892c-74e02328d7ee), and ValuationBuildingApartmentAxiomsStatement Task 5554 (265c7ec0-42c1-44ad-9e4f-06f38c5e51d3). SpecialTorusExistenceStatement is in the Proposition 9.3.4 row. UnramifiedQuasiSplitStatement follows from HenselianDiscreteQuasiSplitStatement by the published unramifiedQuasiSplit_of_henselianDiscrete; that statement has proof task 7568ebe8-7b19-4e71-8918-de7d3492bacc and the published conditional reduction henselianDiscreteQuasiSplitReduction from QuasiSplitRegularClassRationalStatement. QuasiSplitIntegerApartmentExistenceStatement has proof task 8ffe0456-3bbd-46c6-9fe1-91be8c433458 and the published conditional reduction quasiSplitIntegerApartmentExistence_of_coordinates from CentralSplitTorusCharacterStatement and QuasiSplitCoordinateApartmentStatement. A proof of the descent statement also needs the Γ-fixed point of the Section 9.2.1 row."
      ],
      "consumer_or_regression": "The published rootValuationBuildingConstructionReduction (Theorem 9.2.7 row) derives RootValuationBuildingConstructionStatement from ValuationApartmentAxiomsExistenceStatement and three further statements. The §9.6.6 comparison feeds the derived route for Axiom 4.1.16, and the §9.8 concave function groups use this class. Regression: for the unramified quasi-split SU_3, the relative root system is BC_1, and the upstairs root restricting to 2a must be filtered at depth 2r by V 4; the uniform depth of the printed Lemma 9.6.3 display fails there.",
      "formal_status": "statement",
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [
        "e0b14a71-bc99-4ac1-b5b5-041d9f4ca3e6",
        "cab86217-ea50-409b-9d4d-3440ee3e3a43"
      ],
      "publication_commits": [
        "58a91d4ff65b8d6dcb8aa417bfc63399feb8b4af",
        "3c9b0579a8f2d36d16294ce48b465d1ec5aee273"
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
        "Proof successor: lean.proof@1 Task 5552 (6f2a4efa-b6d0-4494-a8f4-d65632c460d4). The double-root existence statement has proof successor lean.proof@1 Task 5647 (389efdd6-dfb3-478d-b92e-a38a722094e1)."
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
        "Recorded Lean scope (partial definition): for supplied P : ParahoricBuildingData G over a nonarchimedean local field, P.normalizerZero is the image of P.centralizerZero (the actual Z(F)^0) in normalizerPoints P.i = N(F), and P.IwahoriWeylGroup := normalizerPoints P.i ⧸ P.normalizerZero is Wtilde^0 as a coset type. Its group structure is used under the instance argument [P.normalizerZero.Normal]. Since Library commit e449cde988d4e97ab280b8d4d11262887ccc26e0 that normality is proved for every supplied P: ParahoricBuildingData.normal_normalizerZero (module ZeroSubgroupCommutatorNormality, published with artifact dce35461-bb3e-429c-9068-cf0465a14731) proves that P.zeroSubgroup = G(F)^0 is normal in G(F), because commutators of G(F) lie in G(F)^♮, and concludes through normalizerZero_normal_of_zeroSubgroup_normal and the published cover comparison. The earlier conditional routes (normalizerZero_normal from UnramifiedZeroPointsIndependenceStatement, normalizerZero_normal_of_unipotentNormalizerCoset) remain. The Theorem 7.8.1 statements also assert it as a conclusion. AffineRootSystem.affineWeylGroup P.affineRoots is W_aff, the subgroup of affine automorphisms of the apartment generated by the affine root reflections. P.affinePart is the separate image of N(F) ∩ G(F)^0 in Wtilde^0. Its identification with W_aff is part of IwahoriWeylExactSequence, not of a definition. P.toComponents is the map Wtilde^0 → G(F)/G(F)^0. Wtilde^1=N(k)/Z(k)^1, the adjoint group Wtilde_ad and the maps Wtilde^0→Wtilde^1→Wtilde_ad are not formalized. The definition status of this row covers only Wtilde^0, W_aff and the affine part."
      ],
      "conclusion": "The Iwahori–Weyl group is Wtilde^0=N(k)/Z(k)^0. Keep the distinct quotient Wtilde^1=N(k)/Z(k)^1 and the affine Weyl group W_aff generated by affine root reflections. The maps Wtilde^0→Wtilde^1→Wtilde_ad need not be injective; the affine action can lose component or central data.",
      "lean_declarations": [
        "Langlands.Geometry.Building.ParahoricBuildingData.normalizerZero",
        "Langlands.Geometry.Building.ParahoricBuildingData.IwahoriWeylGroup",
        "Langlands.Geometry.Building.ParahoricBuildingData.affinePart",
        "Langlands.Geometry.Building.ParahoricBuildingData.toComponents",
        "Langlands.Geometry.Building.AffineRootSystem.affineWeylGroup",
        "Langlands.Geometry.Building.ParahoricBuildingData.normal_normalizerZero"
      ],
      "modules": [
        "Langlands.Geometry.Building.IwahoriWeyl",
        "Langlands.Geometry.Building.AffineRootSystem",
        "Langlands.Geometry.Building.ZeroSubgroupCommutatorNormality"
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
        "dce35461-bb3e-429c-9068-cf0465a14731"
      ],
      "publication_commits": [
        "c4a16df784376405a45b60df82583e8c26d8a4e3",
        "e449cde988d4e97ab280b8d4d11262887ccc26e0"
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
        "Recorded Lean scope: LeviApartmentRestrictionStatement quantifies over every nonarchimedean local field F of either characteristic in universe u with ω = localFieldOrder F, every G with hG : IsConnectedReductive G, every maximal split torus i : S → G, every generic cocharacter ν and every J ⊆ simpleRelativeRoots i ν, with the actual standard Levi M_J = Standard.leviScheme i ν J, j = Standard.leviHom i ν J and iM = Standard.leviTorusHom i ν J. For every D : KPApartmentData i (localFieldOrder F) it asserts ∃ DM : KPApartmentData iM (localFieldOrder F) such that every point of D has a restriction in DM (IsLeviRestriction j), every point of DM is such a restriction, and restrictions xM, xM' of x, x' are equal iff x'.val = v +ᵥ x.val for some v ∈ V(S) on which every relative root of (M_J, S) vanishes. Only standard Levi subgroups at the same torus are covered. Compatibility with ω is the S(F) part recorded by KPApartmentData, whose normalizer stability for M_J is part of the conclusion. Part (4) is expressed by surjectivity and this fibre description, and part (5) (Chevalley valuations of quasi-split G) is not formalized. Existence of D is not asserted."
      ],
      "conclusion": "Each φ_M is a valuation of the root datum of (M,S), compatible with ω if φ is; A(M,S) = {φ_M} is an equipollence class; φ ↦ φ_M descends to an isomorphism A(S,G)/V(A) → A(M,S) of affine spaces over V(S'_M), where A is the maximal torus in S'_G ∩ Z(M); for quasi-split G, Chevalley valuations restrict to Chevalley valuations.",
      "lean_declarations": [
        "Langlands.Geometry.Building.LeviApartmentRestrictionStatement"
      ],
      "modules": [
        "Langlands.Geometry.Building.LeviApartmentRestrictionStatement"
      ],
      "dependencies": [
        "Definitions 6.1.2 and 6.1.7 and Lemma 6.1.6; restriction of the root groups of M to those of G.",
        "Suggested proof route: the published construction leviRestrictedApartmentData with leviApartmentProjection (module Langlands.BruhatTits.SpecialCompact.LeviApartmentRestriction, artifact 81fa76f0-f8d0-49cb-a920-8453d82a3523, Worker 164) gives the restricted class and the surjective projection for a Levi presented as one cocharacter centralizer; the fibre clause is additional.",
        "Proof successor: lean.proof@1 Task 5414 (4413f5d7-43ca-46d6-a3f8-d4799eba2603)."
      ],
      "consumer_or_regression": "Section 6.7.2 special points; Levi inheritance of special compact subgroups (Langlands.BruhatTits.SpecialCompact.AvailableSpecialLeviCompactStatement, proof task bbd398f5-8ddc-4b82-85ab-bf3f0ef59d81) for Renard V.5.1(5). The published theorem Langlands.BruhatTits.SpecialCompact.exists_leviRestriction_of_omegaCompatible (module LeviApartmentComparison, Worker 123) takes LeviApartmentRestrictionStatement as a premise and gives every point of an ω-compatible class a restriction in any supplied ω-compatible standard-Levi class at the same torus. The published statement Langlands.Geometry.Building.LeviApartmentAxiomsInheritanceStatement of this program (first in Library commit 8c11c93f98b439395e0e7da779c98bb27e24bd6d; proof task Task 5471, 48fef6af-65b7-4623-bb54-9305ae84fcf6) asserts that V 7 and AS 2–AS 5 pass from D to a standard-Levi class DM related to D by some restriction pair.",
      "formal_status": "statement",
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [
        "851e3550-d582-4076-a891-8d9b00badf3e"
      ],
      "publication_commits": [
        "d39b5aee822fe2ad1aadf07861ebd9a4c2df62a8"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.LeviApartmentRestrictionStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "43b9ea6e-ac3f-4609-819c-182735779ab3",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-10 at Library commit e7487341; statement_returns_prop true."
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
        "Recorded Lean scope: LeviSpecialPointRestrictionStatement has the quantifiers of the Lemma 6.7.1 row and quantifies over D : KPApartmentData i (localFieldOrder F) and DM : KPApartmentData (Standard.leviTorusHom i ν J) (localFieldOrder F). Its premise is that IsLeviRestriction j x xM holds for some pair. It concludes that every ψM ∈ DM.affineRoots has some ψ ∈ D.affineRoots with ψ x = ψM xM for all restriction pairs, the same for extendedAffineRoots (Ψ′), and that for every restriction pair with x special for D.affineRoots, xM is special for DM.affineRoots (AffineRootSystem.IsSpecialPoint) and a vertex (AffineRootSystem.IsVertex). IsLeviRestriction replaces the projection of Lemma 6.7.1; the hyperplane-preimage sentence is left implicit and the extra-special sentence is not formalized. Only standard Levi subgroups at the same torus over nonarchimedean local fields are covered."
      ],
      "conclusion": "Under the dual of the projection, Ψ(M,S) ⊂ Ψ(S,G) and Ψ′(M,S) ⊂ Ψ′(S,G); affine root hyperplanes of M pull back to affine root hyperplanes; the image of a special point is special, in particular a vertex, and the same holds for extra special points. The image of a vertex need not be a vertex.",
      "lean_declarations": [
        "Langlands.Geometry.Building.LeviSpecialPointRestrictionStatement"
      ],
      "modules": [
        "Langlands.Geometry.Building.LeviSpecialPointRestrictionStatement"
      ],
      "dependencies": [
        "Lemma 6.7.1; Definition 6.3.4; Definition 1.3.39 and Proposition 1.3.43(3).",
        "Suggested proof route: root-group transport (modules LeviRootTransport and LeviValuationRestriction of Langlands.BruhatTits.SpecialCompact) for the affine roots; the vertex clause from axiom V 0, because AffineRootSystem.isVertex_of_isSpecialPoint needs IsAffineRootSystemWithRankZero, which is not a premise.",
        "Proof successor: lean.proof@1 Task 5415 (bd8b3443-747f-4eec-bc01-3311650f8e95)."
      ],
      "consumer_or_regression": "Special vertices of Levi data for AvailableSpecialLeviCompactStatement and Renard V.5.1(5). Regression: the image of a non-special vertex need not be a vertex.",
      "formal_status": "statement",
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [
        "d664e902-3b89-4fdd-b136-5b2f070a1844"
      ],
      "publication_commits": [
        "d39b5aee822fe2ad1aadf07861ebd9a4c2df62a8"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.LeviSpecialPointRestrictionStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "f70e9f89-d3b3-498b-8ca0-5059f1782a9b",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-10 at Library commit e7487341; statement_returns_prop true."
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
        "Proof of AvailableIwasawaStatement: availableIwasawa, from lean.proof@1 task 5e9b97bd-7a9c-43fb-bb8f-b017b7028adc (artifact 42bb1c08-a7ac-49f5-a197-dc1d5707a42e; the task was closed as complete on 2026-11-10). Its only building premise is IsAvailableFor, and it proves the inclusion P_x ≤ K_0 for available data. The Library states that inclusion for all supplied data as Langlands.BruhatTits.SpecialCompact.ParahoricLeCompactStabilizer, which is still unproved and has no proof task. The chamber form 5.3.3 has a published proof (see that row). TaskHub searches on 2026-11-08 found no proof task for IwasawaExistenceStatement. It also requires the existence of available data, the Theorem 9.2.7 obligation stated as BruhatTitsAvailabilityStatement (see that row)."
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
        "Recorded Lean scope: UnipotentNormalizerCosetStatement has the same quantifiers and hypotheses as the Theorem 5.3.3 row's IwasawaDecompositionStatement (HenselianLocalRing 𝒪[F], PerfectField 𝓀[F], P.apartment.SatisfiesApartmentAxioms P.centralizer, every chamber C and every generic cocharacter nu). It concludes P.UnipotentNormalizerCoset C nu: for all n, n' ∈ normalizerPoints P.i, there exist u ∈ standardUnipotentPoints P.i nu ∅ and p ∈ P.parahoric C with n = u·n'·p if and only if n'·n^(-1) ∈ P.normalizerZero, the image of Z(F)^0 in N(F). Only the replaced lemma is stated; the printed version is not. The standardUnipotentPoints convention and the Chapter 4 versus Chapter 7 hypothesis difference of the Theorem 5.3.3 row apply unchanged. No existence of P is asserted."
      ],
      "conclusion": "n∈U(k) n' P_C if and only if n' n^(-1)∈Z(k)^0. The printed statement with an arbitrary bounded subgroup P is replaced and is not the target.",
      "lean_declarations": [
        "Langlands.Geometry.Building.UnipotentNormalizerCosetStatement",
        "Langlands.Geometry.Building.ParahoricBuildingData.UnipotentNormalizerCoset"
      ],
      "modules": [
        "Langlands.Geometry.Building.IwahoriWeylStatement"
      ],
      "dependencies": [
        "Iwahori decomposition for the translated chamber C'=nC",
        "Algebraic Bruhat/open-cell uniqueness forces n' n^(-1) into Z(k), then the Iwahori intersection identifies Z(k)^0",
        "Open proof task: 0b383eb0-185c-415b-8def-5fcbac419374, whose Theorem 5.3.3 unit is published. The Library has only conditional assemblies (module Langlands.Geometry.Building.UnipotentNormalizerCosetReduction). unipotentNormalizerCosetReduction proves the conclusion for supplied P from normality of P.normalizerZero, P.ChamberIwahoriDecompositionStatement and the apartment axioms. unipotentNormalizerCosetStatement_of_chamberIwahori_and_exactSequence derives the global statement from the chamber products for all supplied data and IwahoriWeylExactSequenceStatement. On 2026-11-09 the Library had no unconditional proof of either input. Library commit e449cde988d4e97ab280b8d4d11262887ccc26e0 proves both inputs of unipotentNormalizerCosetReduction for every supplied P: the normality of P.normalizerZero by ParahoricBuildingData.normal_normalizerZero (module ZeroSubgroupCommutatorNormality) and the chamber products by ParahoricBuildingData.chamberIwahoriDecomposition (Corollary 7.4.9 row). The published proof of Theorem 7.8.1(4), unipotentIwahoriDoubleCoset, applies unipotentNormalizerCoset_of_chamberIwahori with normal_normalizerZero and a proved chamber Iwahori decomposition. No theorem of type UnipotentNormalizerCosetStatement is published yet, so the row stays statement. No theorem has type IwahoriWeylExactSequenceStatement."
      ],
      "consumer_or_regression": "Actual injectivity of the map in corrected Theorem 7.8.1(4); a surjective Iwasawa product alone cannot establish this conclusion.",
      "formal_status": "statement",
      "owner_task": "0b383eb0-185c-415b-8def-5fcbac419374",
      "acceptance_artifact_ids": [],
      "publication_commits": [
        "c4a16df784376405a45b60df82583e8c26d8a4e3"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.UnipotentNormalizerCosetStatement",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "73e1c9df-449b-437b-a777-b5a80c824b09",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-08 at Library commit c4a16df7; statement_returns_prop true."
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
        "Recorded Lean scope: closed Prop-valued targets at universe u quantify over every nonarchimedean local field F, every affine F-group scheme G and supplied P : ParahoricBuildingData G, retaining SatisfiesApartmentAxioms. Part (4) explicitly requires HenselianLocalRing O[F], PerfectField k[F] and a generic cocharacter nu. The actual U(F) is standardUnipotentPoints P.i nu empty. Its comparison with the single Dynamic.unipotent group is proved: standardUnipotent_empty_eq_dynamic (module Langlands.GroupScheme.Rational.MinimalStandardDynamicComparison) gives standardUnipotent i nu ∅ = Dynamic.unipotent for connected reductive G and a maximal split torus, without a genericity hypothesis, and IwasawaDecompositionReduction specializes it to the rational points of the same supplied P (see the Theorem 5.3.3 row). This comparison alone does not prove part (4). Part (4) is now proved on supplied data: the theorem unipotentIwahoriDoubleCoset (module UnipotentIwahoriDoubleCosetProof) proves UnipotentIwahoriDoubleCosetStatement from iwasawaDecomposition (Theorem 5.3.3 row), unipotentNormalizerCoset_of_chamberIwahori, normal_normalizerZero and a proved chamber Iwahori decomposition. It was accepted as artifact dce35461-bb3e-429c-9068-cf0465a14731 (proof task 7bfe81b2-233e-47a8-85c1-1fd296f32c05) and first published in Library commit e449cde988d4e97ab280b8d4d11262887ccc26e0. Parts (1)–(3) remain unproved, so the row stays statement. No general building existence is asserted."
      ],
      "conclusion": "(1) Exact sequence 1→W_aff→Wtilde^0→G(k)/G(k)^0→1. (2) Inclusion induces a bijection Wtilde^0→I\\G(k)/I. (3) Inclusion induces a bijection W_aff_F1\\Wtilde^0/W_aff_F2 →G(k)^0_F1\\G(k)/G(k)^0_F2. (4) Inclusion induces a bijection Wtilde^0→U(k)\\G(k)/I=U(k)Z(k)^0\\G(k)/I. These are actual quotient bijections, including the component contribution beyond W_aff. The exact-sequence target includes the needed normality conclusions and an identification of its kernel with the affine Weyl group through the actual apartment action. Each quotient equivalence is prescribed on every normalizer representative; the added part (4) contains both bijections.",
      "lean_declarations": [
        "Langlands.Geometry.Building.IwahoriWeylExactSequenceStatement",
        "Langlands.Geometry.Building.IwahoriDoubleCosetStatement",
        "Langlands.Geometry.Building.ParahoricDoubleCosetStatement",
        "Langlands.Geometry.Building.UnipotentIwahoriDoubleCosetStatement",
        "Langlands.Geometry.Building.unipotentIwahoriDoubleCoset"
      ],
      "modules": [
        "Langlands.Geometry.Building.IwahoriWeylStatement",
        "Langlands.Geometry.Building.UnipotentIwahoriDoubleCosetProof"
      ],
      "dependencies": [
        "Fact 4.1.25, corrected Theorem 7.5.3 and Proposition 7.5.5",
        "Corrected (2) injectivity: use 7.8.2 and Lemma 1.3.17 to write w_i rho_i, use (1) and I⊂G(k)^0 to identify the rho_i, cancel their normalizing action, then apply actual affine Bruhat injectivity in G(k)^0 (Proposition 1.4.5). I∩N(k)=Z(k)^0 alone is insufficient",
        "Part (4): Theorem 5.3.3 for surjectivity and replaced Lemma 5.3.5 for injectivity, with their source hypotheses",
        "7.8.2 gives Wtilde^0=W_aff semidirect Stab(C,Wtilde^0) after choosing C; 7.7.12 identifies that stabilizer with the Iwahori normalizer modulo I"
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
        "e449cde988d4e97ab280b8d4d11262887ccc26e0"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.unipotentIwahoriDoubleCoset",
          "environment_artifact": "bb168ec3-1031-46d9-816b-5c2ed7bbe1a6",
          "inspection_id": "2da48600-4de7-421f-b0da-ff2c84bafbfb",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection by Worker 3557 on 2026-11-10 at Library commit e449cde9; a theorem proving part (4), acceptance artifact dce35461."
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
        "G(k)^1 is the subgroup of Definition 2.6.15, and A_tor is the torsion subgroup of A. No dim(f)≤1 assumption is imposed."
      ],
      "conclusion": "G(k)^1=kappa_G^(-1)((A_tor)^Gamma). This is the preimage of invariant torsion, distinct from the zero kernel identifying G(k)^0.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Actual Kottwitz construction and functoriality, Lemma 11.5.1",
        "Abelianization G→G_ab, its finite-kernel map on fundamental groups and inertia coinvariants; Lemma 11.1.3 and Definition 2.6.15"
      ],
      "consumer_or_regression": "The second and third quotient identifications of 11.7.6 and retention of the G(k)^0/G(k)^1 distinction in Hecke and stabilizer interfaces.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
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
        "G(k)^0 is the subgroup of Definition 2.6.23. Neither finiteness of f nor dim(f)≤1 is assumed in this kernel identity."
      ],
      "conclusion": "G(k)^0=ker(kappa_G). The homomorphism is the actual Kottwitz map, not an arbitrary map postulated to have this kernel.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Proposition 9.3.24, G(k)^0=G(K)^0 intersect G(k), reduces to k=K",
        "Quasi-splitness Corollary 2.3.8, torus kernel Proposition 11.1.5, induced-torus lifting Lemma 2.5.20 and z-extension surjectivity Proposition 11.5.3"
      ],
      "consumer_or_regression": "Identify the component quotient in Theorem 7.8.1(1), while keeping surjectivity and the Section 11.7 residue hypothesis separate.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
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
        "For the chamber quotient choose a Gamma-stable K-chamber C in B(G_K), as in the source proof. G(k)_C is its stabilizer and G(k)^0_C=G(k)_C intersect G(k)^0."
      ],
      "conclusion": "kappa_G:G(k)→A^Gamma is surjective and induces an isomorphism G(k)_C/G(k)^0_C≃A^Gamma. The chosen chamber is over K; do not silently replace it by an arbitrary k-chamber.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Existence of a Gamma-stable K-chamber, Proposition 9.10.4",
        "Proposition 11.6.1 exact sequence over K, Theorem 8.3.13 smooth connected-fibre chamber model, and Lemma 8.1.4 cohomology vanishing"
      ],
      "consumer_or_regression": "Length-zero/component representatives for the Iwahori–Weyl and Hecke interfaces over local fields.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
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
        "A_tor is the torsion subgroup of A=pi_1(G)_I. Form invariants before the torsion-free quotient in the third identification."
      ],
      "conclusion": "Kottwitz induces G(k)/G(k)^0≃A^Gamma, G(k)^1/G(k)^0≃(A_tor)^Gamma, and G(k)/G(k)^1≃A^Gamma/(A_tor)^Gamma=(A^Gamma)_free. The explicit third quotient unpacks the source notation using torsion(A^Gamma)=(A_tor)^Gamma; no identification with (A/A_tor)^Gamma is asserted.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Lemma 11.5.2, Proposition 11.5.4 and Corollary 11.7.5",
        "First isomorphism theorem and the elementary fact that the torsion subgroup of an invariant subgroup is the invariant torsion subgroup"
      ],
      "consumer_or_regression": "Combine with Theorem 7.8.1(1) and its chamber-dependent splitting without discarding invariant torsion or length-zero representatives.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
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
        "S is a maximal K-split torus, T=Z_{G_K}(S), and Omega is a nonempty bounded subset of its apartment in the actual building B(G_K). The models in Chapter 8 are over O; their descent over o is a separate construction."
      ],
      "conclusion": "G(K)^1_Omega and G(K)^dagger_Omega are schematic: they are the O-points of actual smooth affine O-group schemes with generic fibre G_K. Their models have the same relative identity component. This does not assert connectedness of the entire models or identify either subgroup with the full fixer.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Proposition 8.3.1: faithful representations, stable lattices, schematic closure and smoothening (A.6.5–A.6.6) construct vertex models",
        "Enlarge Omega to the facets meeting it; Proposition 7.7.1 gives the finite-index inclusions, and A.7.1 propagates schematicity and identifies relative identity components",
        "For nonempty bounded Gamma-stable subsets, Section 9.2.5 constructs the descended smooth affine o-models using invariant coordinate rings and relative identity components; 9.2.6 identifies the parahoric o-points. Chapter 8 models alone do not give this descent."
      ],
      "consumer_or_regression": "Actual integral-model input for the connected model, its reduction and compact/open integral points. The generally nonaffine full-fixer model of Remark 8.3.4 remains a different object.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
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
        "S is a maximal K-split torus, T=Z_{G_K}(S), and Omega is a nonempty bounded subset of its apartment in the actual building B(G_K). The models in Chapter 8 are over O; their descent over o is a separate construction."
      ],
      "conclusion": "The common relative identity component G^0_Omega of the schematic models in 8.3.2 has G^0_Omega(O)=G(K)^0_Omega. It is the actual smooth affine connected-fibre parahoric model with generic fibre G_K. Its connectedness does not identify the parahoric with a full pointwise or setwise fixer.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Theorem 8.3.2; T is a maximal torus since G_K is quasi-split by 2.3.8. The connected Neron model has T^0(O)=T(K)^0 by B.8.7",
        "Sections 8.3.7–8.3.12 construct root models with prescribed integral points and connected fibres. Sections 2.10.10 and 2.10.19 extend the genuine generic-fibre inclusions",
        "Corrected connected-fibre argument: torus and root model maps factor through G^0_Omega; hence the generated G(K)^0_Omega lies in G^0_Omega(O). Proposition 7.7.1 gives openness and finite index there, and Lemma A.4.26 proves equality",
        "Proposition 8.3.14 gives the actual root-product open immersion",
        "For nonempty bounded Gamma-stable subsets, Section 9.2.5 constructs the descended smooth affine o-models using invariant coordinate rings and relative identity components; 9.2.6 identifies the parahoric o-points. Chapter 8 models alone do not give this descent."
      ],
      "consumer_or_regression": "Connected parahoric construction for reduction, inflation and compact induction. Proving compactness and openness further uses the actual scheme-point topology from its owning task.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
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
        "Write H_Omega for the connected special fibre of the connected parahoric model G^0_Omega, and Gred_Omega=H_Omega/R_u(H_Omega) for its maximal reductive quotient. Sbar is the special fibre of the standard O-model of S and is identified with its image in Gred_Omega."
      ],
      "conclusion": "For every choice of positive relative roots, open-cell multiplication is an isomorphism of schemes from the negative nondivisible U^+_{a,Omega,0} factors, T^+, and the positive nondivisible factors onto R_u(H_Omega). These plus groups are special-fibre images of the corresponding 0+ model maps. This is not a direct-product group decomposition. The root datum of Gred_Omega relative to Sbar is (X^*(S),Phi_Omega,X_*(S),Phi_Omega^vee), where Phi_Omega consists of gradients of affine roots vanishing identically on Omega. For a in Phi_Omega, Ubar_{a,Omega,0}/U^+_{a,Omega,0} maps isomorphically to its a-root group. Phi_Omega is reduced even when the ambient relative root system has multipliable roots.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Proposition 8.3.14, Corollary 8.4.5 and Proposition 8.4.8; Lemma 8.4.7 keeps the a-versus-2a alternatives",
        "Dynamic root groups and multiplication, Proposition 2.11.9 and Theorem 2.11.15; torus unipotent radical B.10.12",
        "For nonempty bounded Gamma-stable subsets, Section 9.2.5 constructs the descended smooth affine o-models using invariant coordinate rings and relative identity components; 9.2.6 identifies the parahoric o-points. Chapter 8 models alone do not give this descent.",
        "Section 9.5 uses perfectness to descend the geometric unipotent radical; the displayed split root datum is a geometric description over fbar, not an assertion of splitness over f"
      ],
      "consumer_or_regression": "Maximal reductive quotient for depth zero. Preserve the special-fibre distinction; the ramified SU_3 example of Remark 8.4.11 has quotient SO(3)=PGL_2 although the ambient group is simply connected.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
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
        "Write H_Omega for the connected special fibre of the connected parahoric model G^0_Omega, and Gred_Omega=H_Omega/R_u(H_Omega) for its maximal reductive quotient. Sbar is the special fibre of the standard O-model of S and is identified with its image in Gred_Omega."
      ],
      "conclusion": "Under the natural surjective reduction G(K)^0_Omega=G^0_Omega(O)→H_Omega(fbar), the inverse image of R_u(H_Omega)(fbar) is G(K)_{Omega,0+}. Thus 0+ is the kernel of the composite to Gred_Omega(fbar); it is generally larger than the kernel of reduction to the whole special fibre.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Smooth Henselian reduction is surjective by 8.1.3; the integral-point identification is Theorem 8.3.13",
        "Theorem 8.4.10, Corollary 8.4.5(2), Lemma B.10.11 and Proposition 7.3.12 identify the inverse image",
        "Proposition 2.4.3 makes projection from smooth connected special-fibre rational points to the reductive quotient surjective; Lemma 2.4.2 supplies unipotent H^1 vanishing",
        "For nonempty bounded Gamma-stable subsets, Section 9.2.5 constructs the descended smooth affine o-models using invariant coordinate rings and relative identity components; 9.2.6 identifies the parahoric o-points. Chapter 8 models alone do not give this descent.",
        "Section 9.5 uses G(k)^0=G(K)^0 intersect G(k) from 9.3.24, descends the unipotent radical over perfect f and gives G(k)^0+_F=G(K)^0+_F intersect G(k), hence the kernel over k"
      ],
      "consumer_or_regression": "Use the actual reduction composite in the depth-zero quotient and inflation; neither an arbitrary map with an assumed kernel nor reduction to the entire special fibre meets the target.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
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
        "F and F' are facets in an apartment A with F contained in the closure of F'. The generic-fibre identity induces the actual model morphism G^0_{F'}→G^0_F and its special-fibre morphism rhobar:H_{F'}→H_F. The full bijection ranges over all facets in B(G_K) whose closures contain F, not just those in A."
      ],
      "conclusion": "By Proposition 8.4.15 specialized to these facets, the schematic kernel of rhobar is smooth connected unipotent, and open-cell multiplication identifies it as a scheme with the product of ker(Ubar_{a,F',0}→Ubar_{a,F,0}) over all nondivisible roots a in Phi(S,G_K). The restriction to Phi'_{F'} minus Psi_F(F') printed in Theorem 8.4.19(1) is false and is excluded as a formalization target: Example 8.3.5 gives a split SL_2 open chamber F' incident to a hyperspecial vertex F for which Phi'_{F'} is empty by 8.4.6, but ker(rhobar) is G_a. Theorem 8.4.19(2)–(4) supplies the remaining conclusions. The image p_F(F') is the parabolic of H_F associated to Psi_F(F') and contains R_u(H_F). The inverse image of p_F(F')(fbar) in G^0_F(O) is G^0_{F'}(O). The map F'↦p_F(F') is a bijection from all incident facets onto all parabolics of H_F, equivalently of Gred_F. Facets in A alone correspond to parabolics containing the chosen maximal torus. The kernel product is a scheme isomorphism, not a direct-product group decomposition.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Corrected general morphism setup preceding Proposition 8.4.15; that proposition supplies the smooth connected unipotent kernel and the product over all nondivisible ambient roots, without the false restriction in 8.4.19(1)",
        "Derived source-discrepancy check from Example 8.3.5 and Section 8.4.6: the chamber model maps to the hyperspecial SL_2 model by c=pi*c'; on special fibres its kernel has a=d=1, b=0 and c' free, hence is G_a, whereas Phi'_{F'} and the printed product index are empty",
        "Root-filtration comparisons 6.3.21; Theorem 8.4.10, Proposition 8.4.8(2), Proposition 1.3.35 and Corollary 8.4.12; independence from the apartment and the use of all apartments through F",
        "For nonempty bounded Gamma-stable subsets, Section 9.2.5 constructs the descended smooth affine o-models using invariant coordinate rings and relative identity components; 9.2.6 identifies the parahoric o-points. Chapter 8 models alone do not give this descent.",
        "Section 9.3.2 descends the facet morphisms and identifies Gamma-facets through F with parabolic f-subgroups; Proposition 2.4.5 transfers these to the maximal reductive quotient",
        "Proposition 9.3.3 proves the exact inverse-image equality over o, using 8.1.3 smooth Henselian reduction and Lemma 2.4.2 for the smooth connected unipotent kernel. This does not assert that every geometric parabolic descends"
      ],
      "consumer_or_regression": "Residue/facet correspondence and change-of-parahoric tests for depth-zero induction and double cosets; retain rational parabolics after Chapter 9 descent. The split SL_2 chamber-to-vertex kernel is a regression against the erroneous printed restricted index.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
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
        "Recorded Lean scope: the published modules Langlands.BruhatTits.IntegralModels.DepthZeroReduction (artifact f3a39f0a-0b63-4218-a72a-b3958c3b3740, first in Library commit 7047367a78583edbe335517824e30403414aa3f0) and Langlands.BruhatTits.IntegralModels.DepthZeroInduction (artifact a6b89c9a-222a-4977-b85b-1983338fa594, first in Library commit 7103f5282c4897716543f227940fdb2a0e12e70e) work over a domain R in universe u with fraction field K and a group scheme G over Spec K, with supplied D : RelativeComponentModelData R K G and Q : SpecialFibreQuotientData D. The smooth model D.neutral with connected fibres plays the role of G^0_x, Q.quotient that of Gred_x and Q.projection that of the quotient map; nothing identifies D.neutral with the actual parahoric model or D.neutral.integralPoints with P_{x,0}. The premises hrad : IsUnipotentRadical Q.radicalInclusion and hQ (Q.projection is the represented fppf quotient by that radical) are the first two conjuncts of Q.IsReductiveQuotient; reductivity of the quotient is not used. For a local domain R, ker_parahoricReduction hQ identifies the kernel of parahoricReduction : G^0(R) → Q.quotient(f) with Q.positivePoints.subgroupOf D.neutral.integralPoints, the radical preimage G(K)^{0+} of Axiom 4.1.22(7) inside G^0(R). For a Henselian local domain R with perfect residue field, parahoricReduction_surjective hrad hQ gives surjectivity and depthZeroQuotientEquiv hrad hQ is the induced group isomorphism from G^0(R) modulo that kernel onto Q.quotient(f). The integer rings of k and of K in the source are both such bases, so the source's assertion over K is the same declaration at another base; no instance is supplied. DepthZeroInduction adds the consumer test: inflation of a representation of Q.quotient(f) to G^0(R), the bijection between G^0(R)-maps from an inflation and Q.quotient(f)-maps into kernel invariants, and, for a topological-group structure on G(K) in which G^0(R) and its level-one congruence subgroup are open, compact induction from G^0(R) with Frobenius reciprocity (depthZeroInductionHomEquiv). For a nonarchimedean local field F, R = 𝒪[F] is proved Henselian and localFieldDepthZeroInductionHomEquiv, for affine G locally of finite type with rationalPointTopology, takes those openness premises from the unproved LocalFieldIntegralModel.CongruenceNeighborhoodBasisStatement. The cokernel description of Gred_x is not formalized."
      ],
      "conclusion": "The natural composite P_{x,0}=G^0_x(o)→H_x(f)→Gred_x(f) is surjective with kernel P_{x,0+}, and hence induces P_{x,0}/P_{x,0+}≃Gred_x(f). The analogous assertion holds over K. As an f-group scheme, Gred_x is also the cokernel of the special-fibre map G_{x,0+}→G_{x,0}. The rational-point quotient uses both surjectivity steps and the descended kernel; it does not follow merely from a group-scheme cokernel.",
      "lean_declarations": [
        "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.depthZeroQuotientEquiv",
        "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.parahoricReduction_surjective",
        "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.ker_parahoricReduction",
        "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.depthZeroInductionHomEquiv",
        "Langlands.BruhatTits.IntegralModels.localFieldDepthZeroInductionHomEquiv"
      ],
      "modules": [
        "Langlands.BruhatTits.IntegralModels.DepthZeroReduction",
        "Langlands.BruhatTits.IntegralModels.DepthZeroInduction"
      ],
      "dependencies": [
        "Theorems 8.3.2 and 8.3.13 construct the actual models; Sections 9.2.5–9.2.6 descend them and identify integral points",
        "The first reduction arrow is surjective by 8.1.3. The second is surjective by Proposition 2.4.3 over perfect f, proved using Lemma 2.4.2 on split unipotent groups and H^1",
        "Corollary 8.4.12 and Section 9.5 identify the actual kernel over k; apply the group first isomorphism theorem",
        "The congruence models and their morphism come from Theorem 8.5.2 and Section 8.5.17, with Chapter 9 descent",
        "Section 13.2.2 separates facet-dependent 0 and 0+ from positive-depth variation, and 13.2.3 uses 9.8.3(2) for the Gamma-invariant group comparison",
        "Recorded Lean route: surjectivity composes the Henselian lifting theorem IntegralModel.reduction_surjective for the smooth model (the role of 8.1.3) with projectionPoints_surjective. Over a perfect residue field the latter uses a scheme section of the projection, obtained from the published perfectFieldUnipotentSplit and splitUnipotentAffineTorsorStatement, instead of the Galois cohomology of Lemma 2.4.2 and Proposition 2.4.3 (printed p.84 / PDF p.115). The kernel is the radical preimage by construction. Its identification with the Moy–Prasad group P_{x,0+} (Corollary 8.4.12, printed p.306 / PDF p.337, and Section 9.5) and the construction of the actual models, radical and quotient (Theorems 8.3.2 and 8.3.13, Sections 9.2.5–9.2.6) are not formalized.",
        "Open obligations before unconditional use: construct D and Q with hrad and hQ for the actual parahoric model of a point of the actual descended building; prove Corollary 8.4.12; for the local-field corollary, prove CongruenceNeighborhoodBasisStatement (proof task fc268342-28e9-4dd8-a855-9ae5c09db273)."
      ],
      "consumer_or_regression": "For a nonarchimedean local field, separately prove finiteness of Gred_x(f) from finite residue and finite type, and compactness/openness from the actual model topology. Inflate a finite-quotient representation through this map and prove the quotient factorization, then compactly induce and prove a double-coset or intertwining theorem. This source row supplies no positive-depth acceptance. Recorded progress: inflation, its factorization through kernel invariants, compact induction and Frobenius reciprocity are formalized on supplied data in DepthZeroInduction (see the Recorded Lean scope). Finiteness of Gred_x(f), compactness of P_{x,0} and a double-coset or intertwining theorem for the induced representation remain open.",
      "formal_status": "conditional",
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [
        "f3a39f0a-0b63-4218-a72a-b3958c3b3740",
        "a6b89c9a-222a-4977-b85b-1983338fa594"
      ],
      "publication_commits": [
        "7047367a78583edbe335517824e30403414aa3f0",
        "7103f5282c4897716543f227940fdb2a0e12e70e"
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
      "conclusion": "At finite nonnegative augmented depths, the actual P_{x,r} form a decreasing family of bounded open subgroups, independent of the apartment used to define them. Its separated extension has P_{x,infinity}=intersection_{t>=0, t real} P_{x,t}={1}; this term need not be open. For g in G(k), g P_{x,r} g^-1=P_{gx,r}; hence P_{x,r} is normal in the full point stabilizer. The commutator is contained in P_{x,r+s}. At finite r>0, P_{x,r} has the Iwahori decomposition of 13.2.4 relative to P, including a homeomorphism of the three factors, rather than a group direct product. At every finite nonnegative augmented depth, its intersection with M(k) is P^M_{x_M,r}. The finite-depth restriction on openness independently clarifies the printed wording; it is not an authors' correction. Printed part (3), at positive finite depth, claims an arbitrarily ordered root/centralizer product bijection with products over all positive and negative roots. This indexing conflicts with its cited 7.3.12(5), which uses indivisible roots and concave-function blocks. The discrepancy is recorded. The published MoyPrasadProductStatement states the derived indivisible-root block form on supplied data; its proof is outstanding, and no corrected theorem or author erratum is claimed here. Parts (5) and (6) are recorded at finite positive real depths for the parabolic subgroups containing S. The printed first inclusion aN^+a^{-1} ⊂ N of Definition 13.2.4(2) is read as aN^+a^{-1} ⊂ N^+, the analogue of the printed second inclusion; this derived reading is not an authors' erratum. The proofs of parts (1), (2) and (4) need, for the mixed pairs (2a, -a) and (a, -2a) of a multipliable root, a bound on the Z-component of a commutator that Definition 7.2.1 does not supply (Bundle E notes). No counterexample to the printed parts (1), (2) and (4) is known.",
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
        "Langlands.Geometry.Building.ParahoricBuildingData.CentralizerFiltration.IsDoubleRootCommutatorFriendly"
      ],
      "modules": [
        "Langlands.Geometry.Building.KPMoyPrasadFiltrationStatement",
        "Langlands.Geometry.Building.KPMoyPrasadFiltration",
        "Langlands.Geometry.Building.KPMoyPrasadProductStatement",
        "Langlands.Geometry.Building.KPMoyPrasadLeviStatement",
        "Langlands.Geometry.Building.KPMoyPrasadDoubleRootStatement"
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
        "Proof successors (lean.proof@1, one per conjunct): MoyPrasadSeparatedStatement Task 5509 (090acae8-2f81-4ccd-bd05-3635b01f3955); MoyPrasadBoundedOpenStatement Task 5510 (c593d9f7-612c-43ae-aa67-342ceb78f1d5); MoyPrasadCovarianceStatement Task 5511 (be16ead9-93f4-432a-a7e0-44077e469d85); MoyPrasadCommutatorStatement Task 5512 (05aa82d6-2f2e-4113-908c-edc4ea226133). The conjunction needs no further mathematics once the four are proved. Part (3), MoyPrasadProductStatement, has proof successor Task 5579 (f97b9951-9063-4099-b8dd-b986fd1f7205). Parts (5) and (6), MoyPrasadLeviStatement, have proof successor Task 5620 (435ee887-a640-423a-bc30-8ad182e6ba9e). The double-root statements have proof successors Task 5645 (03d53828-0d05-4e3f-960c-dd74256072e0) (MoyPrasadDoubleRootCovarianceStatement) and Task 5646 (a5f35e49-1e6a-4f03-8986-d7b2db8ac2b0) (MoyPrasadDoubleRootCommutatorStatement); Tasks 5511 and 5512 keep their original targets. Worker 164's published iInf_moyPrasad_eq_bot, orderedMoyPrasadProduct_injective and range_orderedMoyPrasadProduct_eq (Library commit cd03c104) take only the apartment axioms and IsCommutatorFriendly; the contexts of Task 5509 (090acae8-2f81-4ccd-bd05-3635b01f3955) and Task 5579 (f97b9951-9063-4099-b8dd-b986fd1f7205) name them. Worker 164's published isMoyPrasadAt_unique_of_double_opposite_bound (module Langlands.Geometry.Building.MoyPrasadCovarianceReduction, Library commit 297a8ef0) derives the conclusion of MoyPrasadCovarianceStatement from the apartment axioms, SatisfiesFiltrationAxioms and one further hypothesis: conjugation of U_{-2a,x,r} by U_{a,x,0} stays in P_{x,r}. conjugate_double_opposite_mem_moyPrasad_of_central_bound (module Langlands.Geometry.Building.MoyPrasadMixedConjugation, same commit) reduces that hypothesis to a bound on the Z-component, the bound that IsDoubleRootCommutatorFriendly supplies. The revision-2 contexts of Tasks 5511, 5512 and 5552 record the gap and name these reductions."
      ],
      "consumer_or_regression": "Regression: a nonsplit group with a multipliable root must detect overlapping a/2a scalar factors and test the separately proved block formulation. Check finite r/r+ openness separately from the non-open infinite term for G_m(Q_2), point variation inside a facet, full-stabilizer normality and the actual Levi embedding. Boundedness alone is not compactness over general Henselian k. For the part (3) central factor: for G = G_m there are no roots, so G(k)♯_{x,r} = Z♯_{x,r} = {1}, while Z(k)_r = P_{x,r} is a nontrivial congruence subgroup; the middle factor must be the full filtration. Consumer: the positive-depth Iwahori factorization of Task 5310; the published regrouping in Langlands.BruhatTits.SpecialCompact.MoyPrasadParabolicProduct takes ordered-root covering as a hypothesis. Parts (5) and (6): consumer is the positive-depth Iwahori decomposition (HasIwahoriIntersectionDecomposition and WeakChamberContraction) of Task 5310. Double-root regression: for the unramified quasi-split SU_3 (relative root system BC_1) and u ∈ U_{2a}(k), the Z-component of (u, u') has depth 2(φ_a(u) + φ_{-a}(u')), twice the bound of Definition 7.2.1; for a reduced root system the premise IsDoubleRootCommutatorFriendly is implied by IsCommutatorFriendly.",
      "formal_status": "statement",
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [
        "cdc002e4-4628-4026-91c9-c4add6280308",
        "38dd6045-a386-43d6-a804-1de56fa51d14",
        "abed4e85-f69b-404f-ab1b-76a194d2d0d0",
        "a10cf7b9-8244-4125-94c1-9eb4aa404e35"
      ],
      "publication_commits": [
        "642008d6b3b837d8bd76de0cabcaff3db00088c0",
        "63d9b857523edf47443b7bf30844159e526d00b0",
        "6bff2655fd831aefb39f6688f904aa7410cb0f73",
        "297a8ef0ba780a488196cf62285af3ded2e2baa6"
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
        "Additionally k is a local field: complete with finite residue field f of characteristic p. Use the actual parahoric subgroups, positive-depth filtrations and the point topology of G(k). Maximality and the normalizer below are taken in G(k)^0."
      ],
      "conclusion": "For every x, P_{x,0+} is an open pro-p subgroup of G(k)^0. It is maximal among open pro-p subgroups there exactly when x lies in a chamber, equivalently P_{x,0} is Iwahori. Every maximal open pro-p subgroup of G(k)^0 is P_{x,0+} for an Iwahori P_{x,0}, and its normalizer in G(k)^0 is P_{x,0}. Neither the maximality claim nor the normalizer identity is extended to the full G(k).",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Actual model point topology and local compactness turn bounded open subgroups into compact ones. Realize P_{x,0+} as the inverse limit of its finite p-group filtration quotients, using 13.5.1 for their steps",
        "Fixed points 4.2.14, type preservation 1.5.13(3), the actual reduction and incident-facet/parabolic correspondence 8.4.19 with Chapter 9 descent; finite-field p-subgroup structure and the Iwahori-Tits system in G(k)^0",
        "The normalizer argument uses 2.2.16 and 6.3.21",
        "Release 1 constructions, the corrected Theorem 9.2.7 certificate and the inflation/compact-induction consumer remain prerequisites for positive-depth implementation. A source row supplies no release or formal acceptance."
      ],
      "consumer_or_regression": "Check the exact ambient group in both maximality and normalization, including a case with nontrivial component or length-zero data. An abstract pro-p predicate does not supply the compactness, inverse limit or building fixed-point proof.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
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
by this note.

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

## Bundle E: filtrations, comparison alternatives and later instability

These nine source-only rows cover Proposition 13.2.5, Sections 13.3.1–4,
Theorem 13.5.1, corrected Proposition 13.5.2, and the later Propositions
13.6.7 and 13.7.4. Positive-depth implementation remains behind the depth-zero
release and its inflation/compact-induction consumer. The seventh pass
records a published statement of Proposition 13.2.5 on supplied data,
the eighth pass adds its part (3), and the ninth adds parts (5) and (6)
and a double-root restatement of parts (1), (2) and (4); the other eight
rows remain source-only. The two instability
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
full `G(k)`. Actual compactness, finite filtration quotients, fixed points,
type preservation, reduction and the rational parabolic correspondence
remain part of its proof boundary.

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
remains open in that task, although both inputs of its published reduction are
now proved (Lemma 5.3.5 row). Proofs of three other targets in the table were
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
adopted by this note. The roadmap's external pins remain survey leads. Any
adoption still requires a focused host compile, a mathematical and dependency
audit, and its exact pin and licence. The theorem-level axiom inspections
in the verified-proof sections above concern published metric proofs and
their aggregate. The 8 November 2026 refresh and its later passes add declaration inspections in
environment `bb168ec3-1031-46d9-816b-5c2ed7bbe1a6` to the rows it updates. For a
Prop-valued statement or a definition, such a report covers only the elaborated
declaration; it is not evidence that the target is proved.

Bundle A is open. Bundles B–F, the general constructed instance, the depth-zero
and positive-depth consumers, regression examples, GL comparisons and Renard
bridges are also open. This source ledger neither narrows those obligations nor
claims that the proposed Chapter V structural interfaces have already been
published in the Renard program.
