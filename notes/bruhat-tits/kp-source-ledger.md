# KP Bundles A–F source ledger and construction boundaries

This ledger connects the Library's Bruhat–Tits constructions and statements
with Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), and the
authors' corrections of 1 November 2024. Its dated sections record earlier
Library snapshots. The structured rows for Theorem 9.2.7, Section 13.2.6
and Proposition 13.5.2 include the results checked at Library commit
`2f86a99eb5616254ac5b9c399603c9bbbea15f7a`. The rows for Proposition
A.5.19 and Lemma A.5.13(4) describe the congruence–Lie map and its exact
proposition targets at that same commit.

`bruhatTitsCompletionCertificate` constructs one assignment for connected
reductive groups over nonarchimedean local fields of either characteristic
in universe `u`. This assignment satisfies the ten axioms of corrected
Definition 4.1.26 and unramified descent in Axiom 4.1.27, with UR 3 stated
as equality with the set of nonconstant upper affine-root restrictions.
The reduction transports the inter-group comparisons of Axioms 4.1.1 and
4.1.17 to the descended assignment along equivariant building
equivalences.

`depthZeroConsumer` applies to every facet of this assignment by
`IsAvailableFor.groupAxioms`. It gives the compact open parahoric, its
radical kernel, surjective reduction to finite reductive points, the
quotient equivalence, inflation and smooth compact induction. For
finite-dimensional complex inducing representations it identifies the
space of intertwiners with the equivariant kernels supported on finitely
many double cosets. `availableMaximalProP` applies to the same assignment
by `IsValid.isAvailableFor`. It gives the four facet conclusions of
corrected Proposition 13.5.2, with maximality and normalizers taken in
\(G(F)^0\).

The integral-model modules construct `congruenceLieHom` and
`congruenceLieQuotientHom` for \(0<n\le m\le 2n\) by reducing to a
square-zero kernel and identifying that kernel with the corresponding
Lie-lattice quotient. Their companion propositions state the kernel,
Henselian surjectivity, model functoriality, adjoint equivariance and
maximal-unramified compatibility, and the Lie-lattice formula for the
actual congruence models. Theorem 13.5.1 has separate centralizer, root
block and torus comparisons with the real-depth filtrations.

## Refresh of 8 November 2026

This refresh was made against Library commit
`c4a16df784376405a45b60df82583e8c26d8a4e3`. The six rows updated in this
refresh (Propositions 4.2.7 and 4.4.4, Theorem 4.2.10, Corollary 4.4.5,
Definition 4.1.26 and Theorem 7.5.3) cite that commit as the place of
their declarations. Each declaration was located in the modules listed
in its row and inspected with a Lean declaration inspection. The
inspections are recorded in the `axiom_reports`; every reported axiom
set is `propext`, `Classical.choice`, `Quot.sound`. Each row's last
`hypotheses` entry, beginning "Recorded Lean scope", states the Lean
hypotheses and their differences from the source.

`conditional` means the following here. The theorem is proved on
supplied `ValuationBuildingData` or `ParahoricBuildingData` with the
listed axiom predicates as hypotheses, or (for Proposition 4.4.4) for
abstract group-action data. It stays conditional until the data and
witnesses are constructed. For the Section 4.2 rows that construction is
the published target `RootValuationBuildingConstructionStatement`. The
source and correction fields of the updated rows are unchanged; they
were compared with the originals afterwards, as described below.

A second update on the same day recorded five Bundle C rows on the same
terms. Theorem 5.2.1, Theorem 5.3.3, Theorem 5.3.4 and replaced Lemma
5.3.5 are recorded as `statement`. Their Lean targets are unproved
Prop-valued statements. Those for 5.2.1 and 5.3.4 assume the full
corrected Definition 4.1.26 through
`KPBuildingAssignment.IsAvailableFor`. Those for 5.3.3 and 5.3.5 assume
only the Chapter 7 apartment axioms on supplied `ParahoricBuildingData`,
together with the Chapter 5 Henselian and perfect-residue hypotheses.
Definition 6.6.1 is recorded as a partial `definition`: `Wtilde^0` and
`W_aff` are formalized, `Wtilde^1` is not. The inspections are recorded
in the `axiom_reports`, with the same axiom set as above.

Both updates were first prepared while the original PDFs could not be
opened. On 9 November 2026 they were readable again, with the SHA-256
fingerprints recorded in the rows, and the source and correction fields
of all eleven updated rows were compared with the originals: book PDF
pages 196, 199–204, 213–215, 217–222, 261–262, 266–267 and 291–292, and
corrections PDF pages 1–2, 24–25, 27–30, 33 and 35. They agree with the
originals. The only change is that the Theorem 5.3.4 locator was
narrowed to the page carrying the theorem and its proof. The same day
the Theorem 7.5.3 row was corrected: three of the eight fields of
`AffineIwahoriTitsInputs` have published proofs and are no longer
described as unproved.

A third update on 9 November 2026 records Corollary 4.2.14 as
`statement`. Its target `BoundedSubgroupFixedPointStatement` first
appeared in Library commit `3f0bcbd4638c9c42befdc9f7e1578d62fde2c959`,
which the row cites. It assumes the same seven axiom predicates as the
Proposition 4.2.7 row and covers both assertions of the corollary. The
row's source and correction fields are unchanged and agree with the
originals, compared on 9 November 2026 at book PDF pages 101 (Definition
2.2.1) and 204 and corrections PDF pages 1–2 and 28–29. Its target was
unproved at that update.

A fourth update on 9 November 2026 records Theorem 5.3.3 as
`conditional`. The theorem `iwasawaDecomposition` proves
`IwasawaDecompositionStatement` on supplied `ParahoricBuildingData`
satisfying the Chapter 7 apartment axioms. It first appears in Library
commit `0646cc6120e56febaf6f88f723f3b147d0e23d59`. The same update
records the conditional assemblies now available for replaced Lemma
5.3.5. It also replaces the remarks in the Theorem 5.3.3 and Theorem
7.8.1 rows that `standardUnipotentPoints` had not been compared with
`Dynamic.unipotent`. The Library now proves this equality for every
cocharacter of a maximal split torus of a connected reductive group; no
genericity hypothesis is needed.

The fourth update, completed on 10 November 2026, also records two
statements first published in Library commit
`230ec08a058832bd6941fa887c30897e4826429b`, which their rows cite.
`FacetClosureUnionClosedStatement` is the second assertion of Theorem
4.2.10, under the hypotheses of the published completeness theorem. The
Theorem 4.2.10 row stays `conditional`, a status that refers to its
first assertion. `BruhatTitsAvailabilityStatement` states the corrected
Definition 4.1.26 part of Theorem 9.2.7: some `KPBuildingAssignment`
satisfies `IsValid`. The Theorem 9.2.7 row therefore becomes
`statement`. That statement omits Axiom 4.1.27 and asserts the existence
of some data rather than the source's descended construction, so it is
not the full certificate. It had no proof. The source and correction
fields of both rows are unchanged. On 10 November 2026 their statement
locators were compared again with book PDF pages 202 and 360 and
corrections PDF page 27; they agree. For the check of the statements the
originals were read at book PDF pages 196–197, 199, 202–203, 230, 354
and 360 and corrections PDF pages 1 and 27–29.

A fifth update on 10 November 2026 records proofs first published in
Library commit `e449cde988d4e97ab280b8d4d11262887ccc26e0`, which each
row cites. Corollary 4.2.14 becomes `conditional`:
`boundedSubgroupFixedPoint` proves its statement. The second assertion
of Theorem 4.2.10 is proved by `facetClosureUnionClosed`, so both
assertions of that row are now proved on supplied data. Theorem 5.3.4
becomes `conditional`: `availableIwasawa` proves
`AvailableIwasawaStatement` under `IsAvailableFor`, while
`IwasawaExistenceStatement` stays unproved. Corollary 7.4.9 becomes
`conditional`: `ParahoricBuildingData.chamberIwahoriDecomposition`
proves its statement for every supplied datum.
`unipotentIwahoriDoubleCoset` proves part (4) of Theorem 7.8.1. That row
stays `statement`, because parts (1)–(3) are unproved. The same commit
proves that `Z(F)^0` is normal in `N(F)` for every supplied datum
(`ParahoricBuildingData.normal_normalizerZero`). This updates the
Definition 6.6.1 row and supplies both inputs of the published reduction
for replaced Lemma 5.3.5. That row stays `statement`, because no theorem
of its exact type is published. The Theorem 9.2.7 row also lists three
statements of `Langlands.BruhatTits.SpecialCompact` that assume
availability or validity. Each new declaration was inspected at commit
`e449cde9`; every reported axiom set is `propext`, `Classical.choice`,
`Quot.sound`. The source and correction fields of these rows are
unchanged.

A sixth update on 10 November 2026 adds three rows, so the ledger now
has forty-eight. Proposition 4.2.24, Lemma 6.7.1 and Section 6.7.2 are
recorded as `statement`. Their targets
`ApartmentConjugacyFixingIntersectionStatement`,
`LeviApartmentRestrictionStatement` and
`LeviSpecialPointRestrictionStatement` were first published in Library
commit `d39b5aee822fe2ad1aadf07861ebd9a4c2df62a8`. The source and
correction fields of the new rows were compared on 10 November 2026 with
book PDF pages 60–61, 207–208, 226, 230–232, 249 and 264–265 and
corrections PDF pages 28–30 and 32. Theorem 5.2.1 becomes `conditional`:
`availableCartan` (first published in the same commit) proves
`AvailableCartanStatement` under `IsAvailableFor`; its proof does not
use the unproved Proposition 4.2.24. The Theorem 9.2.7 row now records
how `BruhatTitsAvailabilityStatement` is split into six statements first
published in Library commit `58a91d4ff65b8d6dcb8aa417bfc63399feb8b4af`.
It also records the published reduction of
`RootValuationBuildingConstructionStatement` and
`ChapterSevenBuildingAxiomsStatement`, first published in Library commit
`8c11c93f98b439395e0e7da779c98bb27e24bd6d`. The Lemma 6.7.1 row names
`LeviApartmentAxiomsInheritanceStatement` from the same commit as a
consumer. The four declarations added to the rows' `lean_declarations`
were inspected at commit `e7487341`; every reported axiom set is
`propext`, `Classical.choice`, `Quot.sound`. The source and correction
fields of the Theorem 5.2.1 and 9.2.7 rows are unchanged.

A seventh update on 11 November 2026 updates two Bundle D and E rows.
Section 13.2.6 becomes `conditional`. The depth-zero reduction
`depthZeroQuotientEquiv` (first published in Library commit
`7047367a78583edbe335517824e30403414aa3f0`) and its inflation and
compact-induction consumer (first published in Library commit
`7103f5282c4897716543f227940fdb2a0e12e70e`) are proved on supplied
`RelativeComponentModelData` and `SpecialFibreQuotientData` whose
projection is the represented fppf quotient by the unipotent radical.
Here `conditional` means that the row stays conditional until the actual
parahoric model, its radical and reductive quotient are constructed and
Corollary 8.4.12 identifies the radical-preimage kernel with the
Moy–Prasad group `P_{x,0+}`. The local-field corollary additionally
assumes the unproved `CongruenceNeighborhoodBasisStatement`. The five
declarations added to the row were inspected at commit `389dbc16`.

Proposition 13.2.5 becomes `statement`. Its target
`MoyPrasadFiltrationStatement` (first published in Library commit
`642008d6b3b837d8bd76de0cabcaff3db00088c0`) states separatedness,
bounded openness at finite real depths, and parts (1), (2) and (4) for
supplied `ParahoricBuildingData` and a supplied centralizer filtration
with explicit axioms; the Section 9.8 filtration is not constructed.
Parts (3), (5) and (6) remain unformalized, and the printed root-index
discrepancy of part (3) recorded below is unchanged. Its six
declarations were inspected at commit `389dbc16`, where the pair is
byte-identical to commit `642008d6`. Every reported axiom set of this
update is `propext`, `Classical.choice`, `Quot.sound`. The source and
correction fields of both rows are unchanged.

An eighth update on 11 November 2026 adds four Bundle B rows for the
unramified descent of Chapter 9, so the ledger now has fifty-two rows.
All four are `statement`. Section 9.2.1 (a Galois-fixed point of a
stable apartment) and Proposition 9.3.4 record
`UnramifiedGaloisFixedApartmentStatement` and
`SpecialTorusExistenceStatement` (first published in Library commit
`9bc92c384fa84da7ce5811a5979d408fb69d40b0`). Theorem 9.6.5 records
`ValuationApartmentAxiomsExistenceStatement` (first published in Library
commit `58a91d4ff65b8d6dcb8aa417bfc63399feb8b4af`) and this program's
descent module (first published in Library commit
`3c9b0579a8f2d36d16294ce48b465d1ec5aee273`). That module adds two
statements and their conjunction and proves
`valuationApartmentAxiomsExistenceReduction`, which derives
`ValuationApartmentAxiomsExistenceStatement` from five statements. None
of the five is proved yet, so the row stays `statement`. Lemma 9.8.1
records `CentralizerFiltrationExistenceStatement` (first published in
Library commit `3c9b0579a8f2d36d16294ce48b465d1ec5aee273`). The Section
9.2.1 row records the zero-section embedding into the enlarged building
as G(k)^1-equivariant, not G(k)-equivariant as printed; the Bundle B
notes explain the discrepancy. The Theorem 9.2.7 row points to the new
rows. The update also adds part (3) of Proposition 13.2.5, with
indivisible-root blocks, to that row: `MoyPrasadProductStatement` and
its product map (first published in Library commit
`63d9b857523edf47443b7bf30844159e526d00b0`). The row stays `statement`.
The seventh update's remark that parts (3), (5) and (6) remain
unformalized now applies to parts (5) and (6) only.

The source and correction fields of the new rows and of the part (3)
update were compared on 11 November 2026 with book PDF pages 162,
209–211, 278, 281, 283, 354, 356–357, 363–365, 394–398, 405–406 and 500
and corrections PDF pages 33, 39–41 and 50. Eleven declarations were
inspected: `SpecialTorusExistenceStatement` at commit `3c9b0579`, the
two part (3) declarations at commit `8964b41f`, the others at commit
`529b851c`. The inspected Lean files are byte-identical to their first
publications. Every reported axiom set is `propext`, `Classical.choice`,
`Quot.sound`.

A ninth update on 12 November 2026 updates three rows and adds none.
Proposition 13.2.5 gains parts (5) and (6): `MoyPrasadLeviStatement` and
its two conjuncts (first published in Library commit
`6bff2655fd831aefb39f6688f904aa7410cb0f73`), stated at positive real
depth for the parabolic subgroups containing the split torus of the
data. The seventh update's remark that parts (5) and (6) remain
unformalized no longer applies. The same row gains
`MoyPrasadDoubleRootStatement`, its two conjuncts and the predicate
`IsDoubleRootCommutatorFriendly` (first published in Library commit
`297a8ef0ba780a488196cf62285af3ded2e2baa6`). They restate parts (1), (2)
and (4) with an extra premise on the centralizer component of
commutators involving a double root. The source proofs of these parts
use that bound, but Definition 7.2.1 does not give it; the Bundle E
notes explain the gap. The Lemma 9.8.1 row gains the matching existence
statement. Both rows stay `statement`. The Theorem 9.2.7 row records
that `ActualApartmentSplittingStatement` and
`AffineIwahoriTitsBuildingStatement`, two of the four inputs of the
published reduction to `RootValuationBuildingConstructionStatement`, are
proved; the row stays `statement`.

The source and correction fields of the Proposition 13.2.5 and Lemma
9.8.1 rows were compared on 11 November 2026 with book PDF pages 162,
264, 268, 270–273, 276–277, 283–284, 296, 302, 399–401, 405–406 and
499–500 and corrections PDF pages 33–36, 41 and 49–50. Ten declarations
were inspected: `MoyPrasadLeviStatement` at commit `4ed6d979`, its two
conjuncts and the theorems `actualApartmentSplitting` and
`affineIwahoriTitsBuilding` at commit `14c08c22`, and the five
double-root declarations at commit `16c60abd`. The inspected Lean files
are byte-identical to their first publications. Every reported axiom set
is `propext`, `Classical.choice`, `Quot.sound`.

A tenth update on 12 November 2026 updates three rows and adds none.
Section 13.2.6 stays `conditional`. Its local-field corollary
`localFieldDepthZeroInductionHomEquiv` no longer depends on an unproved
statement: `congruenceNeighborhoodBasis_proof` (first published in
Library commit `ba77b83f98d4cbe92842b4645577633e0541fdab`) proves
`CongruenceNeighborhoodBasisStatement`, which also makes the integral
points of every supplied model compact. The seventh update's remark that
the corollary assumes that statement no longer applies. The row also
gains `CompactInductionIntertwiningStatement` and its three conjuncts
(first published in Library commit
`79de65ce5fcd6dc5f182612988e1b529d49a63b4`), statements after Vignéras
1996, I.8.5, that describe the maps between compactly induced
representations from an open subgroup by intertwining kernels and by
their values at double-coset representatives. They state the
intertwining and double-coset theorem that the row's consumer asked for.
Proposition 9.3.4 stays `statement` and gains
`SpecialTorusIntegralModelStatement` (first published in Library commit
`ba77b83f98d4cbe92842b4645577633e0541fdab`), a derived statement of the
building input of its source proof. Theorem 9.2.7 stays `statement`; its
dependencies now record that two conditional statements on available or
valid data, `ValidAssignmentTorusRebasingStatement` and
`AvailableSpecialVertexExistenceStatement`, are proved.

The source and correction fields of the Proposition 9.3.4 row were
compared on 12 November 2026 with book PDF pages 194, 317, 358–359, 363
and 687; the Vignéras locators of the Section 13.2.6 row were compared
with PDF pages 82–86 of that book. Seven declarations were inspected:
the four intertwining statements at commit `9951a27f`,
`SpecialTorusIntegralModelStatement` and the theorem
`congruenceNeighborhoodBasis_proof` at commit `c5b9c2cf`, and the
theorem `availableSpecialVertexExistence` at commit `24a49431`. The
first six inspected Lean files are byte-identical to their first
publications. Every reported axiom set is `propext`, `Classical.choice`,
`Quot.sound`.

An eleventh update on 13 November 2026 updates ten rows and adds none.
The Library had meanwhile advanced through commits
`ed924aef420de137b4cbaa3b063a3618afcd73fd`,
`17dd94ea3f677b20fb5ab95b285cbc3fd7cde03e` and
`8ff9abe94fbb8d61ec05e4a00fc92f7cf1534b96`. The rows cite the commit in
which each proof is present. Proposition 4.2.24, Lemma 6.7.1, Section
6.7.2 and replaced Lemma 5.3.5 change from `statement` to `conditional`:
`apartmentConjugacyFixingIntersection`, `leviApartmentRestriction`,
`leviSpecialPointRestriction` and `unipotentNormalizerCoset` prove their
statements on supplied data. Proposition 13.5.2 changes from an empty
status to `statement`:
`Langlands.BruhatTits.MaximalProP.AvailableMaximalProPStatement` states
the corrected proposition, with ambient group `G(F)^0` in both parts, on
available Bruhat–Tits data. Theorems 7.5.3, 7.8.1, 9.2.7 and 9.6.5 stay
`statement` and record newly proved inputs and published reductions. Six
of the seven inputs of the reduction to the `G(F)^0` branch of Theorem
7.5.3 are proved; the seventh, Theorem 7.8.1(1), and Theorem 7.8.2
reduce through published reductions to
`SimplyConnectedFacetFixingStatement`. Proposition 13.2.5 stays
`statement`. Its separation and finite-depth bounded-openness conjuncts
are proved, and the row records an unformalized paper counterexample:
for ramified quasi-split SU(3) over `Q_2` and the smallest centralizer
filtration satisfying the four published filtration axioms,
`MoyPrasadCovarianceStatement` and `MoyPrasadCommutatorStatement` fail.
The double-root variants and KP's own filtration are not affected.

The source and correction fields of the Proposition 13.5.2 row were
compared on 13 November 2026 with book PDF pages 507–508 and corrections
PDF page 49. Twenty-three declarations were inspected: nineteen at
commit `ed924aef` and `doubleCosetStatementReduction`,
`moyPrasadSeparated`, `moyPrasadBoundedOpen` and
`unipotentNormalizerCoset` at commit `8ff9abe9`. Every reported axiom
set is `propext`, `Classical.choice`, `Quot.sound`.

A twelfth update on 13 November 2026 updates the Section 13.2.6 row and
adds none. The row stays `conditional` and gains two modules, both first
published in Library commit `cfedefb680f317b0ea5d351023e1c9dd886b2547`.
`Langlands.BruhatTits.IntegralModels.FiniteReductiveQuotient` proves
that an affine group scheme locally of finite type over a finite
commutative ring has finitely many points. It obtains this from the
published `LangWeil.CurvePlane.finite_algHom_of_finiteType`. For
supplied data over a local domain with finite residue field and a
quotient locally of finite type, the module packages the residue-field
points of the quotient as a finite group (`finiteQuotientGroup`) and
shows that the radical preimage has finite index in the integral points
of the neutral model. Over a Henselian base,
`index_positivePoints_subgroupOf` computes that index as the number of
residue-field points of the quotient; a separate theorem specializes it
to the integer ring of a nonarchimedean local field.
`Langlands.BruhatTits.IntegralModels.DepthZeroCompactOpen` shows that
the level-one congruence subgroup lies in the radical preimage. Over a
nonarchimedean local field, for `G` affine and locally of finite type
with the canonical topology on `G(F)`, it shows that the radical
preimage is open and compact in `G(F)`, bundled as
`localFieldPositiveOpenSubgroup`. These results discharge, on supplied
data, the finiteness, compactness and openness parts of the row's
consumer test. The identification of the radical preimage with
`P_{x,0+}`, the construction of the actual models and the proofs of the
intertwining statements remain open. Eleven declarations were inspected
at commit `cfedefb6`. Every reported axiom set is `propext`,
`Classical.choice`, `Quot.sound`. The source and correction fields of
the row are unchanged.

A thirteenth update on 13 November 2026 updates eight rows and adds
none; no formal status changes. The Theorem 9.2.7 row records the two
implication statements first published in Library commit
`cfedefb680f317b0ea5d351023e1c9dd886b2547` to split
`BruhatTitsAvailabilityStatement`:
`BruhatTitsAvailabilityReductionStatement` derives it from
`GroupAxiomsExistenceStatement`, and
`GroupAxiomsExistenceReductionStatement` derives that from four focused
statements. Both implications are proved in Library commit
`730bd1f25b056b8106a2697e003c1ef1733a6b30`, so
`BruhatTitsAvailabilityStatement` now follows from those four
statements. The Theorem 9.6.5 row records a proved part of
`ValuationBuildingApartmentAxiomsStatement`:
`ValuationBuildingQuasiSplitAdjointTranslationStatement`, the
translation part of the quasi-split adjoint sentence of AS 5, is proved
(Library commit `7f43c3c930ff92f76dae6589da1678ad729017e5`) from
`QuasiSplitAdjointSimpleRootTransitivityStatement`, which is proved in
Library commit `51e4d8972659f1ffcf0ca89e8eee9540a30b52d3`. The
Proposition 13.2.5 row records that the counterexample note is in the
Library and that the Markdown of the affected statements now reports it.
Lemma 11.5.2, Proposition 11.5.4 and Corollaries 11.7.5 and 11.7.6 stay
source-only; their formalization needs the actual Kottwitz homomorphism,
which is to be constructed first. Nine declarations were inspected: four
in modules first published in commit `cfedefb6`, the two assembly proofs
(commit `730bd1f2`), `quasiSplitAdjointSimpleRootTransitivity` (commit
`51e4d897`), `valuationBuildingQuasiSplitAdjointTranslation` (commit
`7f43c3c9`) and
`ValuationBuildingQuasiSplitAdjointTranslationStatement`. Every reported
axiom set is `propext`, `Classical.choice`, `Quot.sound`. The source and
correction fields of every row are unchanged.

A fourteenth update on 13 November 2026 updates six rows and adds none.
Theorems 8.3.2, 8.3.13, 8.4.10 and 8.4.19 and Corollary 8.4.12 change
from an empty status to `statement`, each for the part described in its
Recorded Lean scope entry. `UnramifiedParahoricModelStatement` (Library
commit `cc5aa77fa8dbdc6e723091c7b710ab0d81162c4e`) asks, over the
integers of the maximal unramified extension `K` of a nonarchimedean
local field and on supplied building data of `G_K`, for a smooth model
with integral points `G(K)^1_Ω` and its relative identity component,
which has connected fibres and integral points `G(K)^0_Ω`. It covers
Theorem 8.3.13 and the `G(K)^1_Ω` part of Theorem 8.3.2; the dagger
model is absent. Its full-model part is proved from five statements,
then all unproved, by `exists_smoothFullModel_of_vertexInputs` (commit
`7f43c3c930ff92f76dae6589da1678ad729017e5`); the nineteenth update
records two of them as proved. `UnramifiedModelKernelStatement` (commit
`51e4d8972659f1ffcf0ca89e8eee9540a30b52d3`) states the smooth connected
unipotent kernel of Proposition 8.4.15, the valid first assertion of
Theorem 8.4.19(1), without the product decomposition.
`UnramifiedFacetRootDatumStatement` and
`UnramifiedFacetPositiveRadicalStatement` (commit
`73b1430a339b037d27e9096762b0400adb4fbd19`) state Axiom 4.1.22(6) and
the inclusion of Axiom 4.1.22(7) for descended facet models over the
integers of the local field; KP 4.1.28 derives these axioms from Theorem
8.4.10 and Corollary 8.4.12. Each of the five rows also cites
`IntegralModelAxiomsStatement`, the descended supplied-data form of
Axioms 4.1.20 and 4.1.22, which contains the only Lean form of Theorem
8.4.19(2)–(4). None of these statements is proved. The Section 13.2.6
row stays `conditional`. It records the proofs of the three intertwining
statements (commit `730bd1f25b056b8106a2697e003c1ef1733a6b30`) and their
depth-zero specialization
`Langlands.BruhatTits.IntegralModels.DepthZeroIntertwining` (commit
`73b1430a`), which over a local field needs only the supplied model and
quotient. Twenty-four declarations were inspected: eight at commit
`eded01f2`, five at commit `451cce4c` and eleven at commit `aae8cb82`.
Each inspected module is byte-identical to the commit cited for it and
to commit `a0627c91`. Every reported axiom set is `propext`,
`Classical.choice`, `Quot.sound`. The source and correction fields of
every row are unchanged.

A fifteenth update on 13 November 2026 updates seven rows and adds none.
The Section 9.2.1 row changes from `statement` to `conditional`: the
theorem `unramifiedGaloisFixedApartment` (Library commit
`b128d289028bf75629e9e364ecf151c484b27a85`) proves
`UnramifiedGaloisFixedApartmentStatement` for every supplied Γ-stable
class of valuations. Lemma 11.5.2, Proposition 11.5.4 and Corollaries
11.7.5 and 11.7.6 change from an empty status to `statement`: The
Library states `CharacterKernelStatement`, `ZeroKernelStatement`,
`ChamberStatement` and `QuotientStatement` (Library commit
`0c3f30c24701c74d5474fca3fbb5324a99aa1d58`) for the rational Kottwitz
map `reductiveKottwitzRational`, which is selected by its characterizing
property. The unproved `ReductiveKottwitzExistenceStatement` and
`ReductiveKottwitzDescentStatement` assert that the selections have
those properties. The chamber clause of Corollary 11.7.5 is stated on
supplied building data. The Theorem 9.6.5 row records that four
published theorems reduce `UnramifiedValuationDescentStatement` to
`UnramifiedTorusUnitFixedApartmentStatement` and
`UnramifiedFixedOppositeStatement`; no published declaration states this
composite. The Proposition 13.5.2 row lists the five intermediate
statements of the proof of `AvailableMaximalProPStatement`. Thirteen
declarations were inspected at Library commit `6948120d`; each inspected
module is byte-identical to the commit that first published it. Every
reported axiom set is `propext`, `Classical.choice`, `Quot.sound`. The
source and correction fields of every row are unchanged.

A sixteenth update on 13 November 2026 updates four rows and adds none.
The Proposition 13.2.5 row changes from `statement` to `conditional`. On
supplied building data and a supplied centralizer filtration,
`moyPrasadProduct`, `moyPrasadLevi`, `moyPrasadDoubleRootCovariance` and
`moyPrasadDoubleRootCommutator` prove part (3), parts (5) and (6), and
the double-root forms of parts (1), (2) and (4) (Library commits
`cfedefb680f317b0ea5d351023e1c9dd886b2547` and
`cc5aa77fa8dbdc6e723091c7b710ab0d81162c4e`). With the earlier proofs of
separation and bounded openness, every part is proved on supplied data.
The supplied-filtration covariance and commutator statements without the
double-root premise remain refuted on paper. The Theorem 9.2.7 row
records that `availableSimultaneousStandardBasis` proves
`AvailableSimultaneousStandardBasisStatement`, so five of the six
conditional statements of the joint-basis reduction are proved. The
Theorem 9.6.5 row records the proof
`torusEquivariantCharacterValueDescent` of
`TorusEquivariantCharacterValueDescentStatement`. It also records three
declarations towards `UnramifiedFixedOppositeStatement` (Library commit
`430cc03fe803c5dbf74bc3baf91e8f7a2c26ea9c`):
`UnramifiedFixedWallInvarianceStatement`, the proved implication
`unramifiedFixedOpposite_of_wallInvariance` from it to
`UnramifiedFixedOppositeStatement`, and
`UnramifiedFixedDepthZeroOppositeStatement`. The Theorem 5.3.4 row
records that `parahoricLeCompactStabilizer` proves
`ParahoricLeCompactStabilizer` for all supplied data. Nine declarations
were inspected, eight at Library commit `0f84a0d8` and one at Library
commit `1bd55dea`; each inspected module is byte-identical to the commit
that first published it. Every reported axiom set is `propext`,
`Classical.choice`, `Quot.sound`. The source and correction fields of
every row are unchanged.

A seventeenth update on 14 November 2026 updates one row and adds none.
The Section 13.2.6 row stays `conditional` and records five published
regression modules in `Langlands.BruhatTits.IntegralModels`:
`MultiplicativeDepthZero` and `SplitTorusDepthZero` (Library commit
`85c2fe719cf62e96f22aaf4ca03961c5814d086b`), `GeneralLinearDepthZero`
(commit `db8d6b3d466f2fd453a4df4624ce6c90db8eed46`), and
`SymplecticDepthZero` and `SpecialLinearDepthZero` (commit
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
instance. Thirty-two declarations were inspected, one at Library commit
`3489c503` and thirty-one at Library commit `410c7947`; each inspected
module is byte-identical to the commit that first published it. Every
reported axiom set is `propext`, `Classical.choice`, `Quot.sound`. The
source and correction fields of every row are unchanged.

An eighteenth update on 14 November 2026 updates three rows and adds
none. The corrected Proposition 13.5.2 row changes from `statement` to
`conditional`: `availableMaximalProP` (Library commit
`410c79471b79f65a02fb0f6070da7f2800793ff3`) proves
`AvailableMaximalProPStatement` for every available Bruhat–Tits
assignment, and the existence of available data,
`BruhatTitsAvailabilityStatement`, remains unproved. The row also
records that four of the five intermediate statements of the proof of
`AvailableMaximalProPStatement` are proved. The Lemma 9.8.1 row records
that published theorems reduce both of its existence statements to
`LocalMoyPrasadGroupPropertiesStatement` and
`UnramifiedComparisonExistenceStatement`; its status stays `statement`.
The Theorem 9.6.5 row records that `UnramifiedQuasiSplitStatement`, one
of the five inputs of its proved reduction, now holds:
`henselianDiscreteQuasiSplit` (Library commit `410c7947`) proves
`HenselianDiscreteQuasiSplitStatement`, and the published
`unramifiedQuasiSplit_of_henselianDiscrete` applies it to the maximal
unramified extension. Two of the five inputs are now proved, and the row
stays `statement`. Eight declarations were inspected, five at Library
commit `410c7947` and three at Library commit `757a6793`. Each inspected
module is byte-identical to the commit that first published it, or, if
that commit is unknown, to commit `ed924aef`. Every reported axiom set
is `propext`, `Classical.choice`, `Quot.sound`. The source and
correction fields of every row are unchanged.

A nineteenth update on 14 November 2026 updates two rows and adds none.
The Theorem 8.3.2 row records that two of the five inputs of its
conditional full-model construction are proved, both first published in
Library commit `410c79471b79f65a02fb0f6070da7f2800793ff3`:
`finiteVertexFixerApproximation` proves
`FiniteVertexFixerApproximationStatement`, and `finiteIndexEnlargement`
proves `FiniteIndexEnlargementStatement`, the finite-index part of KP
Proposition A.7.1. `VertexOneStabilizerMaximalBoundedStatement`,
`MaximalBoundedIntegralModelStatement` and `SmoothIntersectionStatement`
remain unproved, and the row stays `statement`. The proof of
`finiteIndexEnlargement` uses the helper module
`Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargement.SubHopf`,
which is adapted from the `TakK` section of the Anthropic FLT file
`P2M/Sol/S_HopfAlgebra_faithfullyFlat_subalgebra_of_isReduced_of_fg_of_isAlgClosed.lean`
at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (Copyright 2026
Anthropic, PBC; Apache License 2.0; licence, notice and attribution
files under `licenses/Anthropic-FLT/`). The row's `external_code` field
records this reuse, with its pin and licence. The Definition 6.6.1 row
records that `unramifiedZeroPointsIndependence` (Library commit
`db8d6b3d466f2fd453a4df4624ce6c90db8eed46`) proves
`UnramifiedZeroPointsIndependenceStatement`, the independence part of KP
Lemma 2.6.24, so the earlier route `normalizerZero_normal` to the
normality of `Z(F)^0` in `N(F)` now needs no premise; the row stays
`definition`. Three declarations were inspected at Library commit
`20f83141`; each inspected module is byte-identical to the commit that
first published it. Every reported axiom set is `propext`,
`Classical.choice`, `Quot.sound`. The source and correction fields of
every row are unchanged.

A twentieth update on 14 November 2026 updates five rows, adds none and
changes no status. The Theorem 9.6.5 row corrects a stale sentence:
since Library commit `85c2fe71`,
`unramifiedFixedWallInvariance_of_depthZero_of_leviTransport` takes
`UnramifiedFixedDepthZeroOppositeStatement` as a hypothesis. The row
also records the published split of
`UnramifiedTorusUnitFixedApartmentStatement` (KP Proposition 9.3.13 as
corrected) into three statements, of which
`UnramifiedSplitTranslationFixerStatement` is proved by
`unramifiedSplitTranslationFixer` (Library commit
`c40a01345b2f4172fa41e07ff31644b40e695003`), and the published
reductions of the transporter statement to KP Proposition 9.3.11(1) and
of the depth-zero statement to recovered models and KP Theorem 8.2.9.
Its descent input now rests on three unproved statements. The Lemma
9.8.1 row records the reduction of
`UnramifiedComparisonExistenceStatement` to special-torus existence,
valuation descent and four field statements. The Lemma 11.5.2,
Proposition 11.5.4 and Corollary 11.7.5 rows record their published
reductions to four, three and seven statements; the only proved input
among them is `UnramifiedSmoothModelDescentStatement`. Two composites
that no published declaration states were checked with separate Lean
checks. Ten declarations were inspected at Library commit `c40a0134`;
each inspected module is byte-identical to the commit that first
published it. Every reported axiom set is `propext`, `Classical.choice`,
`Quot.sound`. The source and correction fields of every row are
unchanged.

A twenty-first update on 14 November 2026 updates one row and adds none.
The Section 13.2.6 row stays `conditional` and records four further
published regression modules in `Langlands.BruhatTits.IntegralModels`:
`NormOneTorusDepthZero` (Library commit `e5365902`),
`QuadraticNormOneDepthZero` (Library commit `b3a1bdaf`),
`NormOneTraceSmoothness` (Library commit `b3a1bdaf`) and
`GeneralLinearIwahoriComparison` (Library commit `c40a0134`). For the
norm-one torus `R¹_{E/F} G_m` of a finite separable extension of a
nonarchimedean local field, `NormOneTorusDepthZero` takes as supplied
integral data a finite free `𝒪[F]`-algebra `B` with generic fibre `E`, a
proof `hB` that its norm-one kernel is smooth, and an isomorphism `eκ`
of its special fibre over `𝓀[F]` with a field `k'`. From these the
kernel gives actual model data whose special fibre, the norm-one torus
of `k'` over the residue field, is its own reductive quotient; the index
of the radical preimage is the number of norm-one units of `k'`, `q+1`
when `[k':𝓀[F]]=2`, and the torus is anisotropic. The field-fibre
hypothesis `eκ` is used to show that the special fibre is a torus;
smoothness of the kernel alone does not imply it. Unramified quadratic
data exist over every such field, so `exists_unramifiedQuadraticNormOne`
gives an actual anisotropic instance with index `q+1`.
`normOne_smooth_of_hasTraceOne` proves smoothness of the norm-one kernel
over a noetherian base when some element has trace one; it supplies `hB`
only, not `eκ`, connectedness of the special fibre or a reductive
quotient. For `GL_N`, write `K = GL_N(𝒪[F])` and `K^+` for the kernel of
reduction; the preimages `I^+ ≤ I` in `K` of the upper unipotent and
upper triangular groups over the residue field satisfy `[I:I^+]=(q-1)^N`
and `[I^+:K^+]=q^(N choose 2)`, `I/I^+` is the diagonal torus,
`[K:I]=q+1` for `N=2`, and `I` is proper in `K` for `N ≥ 2`. No building
point appears, and none of these groups is identified with KP's
`P_{x,0}`, `P_{x,0+}` or `T(k)_0`. Multipliable roots and nontrivial
component groups still have no regression instance. Thirty-three
declarations were inspected at Library commits `457e31a2` and
`c40a0134`; each inspected module is byte-identical to the commit that
first published it. Every reported axiom set is `propext`,
`Classical.choice`, `Quot.sound`. The source and correction fields of
every row are unchanged.

A twenty-second update on 14 November 2026 updates eight rows, adds none
and changes no status. It records proofs published since Library commit
`c40a0134`. In the Theorem 9.6.5 row,
`unramifiedTwistedFixedTranslation` proves
`UnramifiedTwistedFixedTranslationStatement`, so the descent input now
rests on two unproved statements,
`UnramifiedFixedPairSpecialApartmentStatement` and
`UnramifiedFixedDepthZeroOppositeStatement`. In the Lemma 9.8.1 row,
`unramifiedComparisonLeviField` proves one of the four field statements
and `MaximalUnramified.localMoyPrasadPositiveProduct` proves the
positive-depth product prerequisite; the row also records the published
statements of the doubled-root commutator bound and of the depth-zero
cases of the group properties. In the Lemma 11.5.2 row,
`Kottwitz.cocenterTargetTorsion_proof` and the published proofs of the
torus character kernel prove two of the four inputs, and a published
reduction of functoriality leaves three unproved statements besides the
descent statement. In the Corollary 11.7.5 row, a published reduction of
Proposition 11.6.1 on supplied chambers uses
`MaximalUnramified.simplyConnectedNormalizerAffineWeyl`, which concerns
the maximal unramified extension and is not the unproved
`SimplyConnectedNormalizerAffineWeylStatement` of the Theorem 7.5.3 and
7.8.1 rows; a note in the Theorem 7.5.3 row says the same. The Corollary
11.7.6 row records its published reduction to the other three Kottwitz
rows; together the four rested on nine unproved statements at Library
commit `4f4af6ba`. Follow-ups at Library commit `58ad0f79` record the
proofs and reductions first published in commit `af5d652c`.
`IntegralModels.integralOppositeFactors` proves
`IntegralOppositeFactorsStatement` (Theorem 9.6.5 row).
`unramifiedComparisonOpenField` proves a second field statement of Lemma
9.8.1, and a published reduction derives the root field statement from
`UnramifiedDoubledRootDepthModelStatement`.
`Kottwitz.fundamentalInertiaMapStatement` proves
`FundamentalInertiaMapStatement`, and `Kottwitz.torusCharacterKernel`
proves the torus character kernel directly (Lemma 11.5.2 row). Published
reductions derive `ReductiveKottwitzExistenceStatement` from three
unproved statements (Lemma 11.5.2 row) and Proposition 11.5.4 from five
(Proposition 11.5.4 row); the four Kottwitz rows now rest on eight
unproved statements. In the Proposition 13.5.2 row,
`RationalPoints.boundedOpenNormalizer` proves the last of the five
intermediate statements of the proof of `AvailableMaximalProPStatement`;
the status of that row is unchanged. Composites that no published
declaration states were checked with separate Lean checks. Nine
declarations were inspected at Library commit `4f4af6ba` and eight at
Library commit `58ad0f79`; each inspected module is byte-identical to
the commit that first published it. Every reported axiom set is
`propext`, `Classical.choice`, `Quot.sound`. The source and correction
fields of every row are unchanged. Library commits `2d45c8a0` and
`f676fad7` differ from `58ad0f79` only in the notes
`notes/renard/item-ledger-v.md`, `notes/renard/item-ledger-vi.md` and
`notes/henniart/harris-cohomology-coverage.md`.

A twenty-third update on 14 November 2026 updates five rows, adds none
and changes one status: the Theorem 8.4.10 row changes from `statement`
to `conditional`. `unramifiedFacetRootDatum` (Library commit `af5d652c`)
proves `UnramifiedFacetRootDatumStatement` for all supplied data, by
applying the published reduction to integral opposite factors to
`integralOppositeFactors`. In the Theorem 8.3.2 row,
`vertexOneStabilizerMaximalBounded`, `maximalBoundedIntegralModel` and
`smoothIntersection` (Library commit `b3a1bdaf`) prove the remaining
three of the five inputs of the full-model construction, so the
`G(K)^1_Ω` model exists for every supplied building datum.
`unramifiedParahoricModel_of_torusInputs` (Library commit `af5d652c`)
proves `UnramifiedParahoricModelStatement` from two torus statements,
and the Theorem 8.3.13 row records the published reductions of these to
four unproved statements: connected generation (KP Lemma A.4.26),
rational surjectivity of torus quotients, finite generation modulo
neutral integral points and isogeny sections of torus surjections. The
Theorem 8.4.19 row records the published statements of parts (2)–(4) for
descended facet models (Library commit `0c3f30c2`) and published
reductions: `UnramifiedModelKernelStatement` follows from its
smooth-connected special case
`UnramifiedCompatibleModelKernelSmoothConnectedStatement`, and
`UnramifiedFacetParabolicImageStatement` from that statement, the
singleton radical generation statement and
`UnramifiedFacetPositiveRadicalStatement`. The Section 13.2.6 row
records the ramified quadratic norm-one regression
`RamifiedQuadraticNormOne` (Library commit `af5d652c`): for `F(√ϖ)` with
`2` a unit, the smooth norm-one model has a disconnected special fibre,
every point of `T(F)` is integral and the points reducing into the
identity component have index `2`, the value of corrected Remark 2.5.15.
Composites that no published declaration states were checked with
separate Lean checks. Forty declarations were inspected at Library
commit `70eca2e4`; each inspected module is byte-identical to the commit
that first published it, except
`Langlands.GroupScheme.IntegralModel.SmoothHomExtensionProof`, which is
byte-identical to commit `e5365902` and was first published in commit
`db8d6b3d`. Every reported axiom set is `propext`, `Classical.choice`,
`Quot.sound`. The source and correction fields of every row are
unchanged. Library commits `320321b3` and `1ddfc485` differ from
`70eca2e4` only in notes and the wiki index.

A twenty-fourth update on 14 and 15 November 2026 updates six rows, adds
none and changes no status. It records the proofs and reductions first
published in Library commits `7f5b5f04` and `aeb3911c`. In the
Proposition 9.3.4 row, `specialTorusBoundedModel` proves
`SpecialTorusBoundedModelStatement`, the premise of the published
reduction `specialTorusIntegralModelReductionStatement`, so
`SpecialTorusIntegralModelStatement` follows from published proofs;
`SpecialTorusExistenceStatement` is still unproved. In the Lemma 9.8.1
row, `unramifiedComparisonZeroField` proves a third field statement, so
both existence statements of that row follow from five unproved
statements; `MaximalUnramified.localMoyPrasadDepthZero` proves the
depth-zero statement; and
`kpLocalDoubleRootCommutator_of_valuedRankOneCoordinates` derives
`KPLocalDoubleRootCommutatorStatement` from
`QuasiSplitValuedRankOneCoordinatesStatement`. In the Lemma 11.5.2 row,
`Kottwitz.simplyConnectedDerivedKottwitz_proof` is a named theorem for
`SimplyConnectedDerivedKottwitzStatement`, which was already
unconditional at Library commit `58ad0f79`;
`zExtensionMorphismDomination` proves
`ZExtensionMorphismDominationStatement`; and
`inducedTorusQuotientPointSurjectivity` makes
`ZExtensionPointSurjectivityStatement` follow from published proofs. So
`CharacterKernelStatement` follows from three unproved statements. In
the Proposition 11.5.4 row, `Kottwitz.torusKottwitzKernel` proves
`TorusKottwitzKernelStatement`, and
`Kottwitz.zExtensionUnramifiedKernelReduction` and
`Kottwitz.zExtensionRationalKernelReduction` reduce the two clauses of
`ZExtensionKottwitzKernelSurjectivityStatement`. The published reduction
of Proposition 11.5.4 uses only the first clause, and a private copy of
its proof with the weaker premise compiles. With it,
`ZeroKernelStatement` follows from four unproved statements, and the
Corollary 11.7.5 and 11.7.6 rows record that `ChamberStatement` and
`QuotientStatement` follow from seven. Counting published reductions
only, the four Kottwitz rows now rest on seven unproved focused
statements instead of eight, because
`ZExtensionMorphismDominationStatement` is proved. Composites that no
published declaration states were checked with separate Lean checks at
Library commit `7229bb45`. Eleven declarations were inspected, four at
Library commit `320321b3` and seven at Library commit `51e9457f`. Each
inspected module is byte-identical to the commit that first published
it, except `SpecialTorusIntegralModelReduction`, whose Lean was first
published in commit `51e4d897` and whose Markdown commit `0c3f30c2`
revised. Every reported axiom set is `propext`, `Classical.choice`,
`Quot.sound`. Library commits `7f5b5f04`, `70eca2e4`, `320321b3` and
`88a89ad3` have the same Lean files, and so do Library commits
`544dba09`, `51e9457f`, `9243fdc2`, `7229bb45` and `5764b3a9`; the
update extends to Library head `5764b3a9`. The source and correction
fields of every row are unchanged.

A twenty-fifth update on 15 November 2026 updates five rows, adds none
and changes no status. It records the proofs and reductions first
published in Library commit `4abbe7aa` and the published reductions of
`UnramifiedTwistedChamberStatement`, first published in Library commits
`85c2fe71`, `af5d652c`, `e5365902`, `410c7947`, `b3a1bdaf` and
`4abbe7aa`. In the Proposition 9.3.4 row, `specialTorusIntegralModel` is
a named theorem for `SpecialTorusIntegralModelStatement`, which already
followed from published proofs. In the Lemma 11.5.2 row,
`zExtensionCommonDomination` proves
`ZExtensionCommonDominationStatement` and `zExtensionPointSurjectivity`
names a composite of the previous update, so
`ReductiveKottwitzExistenceStatement` follows from
`CentralTorusInertiaExactnessStatement` alone and
`CharacterKernelStatement` follows from two unproved statements.
`AlgebraicFundamentalGroup.centralTorusFundamentalExactness` proves the
exactness of fundamental groups for a central torus quotient, without
inertia coinvariants; `CentralTorusInertiaExactnessStatement` is still
unproved. In the Proposition 11.5.4 row, with the private weakening of
the previous update, `ZeroKernelStatement` follows from three unproved
statements. In the Corollary 11.7.5 row, published theorems reduce
`UnramifiedTwistedChamberStatement` to
`UnramifiedParahoricModelStatement`,
`UnramifiedUpstairsRadicalRootGenerationStatement` and
`UnramifiedTwistedReductiveQuotientDescentStatement`; with the
weakening, `ChamberStatement` follows from six unproved statements, or
from seven with that reduction. In the Corollary 11.7.6 row, counting
published reductions only, `QuotientStatement` follows from seven
unproved statements, and with the weakening from six. So the four
Kottwitz rows still rest on seven unproved focused statements, but
`CentralTorusInertiaExactnessStatement` has replaced
`ReductiveKottwitzExistenceStatement` among them. Composites that no
published declaration states were checked with separate Lean checks at
Library commit `c2a69151`. Ten declarations were inspected at Library
commit `49668e4d`; each inspected module is byte-identical to the commit
that first published it, and every reported axiom set is `propext`,
`Classical.choice`, `Quot.sound`. Library commits `4abbe7aa`,
`e5bc828a`, `c2a69151` and `49668e4d` have the same Lean files. Between
Library commits `7229bb45` and `49668e4d` the only module files that
changed are those of `GroupScheme.Rational.SimpleRootValueCharacter` and
`GroupScheme.Rational.VectorPointLieBaseChange`, which the ledger does
not cite. The update extends to Library head `49668e4d`. The source and
correction fields of every row are unchanged.

A twenty-sixth update on 15 November 2026 updates seven rows, adds none
and changes one status. It records the proofs first published in Library
commit `fab9caea`, the proof of the functoriality and
torus-compatibility statement of KP Lemma 11.5.1 first published in
Library commit `0b7bb3fd` and the statements
`InducedCentralTorusInertiaInjectivityStatement` and
`InducedTorusKottwitzRationalSurjectivityStatement`. In the Proposition
9.3.4 row, `specialTorusExistence` proves
`SpecialTorusExistenceStatement` for nonarchimedean local fields, and
the status of the row changes from statement to proved. In the Theorem
9.6.5 row, `unramifiedFixedRecoveredParabolicModels` and
`unramifiedFixedDepthZeroOpposite` are proved, so the descent input
follows from `UnramifiedFixedPairSpecialApartmentStatement` alone, and
three of the five inputs of the reduction are proved. In the Lemma 9.8.1
row, both existence statements follow from three unproved statements. In
the Lemma 11.5.2 row, `Kottwitz.centralTorusInertiaExactness` proves
`CentralTorusInertiaExactnessStatement`, so
`ReductiveKottwitzExistenceStatement` follows from published proofs, and
`Kottwitz.reductiveKottwitzFunctoriality` proves
`ReductiveKottwitzFunctorialityStatement`; the residual Galois
equivariance of Lemma 11.5.1 and the rational restriction, stated
together as `ReductiveKottwitzDescentStatement`, remain unproved. In the
Proposition 11.5.4 row, these two statements state the two propositions
written out in `zExtensionRationalKernelReduction`; with them, published
assemblies reduce `ZeroKernelStatement` to four unproved statements
without the private weakening, and with it to two. In the Corollary
11.7.5 row, with the weakening, `ChamberStatement` follows from four
unproved statements, or from five with the published reduction of
`UnramifiedTwistedChamberStatement`. In the Corollary 11.7.6 row,
counting published reductions only, `QuotientStatement` follows from
five unproved statements, and with the weakening from four. So the four
Kottwitz rows now rest on five unproved focused statements. Composites
that no published declaration states were checked with separate Lean
checks at Library commit `fab9caea`. Nine declarations were inspected,
five at Library commit `fab9caea`, three at Library commit `61b7fa40`
and one at Library commit `0b7bb3fd`; the module of the last was first
published in `0b7bb3fd`, each other inspected module was first published
in `fab9caea` and is byte-identical at `0b7bb3fd`, and every reported
axiom set is `propext`, `Classical.choice`, `Quot.sound`. Between
Library commits `49668e4d` and `fab9caea` the only previously published
module files that changed are those of
`BruhatTits.IntegralModels.UnramifiedComponentModelComparison`, Library
commits `fab9caea` and `61b7fa40` have the same Lean files, and between
Library commits `61b7fa40` and `0b7bb3fd` the only previously published
module files that changed are those of
`Algebra.NoetherianFiberwiseFlatness`; the ledger cites neither module.
The update extends to Library head `0b7bb3fd`. The source and correction
fields of every row are unchanged.

A twenty-seventh update on 15 November 2026 updates three rows, adds
none and changes no status. In the Theorem 8.3.13 row,
`torusQuotientRationalSurjectivity`,
`unramifiedTorusNeutralFiniteGeneration` and
`torusSurjectionIsogenySection`, first published in Library commit
`4abbe7aa`, prove three of the four torus statements of the published
reduction, so `UnramifiedParahoricModelStatement` follows from
`ConnectedGenerationStatement` (KP Lemma A.4.26) alone; the Theorem
8.3.2 row and the header say the same. That composite was checked with a
separate Lean check. The Section 13.2.6 row stays `conditional` and
records `FiniteFreeAlgebraUnits` (Library commit `7f5b5f04`),
`GeneralLinearIwahoriModel` (Library commit `aeb3911c`),
`FiniteFreeAlgebraUnitsQuotient` (Library commit `4abbe7aa`),
`FiniteFreeAlgebraUnipotentUnits` (Library commit `fab9caea`) and
`GeneralLinearIwahoriQuotient` (Library commit `0b7bb3fd`). They make
the standard Iwahori subgroup `I` of `GL_N(F)` the neutral integral
points of actual model data: the unit group scheme of the Iwahori order
is smooth with integral points `I`, its special fibre has unipotent
radical `1 + J` with the diagonal torus as reductive quotient, and the
radical preimage is `I^+`. For `N ≥ 2`, `I` is a proper subgroup of the
hyperspecial `GL_N(𝒪[F])`. No building point appears. Thirty-one
declarations were inspected at Library commit `0b7bb3fd`; each inspected
module is byte-identical to the commit that first published it, and
every reported axiom set is `propext`, `Classical.choice`, `Quot.sound`.
The source and correction fields of every row are unchanged.

A twenty-eighth update on 15 November 2026 updates two rows, adds none
and changes no status. The Theorem 8.4.19 row records the root-group
kernel results for KP Lemma C.5.3, which KP's proof of Proposition
8.4.15 applies to each factor of the kernel product.
`UnramifiedRootDepthKernelStatement` (Library commit `430cc03f`) states
the lemma over the integers of the maximal unramified extension on
supplied root models. `unramifiedNoHigherRootDepthKernel` (Library
commit `fab9caea`) proves it for relative roots without higher
multiples, and `unramifiedRootDepthKernel_of_multipliableCoordinates`
(Library commit `b3dcc8cc`) derives the whole lemma from
`MultipliableRootGroupCoordinatesExistenceStatement` (Library commit
`0b7bb3fd`), the unproved existence of valued unitary coordinates
`R_{E/K} U_{L/E} → U_b` for multipliable roots `b` (KP Construction
2.9.16 and Construction 6.1.17). The chart theorems
`smooth_connected_kernel_of_orderedCharts` and
`smooth_connected_kernel_of_orderedOpenCharts` (Library commit
`410c7947`) derive smoothness and connectedness of a model-map kernel
from the lemma, given supplied torus and root model families, ordered
multiplication charts and a lift or range condition. The row also
records the published results that supply these under further
hypotheses: `unramifiedOrderedIntegralOpenCellReduction` (Library commit
`e5365902`) constructs the families with open ordered charts
(`UnramifiedOrderedIntegralOpenCellStatement`, KP Proposition 8.3.14(3))
assuming the unproved `UnramifiedTorusConnectedBoundStatement` and the
proved connected-image statement, `closedPoint_mem_range_orderedChart`
(Library commit `410c7947`) proves the range condition from an open
target chart and an ordered fixer factorization, and
`unramifiedOrderedFixerFactorization` (Library commit `b3a1bdaf`) proves
that factorization in the open-cell order. No published declaration
assembles them into
`UnramifiedCompatibleModelKernelSmoothConnectedStatement`, so the kernel
statement of Theorem 8.4.19 still reduces to that statement alone. The
Section 13.2.6 row adds item (12) for `GeneralLinearIwahoriDepthZero`
(Library commit `b3dcc8cc`): on the Iwahori model and quotient data of
item (11), the general depth-zero quotient is `(𝓀ˣ)^N` and agrees with
the residue diagonal, the general index theorem gives `[I : I^+] = (q −
1)^N`, and `I` and `I^+` are compact open. The header, coverage and
README record both changes. Twenty-four declarations were inspected at
Library commit `b3dcc8cc`; each inspected module is byte-identical to
the commit that first published it, and every reported axiom set is
`propext`, `Classical.choice`, `Quot.sound`. The source and correction
fields of every row are unchanged.

A twenty-ninth update on 15 November 2026 updates two rows, adds none
and changes no status. In the Corollary 11.7.5 row,
`IntegralModels.unramifiedTwistedReductiveQuotientDescent` (first
published in Library commit `b3dcc8cc`) proves
`UnramifiedTwistedReductiveQuotientDescentStatement`, and by the
reduction recorded in the twenty-seventh update
`ConnectedGenerationStatement` replaces
`UnramifiedParahoricModelStatement` among the unproved inputs. With the
private weakening, `ChamberStatement` follows from four unproved
statements, with either `UnramifiedTwistedChamberStatement` or
`UnramifiedUpstairsRadicalRootGenerationStatement` among them. In the
Corollary 11.7.6 row, counting published reductions and proofs only,
`QuotientStatement` follows from five unproved statements, and with the
weakening from four. So the four Kottwitz rows still rest on five
unproved focused statements, now with `ConnectedGenerationStatement` in
place of `UnramifiedParahoricModelStatement`. At Library commit
`b3dcc8cc` no Lean file can import both the module of the new proof and
that of the published `unramifiedBuildingMetric`, whose statement is an
input of the published reduction of `UnramifiedTwistedChamberStatement`:
the published modules `Geometry.Building.IntegerBuildingFacetCentroids`,
which the first imports indirectly, and
`Geometry.Building.IntegerValuationBuildingMetricReduction`, which the
second imports indirectly, declare unnamed local instances with the same
automatic name. The composites that use both proofs were therefore
checked in two steps, and also in one file with a private copy of the
first module whose three local instances are named. Composites that no
published declaration states were checked with separate Lean checks at
Library commit `b3dcc8cc`. One declaration was inspected at Library
commit `b3dcc8cc`, which first published its module, and the reported
axiom set is `propext`, `Classical.choice`, `Quot.sound`. No module
cited in the two rows changed between Library commits `0b7bb3fd` and
`7cb8c3d3`. The update extends to Library head `7cb8c3d3`. The source
and correction fields of every row are unchanged.

A thirtieth update on 15 November 2026 updates one row, adds none and
changes no status. The Theorem 8.4.19 row records a `GL_N` regression
instance for the standard alcove `F'` and its hyperspecial vertex `F`,
built on the Iwahori model and quotient data of item (11) of the Section
13.2.6 row. `GeneralLinearIwahoriKernel` (Library commit `9ed11fc6`)
defines the model map `iwahoriMatrixHom` from the Iwahori model to the
unit group scheme of `M_N(𝒪)`, induced by the inclusion of orders, and
proves that its special-fibre kernel, the unit group `1 + J_-` of the
strictly lower part, is smooth, connected and unipotent.
`GeneralLinearIwahoriImage` (Library commit `2016a0d9`) identifies the
special-fibre image with the upper triangular Borel subgroup and proves
the Library predicates `HasSmoothConnectedUnipotentKernel`,
`HasParabolicSpecialFibreImage` and `HasParabolicReductionPreimage` for
the corresponding map of model data. `GeneralLinearIwahoriStandard`
(Library commit `497ef498`) identifies that target model with the
Library's standard model of `GL_N`, transports the three predicates and
Borelness to `iwahoriStandardModelHom` into `generalLinearModelData`,
proves that the image in the identity reductive quotient is parabolic,
indeed Borel, and proves `SatisfiesPositiveRadicalClause` for the
hyperspecial and Iwahori quotient data: the principal congruence
subgroup lies in `I^+`. These are the first assertion of part (1), parts
(2) and (3), the parabolicity of `℘_F(F')` and the Axiom 4.1.22(7)
inclusion of Corollary 8.4.12 at that pair. Nothing identifies the
models with KP's parahoric models. The row also records two further
proofs. `multipliableRootGroupCoordinatesExistence` (Library commit
`2016a0d9`) proves that every multipliable relative root group has
valued unitary coordinates, and `unramifiedRootDepthKernel` (Library
commit `497ef498`) derives from it `UnramifiedRootDepthKernelStatement`,
the Lean form of KP Lemma C.5.3, for every relative root through the
reduction recorded by the twenty-eighth update. This discharges the
root-group hypothesis of both chart theorems, and the lemma leaves the
open obligations. The statements of the row remain unproved. The header,
coverage and README record the changes. Twenty-two declarations were
inspected at Library commit `72480b70`; each inspected Lean module is
byte-identical to the commit that first published it, and every reported
axiom set is `propext`, `Classical.choice`, `Quot.sound`. The source and
correction fields of every row are unchanged.

A thirty-first update on 17 November 2026 updates four rows, adds none
and changes one status. In the Lemma 11.5.2 row,
`Kottwitz.characterKernel` (first published in Library commit
`e4a9b4d0`) proves `CharacterKernelStatement`, and
`Kottwitz.reductiveKottwitzExistence_assembled` and
`Kottwitz.reductiveKottwitzDescent_assembled` (first published in
Library commit `497ef498`) prove the existence and descent statements of
the rational Kottwitz map; the formal status of the row is now proved,
and the recorded Lean scope of all four rows notes the two proofs. In
the Proposition 11.5.4 row, the published
`Kottwitz.zeroKernel_of_unramifiedZeroDescent` derives
`ZeroKernelStatement` from `UnramifiedZeroDescentStatement` (KP
Proposition 9.3.24) alone. In the Corollary 11.7.5 and 11.7.6 rows,
published reductions and proofs derive `ChamberStatement` and
`QuotientStatement` from `UnramifiedZeroDescentStatement` and
`UnramifiedTwistedChamberStatement`. The latter follows from the
published proofs `unramifiedBuildingMetric` and
`unramifiedTwistedChamberThroughFixedPoint`, but at Library commit
`314cfd1a` no Lean file can import both of their modules, because of the
clash of automatically named local instances recorded in the
twenty-ninth update. With a private copy of
`Geometry.Building.IntegerBuildingFacetCentroids` whose three local
instances are named, both corollaries follow from
`UnramifiedZeroDescentStatement` alone. Composites that no published
declaration states were checked with separate Lean checks at Library
commit `276bcb8d`. Fifteen declarations were inspected at Library
commits `b44618a4` and `276bcb8d`, and the reported axiom set is
`propext`, `Classical.choice`, `Quot.sound`. Every module cited in the
four rows is byte-identical between the end point of the previous update
on its row, or its first commit, and Library commit `314cfd1a`. The
update extends to Library head `314cfd1a`. The source and correction
fields of every row are unchanged.

Note of 17 November 2026: the thirty-first update and its row evidence
retain their audit commit `314cfd1a0275806b9ff4281f3d3e51a05e9a6cb5`.
The later Library commit `9e39a73d21bd6ed6fac00b01cc5e01c0db5d105b`
already contains the published naming repair in
[IntegerBuildingFacetCentroids](../../Langlands/Geometry/Building/IntegerBuildingFacetCentroids.md):
its three local instances are named `centroidNormedAddCommGroup`,
`centroidNormedSpace` and `centroidFiniteDimensional`. This removes the
duplicate anonymous instance names described by the audit. The collision
and private-copy diagnostics below remain evidence about their stated
commits. This note records no new composite proof and changes no row's
`formal_status`.

A thirty-second update on 17 November 2026 updates six rows, adds none
and changes six statuses: Theorems 8.3.2, 8.3.13 and 8.4.19 and
Corollary 8.4.12 change from `statement` to `conditional`, and Sections
13.3.1 and 13.3.4 from source-only to `conditional`. In the Theorem
8.3.2 row, `unramifiedParahoricModel` (first published in Library commit
`c0c2e121`) proves `UnramifiedParahoricModelStatement` at every
universe. Its proof combines `connectedGeneration` (first published in
Library commit `e9c05be9`), which proves `ConnectedGenerationStatement`
(KP Lemma A.4.26) from the published Greenberg point model, with the
torus proofs `unramifiedTorusNeutralSurjectivity`,
`unramifiedTorusConnectedBound` and `unramifiedTorusIwahoriModel`; the
Theorem 8.3.13 row records all five proofs. The descended
`IntegralModelAxiomsStatement`, also recorded in both rows, remains
unproved. In the Corollary 8.4.12 row, `unramifiedFacetPositiveRadical`
(first published in Library commit `a98af0ff`) proves the Axiom
4.1.22(7) inclusion, and `unramifiedUpstairsRadicalRootGeneration`
(first published in Library commit `e9c05be9`) and
`unramifiedRadicalRootGeneration` (first published in Library commit
`a2dba61c`) prove that, for nonempty subsets of one facet, the radical
preimage is generated by the positive root groups and one subgroup that
is not identified with KP's torus factor; the row records both
statements. In the Theorem 8.4.19 row, `unramifiedModelKernel` (first
published in Library commit `9e39a73d`) proves
`UnramifiedModelKernelStatement`, `unramifiedFacetCommonTorus` (first
published in Library commit `aeb3911c`) and
`unramifiedFacetParabolicOrder` (first published in Library commit
`a2dba61c`) prove the common-torus and parabolic-order statements, and
`unramifiedOrderedIntegralOpenCell` (first published in Library commit
`d210ab55`) proves the integral open-cell statement.
`UnramifiedFacetParabolicImageStatement` follows from published proofs;
no published declaration states this composite, which a separate Lean
check confirmed at Library commit `fcb85a7e`. In the Section 13.3.1 row,
the module `LieLattice` (first published in Library commit `c9fdbede`)
defines the Lie lattice of an integral model, the image of its Lie
algebra in the Lie algebra of the generic fibre, and proves that it is a
lattice for smooth models; in the Section 13.3.4 row, the module
`LieLatticeAdjoint` (first published in Library commit `9e39a73d`)
proves that the integral points of a model preserve its Lie lattice
under the adjoint action. For these two rows, `conditional` means proved
for every supplied integral model, smooth in the case of Section 13.3.1;
the congruence and parahoric models of Section 8.5 and Chapter 9 are not
constructed in Lean. The header, coverage, Bundle D and Bundle E texts
and the README record the changes. Twenty-four declarations were
inspected at Library commits `97101ec2`, `8f4a33d7` and `fcb85a7e`,
whose Lean files are identical; each inspected Lean module is
byte-identical to the commit that first published it, and every reported
axiom set is `propext`, `Classical.choice`, `Quot.sound`. The source and
correction fields of every row are unchanged.

A thirty-third update on 17 November 2026 updates five rows, adds none
and changes one status: Lemma 9.8.1 changes from `statement` to
`conditional`. In the Lemma 9.8.1 row,
`centralizerFiltrationDoubleRootExistence` (first published in Library
commit `9e39a73d`) proves
`CentralizerFiltrationDoubleRootExistenceStatement`. Its proof assembles
published proofs of the Moy–Prasad group properties over the maximal
unramified extension (`MaximalUnramified.localMoyPrasadGroupProperties`)
and of the comparison of the building data with that extension, whose
inputs `quasiSplitValuedRankOneCoordinates`,
`kpLocalDoubleRootCommutator`, `unramifiedDoubledRootDepthModel`,
`unramifiedComparisonRootField` and `unramifiedComparisonExistence` the
row also records. The intermediate statement
`UnramifiedRationalMoyPrasadStatement` that this proof composes inline
is now proved by `unramifiedRationalMoyPrasad` (first published in
Library commit `f24f9744`), also recorded in the row. The theorem
`centralizerFiltrationExistence` (first published in Library commit
`f24f9744`) derives `CentralizerFiltrationExistenceStatement` from it by
dropping a conjunct. Both statements quantify over supplied building
data satisfying the apartment axioms, so the row is `conditional`, not
`proved`. In the Theorem 9.6.5 row, `unramifiedValuationDescent` (first
published in Library commit `d210ab55`) proves
`UnramifiedValuationDescentStatement` through the published proofs
`unramifiedFixedPairSpecialApartment`,
`unramifiedFixedPointTransporter`, `unramifiedTorusUnitFixedApartment`,
`unramifiedFixedLeviTransport` and `unramifiedFixedOpposite`, which the
row records; `ValuationApartmentAxiomsExistenceStatement` now follows
from `ValuationBuildingApartmentAxiomsStatement` alone, and the status
stays `statement`. In the Proposition 13.2.5 row, the filtration
provided by `centralizerFiltrationDoubleRootExistence` meets the
premises on the filtration of all six published Moy–Prasad proofs for
every supplied building datum satisfying the apartment axioms; that
datum is still supplied, so the row stays `conditional`. In the
Corollary 11.7.5 row, `unramifiedTwistedChamber` (first published in
Library commit `9e39a73d`) proves `UnramifiedTwistedChamberStatement`;
the module of this proof and a new version of
`IntegerBuildingFacetCentroids` carry the naming repair recorded in the
note of 17 November 2026 above. So `ChamberStatement` (Corollary 11.7.5)
and `QuotientStatement` (Corollary 11.7.6) follow from
`UnramifiedZeroDescentStatement` (KP Proposition 9.3.24) alone, without
a private copy of any module. Composites that no published declaration
states were checked with separate Lean checks at Library commits
`8f4a33d7` and `fcb85a7e`. Sixteen declarations were inspected at
Library commits `8f4a33d7`, `fcb85a7e` and `b369a8f2`, and every
reported axiom set is `propext`, `Classical.choice`, `Quot.sound`. Every
module cited in the five rows is byte-identical between the end point of
the previous update on its row, or its first commit, and Library commit
`b369a8f2`, except `IntegerBuildingFacetCentroids`, which the naming
repair changed in commit `9e39a73d`. The header, coverage and README
texts record the changes. The source and correction fields of every row
are unchanged.

A thirty-fourth update on 18 November 2026 updates one row, adds none
and changes one status: Theorem 13.5.1 changes from source-only to
`statement`. It records `MoyPrasadIsomorphismStatement` (first published
in Library commit `b86269dd`), a statement of part (1) on supplied data
without the compatibility with unramified extensions, and the torus
clause `HasWeaklyInducedMaximallySplitTorus` of its first alternative
(first published in Library commit `fd643ece`). The statement assumes
the component isomorphisms for the centralizer and each root block and
the published double-root commutator premise; the row explains why. Five
declarations were inspected at Library commit `ba9d1e9a`, and every
reported axiom set is `propext`, `Classical.choice`, `Quot.sound`. Both
cited modules are byte-identical between their first commits and Library
commit `ba9d1e9a`. The header, Bundle E, coverage and README texts
record the changes. The source and correction fields of every row are
unchanged.

A thirty-fifth update on 18 November 2026 updates three rows, adds none
and changes two statuses: Section 13.3.2 changes from source-only to
`conditional` and Section 13.3.3 from source-only to `definition`;
Section 13.3.1 stays `conditional` with a second recorded scope. In the
Section 13.3.2 row, the module `ReductiveQuotientLie` and its companion
`LieLatticeReduction` (first published in Library commit `fd643ece`)
prove, for supplied integral-model data and reductive-quotient data,
that `g_0/g_0+ ≃ Lie(Gred)` (`reductiveQuotientLieEquiv`) for the
intrinsic lattice `g_0+` of the elements of `g_0` whose reduction lies
in `Lie(R_u)`, and identify `g_0+` with the Lie lattice of a supplied
smooth model under hypotheses standing for Section 13.2.6, Proposition
8.5.18 and `m g_{x,0} ⊂ g_{x,0+}` (`positiveLieLattice_eq`). When
`LieLatticeReduction` entered the Library, its auxiliary isomorphism
`specialFibreBaseChangeIso` was renamed `specialFibreAlgebraBaseIso`; no
recorded declaration is affected. In the Section 13.3.3 row, the module
`KPLieFiltration` (first published in Library commit `fd643ece`) defines
`g_{x,r}` for `r >= 0` as the span of supplied lattices `z_r` and
`u_psi` with `psi(x) >= r` (`lieFiltration`), KP's intrinsic description
taken as a definition; the row is `definition` because the supplied
lattices are not identified with those of the models. In the Section
13.3.1 row, that module and `KPLieFiltrationDual` (first published in
Library commit `b86269dd`) give the filtration, its extension to real
depths under the periodicity hypothesis `IsPeriodic` and the dual
lattices `g^*_{x,r}` (`dualLieFiltration`). The header, coverage and
Bundle E texts, the Lie-lattice prose of Bundle E and the README record
the changes. Twenty-seven declarations were inspected at Library commits
`fd643ece` (sixteen declarations) and `ba9d1e9a` (eleven declarations);
each inspected Lean module is byte-identical to the commit that first
published it, and every reported axiom set is `propext`,
`Classical.choice`, `Quot.sound`. The source and correction fields of
every row are unchanged. The header's count of the rows without a formal
status, which read thirteen after the previous update although twelve
rows were source-only, is corrected to the current ten.

A thirty-sixth update on 19 November 2026 updates two rows, adds none
and changes one status: Proposition 13.7.4 changes from source-only to
`statement`. It records `DegenerateCosetOfDeeperIntersectionStatement`
(first published in Library commit `5f5d3a91`), a statement of part (1)
for points of one apartment on the supplied real-depth Lie lattices of
the Section 13.3.1 row, and the Definition 13.6.5 predicates
`IsCocharacterNilpotent` and `IsDegenerateLieCoset` with
`cocharacterPositiveLie` (first published in Library commit `b86269dd`).
The Proposition 13.6.7 row stays source-only; a new dependency entry
names these definitions and the inputs its two clauses lack. Four
declarations were inspected at Library commit `5f5d3a91`, and every
reported axiom set is `propext`, `Classical.choice`, `Quot.sound`. The
module `KPNilpotentCoset` is byte-identical between its first commit and
Library commit `5f5d3a91`, which first published
`KPDegenerateCosetStatement`. The header, Bundle E, coverage and README
texts record the changes, and the header's count of rows without a
formal status changes from ten to nine. The source and correction fields
of every row are unchanged.

A thirty-seventh update on 21 November 2026 updates four rows (Sections
13.3.1, 13.3.3 and 13.3.4 and the dependency note in Proposition 13.6.7)
and adds two, Definitions 13.4.1 and 13.4.2. No existing row changes
formal status. The publications are `KPLieGradedAction` (first published
`5f5d3a91`); `KPLieGradedPairing` (first published `6e9e589b`);
`KPLieFiltrationLeftContinuity` (first published `6e9e589b`);
`KPOptimalPoints` (first published `03296177`); `KPLieGradedResidue`
(first published `2d12bd93`); `KPLieJumpDepths` (first published
`2d12bd93`); `KPSplitTorusLieFiltration` (first published `2d12bd93`).
The §13.3 rows retain precisely the periodicity, lattice,
finite-generation, left-continuity and subgroup-action premises of the
individual results. The split-torus calculation is a regression for the
standard torus, not a comparison with constructed positive-depth models.
In §13.4, KPOptimalPoints uses a regular chamber and the literal
positive-indecomposable generator rule, not the wall-root definition. It
gives the least period and finite strip in the stated scope and the
empty-root obstruction, not existence of optimizers or Lemma 13.4.4. The
47 newly indexed declarations have standard axiom reports (`propext`,
`Classical.choice`, `Quot.sound`) from Lean service checks; their module
sources match the published files checked at Library commit `b47a2385`.
The source and correction fields of the existing rows are unchanged.

The normative sources are Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, and the authors'
corrections of 1 November 2024, registered as
`kaletha-prasad-2024-corrections`. Both readable originals are in
`central-library/Kaletha-Prasad--Bruhat-Tits theory, a new approach
(book)--2023/`. Their fingerprints and precise locators are included in
every relevant row. The operator roadmap is design guidance, not theorem
evidence.

## Reading and scope

The original passages behind these rows were read at PDF pages 34–40, 161–163,
188, 199–205 and 213–215, together with corrections PDF pages 1–3, 25 and 27–29.
Book PDF pages 35–36 and 202 were visually checked. In particular, the overbar
in Theorem 4.2.10 matters: the closed union is a union of **facet closures**.
The OCR text alone drops that overbar. The theorem does not require the building
to be locally finite; that is only the first case in its proof.

The Chapter 4 targets use specified building axioms. Theorem 9.2.7 supplies
these axioms for the descended assignment in the nonarchimedean local-field
scope of the Library's completion certificate. The following paragraphs
record the original scope and source checks of the ledger's extensions.

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
Theorem 1.1.15 and the two later metric results below leaves the release order
and construction gates open.

## Structured ledger

The JSON block is the structured ledger. Each row has the same fields.
`lean_declarations` and `modules` name verified declarations and their
modules. `publication_commits` records the Library commits where the
listed results appeared. `axiom_reports` records declaration inspections.
The formal status of a row refers to its stated Lean scope. Earlier rows
record results at the commits they name. The historical proof inventory at
the end records the status at an earlier Library snapshot.

```json
{
  "schema_version": 1,
  "coverage": "Named targets from Bundles A–F cover metric geometry, availability and unramified descent, decompositions and components, parahoric models and depth-zero reduction, congruence–Lie maps and filtrations, and tame descent and embeddings. The rows for Theorem 9.2.7, Section 13.2.6 and Proposition 13.5.2 record the completion certificate and its facet consequences over nonarchimedean local fields. Rows for Proposition A.5.19 and Lemma A.5.13(4) record the integral-model construction and proposition targets at the same Library pin. The other rows record the scopes and Library commits specified in their evidence fields.",
  "status_convention": "A null formal_status means no verified Lean declaration of this target is recorded. Non-null values are definition, statement, proved or conditional.",
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
      "publication_commits": [
        "11dedf3c6982c420e1eee5dc7a82ee37ad2dcc0e"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Metric.KP.barycenter",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection."
        },
        {
          "declaration": "Langlands.Geometry.Metric.KP.boundedSetStabilizerFixedPoint",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection."
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
        "change": "Convexity includes nonemptiness. The printed coefficient-2 minimizing-sequence estimate is false, and the added multiplicative continuity argument misses zero minimum distance. The proof in the Library uses the independent squared midpoint deficit and division-free continuity repair described below; the theorem statement is unchanged."
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
      "publication_commits": [
        "c4a16df784376405a45b60df82583e8c26d8a4e3"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Metric.KP.IsRetractionGluedDistance.isNonpositivelyCurved",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-08 at Library commit c4a16df7."
        },
        {
          "declaration": "Langlands.Geometry.Building.metricRealization",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-08 at Library commit c4a16df7."
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
        "Recorded Lean scope (second assertion): the published FacetClosureUnionClosedStatement quantifies over every nonarchimedean local field F in universe u, group scheme G over Spec F and supplied B : ValuationBuildingData G, with the same metric, isometric-action, common-apartment, SatisfiesApartmentAxioms and isometric-apartment-map premises as the completeness theorem. For every X : Set (Set B.ReducedBuilding) with B.IsFacet Y for all Y ∈ X it concludes IsClosed (⋃ Y ∈ X, closure Y), with the topological closure of each facet. Neither the data nor the premises are asserted to exist. The theorem facetClosureUnionClosed (module FacetClosureUnionClosedProof) proves this statement; it first appeared in Library commit e449cde988d4e97ab280b8d4d11262887ccc26e0. Both assertions are therefore proved on supplied data, and the row stays conditional until the data and premises are constructed."
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
        "Proof of FacetClosureUnionClosedStatement: facetClosureUnionClosed. It follows the first part of Lemma 4.2.11: local finiteness at an apartment coordinate of x gives a ball meeting only facets whose closures contain x, after moving each facet into a common apartment chart with x; a combinatorial closed facet lies in the topological closure of its facet. Both assertions are conditional on the data and premises, whose construction is RootValuationBuildingConstructionStatement."
      ],
      "consumer_or_regression": "Fixed-point theorem on the constructed building; finite-residue and non-locally-finite cases must not be conflated.",
      "formal_status": "conditional",
      "publication_commits": [
        "c4a16df784376405a45b60df82583e8c26d8a4e3",
        "230ec08a058832bd6941fa887c30897e4826429b",
        "e449cde988d4e97ab280b8d4d11262887ccc26e0"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.ValuationBuildingData.completeSpace_of_isometry_apartmentMap_of_satisfiesApartmentAxioms",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-08 at Library commit c4a16df7."
        },
        {
          "declaration": "Langlands.Geometry.Building.FacetClosureUnionClosedStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-10 at Library commit 230ec08a; statement_returns_prop true. This inspection covers this statement only; the declarations inspected on 2026-11-08 were already in the Library."
        },
        {
          "declaration": "Langlands.Geometry.Building.facetClosureUnionClosed",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-10 at Library commit e449cde9; a theorem."
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
        "Recorded Lean scope: BoundedSubgroupFixedPointStatement quantifies over every nonarchimedean local field F of either characteristic in universe u, every group scheme G over Spec F with hG : IsConnectedReductive G, and supplied P : ParahoricBuildingData G with a polysimplicial realization R and an apartment splitting T of P.toValuationBuildingData. Its premises are the seven Library predicates of MetricRealizationStatement expressing the five axioms: SatisfiesBuildingAxiom R (4.1.1), HasBoundedOpenStabilizers (4.1.2), SatisfiesAffineApartmentAxiom T (4.1.4), HasRootReflections, SatisfiesApartmentAxioms and HasCompatibleApartmentFacets (4.1.6) and HasTitsSystem (4.1.9). For every subgroup H of rationalPoints G with IsAlgebraicallyBounded F G.X H (Definition 2.2.1) it concludes (1) some x : ReducedBuilding has h • x = x for all h ∈ H, and (2) for every MetricRealization M, with M.metric installed, every closed Y with IsGeodesicallyConvex Y (which includes nonemptiness) and h • y ∈ Y for h ∈ H, y ∈ Y contains such a fixed x. The source's Henselian discretely valued fields with perfect residue field are specialized to nonarchimedean local fields; the specific metric of Proposition 4.2.1 is replaced by an arbitrary complete NPC realization with isometric action and continuous orbit maps, which includes the source metric through metricRealization. Existence of the data, of the axiom witnesses or of a realization is not asserted. The theorem boundedSubgroupFixedPoint (module BoundedSubgroupFixedPointProof) proves this statement; it first appeared in Library commit e449cde988d4e97ab280b8d4d11262887ccc26e0."
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
        "Proof: boundedSubgroupFixedPoint. Its route differs from the source: compactness of the closure of an algebraically bounded set and continuity of orbit maps give bounded orbits, then Theorem 1.1.15(2) and the equivariant nearest-point projection of Proposition 1.1.20 give the fixed points; Proposition 4.2.13 is not used. The statement is conditional on the data and witnesses, whose construction is RootValuationBuildingConstructionStatement."
      ],
      "consumer_or_regression": "Actual parahoric/fixer and compact-subgroup consumers, retaining the reduced/enlarged and G(k)^0/G(k)^1 distinctions.",
      "formal_status": "conditional",
      "publication_commits": [
        "3f0bcbd4638c9c42befdc9f7e1578d62fde2c959",
        "e449cde988d4e97ab280b8d4d11262887ccc26e0"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.BoundedSubgroupFixedPointStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-09 at Library commit 3f0bcbd4; statement_returns_prop true."
        },
        {
          "declaration": "Langlands.Geometry.Building.boundedSubgroupFixedPoint",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-10 at Library commit e449cde9; a theorem."
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
        "Proof: apartmentConjugacyFixingIntersection (module ApartmentConjugacyFixingIntersectionProof), present in Library commit ed924aef420de137b4cbaa3b063a3618afcd73fd. The proof follows the source's convex-intersection and facet-fixer strategy. The NPC metric built by MetricRealizationProof makes every translated apartment chart an isometry, which gives segment-convexity of the intersection without closedness or completeness. A point maximizing the dimension of the common kernel of its vanishing roots replaces the source's facet of maximal dimension. A two-facet Tits transport and the normalizer action on the apartment then show that the transporter fixes the intersection pointwise. An empty intersection is handled by the transitivity of G(F)^0 on apartments. The construction of the data and witnesses is RootValuationBuildingConstructionStatement."
      ],
      "consumer_or_regression": "Corollaries 4.2.25 and 4.2.26, and the corrected source proof of Theorem 5.2.1. The published formal proof availableCartan uses the sharp fixer and a two-facet Tits transport instead.",
      "formal_status": "conditional",
      "publication_commits": [
        "d39b5aee822fe2ad1aadf07861ebd9a4c2df62a8",
        "ed924aef420de137b4cbaa3b063a3618afcd73fd"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.ApartmentConjugacyFixingIntersectionStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-10 at Library commit e7487341; statement_returns_prop true."
        },
        {
          "declaration": "Langlands.Geometry.Building.apartmentConjugacyFixingIntersection",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit ed924aef; a theorem."
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
      "consumer_or_regression": "Actual building quotient presentation; the conditional algebraic quotient supplies only a reusable prerequisite.",
      "formal_status": "conditional",
      "publication_commits": [
        "c4a16df784376405a45b60df82583e8c26d8a4e3"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.ApartmentQuotient.liftEquiv_smul",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-08 at Library commit c4a16df7."
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
      "publication_commits": [
        "c4a16df784376405a45b60df82583e8c26d8a4e3"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.ValuationBuildingData.quotientComparisonEquiv_isEquivariantBuildingIso",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-08 at Library commit c4a16df7."
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
      "publication_commits": [
        "c4a16df784376405a45b60df82583e8c26d8a4e3"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.KPBuildingAssignment.IsAvailableFor",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-08 at Library commit c4a16df7."
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
        "Recorded Lean scope: AffineIwahoriTitsStatement states only the G(F)^0 branch of 7.5.3(1),(2), for every nonarchimedean local field F, affine F-group scheme G and supplied P : ParahoricBuildingData G with P.apartment.SatisfiesApartmentAxioms P.centralizer and every chamber C of A(S): normality of P.normalizerZero and P.zeroSubgroup, and P.AffineIwahoriTits C (a multiplicative equivalence of the affine part of N(F) ∩ G(F)^0 with the affine Weyl group W(Ψ) realizing the actual apartment action, the published IsTitsSystem for G(F)^0, the generated parahoric of C, N(F) ∩ G(F)^0 and the chamber-simple reflections, and the corrected saturation as an intersection of conjugates). The G(F)^natural branch and the conjugacy of choices are not stated. affineIwahoriTits_of_inputs derives P.AffineIwahoriTits C from normality of P.normalizerZero, an action comparison and the eight fields of AffineIwahoriTitsInputs C, which are explicit hypotheses of that lemma. At c4a16df7 three fields are proved under the apartment axioms: closure_chamberSimpleReflections (closure_chamberSimpleReflections_affineRoots, KP Proposition 1.3.22(1)), parahoric_le_zeroSubgroup (from ApartmentRootCover) and zeroSubgroup_le_sup (chamberParahoricGeneration : ChamberParahoricGenerationStatement). affineIwahoriTitsStatement_of_inputStatements derives AffineIwahoriTitsStatement from IwahoriWeylExactSequenceStatement (KP 7.8.1(1), which supplies both normalities and the comparison), AffineRankOneTwoCellStatement (KP Lemma 7.1.5(3)) and the five statements of AffineIwahoriTitsInputStatements. Of these seven, six have published proofs, all present in Library commit ed924aef420de137b4cbaa3b063a3618afcd73fd: chamberParahoricGeneration, chamberParahoricNormalizer, rootGroupParahoricFiltration, chamberConjugateIntersection, chamberSimpleFactorization and affineRankOneTwoCell. Only IwahoriWeylExactSequenceStatement (KP 7.8.1(1)) is open. The published reduction iwahoriWeylNormalizerAffineWeylReduction derives it, together with IwahoriWeylChamberSplittingStatement (KP 7.8.2), from SimplyConnectedNormalizerAffineWeylStatement (the range part of 7.5.3(2)). The published reduction simplyConnectedNormalizerAffineWeylReduction derives that statement from SimplyConnectedFacetFixingStatement and Langlands.GroupScheme.DerivedCentralSplitTorusProductStatement, which is proved by Langlands.GroupScheme.derivedCentralSplitTorusProduct. So AffineIwahoriTitsStatement now waits only on SimplyConnectedFacetFixingStatement. The published module SimplyConnectedFacetFixingReduction reduces that statement further to SimplyConnectedReflectionTranslationStatement, to SimplyConnectedRankOneCentralizerGenerationStatement or to SimplyConnectedKneserTitsCentralizerStatement, none of them proved."
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
        "Open statements: AffineIwahoriTitsStatement, SimplyConnectedNormalizerAffineWeylStatement (range part of 7.5.3(2)) and SimplyConnectedFacetFixingStatement. On 13 November 2026 the first two follow from the third through the published reductions listed in the last hypotheses entry; the third is the only open input of AffineIwahoriTitsStatement. Note (twenty-second update, 14 November 2026): the theorem MaximalUnramified.simplyConnectedNormalizerAffineWeyl, recorded in the Corollary 11.7.5 row, proves MaximalUnramified.SimplyConnectedNormalizerAffineWeylStatement, the analogous statement for simply connected groups over the maximal unramified extension. It does not prove SimplyConnectedNormalizerAffineWeylStatement of this row; that statement and SimplyConnectedFacetFixingStatement are unproved at Library commit 4f4af6ba."
      ],
      "consumer_or_regression": "Restricted building construction 7.6.1 and the affine part of later double-coset decompositions. A nontrivial length-zero/component example must retain the full Iwahori–Weyl data separately.",
      "formal_status": "statement",
      "publication_commits": [
        "c4a16df784376405a45b60df82583e8c26d8a4e3",
        "ed924aef420de137b4cbaa3b063a3618afcd73fd"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.AffineIwahoriTitsStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-08 at Library commit c4a16df7; statement_returns_prop true."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.affineIwahoriTits_of_inputs",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-08 at Library commit c4a16df7."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.affineIwahoriTitsInputs_of_statements",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-09 at Library commit c4a16df7."
        },
        {
          "declaration": "Langlands.Geometry.Building.affineIwahoriTitsStatement_of_inputStatements",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-09 at Library commit c4a16df7."
        },
        {
          "declaration": "Langlands.Geometry.Building.chamberParahoricGeneration",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-09 at Library commit c4a16df7."
        },
        {
          "declaration": "Langlands.Geometry.Building.chamberParahoricNormalizer",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit ed924aef; a theorem proving ChamberParahoricNormalizerStatement."
        },
        {
          "declaration": "Langlands.Geometry.Building.rootGroupParahoricFiltration",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit ed924aef; a theorem proving RootGroupParahoricFiltrationStatement."
        },
        {
          "declaration": "Langlands.Geometry.Building.chamberConjugateIntersection",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit ed924aef; a theorem proving ChamberConjugateIntersectionStatement."
        },
        {
          "declaration": "Langlands.Geometry.Building.chamberSimpleFactorization",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit ed924aef; a theorem proving ChamberSimpleFactorizationStatement."
        },
        {
          "declaration": "Langlands.Geometry.Building.affineRankOneTwoCell",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit ed924aef; a theorem proving AffineRankOneTwoCellStatement."
        },
        {
          "declaration": "Langlands.Geometry.Building.iwahoriWeylNormalizerAffineWeylReduction",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit ed924aef; a theorem proving IwahoriWeylNormalizerAffineWeylReductionStatement (SimplyConnectedNormalizerAffineWeylStatement implies IwahoriWeylExactSequenceStatement and IwahoriWeylChamberSplittingStatement)."
        },
        {
          "declaration": "Langlands.Geometry.Building.simplyConnectedNormalizerAffineWeylReduction",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit ed924aef; a theorem proving SimplyConnectedNormalizerAffineWeylReductionStatement (SimplyConnectedFacetFixingStatement and DerivedCentralSplitTorusProductStatement imply SimplyConnectedNormalizerAffineWeylStatement)."
        },
        {
          "declaration": "Langlands.GroupScheme.derivedCentralSplitTorusProduct",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit ed924aef; a theorem proving Langlands.GroupScheme.DerivedCentralSplitTorusProductStatement."
        },
        {
          "declaration": "Langlands.Geometry.Building.simplyConnectedFacetFixingReduction",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit ed924aef; a theorem proving SimplyConnectedFacetFixingReductionStatement (SimplyConnectedReflectionTranslationStatement implies SimplyConnectedFacetFixingStatement)."
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
        "Lean scope. For each universe u the assignment covers all nonarchimedean local fields F of either characteristic in u and all connected reductive group schemes over Spec F. The same KPBuildingAssignment is valid for corrected Definition 4.1.26 and satisfies KPBuildingDatum.SatisfiesUnramifiedDescent on each assigned datum. UR 3 identifies the set of lower affine roots with the set of nonconstant restrictions of upper affine roots. The other descent clauses compare the reduced building, apartments and models."
      ],
      "conclusion": "B with these apartments and polysimplices is a building whose apartments correspond bijectively to maximal k-split tori. Chambers and facets are fixed parts of Gamma-chambers and Gamma-facets, and G(k) acts by polysimplicial isometries. For the program's certificate, the constructed geometry and descended models must satisfy every axiom of corrected Definition 4.1.26 and Axiom 4.1.27, using the source assembly and the explicitly derived completion routes below.",
      "lean_declarations": [
        "Langlands.Geometry.Building.BruhatTitsAvailabilityStatement",
        "Langlands.Geometry.Building.BruhatTitsAvailabilityReductionStatement",
        "Langlands.Geometry.Building.GroupAxiomsExistenceReductionStatement",
        "Langlands.Geometry.Building.bruhatTitsAvailabilityReduction",
        "Langlands.Geometry.Building.groupAxiomsExistenceReduction",
        "Langlands.Geometry.Building.bruhatTitsAvailability",
        "Langlands.Geometry.Building.KPBuildingDatum.SatisfiesUnramifiedDescent",
        "Langlands.Geometry.Building.unramifiedDescentOfGroupAxioms",
        "Langlands.Geometry.Building.BruhatTitsCompletionCertificateStatement",
        "Langlands.Geometry.Building.bruhatTitsCompletionCertificateReduction",
        "Langlands.Geometry.Building.bruhatTitsCompletionCertificate"
      ],
      "modules": [
        "Langlands.Geometry.Building.BruhatTitsAvailabilityStatement",
        "Langlands.Geometry.Building.FullValidity.Assignment",
        "Langlands.Geometry.Building.BruhatTitsAvailabilityReductionStatement",
        "Langlands.Geometry.Building.GroupAxiomsExistenceReductionStatement",
        "Langlands.Geometry.Building.BruhatTitsAvailabilityReductionProof",
        "Langlands.Geometry.Building.GroupAxiomsExistenceReduction",
        "Langlands.Geometry.Building.BruhatTitsAvailabilityProof",
        "Langlands.Geometry.Building.FullValidity.UnramifiedDescent",
        "Langlands.Geometry.Building.UnramifiedDescentOfGroupAxiomsProof",
        "Langlands.Geometry.Building.BruhatTitsCompletionCertificateStatement",
        "Langlands.Geometry.Building.BruhatTitsCompletionCertificateReductionStatement",
        "Langlands.Geometry.Building.BruhatTitsCompletionCertificateProof"
      ],
      "dependencies": [
        "Quasi-split Chapter 6–8 building and actual integral models; Corollary 2.3.8; descent Fact 2.10.16; special k-tori Proposition 9.3.4",
        "Complete NPC fixed-point theory (Theorem 1.1.15), corrected 9.2.1; geometry and restricted-building arguments of Sections 9.3–9.4, including corrected 9.3.25 and AS5 Proposition 9.4.35",
        "Axiom-by-axiom source map in Section 9.5, expanded below; for 4.1.16 use Sections 9.6 and 7.3–7.4 with corrected every-point Corollary 4.4.5",
        "For 4.1.17, Proposition 7.9.5 and transport of the descended construction under all covering field/group isomorphisms; a Gamma action alone is not the full axiom",
        "G(k)^0=G(K)^0 intersect G(k) (9.3.24) and the G(k)^1 intersection identity; model base change and root compatibility for Axiom 4.1.27",
        "The theorem bruhatTitsAvailability, first in Library commit af4ce7d54ba8e700648f7583ea70946256e67a46, supplies a valid KPBuildingAssignment. The availability and group-axiom reductions separate the single-group axioms from extension and isomorphism comparisons.",
        "The theorem unramifiedDescentOfGroupAxioms, first in Library commit 99e4a586253ae0b5bad1472a73c984acb1a6b033, replaces each single-group datum with a group-valid datum satisfying unramified descent. An equivariant equivalence of reduced buildings over the identity on rational points compares the original datum with its replacement.",
        "The theorem bruhatTitsCompletionCertificateReduction assembles these replacements. The theorem KPBuildingAssignment.ofData_isValid transports the Axiom 4.1.1 extension comparisons and the Axiom 4.1.17 covering-isomorphism comparisons along the building equivalences. The theorem bruhatTitsCompletionCertificate applies that reduction to the two existence theorems.",
        "The set-equality formulation of UR 3 and the obstruction to the printed quantifier over every upper derivative are described in Langlands/Geometry/Building/FullValidity/UnramifiedDescent.md."
      ],
      "consumer_or_regression": "The descended assignment supplies the premises of depthZeroConsumer and availableMaximalProP for the same data at every facet. The regression statements compare the assigned buildings with the reduced and enlarged factors for tori, the GL₂ tree, the parahorics and component data of GLₙ, and the building of SU₃ with a multipliable root.",
      "formal_status": "proved",
      "publication_commits": [
        "230ec08a058832bd6941fa887c30897e4826429b",
        "cfedefb680f317b0ea5d351023e1c9dd886b2547",
        "af4ce7d54ba8e700648f7583ea70946256e67a46",
        "99e4a586253ae0b5bad1472a73c984acb1a6b033",
        "db940683e1d682d84831e8365720f1c79b5c9b0c"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.BruhatTitsAvailabilityStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-10 at Library commit 230ec08a; statement_returns_prop true."
        },
        {
          "declaration": "Langlands.Geometry.Building.BruhatTitsAvailabilityReductionStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 of the module as published in Library commit cfedefb6; kind definition; statement_returns_prop true."
        },
        {
          "declaration": "Langlands.Geometry.Building.GroupAxiomsExistenceReductionStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 of the module as published in Library commit cfedefb6; kind definition; statement_returns_prop true."
        },
        {
          "declaration": "Langlands.Geometry.Building.bruhatTitsAvailabilityReduction",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 of the module as first published in Library commit 730bd1f2; kind theorem, proving BruhatTitsAvailabilityReductionStatement."
        },
        {
          "declaration": "Langlands.Geometry.Building.groupAxiomsExistenceReduction",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 of the module as first published in Library commit 730bd1f2; kind theorem, proving GroupAxiomsExistenceReductionStatement."
        },
        {
          "declaration": "Langlands.Geometry.Building.bruhatTitsCompletionCertificate",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Declaration inspection on 2026-11-27 at Library commit 2f86a99eb5616254ac5b9c399603c9bbbea15f7a. The theorem has universe parameter u and type BruhatTitsCompletionCertificateStatement.{u}."
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
        "Proof: the theorem unramifiedGaloisFixedApartment (module UnramifiedGaloisFixedApartmentProof, first in Library commit b128d289028bf75629e9e364ecf151c484b27a85) proves UnramifiedGaloisFixedApartmentStatement. The status is conditional: the class D and its Γ-stability are supplied, and the Γ-action on B(G_K), the finiteness of Γ-orbits, the enlarged-building embedding and the added bounded-subgroup assertion still have no declaration (see the Recorded Lean scope). The published reduction unramifiedValuationDescent_of_fixedLocus (Theorem 9.6.5 row) takes this statement as its first input."
      ],
      "consumer_or_regression": "The apartments A^Γ of §9.2.3 and Construction 9.6.1. The fixed-point set of UnramifiedValuationDescentStatement (Theorem 9.6.5 row) is nonempty only by this statement. Regression: for the norm-one torus T of the unramified quadratic extension in SL_2, T_K is a maximal K-split torus, Frobenius acts on V(T_K) by −1 and the Γ-fixed part of A_T is a single point; T is not special, which the Lean statement allows. Regression for the zero section: for k = Q_2 and G = G_m, B(G_K)^Γ is a single point and the Γ-fixed enlarged building is R, on which 2 ∈ G(k) (normalized valuation 1) acts by t ↦ t − 1; no G(k)-equivariant map from the point exists, while G(k)^1 = Z_2^× acts trivially on R.",
      "formal_status": "conditional",
      "publication_commits": [
        "9bc92c384fa84da7ce5811a5979d408fb69d40b0",
        "b128d289028bf75629e9e364ecf151c484b27a85"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.UnramifiedGaloisFixedApartmentStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-11 at Library commit 529b851c; kind definition; statement_returns_prop true; the module is byte-identical to commit 9bc92c38."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedGaloisFixedApartment",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit 6948120d; kind theorem, proving UnramifiedGaloisFixedApartmentStatement; the module is byte-identical to commit b128d289."
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
        "Recorded Lean scope: SpecialTorusExistenceStatement (module Langlands.Geometry.Building.UnramifiedSpecialApartmentStatement) quantifies over every nonarchimedean local field F, every connected reductive G over Spec F and every maximal split torus iS : S.toGrp ⟶ G (IsMaximalSplitTorus). K is the Library's maximal unramified extension inertiaFixedField F (definitionally UnramifiedClosure F) with its F-algebra structure, and scalar extension is base change along algebraBaseMap F K. It asserts a commutative group scheme T with iT : T.toGrp ⟶ G and f : S ⟶ T such that CommGroupScheme.groupHom f ≫ iT = iS, iT is a closed subgroup (IsClosedSubgroup), and the scalar extension iT_K is a maximal split torus of G_K. That T is an F-torus follows from the last condition and is not stated separately. The source's Henselian discretely valued fields with perfect residue field are specialized to nonarchimedean local fields of either characteristic in universe u. SpecialTorusIntegralModelStatement (module Langlands.Geometry.Building.SpecialTorusIntegralModelStatement) states the building input of the source proof under the same quantifiers: there is an IntegralModel M of G over 𝒪[F] with M.IsSmooth and connected special fibre, a closed split 𝒪[F]-torus j : 𝒮 → M.group whose generic fibre is iS (M.genericTorusMap 𝒮 j = groupHom e.hom ≫ iS for an isomorphism e of the generic fibre of 𝒮 with S), and a closed split torus of the base change M.baseChangeUnramified to the integers of K whose generic fibre is a maximal split torus of G_K. It is derived: the source proof uses G^1_x, while the statement asks for a model with connected special fibre (the role of G^0_x), and it asks for a split integral torus where Proposition B.2.4 gives a torus. It records neither the point x, nor an identification of M with a Bruhat–Tits model, nor reductivity of the special fibre."
      ],
      "conclusion": "Every maximal k-split torus S of G is contained in a special k-torus.",
      "lean_declarations": [
        "Langlands.Geometry.Building.SpecialTorusExistenceStatement",
        "Langlands.Geometry.Building.SpecialTorusIntegralModelStatement",
        "Langlands.Geometry.Building.specialTorusIntegralModelReductionStatement",
        "Langlands.Geometry.Building.specialTorusBoundedModel",
        "Langlands.Geometry.Building.specialTorusIntegralModel",
        "Langlands.Geometry.Building.specialTorusExistence_of_integralModel",
        "Langlands.Geometry.Building.specialTorusExistence"
      ],
      "modules": [
        "Langlands.Geometry.Building.UnramifiedSpecialApartmentStatement",
        "Langlands.Geometry.Building.SpecialTorusIntegralModelStatement",
        "Langlands.Geometry.Building.SpecialTorusIntegralModelReduction",
        "Langlands.Geometry.Building.SpecialTorusBoundedModelProof",
        "Langlands.Geometry.Building.SpecialTorusIntegralModelProof",
        "Langlands.Geometry.Building.SpecialTorusExistenceFromModel",
        "Langlands.Geometry.Building.SpecialTorusExistenceProof"
      ],
      "dependencies": [
        "Source proof: S(K)^1 is Γ-stable and acts boundedly on B(G_K) (Proposition 4.2.13); with the finite-quotient action of corrected 9.2.1, Theorem 1.1.15 gives a point x fixed by Γ and S(K)^1. The schematic closure of S in the descended model G^1_x of 9.2.5 is a torus (Proposition B.2.4); Proposition 8.2.1(1) gives a closed o-torus containing it whose special fibre is a maximal f-torus of the special fibre, and its generic fibre is the special torus.",
        "Split of the source proof: SpecialTorusIntegralModelStatement covers the building input up to the schematic closure of S (point x, the descended model of Section 9.2.5, Proposition B.2.4) and the torus that Axiom 4.1.20(3) gives over O at x. The remaining algebraic step, Proposition 8.2.1(1) lifting a maximal torus of the special fibre that contains the closure of S, and the conclusion that its generic fibre is special stay with the proof of SpecialTorusExistenceStatement.",
        "Follow-up (twenty-fourth update, Library commit 7229bb45): the module Langlands.Geometry.Building.SpecialTorusIntegralModelReduction (whose entry declaration is SpecialTorusIntegralModelReductionStatement, first in Library commit 51e4d8972659f1ffcf0ca89e8eee9540a30b52d3; its Markdown was revised in Library commit 0c3f30c24701c74d5474fca3fbb5324a99aa1d58 and left its Lean unchanged) proves, as the theorem specialTorusIntegralModelReductionStatement, the implication from SpecialTorusBoundedModelStatement to SpecialTorusIntegralModelStatement; the theorem specialTorusIntegralModelStatement_of_boundedModel of the same module is this implication. SpecialTorusBoundedModelStatement (module Langlands.Geometry.Building.SpecialTorusBoundedModelStatement, added in the same commit) asks for a smooth integral model M of G over the integers of F such that the integral points of the base change of M to the integers of the maximal unramified extension K contain the maximal bounded subgroup S(K)^1 and, for some maximal K-split torus A of G_K, the maximal bounded subgroup A(K)^1. The theorem specialTorusBoundedModel (module Langlands.Geometry.Building.SpecialTorusBoundedModelProof, first in Library commit aeb3911c4e1bf6e3a2f653e874e4ebc422d2a61a) proves SpecialTorusBoundedModelStatement. So SpecialTorusIntegralModelStatement follows from published proofs. No published theorem has that type; the composite was checked with a separate Lean check (Library commit 7229bb45, type exactly SpecialTorusIntegralModelStatement.{u}, only propext, Classical.choice and Quot.sound). Lean inspections of the two theorems are recorded below. SpecialTorusExistenceStatement is unproved at Library commit 7229bb45. The modules SpecialTorusIntegralModelReduction and SpecialTorusBoundedModelStatement are byte-identical between commit 0c3f30c2 and Library commit 7229bb45, the module SpecialTorusBoundedModelProof between commit aeb3911c and Library commit 7229bb45, and the two modules cited earlier in this entry between Library commits 0c3f30c2 and 7229bb45. Follow-up (twenty-fifth update, Library commit 49668e4d): the theorem specialTorusIntegralModel (module Langlands.Geometry.Building.SpecialTorusIntegralModelProof, first in Library commit 4abbe7aabd9c92005d91c9d5bba86b879e928bb3) has type SpecialTorusIntegralModelStatement. Its proof applies specialTorusIntegralModelReductionStatement to specialTorusBoundedModel, so it adds a named theorem but no new step: the statement already followed from published proofs at Library commit 7229bb45. The Lean inspection of this theorem is recorded below. SpecialTorusExistenceStatement is unproved at Library commit 49668e4d. The module SpecialTorusIntegralModelProof is byte-identical between commit 4abbe7aa and Library commit 49668e4d, and the modules cited earlier in this entry between Library commits 7229bb45 and 49668e4d. Follow-up (twenty-sixth update, Library commit 0b7bb3fd): the theorem specialTorusExistence (module Langlands.Geometry.Building.SpecialTorusExistenceProof, first in Library commit fab9caeae532b7a65e67e702bcab72d3194371ae) proves SpecialTorusExistenceStatement. Its proof applies the theorem specialTorusExistence_of_integralModel (module Langlands.Geometry.Building.SpecialTorusExistenceFromModel, added in the same commit), the implication from SpecialTorusIntegralModelStatement to SpecialTorusExistenceStatement, to specialTorusIntegralModel. As the Markdown of that module describes, the implication follows the source proof: it lifts a maximal torus of the special fibre that contains the closed fibre of the split torus, by the published theorem HenselianTorusLifting.nonempty_liftData (KP Proposition 8.2.1(1)), and the lift splits over the integers of K. It departs from KP in two places: the torus is formed as a schematic image over F, and its maximality over K comes from a rank count. The other modules added with it are the helper modules Langlands.GroupScheme.Rational.CommutingTorusImage, Langlands.GroupScheme.Rational.SplitRankMaximality, Langlands.GroupScheme.Torus.ResidueRankComparison and Langlands.GroupScheme.Torus.StrictHenselianRelativeSplit. So Proposition 9.3.4 is proved in the recorded Lean scope, for nonarchimedean local fields of either characteristic in place of Henselian discretely valued fields with perfect residue field, and the formal status of this row is proved. Lean inspections of the two theorems are recorded below. The modules SpecialTorusExistenceFromModel and SpecialTorusExistenceProof are byte-identical between commit fab9caea and Library commit 0b7bb3fd, and the modules cited earlier in this entry between Library commits 49668e4d and 0b7bb3fd."
      ],
      "consumer_or_regression": "Special k-apartments (§9.2.2–9.2.3); Axiom 4.1.27 in §9.5; the proof of Lemma 9.8.1; the published reduction valuationApartmentAxiomsExistenceReduction (Theorem 9.6.5 row), which takes SpecialTorusExistenceStatement as an input. Regression: for anisotropic G the maximal split torus is trivial, and the statement asserts a k-torus that is maximally split over K. The published proof specialTorusExistence derives SpecialTorusExistenceStatement from the published proof specialTorusIntegralModel of SpecialTorusIntegralModelStatement through specialTorusExistence_of_integralModel.",
      "formal_status": "proved",
      "publication_commits": [
        "9bc92c384fa84da7ce5811a5979d408fb69d40b0",
        "ba77b83f98d4cbe92842b4645577633e0541fdab",
        "fab9caeae532b7a65e67e702bcab72d3194371ae"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.SpecialTorusExistenceStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-11 at Library commit 3c9b0579; kind definition; statement_returns_prop true; the module is byte-identical to commit 9bc92c38."
        },
        {
          "declaration": "Langlands.Geometry.Building.SpecialTorusIntegralModelStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-12 at Library commit c5b9c2cf; kind definition; statement_returns_prop true; the module is byte-identical to commit ba77b83f."
        },
        {
          "declaration": "Langlands.Geometry.Building.specialTorusIntegralModelReductionStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 51e9457f; kind theorem, at universe level u, whose type is exactly SpecialTorusIntegralModelReductionStatement.{u}, the implication from SpecialTorusBoundedModelStatement to SpecialTorusIntegralModelStatement; the module is byte-identical to commit 0c3f30c2, which revised its Markdown; its Lean was first published in commit 51e4d897."
        },
        {
          "declaration": "Langlands.Geometry.Building.specialTorusBoundedModel",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 51e9457f; kind theorem, at universe level u, whose type is exactly SpecialTorusBoundedModelStatement.{u}; the module is byte-identical to commit aeb3911c, which first published it."
        },
        {
          "declaration": "Langlands.Geometry.Building.specialTorusIntegralModel",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 49668e4d; kind theorem, at universe level u, whose type is exactly SpecialTorusIntegralModelStatement.{u}; the module is byte-identical to commit 4abbe7aa, which first published it."
        },
        {
          "declaration": "Langlands.Geometry.Building.specialTorusExistence_of_integralModel",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit fab9caea; kind theorem, at universe level u, whose type is the implication from SpecialTorusIntegralModelStatement to SpecialTorusExistenceStatement; the module was first published in that commit and is byte-identical at Library commit 0b7bb3fd."
        },
        {
          "declaration": "Langlands.Geometry.Building.specialTorusExistence",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit fab9caea; kind theorem, at universe level u, whose type is exactly SpecialTorusExistenceStatement.{u}; the module was first published in that commit and is byte-identical at Library commit 0b7bb3fd."
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
        "Recorded Lean scope: ValuationApartmentAxiomsExistenceStatement (module of the same name) asserts, for every nonarchimedean local field F and connected reductive G over Spec F, some B : ValuationBuildingData G (a maximal split torus, an N(F)-stable equipollence class of localFieldOrder F-compatible valuations of its root datum, the actual centralizer and V 6) with B.SatisfiesApartmentAxioms (V 7 and AS 2–AS 5). It asks for some torus and some class, whereas KP's class is canonical for every torus, and it includes the §9.5 apartment axioms transported by §9.6.6. This program's module Langlands.Geometry.Building.UnramifiedValuationDescentStatement splits it. K is the Library's maximal unramified extension inertiaFixedField F (definitionally UnramifiedClosure F) with its F-algebra structure, and scalar extension is base change along algebraBaseMap F K. UnramifiedValuationDescentStatement takes a maximal split torus iS, a torus T with iT and f : S ⟶ T, groupHom f ≫ iT = iS and iT_K a maximal split torus of G_K, opposite factor pairs hE for iT_K (a Prop that the published rootRankOneFactorization proves), a class D : KPApartmentData iT_K ω for the order ω of MaximalUnramified.valuation F, and a centralizer datum C with full V 6 (IntegerValuation.IsOmegaCompatible). Call x fixed when galoisAction σ x = x for every σ : K ≃ₐ[F] K, and let φ x be the published torus-then-field restriction torusFieldRestrictedRootFunctionFamily of x along f_K. The statement asserts DS : KPApartmentData iS (localFieldOrder F) and CS : CentralizerDatum iS with DS.IsOmegaCompatible CS (V 6 over F), such that ψ ∈ DS.carrier iff ψ = φ x for a fixed x, φ is injective on fixed points, and for every n ∈ N(F) and fixed x some fixed y has φ y = n • φ x and D.apartmentMap y = n • D.apartmentMap x in D.ReducedBuilding. ValuationBuildingApartmentAxiomsStatement asserts B.SatisfiesApartmentAxioms for every B : ValuationBuildingData G with [IsAffineHom G.X.hom]; quantifying over every class instead of the constructed one relies on the uniqueness of Proposition 6.2.6. UnramifiedValuationDescentPackageStatement is their conjunction. The theorem valuationApartmentAxiomsExistenceReduction proves ValuationApartmentAxiomsExistenceReductionStatement: UnramifiedQuasiSplitStatement, QuasiSplitIntegerApartmentExistenceStatement, SpecialTorusExistenceStatement and the two statements above imply ValuationApartmentAxiomsExistenceStatement. KP construct ϕ^x from the descended building; the Lean statement uses the restriction, which agrees with ϕ^x by Lemma 9.6.3 read with depth m·r for upstairs roots restricting to m·a. The source's Henselian discretely valued fields with perfect residue field are specialized to nonarchimedean local fields of either characteristic in universe u."
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
        "Langlands.Geometry.Building.unramifiedFixedDepthZeroOpposite_of_recoveredParabolicModels",
        "Langlands.Geometry.Building.unramifiedTwistedFixedTranslation",
        "Langlands.BruhatTits.IntegralModels.integralOppositeFactors",
        "Langlands.Geometry.Building.unramifiedFixedRecoveredParabolicModels",
        "Langlands.Geometry.Building.unramifiedFixedDepthZeroOpposite",
        "Langlands.Geometry.Building.unramifiedFixedPairSpecialApartment",
        "Langlands.Geometry.Building.unramifiedFixedPointTransporter",
        "Langlands.Geometry.Building.unramifiedTorusUnitFixedApartment",
        "Langlands.Geometry.Building.unramifiedFixedLeviTransport",
        "Langlands.Geometry.Building.unramifiedFixedOpposite",
        "Langlands.Geometry.Building.unramifiedValuationDescent"
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
        "Langlands.Geometry.Building.UnramifiedRecoveredDepthZeroOpposite",
        "Langlands.Geometry.Building.UnramifiedTwistedFixedTranslationProof",
        "Langlands.BruhatTits.IntegralModels.IntegralOppositeFactorsProof",
        "Langlands.BruhatTits.IntegralModels.UnramifiedNearbyParabolicComparisons",
        "Langlands.Geometry.Building.UnramifiedFixedDepthZeroOppositeProof",
        "Langlands.Geometry.Building.UnramifiedFixedPairSpecialApartmentProof",
        "Langlands.Geometry.Building.UnramifiedFixedPointTransporterProof",
        "Langlands.Geometry.Building.UnramifiedTorusUnitFixedApartmentProof",
        "Langlands.Geometry.Building.UnramifiedFixedLeviTransportProof",
        "Langlands.Geometry.Building.UnramifiedFixedOppositeProof",
        "Langlands.Geometry.Building.UnramifiedValuationDescentProof"
      ],
      "dependencies": [
        "Source proof: V 0 and V 1 from Construction 9.6.1 and Proposition 9.4.3; equivariance from Lemma 9.4.15; V 2 from the same computation; V 6 from Proposition 9.3.16; V 3 from Proposition 9.4.8 and Remark 9.6.4; V 4 and V 5 from Corollary 9.4.10. Lemma 9.6.3 (Lemma 9.4.21, Propositions 7.3.12 and 9.3.24) compares U_{a,x,r} with the upstairs filtrations.",
        "Recorded Lean route: valuationApartmentAxiomsExistenceReduction takes a maximal split torus from exists_maximalSplitTorus and a special torus T ⊇ S from SpecialTorusExistenceStatement (Proposition 9.3.4 row). It makes G_K connected reductive by connectedReductiveFieldExtensionStatement and quasi-split by UnramifiedQuasiSplitStatement. QuasiSplitIntegerApartmentExistenceStatement, applied to K with MaximalUnramified.valuation_surjective and valuationSubring_isHenselian, gives the upstairs class with V 6. rootRankOneFactorization gives hE. UnramifiedValuationDescentStatement descends the class, and ValuationBuildingApartmentAxiomsStatement supplies the apartment axioms.",
        "Proof obligations: the reduction reduces ValuationApartmentAxiomsExistenceStatement to its five inputs. SpecialTorusExistenceStatement is in the Proposition 9.3.4 row. UnramifiedQuasiSplitStatement holds. The theorem unramifiedQuasiSplit_of_henselianDiscrete (module UnramifiedQuasiSplitReduction, present in Library commit ed924aef420de137b4cbaa3b063a3618afcd73fd) proves UnramifiedQuasiSplitReductionStatement, that HenselianDiscreteQuasiSplitStatement implies UnramifiedQuasiSplitStatement; it applies the Henselian statement to the maximal unramified extension K with the integer-normalized valuation, whose valuation ring is Henselian and whose residue field is algebraically closed. The theorem Langlands.GroupScheme.henselianDiscreteQuasiSplit (module Langlands.GroupScheme.Rational.HenselianDiscreteQuasiSplitProof, first in Library commit 410c79471b79f65a02fb0f6070da7f2800793ff3) proves HenselianDiscreteQuasiSplitStatement (KP Corollary 2.3.8) by applying the published reduction henselianDiscreteQuasiSplit_of_dimensionLEOne to dimensionLEOneQuasiSplit (Steinberg's theorem, KP Theorem 2.3.3(2)). Lean inspections on 2026-11-14 at Library commit 757a6793 report kind theorem and only propext, Classical.choice and Quot.sound for both theorems, whose types are exactly UnramifiedQuasiSplitReductionStatement.{u} and HenselianDiscreteQuasiSplitStatement.{u}. No published theorem has UnramifiedQuasiSplitStatement as its type; the composite was checked with a separate Lean check (Library commit 757a6793, only propext, Classical.choice and Quot.sound). The published conditional reduction henselianDiscreteQuasiSplitReduction derives HenselianDiscreteQuasiSplitStatement from QuasiSplitRegularClassRationalStatement, and that statement is proved as well: the theorem Langlands.GroupScheme.quasiSplitRegularClassRational (module Langlands.GroupScheme.Rational.QuasiSplitRegularClassRational, first in Library commit db8d6b3d466f2fd453a4df4624ce6c90db8eed46) has it as its type; an inspection on 2026-11-14 at Library commit 757a6793 reports kind theorem, a type that is exactly QuasiSplitRegularClassRationalStatement.{u}, and only propext, Classical.choice and Quot.sound. QuasiSplitIntegerApartmentExistenceStatement is proved: the theorem quasiSplitIntegerApartmentExistence (module QuasiSplitIntegerApartmentExistenceProof) is present in Library commit ed924aef420de137b4cbaa3b063a3618afcd73fd. So two of the five inputs of the reduction are proved. On 14 November 2026 the other three (SpecialTorusExistenceStatement, UnramifiedValuationDescentStatement and ValuationBuildingApartmentAxiomsStatement) have no published proof. The modules UnramifiedQuasiSplitReduction, HenselianDiscreteQuasiSplitProof and QuasiSplitRegularClassRational are byte-identical between the commits cited above and Library commit 757a6793. The entry \"Partial route inside UnramifiedValuationDescentStatement\" below reduces the descent statement to two unproved statements. Follow-up (twenty-sixth update, Library commit 0b7bb3fd): the theorem specialTorusExistence proves SpecialTorusExistenceStatement (Proposition 9.3.4 row), so three of the five inputs of the reduction are proved. ValuationApartmentAxiomsExistenceStatement therefore follows from UnramifiedValuationDescentStatement and ValuationBuildingApartmentAxiomsStatement and, by the follow-up of the twenty-sixth update of the entry \"Partial route inside UnramifiedValuationDescentStatement\", from ValuationBuildingApartmentAxiomsStatement and UnramifiedFixedPairSpecialApartmentStatement. No published declaration states these composites; the second was checked with a separate Lean check (Library commit fab9caea, only propext, Classical.choice and Quot.sound), which applies the reduction to the three proved inputs, to ValuationBuildingApartmentAxiomsStatement and to the descent composite of that entry. That entry now reduces the descent statement to one unproved statement. None of UnramifiedValuationDescentStatement, ValuationBuildingApartmentAxiomsStatement and UnramifiedFixedPairSpecialApartmentStatement is proved at Library commit 0b7bb3fd. The modules cited earlier in this entry are byte-identical between Library commits 757a6793 and 0b7bb3fd. Follow-up (thirty-third update, Library commit b369a8f2): the theorem unramifiedValuationDescent proves UnramifiedValuationDescentStatement (entry \"Partial route inside UnramifiedValuationDescentStatement\"), so four of the five inputs of the reduction are proved, and ValuationApartmentAxiomsExistenceStatement follows from ValuationBuildingApartmentAxiomsStatement alone. No published declaration states this composite; it was checked with a separate Lean check that applies valuationApartmentAxiomsExistenceReduction to unramifiedQuasiSplit_of_henselianDiscrete applied to GroupScheme.henselianDiscreteQuasiSplit, quasiSplitIntegerApartmentExistence, specialTorusExistence, unramifiedValuationDescent and the premise (Library commit 8f4a33d7, only propext, Classical.choice and Quot.sound). ValuationBuildingApartmentAxiomsStatement is unproved at Library commit b369a8f2, so the formal status of this row stays statement. The modules cited earlier in this entry are byte-identical between Library commits 0b7bb3fd and b369a8f2.",
        "Partial route inside ValuationBuildingApartmentAxiomsStatement: the last sentence of AS 5 (KP Axiom 4.1.6, Proposition 6.6.2), that for quasi-split adjoint G the image of N(F) in the affine automorphisms of the apartment is W(Ψ)^ext. The module Langlands.Geometry.Building.ValuationQuasiSplitAdjointTranslation, present in Library commit 17dd94ea3f677b20fb5ab95b285cbc3fd7cde03e, states its translation part ValuationBuildingQuasiSplitAdjointTranslationStatement: for every B : ValuationBuildingData G of a quasi-split adjoint G over a nonarchimedean local field, every translation of the apartment that preserves the affine roots Ψ is the translation by ν(z) for some z ∈ Z(F). Its theorem range_eq_extendedAffineWeylGroup_of_quasiSplitAdjointTranslation derives the last sentence of AS 5 for B from this statement and the first sentence. The Library states QuasiSplitAdjointSimpleRootTransitivityStatement (first in Library commit cfedefb680f317b0ea5d351023e1c9dd886b2547), the group-theoretic content behind KP Lemma 6.4.10: for every field k, quasi-split adjoint G over k, maximal split torus S and representative Z of its centralizer, some finite family Δ of relative roots generates every relative root, and for each a ∈ Δ and all u, u' ∈ U_a(k) outside U_{2a}(k) some z ∈ Z(k) commutes with U_b(k) for every other b ∈ Δ and conjugates u into u' U_{2a}(k). The theorem valuationBuildingQuasiSplitAdjointTranslation_of_simpleRootTransitivity (module ValuationQuasiSplitAdjointTranslationReduction, same commit) proves the translation statement from it. The theorem quasiSplitAdjointSimpleRootTransitivity (module QuasiSplitAdjointSimpleRootTransitivityProof, first in Library commit 51e4d8972659f1ffcf0ca89e8eee9540a30b52d3) proves QuasiSplitAdjointSimpleRootTransitivityStatement. Its unit also proves the Galois descent of torus points with prescribed character values as exists_rationalPoint_characterValue_eq_of_equivariant (module Langlands.GroupScheme.Torus.EquivariantCharacterValueDescent): for a Galois extension L/k and a commutative k-group scheme T whose base change to L is a split torus, every Galois-equivariant homomorphism X^*(T_L) → L^× is the evaluation of characters at some k-point of T. The theorem valuationBuildingQuasiSplitAdjointTranslation (module ValuationQuasiSplitAdjointTranslationProof, first in Library commit 7f43c3c930ff92f76dae6589da1678ad729017e5) applies the reduction to it and proves ValuationBuildingQuasiSplitAdjointTranslationStatement. So, by range_eq_extendedAffineWeylGroup_of_quasiSplitAdjointTranslation, the last sentence of AS 5 holds for every such B that satisfies the first sentence. The statement Langlands.GroupScheme.TorusEquivariantCharacterValueDescentStatement (module Langlands.GroupScheme.Torus.EquivariantCharacterValueDescentStatement) is present in Library commit 451cce4ca176c34856be86a36801b7a3b585ae77. It has the hypotheses and conclusion of the descent theorem above. The theorem torusEquivariantCharacterValueDescent (module Langlands.GroupScheme.Torus.EquivariantCharacterValueDescentProof, first in Library commit 0c3f30c24701c74d5474fca3fbb5324a99aa1d58) proves it by applying exists_rationalPoint_characterValue_eq_of_equivariant; a Lean inspection on 2026-11-13 at Library commit 0f84a0d8 reports kind theorem and only propext, Classical.choice and Quot.sound. No published reduction yet expresses ValuationBuildingApartmentAxiomsStatement through these statements.",
        "Partial route inside UnramifiedValuationDescentStatement: the theorem unramifiedValuationDescent_of_fixedLocus (module UnramifiedValuationDescentReduction, first in Library commit cc5aa77fa8dbdc6e723091c7b710ab0d81162c4e) proves that UnramifiedGaloisFixedApartmentStatement, UnramifiedFixedLeviTransportStatement, UnramifiedFixedCentralizerCompatibilityStatement (V 6 on Z(F) at the Γ-fixed points) and UnramifiedFixedOppositeStatement (V 5 at the Γ-fixed points, as KP derive it from Corollary 9.4.10) imply UnramifiedValuationDescentStatement. The first input is proved (Section 9.2.1 row). The theorem unramifiedFixedCentralizerCompatibility_of_leviTransport (module UnramifiedFixedCentralizerReduction, first in Library commit 0c3f30c24701c74d5474fca3fbb5324a99aa1d58) derives the third input from the second. The theorem unramifiedFixedLeviTransport_of_fixedApartment_and_leviSharp (module UnramifiedFixedLeviTransportReduction, first in Library commit 73b1430a339b037d27e9096762b0400adb4fbd19) derives the second input from UnramifiedTorusUnitFixedApartmentStatement and UnramifiedLeviSharpApartmentTransportStatement, and the theorem unramifiedLeviSharpApartmentTransport (module UnramifiedLeviSharpApartmentTransportProof, first in Library commit 0c3f30c24701c74d5474fca3fbb5324a99aa1d58) proves the latter. UnramifiedTorusUnitFixedApartmentStatement states the fixed-locus part of KP Proposition 9.3.13 in this setting: every point of the reduced building of D that is fixed by the coefficient action of Aut(K/F) and by the character-valuation kernel of S(K) is the image of an Aut(K/F)-fixed point of the T-apartment. UnramifiedFixedOppositeStatement is in module UnramifiedFixedLocusStatement (whose entry declaration is UnramifiedFixedCentralizerCompatibilityStatement); both are first in Library commit cc5aa77fa8dbdc6e723091c7b710ab0d81162c4e. Composing the four published theorems shows that UnramifiedTorusUnitFixedApartmentStatement and UnramifiedFixedOppositeStatement together imply UnramifiedValuationDescentStatement; no published declaration states this composite. On 13 November 2026 neither of the two is proved. Three further declarations towards UnramifiedFixedOppositeStatement are in the Library, all first in Library commit 430cc03fe803c5dbf74bc3baf91e8f7a2c26ea9c. UnramifiedFixedWallInvarianceStatement (module of the same name) is the last assertion of KP Proposition 9.4.9 at the Aut(K/F)-fixed points z of the apartment of D, stated on the restricted root-function family φ_z: for a relative root a, g ∈ U_a(F) with g ≠ 1 and φ_z(a, g) = 0, and g', g'' ∈ U_{-a}(F) with m = g' g g'' ∈ N(F), the published action of m on root-function families fixes φ_z. The theorem unramifiedFixedOpposite_of_wallInvariance (module UnramifiedFixedOppositeReduction, whose entry declaration UnramifiedFixedOppositeReductionStatement names the implication) proves that UnramifiedFixedWallInvarianceStatement implies UnramifiedFixedOppositeStatement, following KP's proof of Corollary 9.4.10. UnramifiedFixedDepthZeroOppositeStatement (module of the same name) states a consequence of KP Proposition 9.4.9(2) on the restricted root-function family at the Aut(K/F)-fixed points z of the apartment of D: for a relative root a, g ∈ U_a(F) with g ≠ 1 and φ_z(a, g) = 0, and g', g'' ∈ U_{-a}(F) with g' g g'' ∈ N(F), the two opposite factors have nonnegative restricted value, 0 ≤ φ_z(-a, g') and 0 ≤ φ_z(-a, g''). It is not assertion (2) itself: it does not state that g', g'' or KP's m(g) = g' g g'' belong to G^0_z(o), and it constructs neither the parahoric model G^0_z nor its special fibre. KP prove assertion (2) with Theorem 8.2.9 and use it in their proof of the last assertion. Composing the published theorems, UnramifiedTorusUnitFixedApartmentStatement and UnramifiedFixedWallInvarianceStatement together imply UnramifiedValuationDescentStatement; neither of them is proved. Correction and update (twentieth update, 14 November 2026): earlier versions of this entry said that no published theorem takes UnramifiedFixedDepthZeroOppositeStatement as a hypothesis. That has been false since Library commit 85c2fe719cf62e96f22aaf4ca03961c5814d086b. The theorem unramifiedFixedWallInvariance_of_depthZero_of_leviTransport (module UnramifiedFixedWallInvarianceReduction, whose entry declaration UnramifiedFixedWallInvarianceReductionStatement names the implication, first in that commit) proves that UnramifiedFixedDepthZeroOppositeStatement and UnramifiedFixedLeviTransportStatement together imply UnramifiedFixedWallInvarianceStatement. Published theorems also split UnramifiedTorusUnitFixedApartmentStatement, following the proof of KP Proposition 9.3.13 as revised in the 2024 corrections (PDF pp.39–40). The theorem unramifiedTorusUnitFixedApartmentReduction (module UnramifiedTorusUnitFixedApartmentReduction, first in Library commit 4f6abf4c7e19610e4d89edc9bf64b34ba1db9ff2) derives it from three statements. UnramifiedFixedPointTransporterStatement (module of the same name, first in Library commit 51e4d8972659f1ffcf0ca89e8eee9540a30b52d3) takes an apartment point x_0 fixed by Aut(K/F) and a point y of the reduced building fixed by the coefficient action of Aut(K/F) and by the character-valuation kernel of S_K(K), and asserts some h ∈ G(K) that commutes with S_K(K), fixes the image of x_0, has h^{-1}σ(h) in the normalizer of T_K for every σ, and carries some apartment point to y. UnramifiedTwistedFixedTranslationStatement (module of the same name, first in Library commit 430cc03fe803c5dbf74bc3baf91e8f7a2c26ea9c) says that the apartment translations fixed by the twisted coefficient action lie in the image of V(S_K), KP's V(T')^Γ = V(S'). UnramifiedSplitTranslationFixerStatement (module of the same name, first in Library commit 4f6abf4c7e19610e4d89edc9bf64b34ba1db9ff2) says that an element of G(K) that commutes with S_K(K) and fixes the image of an apartment point x also fixes the image of v + x for every v in that image of V(S_K). The theorem unramifiedSplitTranslationFixer (module UnramifiedSplitTranslationFixerProof, first in Library commit c40a01345b2f4172fa41e07ff31644b40e695003) proves the third statement by the orbit-and-convexity argument of the corrections, with finite convex combinations. The theorem unramifiedFixedPointTransporter_of_fixedPairSpecialApartment (module UnramifiedFixedPointTransporterReduction, whose entry declaration is UnramifiedFixedPairSpecialApartmentStatement; first in Library commit c40a01345b2f4172fa41e07ff31644b40e695003) derives the first statement from UnramifiedFixedPairSpecialApartmentStatement and the published unramifiedLeviSharpApartmentTransport. UnramifiedFixedPairSpecialApartmentStatement is KP Proposition 9.3.11(1) for two points y_1, y_2 of that kind: some g ∈ G(K) that commutes with S_K(K) and has g^{-1}σ(g) in the normalizer of T_K for every σ carries an apartment point to y_1 and another to y_2. The theorem unramifiedFixedDepthZeroOpposite_of_recoveredParabolicModels (module UnramifiedRecoveredDepthZeroOpposite, first in Library commit c40a01345b2f4172fa41e07ff31644b40e695003) derives UnramifiedFixedDepthZeroOppositeStatement from two statements. UnramifiedFixedRecoveredParabolicModelsStatement (same module) asks, at each Aut(K/F)-fixed apartment point z, for actual relative-component models over the integers of F and of K with unramified recovery, whose upper integral points are the character-valuation kernel intersected with the pointwise fixer of z, together with nearby parabolic root comparisons. IntegralOppositeFactorsStatement (module Langlands.BruhatTits.IntegralModels.IntegralOppositeFactorsStatement, first in Library commit 410c79471b79f65a02fb0f6070da7f2800793ff3) is KP Theorem 8.2.9 for supplied smooth affine integral models with connected fibres over the integers of a nonarchimedean local field. Composing these theorems with unramifiedGaloisFixedApartment, unramifiedLeviSharpApartmentTransport and the four reductions above, UnramifiedFixedPairSpecialApartmentStatement, UnramifiedTwistedFixedTranslationStatement and UnramifiedFixedDepthZeroOppositeStatement together imply UnramifiedValuationDescentStatement, and the last of the three may be replaced by the two inputs of its reduction. No published declaration states this composite; both forms were checked with a separate Lean check (Library commit c40a0134, only propext, Classical.choice and Quot.sound). At Library commit c40a0134 none of these five statements was proved. The axiom reports below record Lean inspections of the five theorems named in this paragraph. Each module cited in this paragraph with a first commit is byte-identical between that commit and Library commit c40a0134. Twenty-second update (14 November 2026): the theorem unramifiedTwistedFixedTranslation (module UnramifiedTwistedFixedTranslationProof, first in Library commit b3a1bdaf15715f16a43643513b7cbb6cbb58ef3a) proves UnramifiedTwistedFixedTranslationStatement; its Lean inspection is recorded below. With the theorems above, UnramifiedFixedPairSpecialApartmentStatement and UnramifiedFixedDepthZeroOppositeStatement together imply UnramifiedValuationDescentStatement, and the second may again be replaced by UnramifiedFixedRecoveredParabolicModelsStatement and IntegralOppositeFactorsStatement. No published declaration states this composite; both forms were checked with a separate Lean check (Library commit 4f4af6ba, only propext, Classical.choice and Quot.sound). None of these four statements is proved at Library commit 4f4af6ba. The module UnramifiedTwistedFixedTranslationProof is byte-identical between commit b3a1bdaf and Library commit 4f4af6ba, and the modules cited earlier in this paragraph are byte-identical between Library commits c40a0134 and 4f4af6ba. Follow-up (twenty-second update, Library commit 58ad0f79): the theorem IntegralModels.integralOppositeFactors (module Langlands.BruhatTits.IntegralModels.IntegralOppositeFactorsProof, first in Library commit af5d652c2f2ff5b35b4ce4dbbf7cbec8bbf3e99e) proves IntegralOppositeFactorsStatement; its Lean inspection is recorded below. UnramifiedValuationDescentStatement therefore follows from UnramifiedFixedPairSpecialApartmentStatement together with either UnramifiedFixedDepthZeroOppositeStatement or UnramifiedFixedRecoveredParabolicModelsStatement. No published declaration states the second form; it was checked with a separate Lean check (Library commit 58ad0f79, only propext, Classical.choice and Quot.sound). None of these three statements is proved at Library commit 58ad0f79. The module IntegralOppositeFactorsProof is byte-identical between commit af5d652c and Library commit 58ad0f79, and the modules cited earlier in this paragraph are byte-identical between Library commits 4f4af6ba and 58ad0f79. Follow-up (twenty-sixth update, Library commit 0b7bb3fd): the theorem unramifiedFixedRecoveredParabolicModels (namespace Langlands.Geometry.Building, module Langlands.BruhatTits.IntegralModels.UnramifiedNearbyParabolicComparisons) proves UnramifiedFixedRecoveredParabolicModelsStatement, and the theorem unramifiedFixedDepthZeroOpposite (module Langlands.Geometry.Building.UnramifiedFixedDepthZeroOppositeProof) proves UnramifiedFixedDepthZeroOppositeStatement by applying unramifiedFixedDepthZeroOpposite_of_recoveredParabolicModels to it and to IntegralModels.integralOppositeFactors. Both modules were first in Library commit fab9caeae532b7a65e67e702bcab72d3194371ae. Lean inspections of the two theorems are recorded below. So, by either form of the previous follow-up, UnramifiedValuationDescentStatement follows from UnramifiedFixedPairSpecialApartmentStatement alone. No published declaration states this composite; both forms were checked with separate Lean checks (Library commit fab9caea, only propext, Classical.choice and Quot.sound). Neither UnramifiedFixedPairSpecialApartmentStatement nor UnramifiedValuationDescentStatement is proved at Library commit 0b7bb3fd. The modules UnramifiedNearbyParabolicComparisons and UnramifiedFixedDepthZeroOppositeProof are byte-identical between commit fab9caea and Library commit 0b7bb3fd, and the modules cited earlier in this paragraph between Library commits 58ad0f79 and 0b7bb3fd. Follow-up (thirty-third update, Library commit b369a8f2): the theorem unramifiedFixedPairSpecialApartment (module UnramifiedFixedPairSpecialApartmentProof, first in Library commit c0c2e1210454ae2a1888a2989e3de794c1336819) proves UnramifiedFixedPairSpecialApartmentStatement. The theorem unramifiedFixedPointTransporter (module UnramifiedFixedPointTransporterProof, first in Library commit c9fdbede045511865f0ea27259a1e1a35f442905) proves UnramifiedFixedPointTransporterStatement by applying unramifiedFixedPointTransporter_of_fixedPairSpecialApartment to it. The theorem unramifiedTorusUnitFixedApartment (module UnramifiedTorusUnitFixedApartmentProof, first in Library commit d210ab55a138c1f91b826ee47c6280ce6c6b90bc) proves UnramifiedTorusUnitFixedApartmentStatement by applying unramifiedTorusUnitFixedApartmentReduction to unramifiedFixedPointTransporter, unramifiedTwistedFixedTranslation and unramifiedSplitTranslationFixer. The theorem unramifiedFixedLeviTransport (module UnramifiedFixedLeviTransportProof, first in Library commit 9e39a73d21bd6ed6fac00b01cc5e01c0db5d105b) proves UnramifiedFixedLeviTransportStatement by applying unramifiedFixedLeviTransport_of_fixedApartment_and_leviSharp to unramifiedTorusUnitFixedApartment and unramifiedLeviSharpApartmentTransport. The theorem unramifiedFixedOpposite (module UnramifiedFixedOppositeProof, first in Library commit c9fdbede045511865f0ea27259a1e1a35f442905) proves UnramifiedFixedOppositeStatement by applying unramifiedFixedOpposite_of_wallInvariance to unramifiedFixedWallInvariance_of_depthZero_of_leviTransport, applied to unramifiedFixedDepthZeroOpposite and to a proof of UnramifiedFixedLeviTransportStatement that it builds from unramifiedFixedPairSpecialApartment by the three published reductions named above. The theorem unramifiedValuationDescent (module UnramifiedValuationDescentProof, first in Library commit d210ab55a138c1f91b826ee47c6280ce6c6b90bc) proves UnramifiedValuationDescentStatement: it builds the same proof of UnramifiedFixedLeviTransportStatement and applies unramifiedValuationDescent_of_fixedLocus to unramifiedGaloisFixedApartment (Section 9.2.1 row), that proof, unramifiedFixedCentralizerCompatibility_of_leviTransport applied to it, and unramifiedFixedOpposite. So UnramifiedValuationDescentStatement is proved. Lean inspections of the six theorems are recorded below. Each module added to this row in this follow-up is byte-identical between its first commit and Library commit b369a8f2, and the modules cited earlier in this paragraph between Library commits 0b7bb3fd and b369a8f2."
      ],
      "consumer_or_regression": "The published rootValuationBuildingConstructionReduction (Theorem 9.2.7 row) derives RootValuationBuildingConstructionStatement from ValuationApartmentAxiomsExistenceStatement and three further statements. The §9.6.6 comparison feeds the derived route for Axiom 4.1.16, and the §9.8 concave function groups use this class. Regression: for the unramified quasi-split SU_3, the relative root system is BC_1, and the upstairs root restricting to 2a must be filtered at depth 2r by V 4; the uniform depth of the printed Lemma 9.6.3 display fails there.",
      "formal_status": "statement",
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
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-11 at Library commit 529b851c; kind definition; statement_returns_prop true; the module is byte-identical to its artifact."
        },
        {
          "declaration": "Langlands.Geometry.Building.UnramifiedValuationDescentStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-11 at Library commit 529b851c; kind definition; statement_returns_prop true; the module is byte-identical to commit 3c9b0579."
        },
        {
          "declaration": "Langlands.Geometry.Building.ValuationBuildingApartmentAxiomsStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-11 at Library commit 529b851c; kind definition; statement_returns_prop true; the module is byte-identical to commit 3c9b0579."
        },
        {
          "declaration": "Langlands.Geometry.Building.UnramifiedValuationDescentPackageStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-11 at Library commit 529b851c; kind definition; statement_returns_prop true; the module is byte-identical to commit 3c9b0579."
        },
        {
          "declaration": "Langlands.Geometry.Building.ValuationApartmentAxiomsExistenceReductionStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-11 at Library commit 529b851c; kind definition; statement_returns_prop true; the module is byte-identical to commit 3c9b0579."
        },
        {
          "declaration": "Langlands.Geometry.Building.valuationApartmentAxiomsExistenceReduction",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-11 at Library commit 529b851c; kind theorem; the module is byte-identical to commit 3c9b0579."
        },
        {
          "declaration": "Langlands.Geometry.Building.quasiSplitIntegerApartmentExistence",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit ed924aef; a theorem proving QuasiSplitIntegerApartmentExistenceStatement."
        },
        {
          "declaration": "Langlands.Geometry.Building.ValuationBuildingQuasiSplitAdjointTranslationStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit eded01f2; kind definition; statement_returns_prop true. The module is present in Library commit 17dd94ea."
        },
        {
          "declaration": "Langlands.Geometry.Building.QuasiSplitAdjointSimpleRootTransitivityStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 of the module as published in Library commit cfedefb6; kind definition; statement_returns_prop true."
        },
        {
          "declaration": "Langlands.Geometry.Building.valuationBuildingQuasiSplitAdjointTranslation_of_simpleRootTransitivity",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 of the module as published in Library commit cfedefb6; kind theorem, proving QuasiSplitAdjointSimpleRootTransitivityStatement → ValuationBuildingQuasiSplitAdjointTranslationStatement."
        },
        {
          "declaration": "Langlands.Geometry.Building.quasiSplitAdjointSimpleRootTransitivity",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 of the module as first published in Library commit 51e4d897; kind theorem, proving QuasiSplitAdjointSimpleRootTransitivityStatement."
        },
        {
          "declaration": "Langlands.Geometry.Building.valuationBuildingQuasiSplitAdjointTranslation",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 of the module as first published in Library commit 7f43c3c9; kind theorem, proving ValuationBuildingQuasiSplitAdjointTranslationStatement."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedValuationDescent_of_fixedLocus",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit 6948120d; kind theorem, whose type is the implication from the four fixed-locus statements to UnramifiedValuationDescentStatement; the module is byte-identical to commit cc5aa77f."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedFixedCentralizerCompatibility_of_leviTransport",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit 6948120d; kind theorem, whose type is the implication from UnramifiedFixedLeviTransportStatement to UnramifiedFixedCentralizerCompatibilityStatement; the module is byte-identical to commit 0c3f30c2."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedFixedLeviTransport_of_fixedApartment_and_leviSharp",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit 6948120d; kind theorem, proving UnramifiedFixedLeviTransportReductionStatement; the module is byte-identical to commit 73b1430a."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedLeviSharpApartmentTransport",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit 6948120d; kind theorem, proving UnramifiedLeviSharpApartmentTransportStatement; the module is byte-identical to commit 0c3f30c2."
        },
        {
          "declaration": "Langlands.Geometry.Building.UnramifiedTorusUnitFixedApartmentStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit 6948120d; kind definition; statement_returns_prop true; the module is byte-identical to commit cc5aa77f."
        },
        {
          "declaration": "Langlands.Geometry.Building.UnramifiedFixedOppositeStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit 6948120d; kind definition; statement_returns_prop true; the module is byte-identical to commit cc5aa77f."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedFixedOpposite_of_wallInvariance",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit 0f84a0d8; kind theorem, whose type is the implication from UnramifiedFixedWallInvarianceStatement to UnramifiedFixedOppositeStatement; the module is byte-identical to commit 430cc03f."
        },
        {
          "declaration": "Langlands.Geometry.Building.UnramifiedFixedWallInvarianceStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit 1bd55dea; kind definition; statement_returns_prop true; the module is byte-identical to commit 430cc03f."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedQuasiSplit_of_henselianDiscrete",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 757a6793; kind theorem, at universe level u, whose type is exactly UnramifiedQuasiSplitReductionStatement.{u}; the module is byte-identical to commit ed924aef."
        },
        {
          "declaration": "Langlands.GroupScheme.henselianDiscreteQuasiSplit",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 757a6793; kind theorem, at universe level u, whose type is exactly HenselianDiscreteQuasiSplitStatement.{u}; the module is byte-identical to commit 410c7947, which first published it."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedFixedWallInvariance_of_depthZero_of_leviTransport",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit c40a0134; kind theorem, at universe level u, whose type is exactly UnramifiedFixedWallInvarianceReductionStatement.{u}; the module is byte-identical to commit 85c2fe71, which first published it."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedTorusUnitFixedApartmentReduction",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit c40a0134; kind theorem, at universe level u, whose type is exactly UnramifiedTorusUnitFixedApartmentReductionStatement.{u}; the module is byte-identical to commit 4f6abf4c, which first published it."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedSplitTranslationFixer",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit c40a0134; kind theorem, at universe level u, whose type is exactly UnramifiedSplitTranslationFixerStatement.{u}; the module was first published in this commit."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedFixedPointTransporter_of_fixedPairSpecialApartment",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit c40a0134; kind theorem, at universe level u, whose type is the implication from UnramifiedFixedPairSpecialApartmentStatement to UnramifiedFixedPointTransporterStatement; the module was first published in this commit."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedFixedDepthZeroOpposite_of_recoveredParabolicModels",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit c40a0134; kind theorem, at universe level u, whose type is exactly UnramifiedRecoveredDepthZeroOppositeReductionStatement.{u}; the module was first published in this commit."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedTwistedFixedTranslation",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 4f4af6ba; kind theorem, at universe level u, whose type is exactly UnramifiedTwistedFixedTranslationStatement.{u}; the module is byte-identical to commit b3a1bdaf, which first published it."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.integralOppositeFactors",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 58ad0f79; kind theorem, at universe level u, whose type is exactly IntegralModels.IntegralOppositeFactorsStatement.{u}; the module is byte-identical to commit af5d652c, which first published it."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedFixedRecoveredParabolicModels",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit fab9caea; kind theorem, at universe level u, whose type is exactly UnramifiedFixedRecoveredParabolicModelsStatement.{u}; the module was first published in that commit and is byte-identical at Library commit 0b7bb3fd."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedFixedDepthZeroOpposite",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit fab9caea; kind theorem, at universe level u, whose type is exactly UnramifiedFixedDepthZeroOppositeStatement.{u}; the module was first published in that commit and is byte-identical at Library commit 0b7bb3fd."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedFixedPairSpecialApartment",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit fcb85a7e; kind theorem, at universe level u, whose type is exactly UnramifiedFixedPairSpecialApartmentStatement.{u}; the module was first published in Library commit c0c2e121 and is byte-identical between that commit and Library commit b369a8f2."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedFixedPointTransporter",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit fcb85a7e; kind theorem, at universe level u, whose type is exactly UnramifiedFixedPointTransporterStatement.{u}; the module was first published in Library commit c9fdbede and is byte-identical between that commit and Library commit b369a8f2."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedTorusUnitFixedApartment",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit fcb85a7e; kind theorem, at universe level u, whose type is exactly UnramifiedTorusUnitFixedApartmentStatement.{u}; the module was first published in Library commit d210ab55 and is byte-identical between that commit and Library commit b369a8f2."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedFixedLeviTransport",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit fcb85a7e; kind theorem, at universe level u, whose type is exactly UnramifiedFixedLeviTransportStatement.{u}; the module was first published in Library commit 9e39a73d and is byte-identical between that commit and Library commit b369a8f2."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedFixedOpposite",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit fcb85a7e; kind theorem, at universe level u, whose type is exactly UnramifiedFixedOppositeStatement.{u}; the module was first published in Library commit c9fdbede and is byte-identical between that commit and Library commit b369a8f2."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedValuationDescent",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit 8f4a33d7; kind theorem, at universe level u, whose type is exactly UnramifiedValuationDescentStatement.{u}; the module was first published in Library commit d210ab55 and is byte-identical between that commit and Library commit b369a8f2."
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
        "Langlands.Geometry.Building.CentralizerFiltrationDoubleRootExistenceStatement",
        "Langlands.Geometry.Building.centralizerFiltrationExistence",
        "Langlands.Geometry.Building.centralizerFiltrationDoubleRootExistence",
        "Langlands.Geometry.Building.MaximalUnramified.localMoyPrasadGroupProperties",
        "Langlands.Geometry.Building.quasiSplitValuedRankOneCoordinates",
        "Langlands.Geometry.Building.kpLocalDoubleRootCommutator",
        "Langlands.Geometry.Building.unramifiedDoubledRootDepthModel",
        "Langlands.Geometry.Building.unramifiedComparisonRootField",
        "Langlands.Geometry.Building.unramifiedComparisonExistence",
        "Langlands.Geometry.Building.unramifiedRationalMoyPrasad"
      ],
      "modules": [
        "Langlands.Geometry.Building.CentralizerFiltrationExistenceStatement",
        "Langlands.Geometry.Building.KPMoyPrasadDoubleRootStatement",
        "Langlands.Geometry.Building.CentralizerFiltrationExistenceProof",
        "Langlands.Geometry.Building.KPDoubleRootFiltrationExistence",
        "Langlands.Geometry.Building.KPLocalMoyPrasadGroupPropertiesProof",
        "Langlands.Geometry.Building.QuasiSplitValuedRankOneCoordinatesProof",
        "Langlands.Geometry.Building.KPLocalDoubleRootCommutatorProof",
        "Langlands.Geometry.Building.UnramifiedDoubledRootDepthModelProof",
        "Langlands.Geometry.Building.KPUnramifiedComparisonRootFieldProof",
        "Langlands.Geometry.Building.KPUnramifiedComparisonExistenceProof",
        "Langlands.Geometry.Building.KPUnramifiedRationalMoyPrasadProof"
      ],
      "dependencies": [
        "Source proof: Z(k)_0 = Z(k)^0 from Z(K)_{x,0} ⊆ Z(K)^0 and the action of Z(k) on B(Z) = {x}. Commutator friendliness uses a special k-torus of Z containing S (Proposition 9.3.4), Lemma 9.6.3, Lemma 7.1.2 and V 3 for Z_K, Lemma 7.2.3 and Lemma 8.5.19, with the corrected projection B(G)^M → B(Z) of (9.7.1) and Corollary 9.7.3.",
        "Double-root existence (derived in the KPMoyPrasadDoubleRootStatement Markdown, not written out by KP): for quasi-split G_K, Lemma 7.2.3 and functoriality reduce to SU_3, whose formula gives Z-component depth 2(φ_a(u) + φ_{-a}(u')). For general G, translate to the point y with y_{-a}(u') = 0 (Z(k)_r does not depend on the point); with the bound, the argument of Proposition 7.3.17 makes G(K)_{y,2r} normal in G(K)_{y,0}, and the Iwahori decomposition with Lemma 8.5.19 puts the Z-component in Z(K)_{y,2r}, as in the proof of Lemma 9.8.1.",
        "Reduction (14 November 2026): published theorems reduce both existence statements of this row to two unproved statements. The first is MaximalUnramified.LocalMoyPrasadGroupPropertiesStatement (module Langlands.Geometry.Building.KPLocalMoyPrasadGroupProperties, first in Library commit 51e4d8972659f1ffcf0ca89e8eee9540a30b52d3), the eight group properties of the Moy–Prasad groups G(K)_{x,r} over K, the maximal unramified extension (KP Proposition 7.3.17, Lemma 7.3.16, Lemma 8.5.19, Proposition 13.2.5(4) over K). The second is UnramifiedComparisonExistenceStatement (module Langlands.Geometry.Building.KPUnramifiedComparisonExistenceStatement, first in Library commit 85c2fe719cf62e96f22aaf4ca03961c5814d086b): for every P satisfying the apartment axioms there are building data B over K whose centralizer Z is a torus (hZ) and an apartment map e with P.IsUnramifiedComparison B hZ e (KP Construction 9.6.1, Lemma 9.6.3, Theorem 9.6.5, §9.8.2). The theorem unramifiedRationalMoyPrasad_of_unramifiedComparison (module Langlands.Geometry.Building.KPUnramifiedMoyPrasadComparison, first in Library commit 0c3f30c24701c74d5474fca3fbb5324a99aa1d58) derives UnramifiedRationalMoyPrasadStatement (module Langlands.Geometry.Building.KPUnramifiedRationalMoyPrasadStatement, first in Library commit 51e4d8972659f1ffcf0ca89e8eee9540a30b52d3) from these two. For each P satisfying the apartment axioms that statement gives a rational Moy–Prasad family, the preimages in G(F) of the groups G(K)_{e(y),r}, and the theorem ParahoricBuildingData.exists_doubleRootFriendly_filtration_of_rationalMoyPrasadFamily (module Langlands.Geometry.Building.KPRationalMoyPrasadFamily, first in Library commit cc5aa77fa8dbdc6e723091c7b710ab0d81162c4e) turns it into a filtration with the conclusion of CentralizerFiltrationDoubleRootExistenceStatement, which implies CentralizerFiltrationExistenceStatement by dropping a conjunct. No published theorem states the composite implication; it was checked with a separate Lean check (Library commit 410c7947, only propext, Classical.choice and Quot.sound). Each module cited in this entry with a first commit is byte-identical between that commit and Library commit 410c7947. Twentieth update (14 November 2026): the second statement is reduced further. The theorem unramifiedComparisonExistence_of_fields (module Langlands.Geometry.Building.KPUnramifiedComparisonFieldStatements, first in Library commit c40a01345b2f4172fa41e07ff31644b40e695003) derives UnramifiedComparisonExistenceStatement from SpecialTorusExistenceStatement (Proposition 9.3.4 row), UnramifiedValuationDescentStatement (Theorem 9.6.5 row) and four field statements of the same module: UnramifiedComparisonRootFieldStatement, UnramifiedComparisonLeviFieldStatement, UnramifiedComparisonZeroFieldStatement and UnramifiedComparisonOpenFieldStatement. Each of the four quantifies over P satisfying the apartment axioms, a comparison torus t : P.UnramifiedComparisonTorus and an apartment lift L : t.ApartmentLift, and asserts one field of P.IsUnramifiedComparison: the root comparison, the Levi field, the comparison of zero subgroups and openness. The theorem takes the lift from exists_unramifiedApartmentLift (module Langlands.Geometry.Building.KPUnramifiedApartmentLift, first in Library commit e5365902d74534dbf1622c06e695dffdc128d723), which assumes the special-torus and descent statements, and the remaining field apartmentMap_smul from L.normalizer. A Lean inspection on 2026-11-14 at Library commit c40a0134 reports kind theorem at universe level u and only propext, Classical.choice and Quot.sound. So both existence statements of this row follow from LocalMoyPrasadGroupPropertiesStatement, SpecialTorusExistenceStatement, UnramifiedValuationDescentStatement and the four field statements; this composite was checked with a separate Lean check (Library commit c40a0134, only propext, Classical.choice and Quot.sound). None of these seven statements was proved at Library commit c40a0134. Two prerequisite statements of this chain are first in Library commit c40a0134 and were unproved there: MaximalUnramified.LocalMoyPrasadPositiveProductStatement (module Langlands.Geometry.Building.KPLocalMoyPrasadPositiveProductStatement), the positive-depth product cover of the groups G(K)_{x,r}, and QuasiSplitValuedRankOneCoordinatesStatement (module Langlands.Geometry.Building.QuasiSplitValuedRankOneCoordinatesStatement), coherent rank-one coordinates over K for the torus-filtration statements. The statements of the doubled-root commutator bound over K and of the depth-zero cases of the group properties are not in Library commit c40a0134. The modules KPUnramifiedApartmentLift and those cited earlier in this entry are byte-identical between their first commits and Library commit c40a0134. Twenty-second update (14 November 2026): the theorem unramifiedComparisonLeviField (module Langlands.Geometry.Building.KPUnramifiedComparisonLeviFieldProof, first in Library commit ba00e0970dd9ba6222ccc056ca2ee7f06bcc8181) proves UnramifiedComparisonLeviFieldStatement. A Lean inspection on 2026-11-14 at Library commit 4f4af6ba reports kind theorem at universe level u, type exactly UnramifiedComparisonLeviFieldStatement.{u}, and only propext, Classical.choice and Quot.sound. With the Theorem 9.6.5 row, both existence statements of this row therefore follow from LocalMoyPrasadGroupPropertiesStatement, SpecialTorusExistenceStatement, UnramifiedFixedPairSpecialApartmentStatement, UnramifiedFixedDepthZeroOppositeStatement, UnramifiedComparisonRootFieldStatement, UnramifiedComparisonZeroFieldStatement and UnramifiedComparisonOpenFieldStatement; this composite was checked with a separate Lean check (Library commit 4f4af6ba, only propext, Classical.choice and Quot.sound). None of these seven statements is proved at Library commit 4f4af6ba. Of the prerequisites named above, MaximalUnramified.LocalMoyPrasadPositiveProductStatement is proved by the theorem MaximalUnramified.localMoyPrasadPositiveProduct (module Langlands.Geometry.Building.KPLocalMoyPrasadPositiveProductProof, first in Library commit ba00e0970dd9ba6222ccc056ca2ee7f06bcc8181); a Lean inspection on 2026-11-14 at Library commit 4f4af6ba reports kind theorem at universe level u, type exactly MaximalUnramified.LocalMoyPrasadPositiveProductStatement.{u}, and only propext, Classical.choice and Quot.sound. QuasiSplitValuedRankOneCoordinatesStatement is unproved. The statements of the doubled-root commutator bound and of the depth-zero cases are first in Library commit b3a1bdaf15715f16a43643513b7cbb6cbb58ef3a: KPLocalDoubleRootCommutatorStatement (module Langlands.Geometry.Building.KPLocalDoubleRootCommutatorStatement) puts the Z(K)-component of the commutator of opposite root-group elements of total depth r > 0 in Z(K)_{2r} when one of them lies in a doubled-root group, and MaximalUnramified.LocalMoyPrasadDepthZeroStatement (module Langlands.Geometry.Building.KPLocalMoyPrasadDepthZeroStatement) states KP Proposition 7.3.12 and Lemma 8.5.19 at depth zero for the intersections of G(K)_{x,0} with the positive-root subgroups and with the Levi subgroups M_ν(K). Neither is proved at Library commit 4f4af6ba. The four modules cited in this update are byte-identical between their first commits and Library commit 4f4af6ba, and the modules cited earlier in this entry are byte-identical between Library commits c40a0134 and 4f4af6ba. Follow-up (twenty-second update, Library commit 58ad0f79): the theorem unramifiedComparisonOpenField (module Langlands.Geometry.Building.KPUnramifiedComparisonOpenProof, first in Library commit af5d652c2f2ff5b35b4ce4dbbf7cbec8bbf3e99e) proves UnramifiedComparisonOpenFieldStatement. A Lean inspection on 2026-11-14 at Library commit 58ad0f79 reports kind theorem at universe level u, type exactly UnramifiedComparisonOpenFieldStatement.{u}, and only propext, Classical.choice and Quot.sound. The theorem unramifiedComparisonRootField_of_doubledRootDepthModel (module Langlands.Geometry.Building.KPUnramifiedComparisonRootReduction, first in the same commit) derives UnramifiedComparisonRootFieldStatement from UnramifiedDoubledRootDepthModelStatement (module Langlands.Geometry.Building.UnramifiedDoubledRootDepthModelStatement, first in the same commit). That statement asks, for every apartment lift, lower apartment point y, lower root a whose double is a root, closed representative of the root subgroup of 2a and depth s ≥ 0, for a smooth integral model over the integers of F with connected special fibre whose integral points over the maximal unramified extension K are exactly the K-points of the depth-s subgroup generated by the upper root filtrations over the multiples of 2a. A Lean inspection on 2026-11-14 at Library commit 58ad0f79 reports kind theorem at universe level u, a type that is the implication from UnramifiedDoubledRootDepthModelStatement to UnramifiedComparisonRootFieldStatement, and only propext, Classical.choice and Quot.sound. With the Theorem 9.6.5 row, where IntegralOppositeFactorsStatement is now proved, both existence statements of this row follow from six statements: LocalMoyPrasadGroupPropertiesStatement, SpecialTorusExistenceStatement, UnramifiedFixedPairSpecialApartmentStatement, UnramifiedFixedDepthZeroOppositeStatement, UnramifiedComparisonRootFieldStatement and UnramifiedComparisonZeroFieldStatement. They also follow when UnramifiedFixedRecoveredParabolicModelsStatement replaces the fourth and UnramifiedDoubledRootDepthModelStatement the fifth. No published declaration states these composites; both were checked with a separate Lean check (Library commit 58ad0f79, only propext, Classical.choice and Quot.sound). None of the six statements or of the two replacements is proved at Library commit 58ad0f79. The three modules cited in this follow-up are byte-identical between commit af5d652c and Library commit 58ad0f79, and the modules cited earlier in this entry are byte-identical between Library commits 4f4af6ba and 58ad0f79. Follow-up (twenty-fourth update, Library commit 7229bb45): the theorem unramifiedComparisonZeroField (module Langlands.Geometry.Building.KPUnramifiedComparisonZeroFieldProof, first in Library commit 7f5b5f04a855fc0b4671393213c87415a6ee2aaf) proves UnramifiedComparisonZeroFieldStatement. A Lean inspection on 2026-11-14 at Library commit 320321b3 reports kind theorem at universe level u, type exactly UnramifiedComparisonZeroFieldStatement.{u}, and only propext, Classical.choice and Quot.sound. Three of the four field statements are now proved; UnramifiedComparisonRootFieldStatement remains. So both existence statements of this row follow from five statements: LocalMoyPrasadGroupPropertiesStatement, SpecialTorusExistenceStatement, UnramifiedFixedPairSpecialApartmentStatement, UnramifiedFixedDepthZeroOppositeStatement and UnramifiedComparisonRootFieldStatement. They also follow when UnramifiedFixedRecoveredParabolicModelsStatement replaces the fourth and UnramifiedDoubledRootDepthModelStatement the fifth. No published declaration states these composites; they were checked with separate Lean checks (Library commit 7229bb45, only propext, Classical.choice and Quot.sound). The theorem MaximalUnramified.localMoyPrasadDepthZero (module Langlands.Geometry.Building.KPLocalMoyPrasadDepthZeroProof, first in Library commit aeb3911c4e1bf6e3a2f653e874e4ebc422d2a61a) proves MaximalUnramified.LocalMoyPrasadDepthZeroStatement, the depth-zero statement recorded above. Its proof does not follow KP: it uses published results over K on root groups, the Levi sharp transport, the affine Weyl group and G(K)^0, and supplies the published theorem MaximalUnramified.simplyConnectedNormalizerAffineWeyl to the one imported result that takes SimplyConnectedNormalizerAffineWeylStatement as an argument. A Lean inspection on 2026-11-15 at Library commit 51e9457f reports kind theorem at universe level u, type exactly MaximalUnramified.LocalMoyPrasadDepthZeroStatement.{u}, and only propext, Classical.choice and Quot.sound. LocalMoyPrasadGroupPropertiesStatement itself is unproved. The theorem kpLocalDoubleRootCommutator_of_valuedRankOneCoordinates (module Langlands.Geometry.Building.RankOneDoubledInputCoroot, whose entry declaration is the definition DoubledInputCommutatorProperty, first in Library commit 7f5b5f04a855fc0b4671393213c87415a6ee2aaf) derives KPLocalDoubleRootCommutatorStatement, the doubled-root statement recorded above, from QuasiSplitValuedRankOneCoordinatesStatement. A Lean inspection on 2026-11-14 at Library commit 320321b3 reports kind theorem at universe level u, a type that is the implication from QuasiSplitValuedRankOneCoordinatesStatement to KPLocalDoubleRootCommutatorStatement, and only propext, Classical.choice and Quot.sound. None of the five statements, the two replacements, QuasiSplitValuedRankOneCoordinatesStatement and KPLocalDoubleRootCommutatorStatement is proved at Library commit 7229bb45. The modules KPUnramifiedComparisonZeroFieldProof and RankOneDoubledInputCoroot are byte-identical between commit 7f5b5f04 and Library commit 7229bb45, the module KPLocalMoyPrasadDepthZeroProof between commit aeb3911c and Library commit 7229bb45, and the modules cited earlier in this entry between Library commits 58ad0f79 and 7229bb45. Follow-up (twenty-sixth update, Library commit 0b7bb3fd): two of the five statements above are proved: SpecialTorusExistenceStatement by the theorem specialTorusExistence (Proposition 9.3.4 row) and UnramifiedFixedDepthZeroOppositeStatement by the theorem unramifiedFixedDepthZeroOpposite (Theorem 9.6.5 row). The alternative to the fourth, UnramifiedFixedRecoveredParabolicModelsStatement, is also proved, by the theorem unramifiedFixedRecoveredParabolicModels (Theorem 9.6.5 row). So both existence statements of this row follow from three statements: LocalMoyPrasadGroupPropertiesStatement, UnramifiedFixedPairSpecialApartmentStatement and UnramifiedComparisonRootFieldStatement; they also follow when UnramifiedDoubledRootDepthModelStatement replaces the third. No published declaration states these composites; they were checked with separate Lean checks (Library commit fab9caea, only propext, Classical.choice and Quot.sound). None of these four statements is proved at Library commit 0b7bb3fd. The modules cited earlier in this entry are byte-identical between Library commits 7229bb45 and 0b7bb3fd. Follow-up (thirty-third update, Library commit b369a8f2): the four statements named in the previous follow-up are proved. UnramifiedFixedPairSpecialApartmentStatement is proved by unramifiedFixedPairSpecialApartment and UnramifiedValuationDescentStatement by unramifiedValuationDescent (Theorem 9.6.5 row). The theorem MaximalUnramified.localMoyPrasadGroupProperties (module Langlands.Geometry.Building.KPLocalMoyPrasadGroupPropertiesProof, first in Library commit a98af0ff45faf7905209f65d641389deee5d8392) proves MaximalUnramified.LocalMoyPrasadGroupPropertiesStatement by applying the published theorem MaximalUnramified.localMoyPrasadGroupProperties_of_torus_filtration (module Langlands.Geometry.Building.KPLocalMoyPrasadGroupPropertiesReduction) to quasiSplitLocalTorusFiltration (module Langlands.Geometry.Building.KPQuasiSplitLocalTorusFiltrationProof); that reduction uses MaximalUnramified.localMoyPrasadPositiveProduct, MaximalUnramified.localMoyPrasadDepthZero and kpLocalDoubleRootCommutator_of_valuedRankOneCoordinates applied to quasiSplitValuedRankOneCoordinates. The theorem quasiSplitValuedRankOneCoordinates (module Langlands.Geometry.Building.QuasiSplitValuedRankOneCoordinatesProof, first in Library commit e4a9b4d0164a5e0a9828dcaec5fa1cb7837ff8c6) proves QuasiSplitValuedRankOneCoordinatesStatement, and the theorem kpLocalDoubleRootCommutator (module Langlands.Geometry.Building.KPLocalDoubleRootCommutatorProof, first in Library commit e9c05be9da1000900a43de75ec2ede66892aa158) proves KPLocalDoubleRootCommutatorStatement by applying kpLocalDoubleRootCommutator_of_valuedRankOneCoordinates to it. The theorem unramifiedDoubledRootDepthModel (module Langlands.Geometry.Building.UnramifiedDoubledRootDepthModelProof, first in Library commit c0c2e1210454ae2a1888a2989e3de794c1336819) proves UnramifiedDoubledRootDepthModelStatement, and the theorem unramifiedComparisonRootField (module Langlands.Geometry.Building.KPUnramifiedComparisonRootFieldProof, first in Library commit c9fdbede045511865f0ea27259a1e1a35f442905) proves UnramifiedComparisonRootFieldStatement by applying unramifiedComparisonRootField_of_doubledRootDepthModel to it. The theorem unramifiedComparisonExistence (module Langlands.Geometry.Building.KPUnramifiedComparisonExistenceProof, first in Library commit 9e39a73d21bd6ed6fac00b01cc5e01c0db5d105b) proves UnramifiedComparisonExistenceStatement by applying unramifiedComparisonExistence_of_fields to specialTorusExistence, unramifiedValuationDescent and the four field proofs unramifiedComparisonRootField, unramifiedComparisonLeviField, unramifiedComparisonZeroField and unramifiedComparisonOpenField. The theorem centralizerFiltrationDoubleRootExistence (module Langlands.Geometry.Building.KPDoubleRootFiltrationExistence, first in Library commit 9e39a73d21bd6ed6fac00b01cc5e01c0db5d105b) proves CentralizerFiltrationDoubleRootExistenceStatement: it applies unramifiedComparisonExistence_of_fields to the same six proofs, unramifiedRationalMoyPrasad_of_unramifiedComparison to MaximalUnramified.localMoyPrasadGroupProperties and the result, and, for each P satisfying the apartment axioms, ParahoricBuildingData.exists_doubleRootFriendly_filtration_of_rationalMoyPrasadFamily to the rational Moy–Prasad family so obtained. The intermediate statement of that composite, UnramifiedRationalMoyPrasadStatement, is now also proved: the theorem unramifiedRationalMoyPrasad (module Langlands.Geometry.Building.KPUnramifiedRationalMoyPrasadProof, first in Library commit f24f97443f21ff7e59b1cf3b509602157dae54c2) applies unramifiedRationalMoyPrasad_of_unramifiedComparison to MaximalUnramified.localMoyPrasadGroupProperties and unramifiedComparisonExistence. Like the two existence statements of this row, it quantifies over supplied P satisfying the apartment axioms. The theorem centralizerFiltrationExistence (module Langlands.Geometry.Building.CentralizerFiltrationExistenceProof, first in Library commit f24f97443f21ff7e59b1cf3b509602157dae54c2) proves CentralizerFiltrationExistenceStatement: it applies centralizerFiltrationExistence_of_doubleRoot, of the same module, which drops the conjunct IsDoubleRootCommutatorFriendly, to centralizerFiltrationDoubleRootExistence. Both statements quantify over supplied building data P satisfying the apartment axioms, which are not constructed in general, so the formal status of this row is now conditional. Lean inspections of the nine theorems added to this row in this follow-up are recorded below. Each module added to this row in this follow-up is byte-identical between its first commit and Library commit b369a8f2, and the modules cited earlier in this entry between Library commits 0b7bb3fd and b369a8f2."
      ],
      "consumer_or_regression": "Supplies the Zf premise of the published MoyPrasadFiltrationStatement and its four conjuncts (Proposition 13.2.5 row): with proofs of these, the Moy–Prasad results would hold for every P satisfying the apartment axioms without a supplied filtration. The concave function groups G(k)_{x,f} of §9.8.2. Regression: the conclusion fixes only the listed axioms, so different admissible filtrations of tori give different witnesses; a consumer must not assume KP's particular filtration. The double-root existence statement supplies the extra premise of MoyPrasadDoubleRootStatement.",
      "formal_status": "conditional",
      "publication_commits": [
        "3c9b0579a8f2d36d16294ce48b465d1ec5aee273",
        "297a8ef0ba780a488196cf62285af3ded2e2baa6",
        "9e39a73d21bd6ed6fac00b01cc5e01c0db5d105b",
        "f24f97443f21ff7e59b1cf3b509602157dae54c2"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.CentralizerFiltrationExistenceStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-11 at Library commit 529b851c; kind definition; statement_returns_prop true; the module is byte-identical to commit 3c9b0579."
        },
        {
          "declaration": "Langlands.Geometry.Building.CentralizerFiltrationDoubleRootExistenceStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-12 at Library commit 16c60abd; kind definition; statement_returns_prop true; the module is byte-identical to commit 297a8ef0."
        },
        {
          "declaration": "Langlands.Geometry.Building.centralizerFiltrationExistence",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit b369a8f2; kind theorem, at universe level u, whose type is exactly CentralizerFiltrationExistenceStatement.{u}; the module was first published in Library commit f24f9744 and is byte-identical between that commit and Library commit b369a8f2."
        },
        {
          "declaration": "Langlands.Geometry.Building.centralizerFiltrationDoubleRootExistence",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit 8f4a33d7; kind theorem, at universe level u, whose type is exactly CentralizerFiltrationDoubleRootExistenceStatement.{u}; the module was first published in Library commit 9e39a73d and is byte-identical between that commit and Library commit b369a8f2."
        },
        {
          "declaration": "Langlands.Geometry.Building.MaximalUnramified.localMoyPrasadGroupProperties",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit 8f4a33d7; kind theorem, at universe level u, whose type is exactly MaximalUnramified.LocalMoyPrasadGroupPropertiesStatement.{u}; the module was first published in Library commit a98af0ff and is byte-identical between that commit and Library commit b369a8f2."
        },
        {
          "declaration": "Langlands.Geometry.Building.quasiSplitValuedRankOneCoordinates",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit fcb85a7e; kind theorem, at universe level u, whose type is exactly QuasiSplitValuedRankOneCoordinatesStatement.{u}; the module was first published in Library commit e4a9b4d0 and is byte-identical between that commit and Library commit b369a8f2."
        },
        {
          "declaration": "Langlands.Geometry.Building.kpLocalDoubleRootCommutator",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit fcb85a7e; kind theorem, at universe level u, whose type is exactly KPLocalDoubleRootCommutatorStatement.{u}; the module was first published in Library commit e9c05be9 and is byte-identical between that commit and Library commit b369a8f2."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedDoubledRootDepthModel",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit fcb85a7e; kind theorem, at universe level u, whose type is exactly UnramifiedDoubledRootDepthModelStatement.{u}; the module was first published in Library commit c0c2e121 and is byte-identical between that commit and Library commit b369a8f2."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedComparisonRootField",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit fcb85a7e; kind theorem, at universe level u, whose type is exactly UnramifiedComparisonRootFieldStatement.{u}; the module was first published in Library commit c9fdbede and is byte-identical between that commit and Library commit b369a8f2."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedComparisonExistence",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit 8f4a33d7; kind theorem, at universe level u, whose type is exactly UnramifiedComparisonExistenceStatement.{u}; the module was first published in Library commit 9e39a73d and is byte-identical between that commit and Library commit b369a8f2."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedRationalMoyPrasad",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit b369a8f2; kind theorem, at universe level u, whose type is exactly UnramifiedRationalMoyPrasadStatement.{u}; the module was first published in Library commit f24f9744 and is byte-identical between that commit and Library commit b369a8f2."
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
        "Recorded Lean scope (partial definition): for supplied P : ParahoricBuildingData G over a nonarchimedean local field, P.normalizerZero is the image of P.centralizerZero (the actual Z(F)^0) in normalizerPoints P.i = N(F), and P.IwahoriWeylGroup := normalizerPoints P.i ⧸ P.normalizerZero is Wtilde^0 as a coset type. Its group structure is used under the instance argument [P.normalizerZero.Normal]. Since Library commit e449cde988d4e97ab280b8d4d11262887ccc26e0 that normality is proved for every supplied P: ParahoricBuildingData.normal_normalizerZero (module ZeroSubgroupCommutatorNormality) proves that P.zeroSubgroup = G(F)^0 is normal in G(F), because commutators of G(F) lie in G(F)^♮, and concludes through normalizerZero_normal_of_zeroSubgroup_normal and the published cover comparison. The earlier conditional routes (normalizerZero_normal from UnramifiedZeroPointsIndependenceStatement, normalizerZero_normal_of_unipotentNormalizerCoset) remain. The premise of the first is proved: Langlands.Geometry.Building.unramifiedZeroPointsIndependence (module Langlands.Geometry.Building.UnramifiedZeroIndependenceProof, first published in Library commit db8d6b3d466f2fd453a4df4624ce6c90db8eed46) proves UnramifiedZeroPointsIndependenceStatement, the independence part of KP Lemma 2.6.24 (printed p.104 / PDF p.135) for Definition 2.6.23(1) over K = UnramifiedClosure F: any two data E, E' : UnramifiedZeroDatum F H for a group scheme H over K, which may differ in the torus, its splitting field and the simply connected cover, give the same subgroup E.zeroPoints = H(K)^♮ · T(K)^0. So normalizerZero_normal also proves the normality without a premise. The Theorem 7.8.1 statements also assert it as a conclusion. AffineRootSystem.affineWeylGroup P.affineRoots is W_aff, the subgroup of affine automorphisms of the apartment generated by the affine root reflections. P.affinePart is the separate image of N(F) ∩ G(F)^0 in Wtilde^0. Its identification with W_aff is part of IwahoriWeylExactSequence, not of a definition. P.toComponents is the map Wtilde^0 → G(F)/G(F)^0. Wtilde^1=N(k)/Z(k)^1, the adjoint group Wtilde_ad and the maps Wtilde^0→Wtilde^1→Wtilde_ad are not formalized. The definition status of this row covers only Wtilde^0, W_aff and the affine part."
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
      "publication_commits": [
        "c4a16df784376405a45b60df82583e8c26d8a4e3",
        "e449cde988d4e97ab280b8d4d11262887ccc26e0",
        "db8d6b3d466f2fd453a4df4624ce6c90db8eed46"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.IwahoriWeylGroup",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-08 at Library commit c4a16df7."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.affinePart",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-08 at Library commit c4a16df7."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.normal_normalizerZero",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-10 at Library commit e449cde9; a theorem from a supporting module, which is listed for this theorem only."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedZeroPointsIndependence",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 20f83141; kind theorem; the module is byte-identical to commit db8d6b3d, its first publication."
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
        "Proof: leviApartmentRestriction (module LeviApartmentRestrictionProof), present in Library commit ed924aef420de137b4cbaa3b063a3618afcd73fd. It presents M_J as the dynamic centralizer of one cocharacter of S (StandardLeviSplitComponent.exists_standardLevi_eq_dynamicCentralizer) and takes DM to be the published restricted class leviRestrictedApartmentData (module Langlands.BruhatTits.SpecialCompact.LeviApartmentRestriction), whose projection gives the first two clauses. For the fibre clause, restriction commutes with translations, and the valuation stabilizer criterion IsRootDatumValuation.vadd_eq_self_iff, which rests on axiom V 0, replaces the source's dimension count."
      ],
      "consumer_or_regression": "Section 6.7.2 special points; Levi inheritance of special compact subgroups (Langlands.BruhatTits.SpecialCompact.AvailableSpecialLeviCompactStatement, proved by availableSpecialLeviCompact in module AvailableSpecialLeviCompactProof, present in Library commit ed924aef420de137b4cbaa3b063a3618afcd73fd) for Renard V.5.1(5). The published theorem Langlands.BruhatTits.SpecialCompact.exists_leviRestriction_of_omegaCompatible (module LeviApartmentComparison) takes LeviApartmentRestrictionStatement as a premise and gives every point of an ω-compatible class a restriction in any supplied ω-compatible standard-Levi class at the same torus. The published statement Langlands.Geometry.Building.LeviApartmentAxiomsInheritanceStatement of this program (first in Library commit 8c11c93f98b439395e0e7da779c98bb27e24bd6d) asserts that V 7 and AS 2–AS 5 pass from D to a standard-Levi class DM related to D by some restriction pair. It is proved by leviApartmentAxiomsInheritance (module LeviApartmentAxiomsInheritanceProof), present in Library commit ed924aef420de137b4cbaa3b063a3618afcd73fd and inspected on 13 November 2026 (axioms propext, Classical.choice, Quot.sound).",
      "formal_status": "conditional",
      "publication_commits": [
        "d39b5aee822fe2ad1aadf07861ebd9a4c2df62a8",
        "ed924aef420de137b4cbaa3b063a3618afcd73fd"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.LeviApartmentRestrictionStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-10 at Library commit e7487341; statement_returns_prop true."
        },
        {
          "declaration": "Langlands.Geometry.Building.leviApartmentRestriction",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit ed924aef; a theorem."
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
        "Proof: leviSpecialPointRestriction (module LeviSpecialPointRestrictionProof), present in Library commit ed924aef420de137b4cbaa3b063a3618afcd73fd. One restriction pair identifies DM with the restricted class of Lemma 6.7.1, and every restriction of x is then its projection. The affine-root clauses pull Levi affine roots back along the projection (leviAffineRootPullback, module Langlands.BruhatTits.SpecialCompact.LeviAffineRoots), and specialness of the image is isSpecialPoint_leviApartmentProjection (module LeviSpecialPoint), as in the source. For the vertex clause the proof does not use AS 3, which is not a premise. Axiom V 0 and root doubling show that every root direction occurs, up to a nonzero factor, as the derivative of an affine root of DM; the argument of Proposition 1.3.43(3) then makes a special point a vertex."
      ],
      "consumer_or_regression": "Special vertices of Levi data for AvailableSpecialLeviCompactStatement (proved by availableSpecialLeviCompact) and Renard V.5.1(5). Regression: the image of a non-special vertex need not be a vertex.",
      "formal_status": "conditional",
      "publication_commits": [
        "d39b5aee822fe2ad1aadf07861ebd9a4c2df62a8",
        "ed924aef420de137b4cbaa3b063a3618afcd73fd"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.LeviSpecialPointRestrictionStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-10 at Library commit e7487341; statement_returns_prop true."
        },
        {
          "declaration": "Langlands.Geometry.Building.leviSpecialPointRestriction",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit ed924aef; a theorem."
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
        "Recorded Lean scope: AvailableCartanStatement quantifies over every nonarchimedean local field F of either characteristic in universe u, every group scheme G over Spec F with hG : IsConnectedReductive G, and every KPBuildingAssignment 𝔅 with 𝔅.IsAvailableFor F G hG (the full corrected Definition 4.1.26 at this F and G; global IsValid is not assumed). With B := (𝔅.datum F G hG).base it takes every cocharacter nu generic for B.i, whose positive relative roots are Phi^+, and every x : B.Apartment with B.apartment.IsSpecialApartmentVertex x. It concludes ParahoricCartanConclusions B nu x for P_x = B.parahoricAt x, j the point map of the centralizer B.centralizer.j and D = parahoricDominantSet B nu = {z ∈ Z(F) | 0 ≤ a(omega_Z(z)) for every a ∈ positiveRelativeRoots B.i nu}. The three conclusions are Set.univ = P_x · j(D) · P_x as pointwise set products; for z, z' ∈ D, equality of the double cosets of j(z) and j(z') iff z' z^(-1) ∈ B.centralizerZero; and bijectivity of parahoricDominantDoubleCosetMap B nu x from ParahoricDominantQuotient B nu (D modulo the restricted right relation by Z(F)^0) onto P_x\\G(F)/P_x. The source's Henselian discretely valued fields with perfect residue field are specialized to nonarchimedean local fields. Existence of an available assignment is not asserted. The theorem availableCartan (module Langlands.BruhatTits.Cartan.AvailableCartanProof) proves AvailableCartanStatement; it first appeared in Library commit d39b5aee822fe2ad1aadf07861ebd9a4c2df62a8. The row's conditional status refers to AvailableCartanStatement, proved under IsAvailableFor."
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
        "Proof of AvailableCartanStatement: availableCartan. Its only building premise is IsAvailableFor. It applies parahoricCartanConclusions_of_satisfiesGroupAxioms, which needs only KPBuildingDatum.SatisfiesGroupAxioms for the datum of F and G. At commit e7487341 that theorem in turn applies parahoricCartanConclusions_of_buildingGeometry, whose premises on supplied ParahoricBuildingData are SatisfiesApartmentAxioms, HasZeroFixerGenerators, HasNormalizerApartmentStabilizer, injectivity of the apartment map, HasTitsSystem, and that every point of the quotient shares an apartment with the image of x. Proposition 4.2.24 is not among these premises. The general use of the theorem also requires the existence of available data, the Theorem 9.2.7 obligation stated as BruhatTitsAvailabilityStatement (see that row)."
      ],
      "consumer_or_regression": "General special-parahoric Hecke double cosets, with a proved GL_n Cartan comparison and distinctness of the associated compactly supported functions.",
      "formal_status": "conditional",
      "publication_commits": [
        "c4a16df784376405a45b60df82583e8c26d8a4e3",
        "d39b5aee822fe2ad1aadf07861ebd9a4c2df62a8"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.BruhatTits.Cartan.AvailableCartanStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-08 at Library commit c4a16df7; statement_returns_prop true."
        },
        {
          "declaration": "Langlands.BruhatTits.Cartan.availableCartan",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-10 at Library commit e7487341; a theorem."
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
        "Published proof: Langlands.Geometry.Building.iwasawaDecomposition has type exactly IwasawaDecompositionStatement.{u}. It first appears in Library commit 0646cc6120e56febaf6f88f723f3b147d0e23d59. Its route differs from the source: it applies the published conditional theorem iwasawaDecompositionStatement_of_structuralStatements (module Langlands.Geometry.Building.IwasawaDecompositionReduction) to seven published structural proofs. The reduction builds the relative Tits system (G(F), P_∅(F), N(F), S) and shows that P(nu)(F)·N(F)·P_C contains 1 and is stable under left multiplication by the Borel subgroup and by the simple-reflection representatives, using a chamber form of Lemma 5.3.1. A dynamic-limit argument then absorbs the centralizer factor into N(F). The Henselian and perfect-residue hypotheses are retained in the target but unused by this route.",
        "The replaced Lemma 5.3.5 is not proved by this unit (see that row)."
      ],
      "consumer_or_regression": "Corrected Theorem 7.8.1(4), followed by actual double-coset and compact induction computations.",
      "formal_status": "conditional",
      "publication_commits": [
        "c4a16df784376405a45b60df82583e8c26d8a4e3",
        "0646cc6120e56febaf6f88f723f3b147d0e23d59"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.iwasawaDecomposition",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-09 at Library commit eb36be01."
        },
        {
          "declaration": "Langlands.Geometry.Building.IwasawaDecompositionStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-08 at Library commit c4a16df7; statement_returns_prop true."
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
        "Recorded Lean scope: AvailableIwasawaStatement quantifies over every nonarchimedean local field F of either characteristic in universe u, every group scheme G over Spec F with hG : IsConnectedReductive G, every KPBuildingAssignment 𝔅 with 𝔅.IsAvailableFor F G hG, and every cocharacter nu generic for B.i, where B := (𝔅.datum F G hG).base. Its first clause takes every x : B.Apartment with B.apartment.IsSpecialApartmentVertex x. Its second takes every y : B.ReducedBuilding with B.IsSpecialPoint y and B.IsVertex y and every Q with B.IsParahoricAt y Q (a G(F)-conjugate of an apartment parahoric at the translated point). For P_x = B.parahoricAt x, respectively Q, it concludes ParabolicPointProductFamily B.i nu: Set.univ = H·K and Set.univ = K·H as pointwise set products, for H ranging over the rational points of every algebraic parabolic subgroup, every Dynamic.parabolic, every standard P_J and their rational conjugates. It also adds three conclusions beyond the source theorem: the inclusion of P_x (or Q) in the compact stabilizer K_0 = B.apartment.specialCompactSubgroup x = G(F)^1 ∩ Stab(B.apartmentMap x) (or B.compactStabilizer y), the same product family for K_0, and IsCompactOpenMaximal F K_0 for the canonical rational-point topology. IwasawaExistenceStatement adds existence: for every maximal split torus i : S → G and generic nu it asserts an available assignment whose base torus and apartment are identified with i and given apartment data D, a special vertex x of D whose compact subgroup satisfies SpecialCompactProperties, the same product conclusions for G and the whole-building clause, and the corresponding data and product conclusions for every standard Levi M_J. Existence of available data is asserted only by IwasawaExistenceStatement, which is unproved. The theorem availableIwasawa (module Langlands.BruhatTits.Iwasawa.AvailableProof) proves AvailableIwasawaStatement, including the three added conclusions; it first appeared in Library commit e449cde988d4e97ab280b8d4d11262887ccc26e0. The row's conditional status refers to AvailableIwasawaStatement, proved under IsAvailableFor; IwasawaExistenceStatement remains a statement."
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
        "Proof of AvailableIwasawaStatement: availableIwasawa. Its only building premise is IsAvailableFor, and it proves the inclusion P_x ≤ K_0 for available data. The Library states that inclusion for all supplied data as Langlands.BruhatTits.SpecialCompact.ParahoricLeCompactStabilizer. The theorem parahoricLeCompactStabilizer (module Langlands.BruhatTits.SpecialCompact.ParahoricProof, first in Library commit 17dd94ea3f677b20fb5ab95b285cbc3fd7cde03e) proves it with no hypothesis beyond its binders: for every nonarchimedean local field F, every G with IsAffineHom G.X.hom, all P : ParahoricBuildingData G and every apartment point x, P.parahoricAt x ≤ P.apartment.specialCompactSubgroup x. A Lean inspection on 2026-11-13 at Library commit 0f84a0d8 reports kind theorem and only propext, Classical.choice and Quot.sound. The chamber form 5.3.3 has a published proof (see that row). The Library has no proof of IwasawaExistenceStatement. It also requires the existence of available data, the Theorem 9.2.7 obligation stated as BruhatTitsAvailabilityStatement (see that row)."
      ],
      "consumer_or_regression": "Parabolic induction and Jacquet structural bridges, retaining the special-parahoric and parabolic hypotheses.",
      "formal_status": "conditional",
      "publication_commits": [
        "c4a16df784376405a45b60df82583e8c26d8a4e3",
        "e449cde988d4e97ab280b8d4d11262887ccc26e0"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.BruhatTits.Iwasawa.AvailableIwasawaStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-08 at Library commit c4a16df7; statement_returns_prop true."
        },
        {
          "declaration": "Langlands.BruhatTits.Iwasawa.IwasawaExistenceStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-08 at Library commit c4a16df7; statement_returns_prop true."
        },
        {
          "declaration": "Langlands.BruhatTits.Iwasawa.availableIwasawa",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-10 at Library commit e449cde9; a theorem."
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
        "Open: an unconditional proof (the corresponding proof of Theorem 5.3.3 is in the Library). The Library has only conditional assemblies (module Langlands.Geometry.Building.UnipotentNormalizerCosetReduction). unipotentNormalizerCosetReduction proves the conclusion for supplied P from normality of P.normalizerZero, P.ChamberIwahoriDecompositionStatement and the apartment axioms. unipotentNormalizerCosetStatement_of_chamberIwahori_and_exactSequence derives the global statement from the chamber products for all supplied data and IwahoriWeylExactSequenceStatement. On 2026-11-09 the Library had no unconditional proof of either input. Library commit e449cde988d4e97ab280b8d4d11262887ccc26e0 proves both inputs of unipotentNormalizerCosetReduction for every supplied P: the normality of P.normalizerZero by ParahoricBuildingData.normal_normalizerZero (module ZeroSubgroupCommutatorNormality) and the chamber products by ParahoricBuildingData.chamberIwahoriDecomposition (Corollary 7.4.9 row). The published proof of Theorem 7.8.1(4), unipotentIwahoriDoubleCoset, applies unipotentNormalizerCoset_of_chamberIwahori with normal_normalizerZero and a proved chamber Iwahori decomposition. No theorem has type IwahoriWeylExactSequenceStatement.",
        "Proof: unipotentNormalizerCoset (module UnipotentNormalizerCosetProof), present in Library commit 17dd94ea3f677b20fb5ab95b285cbc3fd7cde03e, applies ParahoricBuildingData.unipotentNormalizerCoset_of_chamberIwahori to every supplied P with normal_normalizerZero and chamberIwahoriDecomposition, so no exact-sequence input is needed. It keeps the Henselian and perfect-residue-field premises, which this route does not use. A Lean inspection on 2026-11-13 at Library commit 8ff9abe9 reports kind theorem and only propext, Classical.choice and Quot.sound."
      ],
      "consumer_or_regression": "Actual injectivity of the map in corrected Theorem 7.8.1(4); a surjective Iwasawa product alone cannot establish this conclusion.",
      "formal_status": "conditional",
      "publication_commits": [
        "c4a16df784376405a45b60df82583e8c26d8a4e3",
        "17dd94ea3f677b20fb5ab95b285cbc3fd7cde03e"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.UnipotentNormalizerCosetStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-08 at Library commit c4a16df7; statement_returns_prop true."
        },
        {
          "declaration": "Langlands.Geometry.Building.unipotentNormalizerCoset",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit 8ff9abe9; a theorem proving UnipotentNormalizerCosetStatement."
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
        "Recorded Lean scope: every nonarchimedean local field F of either characteristic and supplied P : ParahoricBuildingData G, with P.apartment.SatisfiesApartmentAxioms P.centralizer, an actual chamber C, x in C and a generic cocharacter nu. The facet clause retains IsFaceOf and FacetChamberPositiveSystem. No existence of P or proof of AS5 is asserted. The theorem ParahoricBuildingData.chamberIwahoriDecomposition (module ChamberIwahoriProof) proves the statement for every supplied P, from the published factor-pair reduction with the rank-one factorization (KP 2.11.17) and Corollary 2.6.28. It first appeared in Library commit e449cde988d4e97ab280b8d4d11262887ccc26e0. The row is conditional on the construction of P."
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
      "publication_commits": [
        "25b91125ea94e88d741b206d633e82eb0d87c3e5",
        "e449cde988d4e97ab280b8d4d11262887ccc26e0"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.chamberIwahoriDecomposition",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-10 at Library commit e449cde9; a theorem."
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
        "Recorded Lean scope: closed Prop-valued targets at universe u quantify over every nonarchimedean local field F, every affine F-group scheme G and supplied P : ParahoricBuildingData G, retaining SatisfiesApartmentAxioms. Part (4) explicitly requires HenselianLocalRing O[F], PerfectField k[F] and a generic cocharacter nu. The actual U(F) is standardUnipotentPoints P.i nu empty. Its comparison with the single Dynamic.unipotent group is proved: standardUnipotent_empty_eq_dynamic (module Langlands.GroupScheme.Rational.MinimalStandardDynamicComparison) gives standardUnipotent i nu ∅ = Dynamic.unipotent for connected reductive G and a maximal split torus, without a genericity hypothesis, and IwasawaDecompositionReduction specializes it to the rational points of the same supplied P (see the Theorem 5.3.3 row). This comparison alone does not prove part (4). Part (4) is now proved on supplied data: the theorem unipotentIwahoriDoubleCoset (module UnipotentIwahoriDoubleCosetProof) proves UnipotentIwahoriDoubleCosetStatement from iwasawaDecomposition (Theorem 5.3.3 row), unipotentNormalizerCoset_of_chamberIwahori, normal_normalizerZero and a proved chamber Iwahori decomposition. It first appeared in Library commit e449cde988d4e97ab280b8d4d11262887ccc26e0. Parts (1)–(3) remain unproved, so the row stays statement. They are reduced to open inputs by published theorems. iwahoriWeylNormalizerAffineWeylReduction (module IwahoriWeylNormalizerAffineWeylReduction) derives part (1) (IwahoriWeylExactSequenceStatement) and the chamber splitting of 7.8.2 (IwahoriWeylChamberSplittingStatement) from SimplyConnectedNormalizerAffineWeylStatement. By the Theorem 7.5.3 row, that statement in turn follows from SimplyConnectedFacetFixingStatement. doubleCosetStatementReduction (module DoubleCosetStatementReduction) derives part (2) (IwahoriDoubleCosetStatement) from IwahoriWeylChamberSplittingStatement and AffineIwahoriTitsStatement. It derives part (3) (ParahoricDoubleCosetStatement) from IwahoriWeylChamberSplittingStatement and FacetParabolicComparisonStatement (the common-chamber comparison of KP Proposition 7.5.5, unproved). A proof of SimplyConnectedFacetFixingStatement would therefore prove parts (1) and (2) on supplied data. Part (3) would also need FacetParabolicComparisonStatement. No general building existence is asserted."
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
        "Open formal inputs on 13 November 2026, through the published reductions in the last hypotheses entry: SimplyConnectedFacetFixingStatement for parts (1) and (2) and 7.8.2; FacetParabolicComparisonStatement in addition for part (3)"
      ],
      "consumer_or_regression": "Distinct Hecke functions and finite-support convolution beyond simply connected split groups. Preserve length-zero data and the chamber dependence of the splitting; no Iwahori–Matsumoto presentation is claimed.",
      "formal_status": "statement",
      "publication_commits": [
        "25b91125ea94e88d741b206d633e82eb0d87c3e5",
        "e449cde988d4e97ab280b8d4d11262887ccc26e0",
        "ed924aef420de137b4cbaa3b063a3618afcd73fd"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.unipotentIwahoriDoubleCoset",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-10 at Library commit e449cde9; a theorem proving part (4)."
        },
        {
          "declaration": "Langlands.Geometry.Building.iwahoriWeylNormalizerAffineWeylReduction",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit ed924aef; a theorem reducing part (1) and 7.8.2 to SimplyConnectedNormalizerAffineWeylStatement."
        },
        {
          "declaration": "Langlands.Geometry.Building.doubleCosetStatementReduction",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit 8ff9abe9; a theorem reducing parts (2) and (3) to IwahoriWeylChamberSplittingStatement with AffineIwahoriTitsStatement and FacetParabolicComparisonStatement respectively."
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
        "Recorded Lean scope: CharacterKernelStatement (module Langlands.Geometry.Building.Kottwitz.CharacterKernelStatement) quantifies over every nonarchimedean local field F and connected reductive G over Spec F and asserts characterValuationKernel (ValuativeRel.valuation F) G = (fundamentalInvariantTorsion F (UnramifiedClosure F) (SeparableClosure F) G hG).comap κ_G. characterValuationKernel is the Library's G(F)^1, the common kernel of the valuations of the F-rational characters (Definition 2.6.15). K is the Library's maximal unramified extension UnramifiedClosure F inside the separable closure SeparableClosure F. ReductiveInvariantTarget F G hG is A^Γ for A = π_1(G)_I, the integral inertia coinvariants of the actual algebraic fundamental group, with the actual residual action of Γ = Gal(K/F); fundamentalInvariantTorsion is (A_tor)^Γ as a subgroup of A^Γ. κ_G is reductiveKottwitzRational F G hG (module Langlands.Geometry.Building.Kottwitz.ReductiveMap), selected by classical epsilon among the homomorphisms G(F) → A^Γ whose composite with A^Γ → A is the K-point map reductiveKottwitz on the image of G(F) in G(K). reductiveKottwitz is in turn selected by its squares with every z-extension, over the simply-connected-derived construction through every cocenter. That both selections have their characterizing properties is asserted by ReductiveKottwitzExistenceStatement (existence of z-extensions and unique existence, surjectivity and independence of the K-point map) and ReductiveKottwitzDescentStatement (residual Galois equivariance and unique existence of the restriction to G(F)), both in module Langlands.Geometry.Building.Kottwitz.ReductiveMapStatement; both are proved, by Kottwitz.reductiveKottwitzExistence_assembled and Kottwitz.reductiveKottwitzDescent_assembled (module Langlands.Geometry.Building.Kottwitz.ZExtensionKernelProof). The source's Henselian discretely valued fields with perfect residue field are specialized to nonarchimedean local fields of either characteristic in universe u; their residue fields are finite."
      ],
      "conclusion": "G(k)^1=kappa_G^(-1)((A_tor)^Gamma). This is the preimage of invariant torsion, distinct from the zero kernel identifying G(k)^0.",
      "lean_declarations": [
        "Langlands.Geometry.Building.Kottwitz.CharacterKernelStatement",
        "Langlands.Geometry.Building.Kottwitz.ReductiveKottwitzExistenceStatement",
        "Langlands.Geometry.Building.Kottwitz.ReductiveKottwitzDescentStatement",
        "Langlands.Geometry.Building.Kottwitz.CharacterKernelInputs.characterKernel",
        "Langlands.Geometry.Building.Kottwitz.cocenterTargetTorsion_proof",
        "Langlands.Geometry.Building.Kottwitz.TorusCharacterKernelInputs.torusCharacterKernel",
        "Langlands.Geometry.Building.Kottwitz.reductiveKottwitzFunctoriality_of_inputs",
        "Langlands.Geometry.Building.Kottwitz.fundamentalInertiaMapStatement",
        "Langlands.Geometry.Building.Kottwitz.torusCharacterKernel",
        "Langlands.Geometry.Building.Kottwitz.reductiveKottwitzExistence_of_remaining_inputs",
        "Langlands.Geometry.Building.Kottwitz.simplyConnectedDerivedKottwitz_proof",
        "Langlands.GroupScheme.zExtensionMorphismDomination",
        "Langlands.GroupScheme.inducedTorusQuotientPointSurjectivity",
        "Langlands.GroupScheme.zExtensionCommonDomination",
        "Langlands.GroupScheme.zExtensionPointSurjectivity",
        "Langlands.GroupScheme.AlgebraicFundamentalGroup.centralTorusFundamentalExactness",
        "Langlands.Geometry.Building.Kottwitz.centralTorusInertiaExactness",
        "Langlands.Geometry.Building.Kottwitz.reductiveKottwitzFunctoriality",
        "Langlands.Geometry.Building.Kottwitz.reductiveKottwitzExistence_assembled",
        "Langlands.Geometry.Building.Kottwitz.reductiveKottwitzDescent_assembled",
        "Langlands.Geometry.Building.Kottwitz.characterKernel"
      ],
      "modules": [
        "Langlands.Geometry.Building.Kottwitz.CharacterKernelStatement",
        "Langlands.Geometry.Building.Kottwitz.ReductiveMapStatement",
        "Langlands.Geometry.Building.Kottwitz.CharacterKernelReduction",
        "Langlands.Geometry.Building.Kottwitz.CocenterTargetTorsionProof",
        "Langlands.Geometry.Building.Kottwitz.TorusCharacterKernelReduction",
        "Langlands.Geometry.Building.Kottwitz.ReductiveFunctorialityReduction",
        "Langlands.Geometry.Building.Kottwitz.FundamentalInertiaMapProof",
        "Langlands.Geometry.Building.Kottwitz.TorusCharacterKernelProof",
        "Langlands.Geometry.Building.Kottwitz.ReductiveMapRemainingInputs",
        "Langlands.Geometry.Building.Kottwitz.SimplyConnectedDerivedKottwitzProof",
        "Langlands.GroupScheme.ZExtensionMorphismDominationProof",
        "Langlands.GroupScheme.Torus.InducedQuotientPointSurjectivityProof",
        "Langlands.GroupScheme.ZExtensionCommonDominationProof",
        "Langlands.GroupScheme.Torus.ZExtensionPointSurjectivityProof",
        "Langlands.GroupScheme.AlgebraicFundamentalGroupCentralTorusProof",
        "Langlands.Geometry.Building.Kottwitz.CentralTorusExactnessProof",
        "Langlands.Geometry.Building.Kottwitz.ReductiveFunctorialityProof",
        "Langlands.Geometry.Building.Kottwitz.ZExtensionKernelProof",
        "Langlands.Geometry.Building.Kottwitz.CharacterKernelProof"
      ],
      "dependencies": [
        "Actual Kottwitz construction and functoriality, Lemma 11.5.1",
        "Abelianization G→G_ab, its finite-kernel map on fundamental groups and inertia coinvariants; Lemma 11.1.3 and Definition 2.6.15",
        "The target is the actual Kottwitz homomorphism (KP Proposition 11.1.1, Definition 11.3.2, Lemma 11.5.1) over every nonarchimedean local field, with this statement over it for the Library's G(F)^0 and G(F)^1. The Library states CharacterKernelStatement (first in Library commit 0c3f30c24701c74d5474fca3fbb5324a99aa1d58) together with the selected maps and ReductiveKottwitzExistenceStatement and ReductiveKottwitzDescentStatement (module ReductiveMapStatement, same commit). On that date none of these statements is proved. Reduction (twentieth update, 14 November 2026): the theorem Kottwitz.CharacterKernelInputs.characterKernel (module Langlands.Geometry.Building.Kottwitz.CharacterKernelReduction, whose entry declaration is CharacterKernelInputs, first in Library commit e5365902d74534dbf1622c06e695dffdc128d723) derives CharacterKernelStatement from CharacterKernelInputs, the conjunction of four statements, by KP's reduction to the cocenter. TorusCharacterKernelStatement (module Langlands.Geometry.Building.Kottwitz.TorusCharacterKernelStatement, first in the same commit) is KP Lemma 11.1.3 on rational points: for every torus T over F, the character-valuation kernel of T(F) is the preimage of torsion under the constructed torus map. CocenterTargetTorsionStatement (module Langlands.Geometry.Building.Kottwitz.CocenterTargetTorsionStatement, first in the same commit) says that the map induced by the actual cocenter quotient on inertia coinvariants has torsion kernel, a step of KP's proof. ReductiveKottwitzFunctorialityStatement (module ReductiveMapStatement; KP Lemma 11.5.1, functoriality and compatibility with the torus map) and ReductiveKottwitzDescentStatement are the other two. Lean inspection is recorded below. At Library commit c40a0134 none of the four inputs was proved. The three modules cited in this paragraph are byte-identical between commit e5365902 and Library commit c40a0134. Twenty-second update (14 November 2026): two of the four inputs are now proved and a third is reduced. The theorem Kottwitz.cocenterTargetTorsion_proof (module Langlands.Geometry.Building.Kottwitz.CocenterTargetTorsionProof, first in Library commit b3a1bdaf15715f16a43643513b7cbb6cbb58ef3a) proves CocenterTargetTorsionStatement. The theorem Kottwitz.TorusCharacterKernelInputs.torusCharacterKernel (module Langlands.Geometry.Building.Kottwitz.TorusCharacterKernelReduction, first in the same commit) derives TorusCharacterKernelStatement from TorusCharacterKernelInputs, the conjunction of TorusKottwitzExistenceStatement (KP Proposition 11.1.1 for the torus Kottwitz homomorphisms) and NormalizedIntermediateValuationStatement (the integer normalization of the splitting-field valuations). Both are proved: Kottwitz.torusKottwitzExistence (module Langlands.Geometry.Building.Kottwitz.TorusMapProof, first in the same commit) and Kottwitz.normalizedIntermediateValuationStatement (module Langlands.Geometry.Building.Kottwitz.TorusNormValuation, added in the same commit). The theorem Kottwitz.reductiveKottwitzFunctoriality_of_inputs (module Langlands.Geometry.Building.Kottwitz.ReductiveFunctorialityReduction, first in the same commit) derives ReductiveKottwitzFunctorialityStatement from AlgebraicFundamentalGroupComparisonStatement, AlgebraicFundamentalGroupMapStatement, FundamentalInertiaMapStatement, TorusInertiaComparisonStatement, SimplyConnectedDerivedKottwitzStatement, ReductiveKottwitzExistenceStatement, a hypothesis whose body is ZExtensionMorphismDominationStatement, and the naturality of the torus maps. Proved inputs: AlgebraicFundamentalGroup.algebraicFundamentalGroupComparison (module Langlands.GroupScheme.AlgebraicFundamentalGroupComparisonProof, first in Library commit c40a01345b2f4172fa41e07ff31644b40e695003), AlgebraicFundamentalGroup.algebraicFundamentalGroupMap (module Langlands.GroupScheme.AlgebraicFundamentalGroupMapProof, first in Library commit b3a1bdaf15715f16a43643513b7cbb6cbb58ef3a) and Kottwitz.torusInertiaComparison_proof (module Langlands.Geometry.Building.Kottwitz.TorusInertiaComparisonProof, first in the same commit). The theorem Kottwitz.simplyConnectedDerivedKottwitz_of_norm_inputs (module Langlands.Geometry.Building.Kottwitz.TorusNormNaturality, first in Library commit c40a01345b2f4172fa41e07ff31644b40e695003) derives SimplyConnectedDerivedKottwitzStatement from the three statements just named, TorusFundamentalComparisonStatement, TorusKottwitzExistenceStatement and FundamentalInertiaMapStatement; Kottwitz.torusFundamentalComparison_proof (module Langlands.Geometry.Building.Kottwitz.TorusFundamentalComparisonProof, first in Library commit e5365902d74534dbf1622c06e695dffdc128d723) proves TorusFundamentalComparisonStatement. Kottwitz.torusKottwitz_natural_of_existence (same module) gives the naturality from torusKottwitzExistence. Unproved inputs: FundamentalInertiaMapStatement (module Langlands.Geometry.Building.Kottwitz.FundamentalGroupStatement, first in Library commit 0c3f30c24701c74d5474fca3fbb5324a99aa1d58; KP Lemma 11.3.6, inertia descent and functoriality of the fundamental-group maps), ReductiveKottwitzExistenceStatement and ZExtensionMorphismDominationStatement (module Langlands.GroupScheme.ZExtensionRefinementStatement, first in Library commit c40a01345b2f4172fa41e07ff31644b40e695003; given z-extensions of G and H and a morphism f : G → H of connected reductive groups, some z-extension of G maps to the first over G and to the second over f). So CharacterKernelStatement follows from FundamentalInertiaMapStatement, ReductiveKottwitzExistenceStatement, ReductiveKottwitzDescentStatement and ZExtensionMorphismDominationStatement, none of which is proved at Library commit 4f4af6ba. No published declaration states this composite; it was checked with a separate Lean check (Library commit 4f4af6ba, only propext, Classical.choice and Quot.sound). Lean inspections of the three theorems named first are recorded below. Each module cited in this update is byte-identical between its first commit and Library commit 4f4af6ba. Follow-up (twenty-second update, Library commit 58ad0f79): the theorem Kottwitz.fundamentalInertiaMapStatement (module Langlands.Geometry.Building.Kottwitz.FundamentalInertiaMapProof, first in Library commit af5d652c2f2ff5b35b4ce4dbbf7cbec8bbf3e99e) proves FundamentalInertiaMapStatement. The theorem Kottwitz.torusCharacterKernel (module Langlands.Geometry.Building.Kottwitz.TorusCharacterKernelProof, first in the same commit) proves TorusCharacterKernelStatement directly. So CharacterKernelStatement follows from ReductiveKottwitzExistenceStatement, ReductiveKottwitzDescentStatement and ZExtensionMorphismDominationStatement. The theorem Kottwitz.reductiveKottwitzExistence_of_remaining_inputs (module Langlands.Geometry.Building.Kottwitz.ReductiveMapRemainingInputs, whose entry declaration is ReductiveKottwitzRemainingInputsStatement, first in the same commit) derives ReductiveKottwitzExistenceStatement from FundamentalInertiaMapStatement and three statements. The first is ZExtensionPointSurjectivityStatement (module Langlands.GroupScheme.Torus.InducedQuotientPointSurjectivityStatement, first in Library commit b3a1bdaf15715f16a43643513b7cbb6cbb58ef3a): for every field extension K/k and every z-extension of a group over k, the map on K-points is surjective. The theorem zExtensionPointSurjectivity_of_inducedTorusQuotient of the same module derives it from InducedTorusQuotientPointSurjectivityStatement. The second is CentralTorusInertiaExactnessStatement (module Langlands.Geometry.Building.Kottwitz.CentralTorusExactnessStatement, first in the same commit): for a closed central torus Z of a connected reductive H with fppf quotient G, the selected maps give an exact sequence π₁(Z)_I → π₁(H)_I → π₁(G)_I → 0, without injectivity on the left. The third is ZExtensionCommonDominationStatement (module Langlands.GroupScheme.ZExtensionRefinementStatement, which also contains ZExtensionMorphismDominationStatement): two z-extensions of the same connected reductive group are dominated by a common z-extension, as in KP Fact 11.4.2. Hence CharacterKernelStatement also follows from these three statements, ReductiveKottwitzDescentStatement and ZExtensionMorphismDominationStatement. No published declaration states these composites; both were checked with a separate Lean check (Library commit 58ad0f79, only propext, Classical.choice and Quot.sound). None of ReductiveKottwitzExistenceStatement, ReductiveKottwitzDescentStatement, ZExtensionMorphismDominationStatement, ZExtensionPointSurjectivityStatement, InducedTorusQuotientPointSurjectivityStatement, CentralTorusInertiaExactnessStatement and ZExtensionCommonDominationStatement is proved at Library commit 58ad0f79. Lean inspections of the three theorems named first are recorded below. Each module cited in this follow-up is byte-identical between its first commit and Library commit 58ad0f79. Follow-up (twenty-fourth update, Library commit 7229bb45): the theorem Kottwitz.simplyConnectedDerivedKottwitz_proof (module Langlands.Geometry.Building.Kottwitz.SimplyConnectedDerivedKottwitzProof, first in Library commit 7f5b5f04a855fc0b4671393213c87415a6ee2aaf) has type SimplyConnectedDerivedKottwitzStatement. Its proof applies Kottwitz.simplyConnectedDerivedKottwitz_of_norm_inputs, recorded above, to the published proofs of its six inputs, so it adds a named theorem but no new step: the statement already followed from published proofs at Library commit 58ad0f79 (Proposition 11.5.4 row). The theorem zExtensionMorphismDomination (module Langlands.GroupScheme.ZExtensionMorphismDominationProof, first in Library commit aeb3911c4e1bf6e3a2f653e874e4ebc422d2a61a) proves ZExtensionMorphismDominationStatement. The theorem inducedTorusQuotientPointSurjectivity (module Langlands.GroupScheme.Torus.InducedQuotientPointSurjectivityProof, first in the same commit) proves InducedTorusQuotientPointSurjectivityStatement, so by zExtensionPointSurjectivity_of_inducedTorusQuotient ZExtensionPointSurjectivityStatement follows from published proofs. No published theorem has that type; the composite was checked with a separate Lean check (Library commit 7229bb45, type exactly ZExtensionPointSurjectivityStatement.{u}, only propext, Classical.choice and Quot.sound). With the reductions recorded above, ReductiveKottwitzExistenceStatement follows from CentralTorusInertiaExactnessStatement and ZExtensionCommonDominationStatement, and CharacterKernelStatement follows from ReductiveKottwitzExistenceStatement and ReductiveKottwitzDescentStatement, hence also from CentralTorusInertiaExactnessStatement, ZExtensionCommonDominationStatement and ReductiveKottwitzDescentStatement. These composites use published reductions only. No published declaration states them; they were checked with separate Lean checks (Library commit 7229bb45, only propext, Classical.choice and Quot.sound). None of ReductiveKottwitzExistenceStatement, ReductiveKottwitzDescentStatement, CentralTorusInertiaExactnessStatement and ZExtensionCommonDominationStatement is proved at Library commit 7229bb45. Lean inspections of the three theorems named first are recorded below. The module SimplyConnectedDerivedKottwitzProof is byte-identical between commit 7f5b5f04 and Library commit 7229bb45, the modules ZExtensionMorphismDominationProof and InducedQuotientPointSurjectivityProof between commit aeb3911c and Library commit 7229bb45, and the modules cited earlier in this entry between Library commits 58ad0f79 and 7229bb45. Follow-up (twenty-fifth update, Library commit 49668e4d): the theorem zExtensionCommonDomination (module Langlands.GroupScheme.ZExtensionCommonDominationProof, first in Library commit 4abbe7aabd9c92005d91c9d5bba86b879e928bb3) proves ZExtensionCommonDominationStatement; its proof specializes zExtensionMorphismDomination to the identity morphism of G. The theorem zExtensionPointSurjectivity (module Langlands.GroupScheme.Torus.ZExtensionPointSurjectivityProof, first in the same commit) has type ZExtensionPointSurjectivityStatement; it applies zExtensionPointSurjectivity_of_inducedTorusQuotient to inducedTorusQuotientPointSurjectivity, so it names the composite of the previous follow-up. With the published reduction Kottwitz.reductiveKottwitzExistence_of_remaining_inputs and the published theorem Kottwitz.fundamentalInertiaMapStatement, both recorded above, ReductiveKottwitzExistenceStatement therefore follows from CentralTorusInertiaExactnessStatement alone, and CharacterKernelStatement follows from CentralTorusInertiaExactnessStatement and ReductiveKottwitzDescentStatement. These composites use published reductions and proofs only. No published declaration states them; they were checked with separate Lean checks (Library commit c2a69151, only propext, Classical.choice and Quot.sound). The theorem AlgebraicFundamentalGroup.centralTorusFundamentalExactness (module Langlands.GroupScheme.AlgebraicFundamentalGroupCentralTorusProof, first in the same commit) proves AlgebraicFundamentalGroup.CentralTorusFundamentalExactnessStatement (module Langlands.GroupScheme.AlgebraicFundamentalGroupCentralTorusStatement): if Z is a closed central torus of a connected reductive group H over a field and G is the fppf quotient of H by Z, then 0 → π₁(Z) → π₁(H) → π₁(G) → 0 is exact for the selected induced maps. That statement takes no inertia coinvariants. CentralTorusInertiaExactnessStatement asks that π₁(H)_I → π₁(G)_I be surjective with kernel the image of π₁(Z)_I; no published declaration derives it from the exact sequence, and it is unproved at Library commit 49668e4d. ReductiveKottwitzExistenceStatement and ReductiveKottwitzDescentStatement are also unproved at Library commit 49668e4d. Lean inspections of the three theorems are recorded below. The modules ZExtensionCommonDominationProof, ZExtensionPointSurjectivityProof and AlgebraicFundamentalGroupCentralTorusProof are byte-identical between commit 4abbe7aa and Library commit 49668e4d, and the modules cited earlier in this entry between Library commits 7229bb45 and 49668e4d. Follow-up (twenty-sixth update, Library commit 0b7bb3fd): the theorem Kottwitz.centralTorusInertiaExactness (module Langlands.Geometry.Building.Kottwitz.CentralTorusExactnessProof, first in Library commit fab9caeae532b7a65e67e702bcab72d3194371ae) proves CentralTorusInertiaExactnessStatement. Its proof applies Representation.Coinvariants.rightExact_of_descent, the right exactness of coinvariants, to the exact sequence of fundamental groups given by AlgebraicFundamentalGroup.centralTorusFundamentalExactness, with Galois equivariance from algebraicFundamentalGroupMap and the representative law of the selected inertia maps from Kottwitz.fundamentalInertiaMapStatement. So ReductiveKottwitzExistenceStatement follows from published proofs, and CharacterKernelStatement follows from ReductiveKottwitzDescentStatement alone. No published declaration states these composites; they were checked with separate Lean checks (Library commit fab9caea, only propext, Classical.choice and Quot.sound). The Lean inspection of the theorem is recorded below. The theorem Kottwitz.reductiveKottwitzFunctoriality (module Langlands.Geometry.Building.Kottwitz.ReductiveFunctorialityProof, first in Library commit 0b7bb3fdbe6e0386b666b6b099a3bc9cd3ad7e18) proves ReductiveKottwitzFunctorialityStatement, the functoriality and torus-compatibility part of KP Lemma 11.5.1; the residual Galois equivariance of that lemma belongs to ReductiveKottwitzDescentStatement. Inside its proof, Kottwitz.reductiveKottwitzExistence_of_remaining_inputs derives ReductiveKottwitzExistenceStatement from published proofs, centralTorusInertiaExactness among them; the theorem Kottwitz.reductiveKottwitzFunctoriality_of_existence of the same module then supplies the other inputs of Kottwitz.reductiveKottwitzFunctoriality_of_inputs from published proofs. Its Lean inspection is recorded below. ReductiveKottwitzDescentStatement is unproved at Library commit 0b7bb3fd. The module CentralTorusExactnessProof is byte-identical between commit fab9caea and Library commit 0b7bb3fd, and the modules cited earlier in this entry between Library commits 49668e4d and 0b7bb3fd. Follow-up (thirty-first update, Library commit 314cfd1a): the theorem Kottwitz.characterKernel (module Langlands.Geometry.Building.Kottwitz.CharacterKernelProof, first in Library commit e4a9b4d0164a5e0a9828dcaec5fa1cb7837ff8c6) proves CharacterKernelStatement. Its proof applies the published theorem Kottwitz.CharacterKernelInputs.characterKernel to four published proofs: Kottwitz.torusCharacterKernel, Kottwitz.cocenterTargetTorsion_proof, Kottwitz.reductiveKottwitzFunctoriality and Kottwitz.reductiveKottwitzDescent_assembled. The last is one of two theorems of the module Langlands.Geometry.Building.Kottwitz.ZExtensionKernelProof (first in Library commit 497ef49830025d23824f6b2e2b1d5d60b594f51e) that prove the two other statements of this row. Kottwitz.reductiveKottwitzExistence_assembled proves ReductiveKottwitzExistenceStatement: it applies Kottwitz.reductiveKottwitzExistence_of_remaining_inputs to Kottwitz.fundamentalInertiaMapStatement, zExtensionPointSurjectivity, Kottwitz.centralTorusInertiaExactness and a proof of ZExtensionCommonDominationStatement, which it obtains from zExtensionMorphismDomination with the identity morphism of G. Kottwitz.reductiveKottwitzDescent_assembled proves ReductiveKottwitzDescentStatement: it applies the published reduction Kottwitz.reductiveKottwitzDescent_of_inputs (module Langlands.Geometry.Building.Kottwitz.ReductiveMapDescentReduction) to Kottwitz.simplyConnectedDerivedKottwitz_proof, Kottwitz.reductiveKottwitzExistence_assembled, Kottwitz.fundamentalInertiaMapStatement, Kottwitz.torusInertiaComparison_proof and Kottwitz.generalTorusKottwitzEquivariance (module Langlands.Geometry.Building.Kottwitz.TorusKottwitzEquivariance). So Lemma 11.5.2 is proved in the recorded Lean scope, for nonarchimedean local fields of either characteristic in place of Henselian discretely valued fields with perfect residue field, and the formal status of this row is proved. Lean inspections of the three theorems are recorded below. The module ZExtensionKernelProof is byte-identical between commit 497ef498 and Library commit 314cfd1a, the module CharacterKernelProof between commit e4a9b4d0 and Library commit 314cfd1a, and the modules cited earlier in this entry between Library commits 0b7bb3fd and 314cfd1a."
      ],
      "consumer_or_regression": "The second and third quotient identifications of 11.7.6 and retention of the G(k)^0/G(k)^1 distinction in Hecke and stabilizer interfaces.",
      "formal_status": "proved",
      "publication_commits": [
        "0c3f30c24701c74d5474fca3fbb5324a99aa1d58",
        "497ef49830025d23824f6b2e2b1d5d60b594f51e",
        "e4a9b4d0164a5e0a9828dcaec5fa1cb7837ff8c6"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.CharacterKernelStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit 6948120d; kind definition; statement_returns_prop true; the module is byte-identical to commit 0c3f30c2."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.ReductiveKottwitzExistenceStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit 6948120d; kind definition; statement_returns_prop true; the module is byte-identical to commit 0c3f30c2."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.ReductiveKottwitzDescentStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit 6948120d; kind definition; statement_returns_prop true; the module is byte-identical to commit 0c3f30c2."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.CharacterKernelInputs.characterKernel",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit c40a0134; kind theorem, at universe level u, whose type is the implication from CharacterKernelInputs to CharacterKernelStatement; the module is byte-identical to commit e5365902, which first published it."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.cocenterTargetTorsion_proof",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 4f4af6ba; kind theorem, at universe level u, whose type is exactly CocenterTargetTorsionStatement.{u}; the module is byte-identical to commit b3a1bdaf, which first published it."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.TorusCharacterKernelInputs.torusCharacterKernel",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 4f4af6ba; kind theorem, at universe level u, whose type is the implication from TorusCharacterKernelInputs to TorusCharacterKernelStatement; the module is byte-identical to commit b3a1bdaf, which first published it."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.reductiveKottwitzFunctoriality_of_inputs",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 4f4af6ba; kind theorem, at universe level u, whose type is the implication from the eight hypotheses named in the dependencies to ReductiveKottwitzFunctorialityStatement; the module is byte-identical to commit b3a1bdaf, which first published it."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.fundamentalInertiaMapStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 58ad0f79; kind theorem, at universe level u, whose type is exactly FundamentalInertiaMapStatement.{u}; the module is byte-identical to commit af5d652c, which first published it."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.torusCharacterKernel",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 58ad0f79; kind theorem, at universe level u, whose type is exactly TorusCharacterKernelStatement.{u}; the module is byte-identical to commit af5d652c, which first published it."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.reductiveKottwitzExistence_of_remaining_inputs",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 58ad0f79; kind theorem, at universe level u, whose type is exactly ReductiveKottwitzRemainingInputsStatement.{u}, the implication from FundamentalInertiaMapStatement, ZExtensionPointSurjectivityStatement, CentralTorusInertiaExactnessStatement and ZExtensionCommonDominationStatement to ReductiveKottwitzExistenceStatement; the module is byte-identical to commit af5d652c, which first published it."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.simplyConnectedDerivedKottwitz_proof",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 320321b3; kind theorem, at universe level u, whose type is exactly SimplyConnectedDerivedKottwitzStatement.{u}; the module is byte-identical to commit 7f5b5f04, which first published it."
        },
        {
          "declaration": "Langlands.GroupScheme.zExtensionMorphismDomination",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 51e9457f; kind theorem, at universe level u, whose type is exactly ZExtensionMorphismDominationStatement.{u}; the module is byte-identical to commit aeb3911c, which first published it."
        },
        {
          "declaration": "Langlands.GroupScheme.inducedTorusQuotientPointSurjectivity",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 51e9457f; kind theorem, at universe level u, whose type is exactly InducedTorusQuotientPointSurjectivityStatement.{u}; the module is byte-identical to commit aeb3911c, which first published it."
        },
        {
          "declaration": "Langlands.GroupScheme.zExtensionCommonDomination",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 49668e4d; kind theorem, at universe level u, whose type is exactly ZExtensionCommonDominationStatement.{u}; the module is byte-identical to commit 4abbe7aa, which first published it."
        },
        {
          "declaration": "Langlands.GroupScheme.zExtensionPointSurjectivity",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 49668e4d; kind theorem, at universe level u, whose type is exactly ZExtensionPointSurjectivityStatement.{u}; the module is byte-identical to commit 4abbe7aa, which first published it."
        },
        {
          "declaration": "Langlands.GroupScheme.AlgebraicFundamentalGroup.centralTorusFundamentalExactness",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 49668e4d; kind theorem, at universe level u, whose type is exactly AlgebraicFundamentalGroup.CentralTorusFundamentalExactnessStatement.{u}; the module is byte-identical to commit 4abbe7aa, which first published it."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.centralTorusInertiaExactness",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit fab9caea; kind theorem, at universe level u, whose type is exactly CentralTorusInertiaExactnessStatement.{u}; the module was first published in that commit and is byte-identical at Library commit 0b7bb3fd."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.reductiveKottwitzFunctoriality",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 0b7bb3fd; kind theorem, at universe level u, whose type is exactly ReductiveKottwitzFunctorialityStatement.{u}; the module was first published in that commit."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.reductiveKottwitzExistence_assembled",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-16 at Library commit b44618a4; kind theorem, at universe level u, whose type is exactly ReductiveKottwitzExistenceStatement.{u}; the module was first published in Library commit 497ef498 and is byte-identical between that commit and Library commit 314cfd1a."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.reductiveKottwitzDescent_assembled",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-16 at Library commit b44618a4; kind theorem, at universe level u, whose type is exactly ReductiveKottwitzDescentStatement.{u}; the module was first published in Library commit 497ef498 and is byte-identical between that commit and Library commit 314cfd1a."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.characterKernel",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-16 at Library commit b44618a4; kind theorem, at universe level u, whose type is exactly CharacterKernelStatement.{u}; the module was first published in Library commit e4a9b4d0 and is byte-identical between that commit and Library commit 314cfd1a."
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
        "Recorded Lean scope: ZeroKernelStatement (module Langlands.Geometry.Building.Kottwitz.ZeroKernelStatement) quantifies over every nonarchimedean local field F, connected reductive G over Spec F and every ZeroSubgroupDatum d for a maximal split torus i : S → G and a representative j : Z → G of its centralizer, which carries data of Definition 2.6.23(1) for Z_K and a simply connected cover of the derived subgroup; d.zeroSubgroup is the Library's G(F)^0 = G(F)^♮ · Z(F)^0 of Definition 2.6.23(3). It asserts d.zeroSubgroup = ker κ_G, so it also says that G(F)^0 does not depend on the datum. K is the Library's maximal unramified extension UnramifiedClosure F inside the separable closure SeparableClosure F. ReductiveInvariantTarget F G hG is A^Γ for A = π_1(G)_I, the integral inertia coinvariants of the actual algebraic fundamental group, with the actual residual action of Γ = Gal(K/F); fundamentalInvariantTorsion is (A_tor)^Γ as a subgroup of A^Γ. κ_G is reductiveKottwitzRational F G hG (module Langlands.Geometry.Building.Kottwitz.ReductiveMap), selected by classical epsilon among the homomorphisms G(F) → A^Γ whose composite with A^Γ → A is the K-point map reductiveKottwitz on the image of G(F) in G(K). reductiveKottwitz is in turn selected by its squares with every z-extension, over the simply-connected-derived construction through every cocenter. That both selections have their characterizing properties is asserted by ReductiveKottwitzExistenceStatement (existence of z-extensions and unique existence, surjectivity and independence of the K-point map) and ReductiveKottwitzDescentStatement (residual Galois equivariance and unique existence of the restriction to G(F)), both in module Langlands.Geometry.Building.Kottwitz.ReductiveMapStatement; both are proved, by Kottwitz.reductiveKottwitzExistence_assembled and Kottwitz.reductiveKottwitzDescent_assembled (module Langlands.Geometry.Building.Kottwitz.ZExtensionKernelProof; Lemma 11.5.2 row). The source's Henselian discretely valued fields with perfect residue field are specialized to nonarchimedean local fields of either characteristic in universe u; their residue fields are finite."
      ],
      "conclusion": "G(k)^0=ker(kappa_G). The homomorphism is the actual Kottwitz map, not an arbitrary map postulated to have this kernel.",
      "lean_declarations": [
        "Langlands.Geometry.Building.Kottwitz.ZeroKernelStatement",
        "Langlands.Geometry.Building.Kottwitz.ReductiveKottwitzExistenceStatement",
        "Langlands.Geometry.Building.Kottwitz.ReductiveKottwitzDescentStatement",
        "Langlands.Geometry.Building.Kottwitz.zeroKernel_of_unramified",
        "Langlands.Geometry.Building.Kottwitz.zeroKernel_of_torus_zExtension",
        "Langlands.Geometry.Building.Kottwitz.zExtensionUnramifiedKernelReduction",
        "Langlands.Geometry.Building.Kottwitz.torusKottwitzKernel",
        "Langlands.Geometry.Building.Kottwitz.zExtensionRationalKernelReduction",
        "Langlands.Geometry.Building.Kottwitz.InducedCentralTorusInertiaInjectivityStatement",
        "Langlands.Geometry.Building.Kottwitz.InducedCentralTorusInertiaInjectivityStatement.zExtension",
        "Langlands.Geometry.Building.Kottwitz.InducedTorusKottwitzRationalSurjectivityStatement",
        "Langlands.Geometry.Building.Kottwitz.inducedCentralTorusInertiaInjectivity",
        "Langlands.Geometry.Building.Kottwitz.inducedTorusKottwitzRationalSurjectivity",
        "Langlands.Geometry.Building.Kottwitz.zExtensionKottwitzKernelSurjectivity",
        "Langlands.Geometry.Building.Kottwitz.unramifiedZeroKernel",
        "Langlands.Geometry.Building.Kottwitz.zeroKernel_of_unramifiedZeroDescent"
      ],
      "modules": [
        "Langlands.Geometry.Building.Kottwitz.ZeroKernelStatement",
        "Langlands.Geometry.Building.Kottwitz.ReductiveMapStatement",
        "Langlands.Geometry.Building.Kottwitz.ZeroKernelReduction",
        "Langlands.Geometry.Building.Kottwitz.ZeroKernelAssembly",
        "Langlands.Geometry.Building.Kottwitz.ZExtensionKernelReduction",
        "Langlands.Geometry.Building.Kottwitz.TorusKernelProof",
        "Langlands.Geometry.Building.Kottwitz.ZExtensionRationalKernelReduction",
        "Langlands.Geometry.Building.Kottwitz.CentralTorusInertiaInjectivityStatement",
        "Langlands.Geometry.Building.Kottwitz.InducedTorusRationalSurjectivityStatement",
        "Langlands.Geometry.Building.Kottwitz.CentralTorusInertiaInjectivityProof",
        "Langlands.Geometry.Building.Kottwitz.InducedTorusRationalSurjectivityProof",
        "Langlands.Geometry.Building.Kottwitz.ZExtensionKernelProof",
        "Langlands.Geometry.Building.Kottwitz.UnramifiedZeroKernelProof"
      ],
      "dependencies": [
        "Proposition 9.3.24, G(k)^0=G(K)^0 intersect G(k), reduces to k=K",
        "Quasi-splitness Corollary 2.3.8, torus kernel Proposition 11.1.5, induced-torus lifting Lemma 2.5.20 and z-extension surjectivity Proposition 11.5.3",
        "The target is the actual Kottwitz homomorphism (KP Proposition 11.1.1, Definition 11.3.2, Lemma 11.5.1) over every nonarchimedean local field, with this statement over it for the Library's G(F)^0 and G(F)^1. The Library states ZeroKernelStatement (first in Library commit 0c3f30c24701c74d5474fca3fbb5324a99aa1d58) together with the selected maps and ReductiveKottwitzExistenceStatement and ReductiveKottwitzDescentStatement (module ReductiveMapStatement, same commit). On that date none of these statements is proved. Reduction (twentieth update, 14 November 2026): the theorem Kottwitz.zeroKernel_of_unramified (module Langlands.Geometry.Building.Kottwitz.ZeroKernelReduction, whose entry declaration is UnramifiedZeroKernelStatement, first in Library commit 4f6abf4c7e19610e4d89edc9bf64b34ba1db9ff2) derives ZeroKernelStatement from three statements, following KP's reduction to k = K by Proposition 9.3.24: ReductiveKottwitzDescentStatement; UnramifiedZeroDescentStatement (module Langlands.Geometry.Building.UnramifiedZeroDescentStatement, first in Library commit 0c3f30c24701c74d5474fca3fbb5324a99aa1d58; KP Proposition 9.3.24 with the Galois stability of G(K)^1 and G(K)^0); and UnramifiedZeroKernelStatement (module ZeroKernelReduction), that for every unramified zero datum E of G_K the subgroup E.zeroPoints is the preimage of the kernel of the K-point map reductiveKottwitz. Lean inspection is recorded below. At Library commit c40a0134 none of the three inputs was proved. The modules ZeroKernelReduction and UnramifiedZeroDescentStatement are byte-identical between their first commits and Library commit c40a0134. Follow-up (twenty-second update, Library commit 58ad0f79): the theorem Kottwitz.zeroKernel_of_torus_zExtension (module Langlands.Geometry.Building.Kottwitz.ZeroKernelAssembly, whose entry declaration is UnramifiedZeroKernelReductionStatement, first in Library commit af5d652c2f2ff5b35b4ce4dbbf7cbec8bbf3e99e) derives ZeroKernelStatement from TorusKottwitzKernelStatement, SimplyConnectedDerivedKottwitzStatement, ReductiveKottwitzExistenceStatement, ZExtensionKottwitzKernelSurjectivityStatement, ReductiveKottwitzDescentStatement and UnramifiedZeroDescentStatement. It combines zeroKernel_of_unramified with Kottwitz.unramifiedZeroKernel_of_torus_zExtension (same module), whose type UnramifiedZeroKernelReductionStatement is the implication from the first four to UnramifiedZeroKernelStatement. TorusKottwitzKernelStatement (module Langlands.Geometry.Building.Kottwitz.TorusKernelStatement, first in Library commit b3a1bdaf15715f16a43643513b7cbb6cbb58ef3a) is KP Proposition 11.1.5, T(K)^0 = ker(κ_T), with T(K)^0 the norm image of the bounded subgroup for every finite Galois splitting field. ZExtensionKottwitzKernelSurjectivityStatement (module Langlands.Geometry.Building.Kottwitz.ZExtensionKernelStatement, first in the same commit) is the kernel clause of KP Proposition 11.5.3: for every z-extension H → G the image of the kernel of the constructed Kottwitz map of H is the kernel of that of G, on K-points and on F-rational points. Neither is proved at Library commit 58ad0f79. SimplyConnectedDerivedKottwitzStatement is unconditional there: Kottwitz.simplyConnectedDerivedKottwitz_of_norm_inputs (Lemma 11.5.2 row) derives it from six statements, and FundamentalInertiaMapStatement, the only one of them unproved at Library commit 4f4af6ba, is now proved (Lemma 11.5.2 row). So ZeroKernelStatement follows from five unproved statements, TorusKottwitzKernelStatement, ReductiveKottwitzExistenceStatement, ZExtensionKottwitzKernelSurjectivityStatement, ReductiveKottwitzDescentStatement and UnramifiedZeroDescentStatement, and UnramifiedZeroKernelStatement from the first three. No published declaration states these composites; both were checked with a separate Lean check (Library commit 58ad0f79, only propext, Classical.choice and Quot.sound). Lean inspection is recorded below. Each module cited in this follow-up is byte-identical between its first commit and Library commit 58ad0f79, and the modules cited earlier in this entry are byte-identical between Library commits c40a0134 and 58ad0f79. Follow-up (twenty-fourth update, Library commit 7229bb45): SimplyConnectedDerivedKottwitzStatement is now the type of the published theorem Kottwitz.simplyConnectedDerivedKottwitz_proof, and ZExtensionMorphismDominationStatement is proved (Lemma 11.5.2 row). The theorem Kottwitz.torusKottwitzKernel (module Langlands.Geometry.Building.Kottwitz.TorusKernelProof, first in Library commit aeb3911c4e1bf6e3a2f653e874e4ebc422d2a61a) proves TorusKottwitzKernelStatement. So four premises of Kottwitz.zeroKernel_of_torus_zExtension remain unproved: ReductiveKottwitzExistenceStatement, ZExtensionKottwitzKernelSurjectivityStatement, ReductiveKottwitzDescentStatement and UnramifiedZeroDescentStatement. The module Langlands.Geometry.Building.Kottwitz.ZExtensionKernelReduction (whose entry declaration is ZExtensionUnramifiedKernelReductionStatement, first in Library commit 7f5b5f04a855fc0b4671393213c87415a6ee2aaf) names the two conjuncts of ZExtensionKottwitzKernelSurjectivityStatement: Kottwitz.zExtensionKottwitzKernelSurjectivityStatement_iff, proved by Iff.rfl, identifies it with the conjunction of ZExtensionUnramifiedKottwitzKernelStatement, the clause on points over K, and ZExtensionRationalKottwitzKernelStatement, the clause on F-rational points. The theorem Kottwitz.zExtensionUnramifiedKernelReduction of that module derives the first conjunct from ReductiveKottwitzExistenceStatement, ReductiveKottwitzFunctorialityStatement and CentralTorusInertiaExactnessStatement. The theorem Kottwitz.zExtensionRationalKernelReduction (module Langlands.Geometry.Building.Kottwitz.ZExtensionRationalKernelReduction, whose entry declaration is ZExtensionRationalKernelReductionStatement, first in Library commit aeb3911c4e1bf6e3a2f653e874e4ebc422d2a61a) derives the second conjunct from six premises: ReductiveKottwitzFunctorialityStatement, ReductiveKottwitzDescentStatement, CentralTorusInertiaExactnessStatement, two propositions written out in its statement, and ZExtensionPointSurjectivityStatement. The first written-out proposition is the injectivity of π₁(Z)_I → π₁(H)_I for every z-extension H → G over a nonarchimedean local field, from the proof of KP Proposition 11.5.3; the second is KP Corollary 11.1.9, the surjectivity of the torus Kottwitz map T(F) → X_*(T)_I^Γ for every induced torus T. Neither a general injectivity statement for induced central torus quotients with a z-extension corollary that implies the first nor a statement of the second is in Library commit 7229bb45. ZExtensionPointSurjectivityStatement follows from published proofs (Lemma 11.5.2 row), and the published reduction of ReductiveKottwitzFunctorialityStatement (Kottwitz.reductiveKottwitzFunctoriality_of_inputs, Lemma 11.5.2 row) has no unproved input other than ReductiveKottwitzExistenceStatement. Lean inspections are recorded below. The published theorem Kottwitz.unramifiedZeroKernel_of_torus_zExtension takes the whole of ZExtensionKottwitzKernelSurjectivityStatement as a premise, but its proof uses only the first conjunct. A private copy of that proof was compiled with the premise weakened to ZExtensionUnramifiedKottwitzKernelStatement. Combined with zExtensionUnramifiedKernelReduction, the published reduction of ReductiveKottwitzFunctorialityStatement and the proofs above, it shows that UnramifiedZeroKernelStatement follows from ReductiveKottwitzExistenceStatement and CentralTorusInertiaExactnessStatement. With the reduction of ReductiveKottwitzExistenceStatement in the Lemma 11.5.2 row, ZeroKernelStatement then follows from CentralTorusInertiaExactnessStatement, ZExtensionCommonDominationStatement, ReductiveKottwitzDescentStatement and UnramifiedZeroDescentStatement, without ZExtensionKottwitzKernelSurjectivityStatement. No published declaration states these composites; both were checked with separate Lean checks (Library commit 7229bb45, only propext, Classical.choice and Quot.sound). None of ReductiveKottwitzExistenceStatement, ReductiveKottwitzFunctorialityStatement, ReductiveKottwitzDescentStatement, CentralTorusInertiaExactnessStatement, ZExtensionCommonDominationStatement and UnramifiedZeroDescentStatement, and neither conjunct of ZExtensionKottwitzKernelSurjectivityStatement, is proved at Library commit 7229bb45. The module ZExtensionKernelReduction is byte-identical between commit 7f5b5f04 and Library commit 7229bb45, the modules TorusKernelProof and ZExtensionRationalKernelReduction between commit aeb3911c and Library commit 7229bb45, and the modules cited earlier in this entry between Library commits 58ad0f79 and 7229bb45. Follow-up (twenty-fifth update, Library commit 49668e4d): ZExtensionCommonDominationStatement is proved, and ReductiveKottwitzExistenceStatement follows from CentralTorusInertiaExactnessStatement alone (Lemma 11.5.2 row). With the private weakening recorded in the previous follow-up, UnramifiedZeroKernelStatement therefore follows from CentralTorusInertiaExactnessStatement alone, and ZeroKernelStatement follows from three statements: CentralTorusInertiaExactnessStatement, ReductiveKottwitzDescentStatement and UnramifiedZeroDescentStatement. No published declaration states these composites; both were checked with separate Lean checks (Library commit c2a69151, only propext, Classical.choice and Quot.sound). None of these three statements is proved at Library commit 49668e4d. The modules cited earlier in this entry are byte-identical between Library commits 7229bb45 and 49668e4d. Follow-up (twenty-sixth update, Library commit 0b7bb3fd): CentralTorusInertiaExactnessStatement is proved by the theorem Kottwitz.centralTorusInertiaExactness, ReductiveKottwitzExistenceStatement follows from published proofs, and ReductiveKottwitzFunctorialityStatement is proved by the theorem Kottwitz.reductiveKottwitzFunctoriality (Lemma 11.5.2 row). With the private weakening recorded in the follow-up of the twenty-fourth update, UnramifiedZeroKernelStatement therefore follows from published proofs, and ZeroKernelStatement follows from ReductiveKottwitzDescentStatement and UnramifiedZeroDescentStatement. Without the weakening, Kottwitz.zExtensionUnramifiedKernelReduction now gives ZExtensionUnramifiedKottwitzKernelStatement, the first conjunct of ZExtensionKottwitzKernelSurjectivityStatement, from published proofs. The Library states the two propositions written out in the statement of Kottwitz.zExtensionRationalKernelReduction. The module Langlands.Geometry.Building.Kottwitz.CentralTorusInertiaInjectivityStatement (first in Library commit fab9caeae532b7a65e67e702bcab72d3194371ae) states Kottwitz.InducedCentralTorusInertiaInjectivityStatement: for every tower k ⊆ K ⊆ E with E a separable closure of k and K/k normal, every closed central induced torus Z of a connected reductive k-group H and every fppf quotient G of H by Z, the selected map π₁(Z)_I → π₁(H)_I is injective. The theorem InducedCentralTorusInertiaInjectivityStatement.zExtension of that module derives the same injectivity for every z-extension; with K the maximal unramified extension and E the separable closure of a nonarchimedean local field, this is the first written-out proposition. The module Langlands.Geometry.Building.Kottwitz.InducedTorusRationalSurjectivityStatement (first in the same commit) states Kottwitz.InducedTorusKottwitzRationalSurjectivityStatement, KP Corollary 11.1.9 for every induced torus over a nonarchimedean local field; its body is the second written-out proposition. So ZExtensionRationalKottwitzKernelStatement and ZExtensionKottwitzKernelSurjectivityStatement follow from three statements: ReductiveKottwitzDescentStatement, InducedCentralTorusInertiaInjectivityStatement and InducedTorusKottwitzRationalSurjectivityStatement. With the published assemblies Kottwitz.unramifiedZeroKernel_of_torus_zExtension and Kottwitz.zeroKernel_of_torus_zExtension, and without the weakening, UnramifiedZeroKernelStatement follows from the same three statements, and ZeroKernelStatement from them and UnramifiedZeroDescentStatement. No published declaration states these composites; The composites of this follow-up were checked with separate Lean checks (two with the weakening and five without it; Library commit fab9caea, only propext, Classical.choice and Quot.sound). Lean inspections of the two statements and the theorem are recorded below. None of ReductiveKottwitzDescentStatement, UnramifiedZeroDescentStatement, InducedCentralTorusInertiaInjectivityStatement, InducedTorusKottwitzRationalSurjectivityStatement, ZExtensionRationalKottwitzKernelStatement and UnramifiedZeroKernelStatement is proved at Library commit 0b7bb3fd. The modules CentralTorusInertiaInjectivityStatement and InducedTorusRationalSurjectivityStatement are byte-identical between commit fab9caea and Library commit 0b7bb3fd, and the modules cited earlier in this entry between Library commits 49668e4d and 0b7bb3fd. Follow-up (thirty-first update, Library commit 314cfd1a): ReductiveKottwitzExistenceStatement and ReductiveKottwitzDescentStatement are proved (Lemma 11.5.2 row). The theorems Kottwitz.inducedCentralTorusInertiaInjectivity (module Langlands.Geometry.Building.Kottwitz.CentralTorusInertiaInjectivityProof) and Kottwitz.inducedTorusKottwitzRationalSurjectivity (module Langlands.Geometry.Building.Kottwitz.InducedTorusRationalSurjectivityProof), both first in Library commit 2016a0d994180c702214a75514a08546aa930f07, prove InducedCentralTorusInertiaInjectivityStatement and InducedTorusKottwitzRationalSurjectivityStatement. The theorem Kottwitz.zExtensionKottwitzKernelSurjectivity (module Langlands.Geometry.Building.Kottwitz.ZExtensionKernelProof, first in Library commit 497ef49830025d23824f6b2e2b1d5d60b594f51e) proves ZExtensionKottwitzKernelSurjectivityStatement: it obtains the first conjunct from Kottwitz.zExtensionUnramifiedKernelReduction and the second from Kottwitz.zExtensionRationalKernelReduction, each applied to published proofs. The theorem Kottwitz.unramifiedZeroKernel (module Langlands.Geometry.Building.Kottwitz.UnramifiedZeroKernelProof, first in Library commit e4a9b4d0164a5e0a9828dcaec5fa1cb7837ff8c6) proves UnramifiedZeroKernelStatement by applying Kottwitz.unramifiedZeroKernel_of_torus_zExtension to Kottwitz.torusKottwitzKernel, Kottwitz.simplyConnectedDerivedKottwitz_proof, Kottwitz.reductiveKottwitzExistence_assembled and Kottwitz.zExtensionKottwitzKernelSurjectivity, so the private weakening recorded in the follow-up of the twenty-fourth update is no longer needed. The theorem Kottwitz.zeroKernel_of_unramifiedZeroDescent of the same module applies Kottwitz.zeroKernel_of_unramified to Kottwitz.reductiveKottwitzDescent_assembled, the premise and Kottwitz.unramifiedZeroKernel; its type is the implication from UnramifiedZeroDescentStatement to ZeroKernelStatement. So ZeroKernelStatement follows from UnramifiedZeroDescentStatement alone by a published theorem. UnramifiedZeroDescentStatement (KP Proposition 9.3.24 with the Galois stability of G(K)^1 and G(K)^0) is unproved at Library commit 314cfd1a. Lean inspections of the five theorems are recorded below. The modules CentralTorusInertiaInjectivityProof and InducedTorusRationalSurjectivityProof are byte-identical between commit 2016a0d9 and Library commit 314cfd1a, the module ZExtensionKernelProof between commit 497ef498 and Library commit 314cfd1a, the module UnramifiedZeroKernelProof between commit e4a9b4d0 and Library commit 314cfd1a, and the modules cited earlier in this entry between Library commits 0b7bb3fd and 314cfd1a."
      ],
      "consumer_or_regression": "Identify the component quotient in Theorem 7.8.1(1), while keeping surjectivity and the Section 11.7 residue hypothesis separate.",
      "formal_status": "statement",
      "publication_commits": [
        "0c3f30c24701c74d5474fca3fbb5324a99aa1d58"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.ZeroKernelStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit 6948120d; kind definition; statement_returns_prop true; the module is byte-identical to commit 0c3f30c2."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.ReductiveKottwitzExistenceStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit 6948120d; kind definition; statement_returns_prop true; the module is byte-identical to commit 0c3f30c2."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.ReductiveKottwitzDescentStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit 6948120d; kind definition; statement_returns_prop true; the module is byte-identical to commit 0c3f30c2."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.zeroKernel_of_unramified",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit c40a0134; kind theorem, at universe level u, whose type is the implication from ReductiveKottwitzDescentStatement, UnramifiedZeroDescentStatement and UnramifiedZeroKernelStatement to ZeroKernelStatement; the module is byte-identical to commit 4f6abf4c, which first published it."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.zeroKernel_of_torus_zExtension",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 58ad0f79; kind theorem, at universe level u, whose type is the implication from TorusKottwitzKernelStatement, SimplyConnectedDerivedKottwitzStatement, ReductiveKottwitzExistenceStatement, ZExtensionKottwitzKernelSurjectivityStatement, ReductiveKottwitzDescentStatement and UnramifiedZeroDescentStatement to ZeroKernelStatement; the module is byte-identical to commit af5d652c, which first published it."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.zExtensionUnramifiedKernelReduction",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 320321b3; kind theorem, at universe level u, whose type is exactly ZExtensionUnramifiedKernelReductionStatement.{u}, the implication from ReductiveKottwitzExistenceStatement, ReductiveKottwitzFunctorialityStatement and CentralTorusInertiaExactnessStatement to ZExtensionUnramifiedKottwitzKernelStatement; the module is byte-identical to commit 7f5b5f04, which first published it."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.torusKottwitzKernel",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 51e9457f; kind theorem, at universe level u, whose type is exactly TorusKottwitzKernelStatement.{u}; the module is byte-identical to commit aeb3911c, which first published it."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.zExtensionRationalKernelReduction",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 51e9457f; kind theorem, at universe level u, whose type is exactly ZExtensionRationalKernelReductionStatement.{u}, the implication from ReductiveKottwitzFunctorialityStatement, ReductiveKottwitzDescentStatement, CentralTorusInertiaExactnessStatement, the two written-out propositions and ZExtensionPointSurjectivityStatement to ZExtensionRationalKottwitzKernelStatement; the module is byte-identical to commit aeb3911c, which first published it."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.InducedCentralTorusInertiaInjectivityStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 61b7fa40; kind definition, at universe level u; statement_returns_prop true; the module is byte-identical to commit fab9caea, which first published it, and to Library commit 0b7bb3fd."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.InducedCentralTorusInertiaInjectivityStatement.zExtension",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 61b7fa40; kind theorem, at universe level u, whose type is the implication from InducedCentralTorusInertiaInjectivityStatement to the injectivity of the selected map π₁(Z)_I → π₁(H)_I for every z-extension and every such tower k ⊆ K ⊆ E; the module is byte-identical to commit fab9caea, which first published it, and to Library commit 0b7bb3fd."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.InducedTorusKottwitzRationalSurjectivityStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 61b7fa40; kind definition, at universe level u; statement_returns_prop true; the module is byte-identical to commit fab9caea, which first published it, and to Library commit 0b7bb3fd."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.inducedCentralTorusInertiaInjectivity",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-16 at Library commit b44618a4; kind theorem, at universe level u, whose type is exactly InducedCentralTorusInertiaInjectivityStatement.{u}; the module was first published in Library commit 2016a0d9 and is byte-identical between that commit and Library commit 314cfd1a."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.inducedTorusKottwitzRationalSurjectivity",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-16 at Library commit b44618a4; kind theorem, at universe level u, whose type is exactly InducedTorusKottwitzRationalSurjectivityStatement.{u}; the module was first published in Library commit 2016a0d9 and is byte-identical between that commit and Library commit 314cfd1a."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.zExtensionKottwitzKernelSurjectivity",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-16 at Library commit b44618a4; kind theorem, at universe level u, whose type is exactly ZExtensionKottwitzKernelSurjectivityStatement.{u}; the module was first published in Library commit 497ef498 and is byte-identical between that commit and Library commit 314cfd1a."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.unramifiedZeroKernel",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-16 at Library commit b44618a4; kind theorem, at universe level u, whose type is exactly UnramifiedZeroKernelStatement.{u}; the module was first published in Library commit e4a9b4d0 and is byte-identical between that commit and Library commit 314cfd1a."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.zeroKernel_of_unramifiedZeroDescent",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-16 at Library commit b44618a4; kind theorem, at universe level u, whose type is the implication from UnramifiedZeroDescentStatement to ZeroKernelStatement; the module was first published in Library commit e4a9b4d0 and is byte-identical between that commit and Library commit 314cfd1a."
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
        "Recorded Lean scope: ChamberStatement (module Langlands.Geometry.Building.Kottwitz.ChamberStatement) asserts, for every nonarchimedean local field F and connected reductive G over Spec F, that κ_G is surjective, together with a chamber clause on supplied building data. For a commutative group scheme T with iT : T → G whose scalar extension to K is a maximal split torus of G_K, a class D : KPApartmentData of valuations of the root datum of (G_K, T_K) with centralizer datum C satisfying V 6 (IntegerValuation.IsOmegaCompatible) and Galois stability (KPApartmentData.GaloisStable), let B be the building data UnramifiedBuildingDescent.buildingData built from them. For every chamber C' of B that the coefficient Galois action of UnramifiedBuildingDescent.semilinearData maps onto itself and for every ZeroSubgroupDatum d of G, whose d.zeroSubgroup is the Library's G(F)^0 (see the Proposition 11.5.4 row), let P be the preimage in G(F) of the stabilizer of C' in G(K) and N = G(F)^0 ∩ P. Then N is normal in P and some isomorphism P/N ≃ A^Γ sends the class of x to κ_G(x). Surjectivity is unconditional; the chamber clause concerns the supplied building data, and the existence of a Γ-stable chamber (Proposition 9.10.4) is not asserted. K is the Library's maximal unramified extension UnramifiedClosure F inside the separable closure SeparableClosure F. ReductiveInvariantTarget F G hG is A^Γ for A = π_1(G)_I, the integral inertia coinvariants of the actual algebraic fundamental group, with the actual residual action of Γ = Gal(K/F); fundamentalInvariantTorsion is (A_tor)^Γ as a subgroup of A^Γ. κ_G is reductiveKottwitzRational F G hG (module Langlands.Geometry.Building.Kottwitz.ReductiveMap), selected by classical epsilon among the homomorphisms G(F) → A^Γ whose composite with A^Γ → A is the K-point map reductiveKottwitz on the image of G(F) in G(K). reductiveKottwitz is in turn selected by its squares with every z-extension, over the simply-connected-derived construction through every cocenter. That both selections have their characterizing properties is asserted by ReductiveKottwitzExistenceStatement (existence of z-extensions and unique existence, surjectivity and independence of the K-point map) and ReductiveKottwitzDescentStatement (residual Galois equivariance and unique existence of the restriction to G(F)), both in module Langlands.Geometry.Building.Kottwitz.ReductiveMapStatement; both are proved, by Kottwitz.reductiveKottwitzExistence_assembled and Kottwitz.reductiveKottwitzDescent_assembled (module Langlands.Geometry.Building.Kottwitz.ZExtensionKernelProof; Lemma 11.5.2 row). The source's Henselian discretely valued fields with perfect residue field are specialized to nonarchimedean local fields of either characteristic in universe u; their residue fields are finite."
      ],
      "conclusion": "kappa_G:G(k)→A^Gamma is surjective and induces an isomorphism G(k)_C/G(k)^0_C≃A^Gamma. The chosen chamber is over K; do not silently replace it by an arbitrary k-chamber.",
      "lean_declarations": [
        "Langlands.Geometry.Building.Kottwitz.ChamberStatement",
        "Langlands.Geometry.Building.Kottwitz.ReductiveKottwitzExistenceStatement",
        "Langlands.Geometry.Building.Kottwitz.ReductiveKottwitzDescentStatement",
        "Langlands.Geometry.Building.Kottwitz.chamberStatement_of_remainingInputs",
        "Langlands.GroupScheme.IntegralModel.unramifiedSmoothModelDescent",
        "Langlands.Geometry.Building.Kottwitz.unramifiedChamberExactSequence_of_statements",
        "Langlands.Geometry.Building.MaximalUnramified.simplyConnectedNormalizerAffineWeyl",
        "Langlands.Geometry.Building.unramifiedTwistedChamber_of_metric",
        "Langlands.Geometry.Building.unramifiedBuildingMetric",
        "Langlands.Geometry.Building.unramifiedTwistedChamberThroughFixedPoint_of_generator",
        "Langlands.Geometry.Building.unramifiedTwistedGeneratorChamber_of_quotient",
        "Langlands.Geometry.Building.unramifiedTwistedChamberQuotient_of_residueQuotient",
        "Langlands.Geometry.Building.unramifiedTwistedResidueQuotient_of_inputs",
        "Langlands.BruhatTits.IntegralModels.unramifiedTwistedReductiveQuotientDescent",
        "Langlands.Geometry.Building.Kottwitz.unramifiedChamberExactSequence",
        "Langlands.BruhatTits.IntegralModels.unramifiedParahoricModel",
        "Langlands.GroupScheme.connectedGeneration",
        "Langlands.BruhatTits.IntegralModels.unramifiedUpstairsRadicalRootGeneration",
        "Langlands.Geometry.Building.unramifiedTwistedResidueQuotient",
        "Langlands.Geometry.Building.unramifiedTwistedChamberQuotient",
        "Langlands.Geometry.Building.unramifiedTwistedChamberThroughFixedPoint",
        "Langlands.Geometry.Building.unramifiedTwistedChamber"
      ],
      "modules": [
        "Langlands.Geometry.Building.Kottwitz.ChamberStatement",
        "Langlands.Geometry.Building.Kottwitz.ReductiveMapStatement",
        "Langlands.Geometry.Building.Kottwitz.RationalSurjectivityReduction",
        "Langlands.GroupScheme.IntegralModel.UnramifiedSmoothDescentProof",
        "Langlands.Geometry.Building.Kottwitz.UnramifiedChamberExactSequenceReduction",
        "Langlands.Geometry.Building.UnramifiedSimplyConnectedNormalizerAffineWeylProof",
        "Langlands.Geometry.Building.UnramifiedTwistedChamberReduction",
        "Langlands.Geometry.Building.UnramifiedBuildingMetricProof",
        "Langlands.Geometry.Building.UnramifiedTwistedChamberThroughFixedPointReduction",
        "Langlands.Geometry.Building.UnramifiedTwistedChamberQuotientReduction",
        "Langlands.Geometry.Building.UnramifiedTwistedChamberQuotientResidueReduction",
        "Langlands.Geometry.Building.UnramifiedTwistedResidueQuotientReduction",
        "Langlands.BruhatTits.IntegralModels.UnramifiedTwistedReductiveQuotientDescent",
        "Langlands.Geometry.Building.Kottwitz.UnramifiedChamberExactSequenceProof",
        "Langlands.BruhatTits.IntegralModels.UnramifiedParahoricModelProof",
        "Langlands.GroupScheme.IntegralModel.ConnectedGenerationProof",
        "Langlands.BruhatTits.IntegralModels.UnramifiedUpstairsRadicalRootGenerationProof",
        "Langlands.Geometry.Building.UnramifiedTwistedResidueQuotientProof",
        "Langlands.Geometry.Building.UnramifiedTwistedChamberQuotientProof",
        "Langlands.Geometry.Building.UnramifiedTwistedChamberThroughFixedPointProof",
        "Langlands.Geometry.Building.UnramifiedTwistedChamberProof"
      ],
      "dependencies": [
        "Existence of a Gamma-stable K-chamber, Proposition 9.10.4",
        "Proposition 11.6.1 exact sequence over K, Theorem 8.3.13 smooth connected-fibre chamber model, and Lemma 8.1.4 cohomology vanishing",
        "The target is the actual Kottwitz homomorphism (KP Proposition 11.1.1, Definition 11.3.2, Lemma 11.5.1) over every nonarchimedean local field, with this statement over it for the Library's G(F)^0 and G(F)^1. The Library states ChamberStatement (first in Library commit 0c3f30c24701c74d5474fca3fbb5324a99aa1d58) together with the selected maps and ReductiveKottwitzExistenceStatement and ReductiveKottwitzDescentStatement (module ReductiveMapStatement, same commit). On that date none of these statements is proved. Reduction (twentieth update, 14 November 2026): the theorem Kottwitz.chamberStatement_of_remainingInputs (module Langlands.Geometry.Building.Kottwitz.RationalSurjectivityReduction, first in Library commit 4f6abf4c7e19610e4d89edc9bf64b34ba1db9ff2) derives ChamberStatement from seven statements: SpecialTorusExistenceStatement (Proposition 9.3.4 row); UnramifiedTwistedChamberStatement (module Langlands.Geometry.Building.UnramifiedTwistedChamberStatement, first in Library commit 51e4d8972659f1ffcf0ca89e8eee9540a30b52d3; a chamber of the building over K stable under the Galois action twisted by a finite-level cocycle, with Proposition 9.10.4 as source); UnramifiedParahoricModelStatement (module Langlands.BruhatTits.IntegralModels.UnramifiedParahoricModelStatement, first in Library commit cc5aa77fa8dbdc6e723091c7b710ab0d81162c4e; KP Theorems 8.3.2 and 8.3.13 over the integers of K); IntegralModel.UnramifiedSmoothModelDescentStatement (module Langlands.GroupScheme.IntegralModel.UnramifiedSmoothDescent, first in the same commit; KP Fact 2.10.16); UnramifiedChamberExactSequenceStatement (module Langlands.Geometry.Building.Kottwitz.UnramifiedChamberExactSequenceStatement, first in Library commit 4f6abf4c7e19610e4d89edc9bf64b34ba1db9ff2; KP Proposition 11.6.1 on supplied K-building data); ReductiveKottwitzDescentStatement; and ZeroKernelStatement (Proposition 11.5.4 row). It applies chamberStatement_of_surjective_of_geometricInputs (module Langlands.Geometry.Building.Kottwitz.RationalChamberQuotientReduction, first in the same commit), which takes the surjectivity of κ_G as a further input, to the surjectivity given by the published rationalSurjectivityReduction. One input is proved: the theorem IntegralModel.unramifiedSmoothModelDescent (module Langlands.GroupScheme.IntegralModel.UnramifiedSmoothDescentProof, first in Library commit e5365902d74534dbf1622c06e695dffdc128d723) proves UnramifiedSmoothModelDescentStatement. Lean inspections of the two theorems are recorded below. On 14 November 2026 the other six inputs are unproved. Each module cited in this paragraph is byte-identical between its first commit and Library commit c40a0134. Twenty-second update (14 November 2026): the theorem Kottwitz.unramifiedChamberExactSequence_of_statements (module Langlands.Geometry.Building.Kottwitz.UnramifiedChamberExactSequenceReduction, first in Library commit b3a1bdaf15715f16a43643513b7cbb6cbb58ef3a) derives UnramifiedChamberExactSequenceStatement from ReductiveKottwitzExistenceStatement, UnramifiedZeroKernelStatement (Proposition 11.5.4 row) and MaximalUnramified.SimplyConnectedNormalizerAffineWeylStatement. The theorem MaximalUnramified.simplyConnectedNormalizerAffineWeyl (module Langlands.Geometry.Building.UnramifiedSimplyConnectedNormalizerAffineWeylProof, first in the same commit) proves the last: for a simply connected group over the maximal unramified extension and any supplied building data, the image of the normalizer action on the apartment is the affine Weyl group of its affine roots. That statement is over the maximal unramified extension; it is not the statement SimplyConnectedNormalizerAffineWeylStatement of the Theorem 7.5.3 and 7.8.1 rows, which is unproved at Library commit 4f4af6ba. With the reduction of the Proposition 11.5.4 row, ChamberStatement therefore follows from SpecialTorusExistenceStatement, UnramifiedTwistedChamberStatement, UnramifiedParahoricModelStatement, ReductiveKottwitzExistenceStatement, ReductiveKottwitzDescentStatement, UnramifiedZeroDescentStatement and UnramifiedZeroKernelStatement, none of which is proved at Library commit 4f4af6ba. No published declaration states this composite; it was checked with a separate Lean check (Library commit 4f4af6ba, only propext, Classical.choice and Quot.sound). Lean inspections of the two theorems are recorded below. The two modules cited in this update are byte-identical between commit b3a1bdaf and Library commit 4f4af6ba, and the modules cited earlier in this paragraph are byte-identical between Library commits c40a0134 and 4f4af6ba. Follow-up (twenty-second update, Library commit 58ad0f79): the reduction recorded in the Proposition 11.5.4 row replaces UnramifiedZeroKernelStatement by TorusKottwitzKernelStatement, ReductiveKottwitzExistenceStatement and ZExtensionKottwitzKernelSurjectivityStatement. So ChamberStatement follows from eight statements: SpecialTorusExistenceStatement, UnramifiedTwistedChamberStatement, UnramifiedParahoricModelStatement, ReductiveKottwitzExistenceStatement, ReductiveKottwitzDescentStatement, UnramifiedZeroDescentStatement, TorusKottwitzKernelStatement and ZExtensionKottwitzKernelSurjectivityStatement. The Lemma 11.5.2 row reduces ReductiveKottwitzExistenceStatement further. No published declaration states this composite; it was checked with a separate Lean check (Library commit 58ad0f79, only propext, Classical.choice and Quot.sound). None of these eight statements is proved at Library commit 58ad0f79. The modules cited in this paragraph are byte-identical between Library commits 4f4af6ba and 58ad0f79. Follow-up (twenty-fourth update, Library commit 7229bb45): TorusKottwitzKernelStatement, one of the eight statements of the previous follow-up, is proved (Proposition 11.5.4 row). With the private weakening recorded in the Proposition 11.5.4 row and the reduction of ReductiveKottwitzExistenceStatement in the Lemma 11.5.2 row, ChamberStatement follows from seven statements that include neither ZExtensionKottwitzKernelSurjectivityStatement nor UnramifiedZeroKernelStatement: SpecialTorusExistenceStatement, UnramifiedTwistedChamberStatement, UnramifiedParahoricModelStatement, CentralTorusInertiaExactnessStatement, ZExtensionCommonDominationStatement, ReductiveKottwitzDescentStatement and UnramifiedZeroDescentStatement. No published declaration states this composite; it was checked with a separate Lean check (Library commit 7229bb45, only propext, Classical.choice and Quot.sound). None of these seven statements is proved at Library commit 7229bb45. The modules cited in this paragraph are byte-identical between Library commits 58ad0f79 and 7229bb45. Follow-up (twenty-fifth update, Library commit 49668e4d): ZExtensionCommonDominationStatement, one of the seven statements of the previous follow-up, is proved (Lemma 11.5.2 row). So, with the private weakening recorded in the Proposition 11.5.4 row, ChamberStatement follows from six statements: SpecialTorusExistenceStatement, UnramifiedTwistedChamberStatement, UnramifiedParahoricModelStatement, CentralTorusInertiaExactnessStatement, ReductiveKottwitzDescentStatement and UnramifiedZeroDescentStatement. Published theorems also reduce UnramifiedTwistedChamberStatement in five steps. The theorem unramifiedTwistedChamber_of_metric (module Langlands.Geometry.Building.UnramifiedTwistedChamberReduction, whose entry declaration is UnramifiedTwistedChamberReductionStatement, first in Library commit 85c2fe719cf62e96f22aaf4ca03961c5814d086b) derives it from UnramifiedBuildingMetricStatement and UnramifiedTwistedChamberThroughFixedPointStatement. The theorem unramifiedBuildingMetric (module Langlands.Geometry.Building.UnramifiedBuildingMetricProof, first in Library commit af5d652c2f2ff5b35b4ce4dbbf7cbec8bbf3e99e) proves UnramifiedBuildingMetricStatement. The theorem unramifiedTwistedChamberThroughFixedPoint_of_generator (module Langlands.Geometry.Building.UnramifiedTwistedChamberThroughFixedPointReduction, whose entry declaration is UnramifiedTwistedChamberThroughFixedPointReductionStatement, first in Library commit e5365902d74534dbf1622c06e695dffdc128d723) derives UnramifiedTwistedChamberThroughFixedPointStatement from UnramifiedTwistedGeneratorChamberStatement, stability under one Frobenius generator. The theorem unramifiedTwistedGeneratorChamber_of_quotient (module Langlands.Geometry.Building.UnramifiedTwistedChamberQuotientReduction, whose entry declaration is UnramifiedTwistedChamberQuotientReductionStatement, first in Library commit 410c79471b79f65a02fb0f6070da7f2800793ff3) derives UnramifiedTwistedGeneratorChamberStatement from UnramifiedTwistedChamberQuotientStatement. The theorem unramifiedTwistedChamberQuotient_of_residueQuotient (module Langlands.Geometry.Building.UnramifiedTwistedChamberQuotientResidueReduction, whose entry declaration is UnramifiedTwistedChamberQuotientResidueReductionStatement, first in Library commit b3a1bdaf15715f16a43643513b7cbb6cbb58ef3a) derives UnramifiedTwistedChamberQuotientStatement from UnramifiedTwistedResidueQuotientStatement. The theorem unramifiedTwistedResidueQuotient_of_inputs (module Langlands.Geometry.Building.UnramifiedTwistedResidueQuotientReduction, whose entry declaration is UnramifiedTwistedResidueQuotientInputsReductionStatement, first in Library commit 4abbe7aabd9c92005d91c9d5bba86b879e928bb3) derives UnramifiedTwistedResidueQuotientStatement from three statements: UnramifiedParahoricModelStatement; IntegralModels.UnramifiedUpstairsRadicalRootGenerationStatement (Theorem 8.4.19 row); and IntegralModels.UnramifiedTwistedReductiveQuotientDescentStatement (module Langlands.BruhatTits.IntegralModels.UnramifiedTwistedReductiveQuotientDescentStatement, first in Library commit aeb3911c4e1bf6e3a2f653e874e4ebc422d2a61a; for a smooth model over the integers of K with connected fibres whose integral points are stable under the twisted action and a lift φ of the arithmetic Frobenius, the reductive quotient of its special fibre descends to the residue field of F compatibly with the twisted action of φ, with KP Fact 2.10.16 and Sections 9.1 and 9.2 as sources). So UnramifiedTwistedChamberStatement follows from these three statements, and ChamberStatement follows from seven: SpecialTorusExistenceStatement, UnramifiedParahoricModelStatement, UnramifiedUpstairsRadicalRootGenerationStatement, UnramifiedTwistedReductiveQuotientDescentStatement, CentralTorusInertiaExactnessStatement, ReductiveKottwitzDescentStatement and UnramifiedZeroDescentStatement. No published declaration states these composites; The reduction of UnramifiedTwistedChamberStatement, which uses published reductions and proofs only, and the two composites for ChamberStatement were checked with separate Lean checks (Library commit c2a69151, only propext, Classical.choice and Quot.sound). Lean inspections of the six theorems are recorded below. None of the eight statements named in the two lists of this follow-up, and none of UnramifiedTwistedChamberThroughFixedPointStatement, UnramifiedTwistedGeneratorChamberStatement, UnramifiedTwistedChamberQuotientStatement and UnramifiedTwistedResidueQuotientStatement, is proved at Library commit 49668e4d. The six modules of these theorems are byte-identical between the commits that first published them and Library commit 49668e4d; for UnramifiedTwistedChamberReduction, the Lean and Markdown files at Library commit 49668e4d have the SHA-256 hashes recorded when they were first checked. The modules cited earlier in this paragraph are byte-identical between Library commits 7229bb45 and 49668e4d. Follow-up (twenty-sixth update, Library commit 0b7bb3fd): SpecialTorusExistenceStatement and CentralTorusInertiaExactnessStatement are proved by the theorems specialTorusExistence (Proposition 9.3.4 row) and Kottwitz.centralTorusInertiaExactness (Lemma 11.5.2 row). So, with the private weakening recorded in the Proposition 11.5.4 row, ChamberStatement follows from four statements: UnramifiedTwistedChamberStatement, UnramifiedParahoricModelStatement, ReductiveKottwitzDescentStatement and UnramifiedZeroDescentStatement. With the published reduction of UnramifiedTwistedChamberStatement recorded in the previous follow-up, it follows from five: UnramifiedParahoricModelStatement, UnramifiedUpstairsRadicalRootGenerationStatement, UnramifiedTwistedReductiveQuotientDescentStatement, ReductiveKottwitzDescentStatement and UnramifiedZeroDescentStatement. No published declaration states these composites; both were checked with separate Lean checks (Library commit fab9caea, only propext, Classical.choice and Quot.sound). None of the six statements named in this follow-up is proved at Library commit 0b7bb3fd. The modules cited earlier in this paragraph are byte-identical between Library commits 49668e4d and 0b7bb3fd. Follow-up (twenty-ninth update, Library commit 7cb8c3d3): the theorem IntegralModels.unramifiedTwistedReductiveQuotientDescent (module Langlands.BruhatTits.IntegralModels.UnramifiedTwistedReductiveQuotientDescent, first in Library commit b3dcc8cc4c93f1140c6b34374f589ccc637a1a22) proves UnramifiedTwistedReductiveQuotientDescentStatement. As the Markdown of that module describes, its proof descends the neutral model along the inner twist, by the published finite inner recovery, to a smooth model over the integers of F, and takes the quotient of the special fibre of that model by its unipotent radical. This quotient is connected reductive because the residue field of F is perfect, and its Frobenius compatibility comes from identifying twisted conjugation with descent transport. Its Lean inspection is recorded below. The Theorem 8.3.13 row records that UnramifiedParahoricModelStatement follows from Langlands.GroupScheme.ConnectedGenerationStatement (KP Lemma A.4.26) alone by published reductions and proofs. So, with the private weakening recorded in the Proposition 11.5.4 row, ChamberStatement follows from four statements: UnramifiedTwistedChamberStatement, ConnectedGenerationStatement, ReductiveKottwitzDescentStatement and UnramifiedZeroDescentStatement. With the published reduction of UnramifiedTwistedChamberStatement recorded in the follow-up of the twenty-fifth update, whose third input is now proved, it also follows from four: ConnectedGenerationStatement, UnramifiedUpstairsRadicalRootGenerationStatement, ReductiveKottwitzDescentStatement and UnramifiedZeroDescentStatement. No published declaration states these composites. The first was checked with a separate Lean check (Library commit b3dcc8cc, only propext, Classical.choice and Quot.sound). For the second, a separate Lean check derives ChamberStatement from these four statements and UnramifiedTwistedReductiveQuotientDescentStatement (same commit and axioms), and the inspection recorded below shows that the published proof has exactly the type of that statement. The second composite also uses the published proof unramifiedBuildingMetric of an input of that reduction (twenty-fifth-pass follow-up), and at Library commit b3dcc8cc no Lean file can import both its module UnramifiedBuildingMetricProof and the module UnramifiedTwistedReductiveQuotientDescent. The first imports, indirectly, Langlands.Geometry.Building.IntegerValuationBuildingMetricReduction and the second, indirectly, Langlands.Geometry.Building.IntegerBuildingFacetCentroids. Both of these modules declare an unnamed local instance NormedSpace ℝ (TranslationSpace B.i) in the namespace Langlands.Geometry.Building.IntegerValuationBuildingData, which Lean names instNormedSpaceRealTranslationSpaceI in both, so the import fails. With a private copy of IntegerBuildingFacetCentroids in which its three unnamed local instances are given names, the second composite compiles in a single file (only propext, Classical.choice and Quot.sound). None of UnramifiedTwistedChamberStatement, ConnectedGenerationStatement, UnramifiedUpstairsRadicalRootGenerationStatement, ReductiveKottwitzDescentStatement and UnramifiedZeroDescentStatement is proved at Library commit 7cb8c3d3. The module UnramifiedTwistedReductiveQuotientDescent is byte-identical between commit b3dcc8cc, which first published it, and Library commit 7cb8c3d3, and the modules cited earlier in this paragraph are byte-identical between Library commits 0b7bb3fd and 7cb8c3d3. Follow-up (thirty-first update, Library commit 314cfd1a): the theorem Kottwitz.unramifiedChamberExactSequence (module Langlands.Geometry.Building.Kottwitz.UnramifiedChamberExactSequenceProof, first in Library commit e9c05be9da1000900a43de75ec2ede66892aa158) proves UnramifiedChamberExactSequenceStatement by applying Kottwitz.unramifiedChamberExactSequence_of_statements to published proofs. The theorem IntegralModels.unramifiedParahoricModel (module Langlands.BruhatTits.IntegralModels.UnramifiedParahoricModelProof, first in Library commit c0c2e1210454ae2a1888a2989e3de794c1336819) proves UnramifiedParahoricModelStatement. ReductiveKottwitzDescentStatement is proved, and ZeroKernelStatement follows from UnramifiedZeroDescentStatement by the published theorem Kottwitz.zeroKernel_of_unramifiedZeroDescent (Lemma 11.5.2 and Proposition 11.5.4 rows). So ChamberStatement follows from UnramifiedTwistedChamberStatement and UnramifiedZeroDescentStatement by published reductions and proofs, without the private weakening. No published declaration states this composite; it was checked with a separate Lean check that applies Kottwitz.chamberStatement_of_remainingInputs to specialTorusExistence, the twisted-chamber premise, IntegralModels.unramifiedParahoricModel, IntegralModel.unramifiedSmoothModelDescent, Kottwitz.unramifiedChamberExactSequence, Kottwitz.reductiveKottwitzDescent_assembled and Kottwitz.zeroKernel_of_unramifiedZeroDescent applied to the zero-descent premise (Library commit 276bcb8d, only propext, Classical.choice and Quot.sound). UnramifiedTwistedChamberStatement now follows from published proofs. The theorem unramifiedTwistedResidueQuotient (module Langlands.Geometry.Building.UnramifiedTwistedResidueQuotientProof, first in Library commit a2dba61c0a2313b5533c11ee999bece88bb28845) proves UnramifiedTwistedResidueQuotientStatement by applying the published reduction unramifiedTwistedResidueQuotientInputsReduction to published proofs: a parahoric model assembled from published torus proofs, the theorem IntegralModels.unramifiedUpstairsRadicalRootGeneration (module Langlands.BruhatTits.IntegralModels.UnramifiedUpstairsRadicalRootGenerationProof), which proves UnramifiedUpstairsRadicalRootGenerationStatement, and IntegralModels.unramifiedTwistedReductiveQuotientDescent. One of the torus assemblies uses the theorem GroupScheme.connectedGeneration (module Langlands.GroupScheme.IntegralModel.ConnectedGenerationProof), which proves ConnectedGenerationStatement; it and unramifiedUpstairsRadicalRootGeneration were first published in Library commit e9c05be9da1000900a43de75ec2ede66892aa158. The theorem unramifiedTwistedChamberQuotient (module Langlands.Geometry.Building.UnramifiedTwistedChamberQuotientProof, first in Library commit a98af0ff45faf7905209f65d641389deee5d8392) applies the published reduction unramifiedTwistedChamberQuotientResidueReduction to unramifiedTwistedResidueQuotient, and the theorem unramifiedTwistedChamberThroughFixedPoint (module Langlands.Geometry.Building.UnramifiedTwistedChamberThroughFixedPointProof, first in Library commit d210ab55a138c1f91b826ee47c6280ce6c6b90bc) applies the published theorems unramifiedTwistedChamberThroughFixedPointReduction and unramifiedTwistedGeneratorChamber_of_quotient to unramifiedTwistedChamberQuotient; it proves UnramifiedTwistedChamberThroughFixedPointStatement. The published theorem unramifiedTwistedChamber_of_metric derives UnramifiedTwistedChamberStatement from it and unramifiedBuildingMetric. No published declaration states this composite, and at Library commit 314cfd1a no Lean file can import both of their modules: UnramifiedTwistedChamberThroughFixedPointProof imports UnramifiedTwistedResidueQuotientProof through UnramifiedTwistedChamberQuotientProof, and the clash described in the follow-up of the twenty-ninth update persists. A private file that imports UnramifiedBuildingMetricProof and UnramifiedTwistedResidueQuotientProof fails with the same error (Library commit 276bcb8d). Without the private copy described there, separate Lean checks derive UnramifiedTwistedChamberStatement from UnramifiedTwistedResidueQuotientStatement, taken as a premise because its proof module cannot be imported together with UnramifiedBuildingMetricProof, through the published chain of reductions recorded in the follow-up of the twenty-fifth update and unramifiedBuildingMetric, and ChamberStatement from UnramifiedTwistedResidueQuotientStatement and UnramifiedZeroDescentStatement. With that private copy, separate Lean checks prove UnramifiedTwistedChamberStatement as unramifiedTwistedChamber_of_metric applied to unramifiedBuildingMetric and unramifiedTwistedChamberThroughFixedPoint, and derive ChamberStatement from UnramifiedZeroDescentStatement alone. These four runs are at Library commit 276bcb8d and report only propext, Classical.choice and Quot.sound. UnramifiedZeroDescentStatement is unproved at Library commit 314cfd1a, and no published declaration has the type UnramifiedTwistedChamberStatement there. Lean inspections of the seven theorems named in this follow-up that are added to this row are recorded below. Each module added to this row in this follow-up is byte-identical between its first commit and Library commit 314cfd1a, and the modules cited earlier in this entry between Library commits 7cb8c3d3 and 314cfd1a. Follow-up (thirty-third update, Library commit b369a8f2): the theorem unramifiedTwistedChamber (module Langlands.Geometry.Building.UnramifiedTwistedChamberProof, first in Library commit 9e39a73d21bd6ed6fac00b01cc5e01c0db5d105b) proves UnramifiedTwistedChamberStatement: it applies the published theorem unramifiedTwistedChamber_of_metric to unramifiedBuildingMetric and unramifiedTwistedChamberThroughFixedPoint, and its module imports both of their modules. The clash described in the follow-up of the twenty-ninth update is gone: two contributions first in Library commit 9e39a73d, this proof and a new version of the module, name the three local instances of the module Langlands.Geometry.Building.IntegerBuildingFacetCentroids centroidNormedAddCommGroup, centroidNormedSpace and centroidFiniteDimensional, and the file at Library commit b369a8f2 is the version of the second, which adds a comment. The private copy described there is no longer needed. The theorems GroupScheme.connectedGeneration, IntegralModels.unramifiedParahoricModel and IntegralModels.unramifiedUpstairsRadicalRootGeneration used in the chain above are proved (thirty-first-pass follow-up). So ChamberStatement follows from UnramifiedZeroDescentStatement alone by published reductions and proofs. No published declaration states this composite; it was checked with a separate Lean check that applies the composite of the follow-up of the thirty-first update to unramifiedTwistedChamber and the zero-descent premise, with published modules only (Library commit 8f4a33d7, only propext, Classical.choice and Quot.sound). UnramifiedZeroDescentStatement is unproved at Library commit b369a8f2. The Lean inspection of unramifiedTwistedChamber is recorded below. The module UnramifiedTwistedChamberProof is byte-identical between commit 9e39a73d and Library commit b369a8f2, and the modules cited earlier in this entry between Library commits 314cfd1a and b369a8f2, except IntegerBuildingFacetCentroids, which changed in commit 9e39a73d as described."
      ],
      "consumer_or_regression": "Length-zero/component representatives for the Iwahori–Weyl and Hecke interfaces over local fields.",
      "formal_status": "statement",
      "publication_commits": [
        "0c3f30c24701c74d5474fca3fbb5324a99aa1d58"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.ChamberStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit 6948120d; kind definition; statement_returns_prop true; the module is byte-identical to commit 0c3f30c2."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.ReductiveKottwitzExistenceStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit 6948120d; kind definition; statement_returns_prop true; the module is byte-identical to commit 0c3f30c2."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.ReductiveKottwitzDescentStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit 6948120d; kind definition; statement_returns_prop true; the module is byte-identical to commit 0c3f30c2."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.chamberStatement_of_remainingInputs",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit c40a0134; kind theorem, at universe level u, whose type is the implication from the seven statements named in the dependencies to ChamberStatement; the module is byte-identical to commit 4f6abf4c, which first published it."
        },
        {
          "declaration": "Langlands.GroupScheme.IntegralModel.unramifiedSmoothModelDescent",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit c40a0134; kind theorem, at universe level u, whose type is exactly IntegralModel.UnramifiedSmoothModelDescentStatement.{u}; the module is byte-identical to commit e5365902, which first published it."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.unramifiedChamberExactSequence_of_statements",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 4f4af6ba; kind theorem, at universe level u, whose type is the implication from ReductiveKottwitzExistenceStatement, UnramifiedZeroKernelStatement and MaximalUnramified.SimplyConnectedNormalizerAffineWeylStatement to UnramifiedChamberExactSequenceStatement; the module is byte-identical to commit b3a1bdaf, which first published it."
        },
        {
          "declaration": "Langlands.Geometry.Building.MaximalUnramified.simplyConnectedNormalizerAffineWeyl",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 4f4af6ba; kind theorem, at universe level u, whose type is exactly MaximalUnramified.SimplyConnectedNormalizerAffineWeylStatement.{u}; the module is byte-identical to commit b3a1bdaf, which first published it."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedTwistedChamber_of_metric",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 49668e4d; kind theorem, at universe level u, whose type is the implication from UnramifiedBuildingMetricStatement and UnramifiedTwistedChamberThroughFixedPointStatement to UnramifiedTwistedChamberStatement; the module is byte-identical to the files first published in commit 85c2fe71."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedBuildingMetric",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 49668e4d; kind theorem, at universe level u, whose type is exactly UnramifiedBuildingMetricStatement.{u}; the module is byte-identical to commit af5d652c, which first published it."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedTwistedChamberThroughFixedPoint_of_generator",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 49668e4d; kind theorem, at universe level u, whose type is exactly UnramifiedTwistedChamberThroughFixedPointReductionStatement.{u}, the implication from UnramifiedTwistedGeneratorChamberStatement to UnramifiedTwistedChamberThroughFixedPointStatement; the module is byte-identical to commit e5365902, which first published it."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedTwistedGeneratorChamber_of_quotient",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 49668e4d; kind theorem, at universe level u, whose type is the implication from UnramifiedTwistedChamberQuotientStatement to UnramifiedTwistedGeneratorChamberStatement; the module is byte-identical to commit 410c7947, which first published it."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedTwistedChamberQuotient_of_residueQuotient",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 49668e4d; kind theorem, at universe level u, whose type is the implication from UnramifiedTwistedResidueQuotientStatement to UnramifiedTwistedChamberQuotientStatement; the module is byte-identical to commit b3a1bdaf, which first published it."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedTwistedResidueQuotient_of_inputs",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 49668e4d; kind theorem, at universe level u, whose type is the implication from UnramifiedParahoricModelStatement, UnramifiedUpstairsRadicalRootGenerationStatement and UnramifiedTwistedReductiveQuotientDescentStatement to UnramifiedTwistedResidueQuotientStatement; the module is byte-identical to commit 4abbe7aa, which first published it."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.unramifiedTwistedReductiveQuotientDescent",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit b3dcc8cc; kind theorem, at universe level u, whose type is exactly UnramifiedTwistedReductiveQuotientDescentStatement.{u}; the module was first published in that commit and is byte-identical at Library commit 7cb8c3d3."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.unramifiedChamberExactSequence",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-16 at Library commit b44618a4; kind theorem, at universe level u, whose type is exactly UnramifiedChamberExactSequenceStatement.{u}; the module was first published in Library commit e9c05be9 and is byte-identical between that commit and Library commit 314cfd1a."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.unramifiedParahoricModel",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-16 at Library commit b44618a4; kind theorem, at universe level u, whose type is exactly UnramifiedParahoricModelStatement.{u}; the module was first published in Library commit c0c2e121 and is byte-identical between that commit and Library commit 314cfd1a."
        },
        {
          "declaration": "Langlands.GroupScheme.connectedGeneration",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-16 at Library commit b44618a4; kind theorem, at universe level u, whose type is exactly ConnectedGenerationStatement.{u}; the module was first published in Library commit e9c05be9 and is byte-identical between that commit and Library commit 314cfd1a."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.unramifiedUpstairsRadicalRootGeneration",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-16 at Library commit b44618a4; kind theorem, at universe level u, whose type is exactly UnramifiedUpstairsRadicalRootGenerationStatement.{u}; the module was first published in Library commit e9c05be9 and is byte-identical between that commit and Library commit 314cfd1a."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedTwistedResidueQuotient",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-16 at Library commit b44618a4; kind theorem, at universe level u, whose type is exactly UnramifiedTwistedResidueQuotientStatement.{u}; the module was first published in Library commit a2dba61c and is byte-identical between that commit and Library commit 314cfd1a."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedTwistedChamberQuotient",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit 276bcb8d; kind theorem, at universe level u, whose type is exactly UnramifiedTwistedChamberQuotientStatement.{u}; the module was first published in Library commit a98af0ff and is byte-identical between that commit and Library commit 314cfd1a."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedTwistedChamberThroughFixedPoint",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit 276bcb8d; kind theorem, at universe level u, whose type is exactly UnramifiedTwistedChamberThroughFixedPointStatement.{u}; the module was first published in Library commit d210ab55 and is byte-identical between that commit and Library commit 314cfd1a."
        },
        {
          "declaration": "Langlands.Geometry.Building.unramifiedTwistedChamber",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit 8f4a33d7; kind theorem, at universe level u, whose type is exactly UnramifiedTwistedChamberStatement.{u}; the module was first published in Library commit 9e39a73d and is byte-identical between that commit and Library commit b369a8f2."
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
        "Recorded Lean scope: QuotientStatement (module Langlands.Geometry.Building.Kottwitz.QuotientStatement) quantifies over every nonarchimedean local field F, connected reductive G over Spec F and every ZeroSubgroupDatum d for a maximal split torus i : S → G and a representative j : Z → G of its centralizer, which carries data of Definition 2.6.23(1) for Z_K and a simply connected cover of the derived subgroup; d.zeroSubgroup is the Library's G(F)^0 = G(F)^♮ · Z(F)^0 of Definition 2.6.23(3). With N = d.zeroSubgroup and H = characterValuationKernel (ValuativeRel.valuation F) G, the Library's G(F)^1, it asserts that N is normal, N ≤ H, and that there are isomorphisms G(F)/N ≃ A^Γ, H/N ≃ (A_tor)^Γ and G(F)/H ≃ A^Γ/(A_tor)^Γ, each sending the class of g to κ_G(g) or its image. The third quotient is formed as A^Γ/(A_tor)^Γ. K is the Library's maximal unramified extension UnramifiedClosure F inside the separable closure SeparableClosure F. ReductiveInvariantTarget F G hG is A^Γ for A = π_1(G)_I, the integral inertia coinvariants of the actual algebraic fundamental group, with the actual residual action of Γ = Gal(K/F); fundamentalInvariantTorsion is (A_tor)^Γ as a subgroup of A^Γ. κ_G is reductiveKottwitzRational F G hG (module Langlands.Geometry.Building.Kottwitz.ReductiveMap), selected by classical epsilon among the homomorphisms G(F) → A^Γ whose composite with A^Γ → A is the K-point map reductiveKottwitz on the image of G(F) in G(K). reductiveKottwitz is in turn selected by its squares with every z-extension, over the simply-connected-derived construction through every cocenter. That both selections have their characterizing properties is asserted by ReductiveKottwitzExistenceStatement (existence of z-extensions and unique existence, surjectivity and independence of the K-point map) and ReductiveKottwitzDescentStatement (residual Galois equivariance and unique existence of the restriction to G(F)), both in module Langlands.Geometry.Building.Kottwitz.ReductiveMapStatement; both are proved, by Kottwitz.reductiveKottwitzExistence_assembled and Kottwitz.reductiveKottwitzDescent_assembled (module Langlands.Geometry.Building.Kottwitz.ZExtensionKernelProof; Lemma 11.5.2 row). The source's Henselian discretely valued fields with perfect residue field are specialized to nonarchimedean local fields of either characteristic in universe u; their residue fields are finite."
      ],
      "conclusion": "Kottwitz induces G(k)/G(k)^0≃A^Gamma, G(k)^1/G(k)^0≃(A_tor)^Gamma, and G(k)/G(k)^1≃A^Gamma/(A_tor)^Gamma=(A^Gamma)_free. The explicit third quotient unpacks the source notation using torsion(A^Gamma)=(A_tor)^Gamma; no identification with (A/A_tor)^Gamma is asserted.",
      "lean_declarations": [
        "Langlands.Geometry.Building.Kottwitz.QuotientStatement",
        "Langlands.Geometry.Building.Kottwitz.ReductiveKottwitzExistenceStatement",
        "Langlands.Geometry.Building.Kottwitz.ReductiveKottwitzDescentStatement",
        "Langlands.Geometry.Building.Kottwitz.quotientStatement_of_chamberStatement"
      ],
      "modules": [
        "Langlands.Geometry.Building.Kottwitz.QuotientStatement",
        "Langlands.Geometry.Building.Kottwitz.ReductiveMapStatement",
        "Langlands.Geometry.Building.Kottwitz.QuotientReduction"
      ],
      "dependencies": [
        "Lemma 11.5.2, Proposition 11.5.4 and Corollary 11.7.5",
        "First isomorphism theorem and the elementary fact that the torsion subgroup of an invariant subgroup is the invariant torsion subgroup",
        "The target is the actual Kottwitz homomorphism (KP Proposition 11.1.1, Definition 11.3.2, Lemma 11.5.1) over every nonarchimedean local field, with this statement over it for the Library's G(F)^0 and G(F)^1. The Library states QuotientStatement (first in Library commit 0c3f30c24701c74d5474fca3fbb5324a99aa1d58) together with the selected maps and ReductiveKottwitzExistenceStatement and ReductiveKottwitzDescentStatement (module ReductiveMapStatement, same commit). On that date none of these statements is proved. Reduction (twenty-second update, 14 November 2026): the theorem Kottwitz.quotientStatement_of_chamberStatement (module Langlands.Geometry.Building.Kottwitz.QuotientReduction, whose entry declaration is QuotientReductionStatement, first in Library commit b3a1bdaf15715f16a43643513b7cbb6cbb58ef3a) derives QuotientStatement from ZeroKernelStatement, CharacterKernelStatement and ChamberStatement (the Proposition 11.5.4, Lemma 11.5.2 and Corollary 11.7.5 rows), using only the surjectivity clause of the last. With the reductions recorded in those rows, QuotientStatement follows from nine statements: FundamentalInertiaMapStatement, ReductiveKottwitzExistenceStatement, ReductiveKottwitzDescentStatement, ZExtensionMorphismDominationStatement, UnramifiedZeroDescentStatement, UnramifiedZeroKernelStatement, SpecialTorusExistenceStatement, UnramifiedTwistedChamberStatement and UnramifiedParahoricModelStatement. None of them is proved at Library commit 4f4af6ba. No published declaration states this composite; it was checked with a separate Lean check (Library commit 4f4af6ba, only propext, Classical.choice and Quot.sound). Lean inspection is recorded below. The module QuotientReduction is byte-identical between commit b3a1bdaf and Library commit 4f4af6ba. Follow-up (twenty-second update, Library commit 58ad0f79): FundamentalInertiaMapStatement is proved (Lemma 11.5.2 row), so QuotientStatement follows from the other eight statements: ReductiveKottwitzExistenceStatement, ReductiveKottwitzDescentStatement, ZExtensionMorphismDominationStatement, UnramifiedZeroDescentStatement, UnramifiedZeroKernelStatement, SpecialTorusExistenceStatement, UnramifiedTwistedChamberStatement and UnramifiedParahoricModelStatement. With the reductions of ReductiveKottwitzExistenceStatement (Lemma 11.5.2 row) and UnramifiedZeroKernelStatement (Proposition 11.5.4 row) it also follows from eleven statements: ZExtensionPointSurjectivityStatement, CentralTorusInertiaExactnessStatement, ZExtensionCommonDominationStatement, TorusKottwitzKernelStatement, ZExtensionKottwitzKernelSurjectivityStatement and the six statements of the first list other than ReductiveKottwitzExistenceStatement and UnramifiedZeroKernelStatement. No published declaration states these composites; both were checked with a separate Lean check (Library commit 58ad0f79, only propext, Classical.choice and Quot.sound). None of the statements in either list is proved at Library commit 58ad0f79. The module QuotientReduction is byte-identical between commit b3a1bdaf and Library commit 58ad0f79. Follow-up (twenty-fourth update, Library commit 7229bb45): ZExtensionMorphismDominationStatement is proved (Lemma 11.5.2 row), so with published reductions only QuotientStatement follows from the other seven statements of the first list: ReductiveKottwitzExistenceStatement, ReductiveKottwitzDescentStatement, UnramifiedZeroDescentStatement, UnramifiedZeroKernelStatement, SpecialTorusExistenceStatement, UnramifiedTwistedChamberStatement and UnramifiedParahoricModelStatement. In the second list, ZExtensionPointSurjectivityStatement now follows from published proofs (Lemma 11.5.2 row), and TorusKottwitzKernelStatement and ZExtensionMorphismDominationStatement are proved. With the private weakening recorded in the Proposition 11.5.4 row, QuotientStatement also follows from seven statements without ZExtensionKottwitzKernelSurjectivityStatement: SpecialTorusExistenceStatement, UnramifiedTwistedChamberStatement, UnramifiedParahoricModelStatement, CentralTorusInertiaExactnessStatement, ZExtensionCommonDominationStatement, ReductiveKottwitzDescentStatement and UnramifiedZeroDescentStatement. No published declaration states these composites; the first was checked with a separate Lean check that uses published reductions only and the second with one that uses the weakening (Library commit 7229bb45, only propext, Classical.choice and Quot.sound). None of the statements in either list of seven is proved at Library commit 7229bb45. The module QuotientReduction is byte-identical between commit b3a1bdaf and Library commit 7229bb45. Follow-up (twenty-fifth update, Library commit 49668e4d): ReductiveKottwitzExistenceStatement follows from CentralTorusInertiaExactnessStatement alone by published reductions and proofs (Lemma 11.5.2 row). So with published reductions and proofs only, QuotientStatement follows from seven statements: CentralTorusInertiaExactnessStatement, ReductiveKottwitzDescentStatement, UnramifiedZeroDescentStatement, UnramifiedZeroKernelStatement, SpecialTorusExistenceStatement, UnramifiedTwistedChamberStatement and UnramifiedParahoricModelStatement. ZExtensionCommonDominationStatement is proved (Lemma 11.5.2 row), so with the private weakening recorded in the Proposition 11.5.4 row QuotientStatement also follows from six statements: SpecialTorusExistenceStatement, UnramifiedTwistedChamberStatement, UnramifiedParahoricModelStatement, CentralTorusInertiaExactnessStatement, ReductiveKottwitzDescentStatement and UnramifiedZeroDescentStatement. With the published reduction of UnramifiedTwistedChamberStatement recorded in the Corollary 11.7.5 row, this becomes a list of seven, with UnramifiedUpstairsRadicalRootGenerationStatement and UnramifiedTwistedReductiveQuotientDescentStatement in place of UnramifiedTwistedChamberStatement. No published declaration states these composites; the first was checked with a separate Lean check that uses published reductions and proofs only and the other two with ones that use the weakening (Library commit c2a69151, only propext, Classical.choice and Quot.sound). None of the statements in these three lists is proved at Library commit 49668e4d. The module QuotientReduction is byte-identical between commit b3a1bdaf and Library commit 49668e4d. Follow-up (twenty-sixth update, Library commit 0b7bb3fd): CentralTorusInertiaExactnessStatement and SpecialTorusExistenceStatement are proved by the theorems Kottwitz.centralTorusInertiaExactness (Lemma 11.5.2 row) and specialTorusExistence (Proposition 9.3.4 row). So with published reductions and proofs only, QuotientStatement follows from five statements: ReductiveKottwitzDescentStatement, UnramifiedZeroDescentStatement, UnramifiedZeroKernelStatement, UnramifiedTwistedChamberStatement and UnramifiedParahoricModelStatement. With the private weakening recorded in the Proposition 11.5.4 row, under which UnramifiedZeroKernelStatement follows from published proofs, it follows from the other four. With the published reduction of UnramifiedTwistedChamberStatement recorded in the Corollary 11.7.5 row, this becomes a list of five, with UnramifiedUpstairsRadicalRootGenerationStatement and UnramifiedTwistedReductiveQuotientDescentStatement in place of UnramifiedTwistedChamberStatement. No published declaration states these composites; the first was checked with a separate Lean check that uses published reductions and proofs only and the other two with ones that use the weakening (Library commit fab9caea, only propext, Classical.choice and Quot.sound). None of the statements in these three lists is proved at Library commit 0b7bb3fd. The module QuotientReduction is byte-identical between commit b3a1bdaf and Library commit 0b7bb3fd. Follow-up (twenty-ninth update, Library commit 7cb8c3d3): UnramifiedTwistedReductiveQuotientDescentStatement is proved, and UnramifiedParahoricModelStatement follows from ConnectedGenerationStatement alone (Corollary 11.7.5 and Theorem 8.3.13 rows). So with published reductions and proofs only, QuotientStatement follows from five statements: ReductiveKottwitzDescentStatement, UnramifiedZeroDescentStatement, UnramifiedZeroKernelStatement, UnramifiedTwistedChamberStatement and ConnectedGenerationStatement. With the private weakening recorded in the Proposition 11.5.4 row, under which UnramifiedZeroKernelStatement follows from published proofs, it follows from the other four. With the published reduction of UnramifiedTwistedChamberStatement recorded in the Corollary 11.7.5 row, UnramifiedUpstairsRadicalRootGenerationStatement replaces UnramifiedTwistedChamberStatement in both lists. No published declaration states these composites. The first two were checked with separate Lean checks, the first with published reductions and proofs only and the second with the weakening (Library commit b3dcc8cc, only propext, Classical.choice and Quot.sound). For the other two, separate Lean checks derive QuotientStatement from the same statements and UnramifiedTwistedReductiveQuotientDescentStatement (same commit and axioms), and the inspection recorded in the Corollary 11.7.5 row shows that the published proof has exactly the type of that statement. As that row records, at Library commit b3dcc8cc no Lean file can import both the module of this proof and that of the published proof unramifiedBuildingMetric, which these composites also use; with the private copy described there, both composites compile in one file (only propext, Classical.choice and Quot.sound). None of the statements in these four lists is proved at Library commit 7cb8c3d3. The module QuotientReduction is byte-identical between commit b3a1bdaf and Library commit 7cb8c3d3. Follow-up (thirty-first update, Library commit 314cfd1a): the published reduction Kottwitz.quotientStatement_of_chamberStatement derives QuotientStatement from ZeroKernelStatement, CharacterKernelStatement and ChamberStatement. CharacterKernelStatement is proved, ZeroKernelStatement follows from UnramifiedZeroDescentStatement by a published theorem, and ChamberStatement follows from UnramifiedTwistedChamberStatement and UnramifiedZeroDescentStatement by published reductions and proofs (Lemma 11.5.2, Proposition 11.5.4 and Corollary 11.7.5 rows). So with published reductions and proofs only, QuotientStatement follows from UnramifiedTwistedChamberStatement and UnramifiedZeroDescentStatement. No published declaration states this composite; it was checked with a separate Lean check (Library commit 276bcb8d, only propext, Classical.choice and Quot.sound). As the Corollary 11.7.5 row records, UnramifiedTwistedChamberStatement follows from two published proofs whose modules no Lean file can import together at Library commit 314cfd1a. Separate Lean checks derive QuotientStatement from UnramifiedTwistedResidueQuotientStatement (proved by unramifiedTwistedResidueQuotient, whose module cannot be imported together with UnramifiedBuildingMetricProof) and UnramifiedZeroDescentStatement, and, with the private copy described in that row, from UnramifiedZeroDescentStatement alone; both runs are at Library commit 276bcb8d and report only propext, Classical.choice and Quot.sound. UnramifiedZeroDescentStatement is unproved at Library commit 314cfd1a. The module QuotientReduction is byte-identical between commit b3a1bdaf and Library commit 314cfd1a. Follow-up (thirty-third update, Library commit b369a8f2): the theorem unramifiedTwistedChamber proves UnramifiedTwistedChamberStatement (Corollary 11.7.5 row), so with published reductions and proofs only, QuotientStatement follows from UnramifiedZeroDescentStatement alone. No published declaration states this composite; it was checked with a separate Lean check that applies the composite of the follow-up of the thirty-first update to unramifiedTwistedChamber and the zero-descent premise, with published modules only (Library commit fcb85a7e, only propext, Classical.choice and Quot.sound). UnramifiedZeroDescentStatement is unproved at Library commit b369a8f2. The module QuotientReduction is byte-identical between commit b3a1bdaf and Library commit b369a8f2."
      ],
      "consumer_or_regression": "Combine with Theorem 7.8.1(1) and its chamber-dependent splitting without discarding invariant torsion or length-zero representatives.",
      "formal_status": "statement",
      "publication_commits": [
        "0c3f30c24701c74d5474fca3fbb5324a99aa1d58"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.QuotientStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit 6948120d; kind definition; statement_returns_prop true; the module is byte-identical to commit 0c3f30c2."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.ReductiveKottwitzExistenceStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit 6948120d; kind definition; statement_returns_prop true; the module is byte-identical to commit 0c3f30c2."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.ReductiveKottwitzDescentStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit 6948120d; kind definition; statement_returns_prop true; the module is byte-identical to commit 0c3f30c2."
        },
        {
          "declaration": "Langlands.Geometry.Building.Kottwitz.quotientStatement_of_chamberStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 4f4af6ba; kind theorem, at universe level u, whose type is the implication from ZeroKernelStatement, CharacterKernelStatement and ChamberStatement to QuotientStatement; the module is byte-identical to commit b3a1bdaf, which first published it."
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
        "Recorded Lean scope (the G(K)^1_Omega model only): UnramifiedParahoricModelStatement (module Langlands.BruhatTits.IntegralModels.UnramifiedParahoricModelStatement, first published in Library commit cc5aa77fa8dbdc6e723091c7b710ab0d81162c4e) quantifies over every nonarchimedean local field F in universe u and every affine group scheme G over F. It takes K = inertiaFixedField F, the maximal unramified extension, with integer ring O = fixedFieldIntegers F; supplied building data C : MaximalUnramified.BuildingData F G_K for the normalized valuation of K, which record that G_K is connected reductive; a datum E : UnramifiedZeroDatum computing G(K)^0; a point g of G(K); and a nonempty bounded subset Omega_a of the apartment of C. It asserts that some D : RelativeComponentModelData O K G_K has D.full.integralPoints = G(K)^1 ⊓ C.pointwiseFixer (g·Omega_a) and D.neutral.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (g·Omega_a). Here G(K)^1 is characterValuationKernel, the common kernel of the valuations of all rational characters of G_K, and E.zeroPoints is G(K)^0 of KP Definition 2.6.23(1) (module Langlands.Geometry.Building.KPZeroSubgroups). D.full is a smooth affine flat O-model of finite type with generic fibre G_K, and D.neutral is a smooth connected-fibre relative identity component of it; the neutral clause is recorded in the Theorem 8.3.13 row. The statement differs from the source in three ways: G(K)^dagger_Omega and its model are absent, so the common relative identity component of the two models is not stated; k is a nonarchimedean local field rather than a Henselian discretely valued field with perfect residue field; and C is supplied rather than the constructed building of G_K. Secondary, descended form: IntegralModelAxiomsStatement (module Langlands.Geometry.Building.IntegralModelAxiomsStatement; Axioms 4.1.20 and 4.1.22) asserts, for every nonarchimedean local field F, affine group scheme G over F and supplied P : ParahoricBuildingData G with a polysimplicial realization and an apartment splitting satisfying the seven Section 4.2 building predicates, that some model family M over 𝒪[F], quotient family and relative root reflection data satisfy M.SatisfiesModelAxioms P and the morphism axioms. Its index sets are the nonempty bounded subsets of translated apartments and the facets of the supplied building, so it is the Section 9.2.5 descended form over 𝒪[F], on supplied data. It is present in Library commit ed924aef420de137b4cbaa3b063a3618afcd73fd. Its clause full_points (BuildingModelFamily.ModelAxiomClauses) gives the full model of every index Omega the integral points oneFixer Omega, the pointwise fixer of Omega in G(F)^1. Langlands.BruhatTits.IntegralModels.unramifiedParahoricModel (recorded in the dependencies) proves UnramifiedParahoricModelStatement at arbitrary universe u, so this part holds for all supplied data; the row is therefore conditional. IntegralModelAxiomsStatement is unproved. The status statement of this row covers only this part."
      ],
      "conclusion": "G(K)^1_Omega and G(K)^dagger_Omega are schematic: they are the O-points of actual smooth affine O-group schemes with generic fibre G_K. Their models have the same relative identity component. This does not assert connectedness of the entire models or identify either subgroup with the full fixer.",
      "lean_declarations": [
        "Langlands.BruhatTits.IntegralModels.UnramifiedParahoricModelStatement",
        "Langlands.BruhatTits.IntegralModels.exists_smoothFullModel_of_vertexInputs",
        "Langlands.BruhatTits.IntegralModels.exists_relativeComponentModelData_of_vertexInputs",
        "Langlands.Geometry.Building.IntegralModelAxiomsStatement",
        "Langlands.Geometry.Building.MaximalUnramified.finiteVertexFixerApproximation",
        "Langlands.GroupScheme.IntegralModel.finiteIndexEnlargement",
        "Langlands.Geometry.Building.MaximalUnramified.vertexOneStabilizerMaximalBounded",
        "Langlands.GroupScheme.maximalBoundedIntegralModel",
        "Langlands.GroupScheme.IntegralModel.smoothIntersection",
        "Langlands.BruhatTits.IntegralModels.unramifiedParahoricModel_of_torusInputs",
        "Langlands.BruhatTits.IntegralModels.unramifiedParahoricModel"
      ],
      "modules": [
        "Langlands.BruhatTits.IntegralModels.UnramifiedParahoricModelStatement",
        "Langlands.BruhatTits.IntegralModels.UnramifiedFullModelConstruction",
        "Langlands.Geometry.Building.IntegralModelAxiomsStatement",
        "Langlands.Geometry.Building.UnramifiedFiniteVertexFixerAssembly",
        "Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargementProof",
        "Langlands.Geometry.Building.UnramifiedVertexMaximalBoundedProof",
        "Langlands.GroupScheme.IntegralModel.MaximalBoundedConstruction",
        "Langlands.GroupScheme.IntegralModel.SmoothIntersectionConstruction",
        "Langlands.BruhatTits.IntegralModels.UnramifiedParahoricModelConstruction",
        "Langlands.BruhatTits.IntegralModels.UnramifiedParahoricModelProof"
      ],
      "dependencies": [
        "Proposition 8.3.1: faithful representations, stable lattices, schematic closure and smoothening (A.6.5–A.6.6) construct vertex models",
        "Enlarge Omega to the facets meeting it; Proposition 7.7.1 gives the finite-index inclusions, and A.7.1 propagates schematicity and identifies relative identity components",
        "For nonempty bounded Gamma-stable subsets, Section 9.2.5 constructs the descended smooth affine o-models using invariant coordinate rings and relative identity components; 9.2.6 identifies the parahoric o-points. Chapter 8 models alone do not give this descent.",
        "Recorded Lean route (the G(K)^1_Omega model only): exists_smoothFullModel_of_vertexInputs and exists_relativeComponentModelData_of_vertexInputs (module Langlands.BruhatTits.IntegralModels.UnramifiedFullModelConstruction, a supporting module of the proof of UnramifiedParahoricModelStatement, first published in Library commit 7f43c3c930ff92f76dae6589da1678ad729017e5) are proved from five statements: Langlands.Geometry.Building.MaximalUnramified.VertexOneStabilizerMaximalBoundedStatement and Langlands.Geometry.Building.MaximalUnramified.FiniteVertexFixerApproximationStatement (module Langlands.Geometry.Building.UnramifiedVertexFixerStatements), Langlands.GroupScheme.MaximalBoundedIntegralModelStatement (module Langlands.GroupScheme.IntegralModel.MaximalBounded), Langlands.GroupScheme.IntegralModel.SmoothIntersectionStatement (module Langlands.GroupScheme.IntegralModel.SmoothIntersection) and Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargementStatement (module Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargement). For every affine group scheme G over K with supplied C : MaximalUnramified.BuildingData F G, every g in G(K) and every nonempty bounded Omega_a, the first gives a smooth O-model with integral points G(K)^1 ⊓ C.pointwiseFixer (g·Omega_a), and the second packages it with its relative identity component. The proof chooses finitely many vertices, takes smooth models of their one-stabilizers, intersects them and enlarges the intersection by finite index to the full fixer. It does not compare the neutral integral points with G(K)^0_Omega, so it does not prove UnramifiedParahoricModelStatement. All five inputs are proved. Langlands.Geometry.Building.MaximalUnramified.finiteVertexFixerApproximation (module Langlands.Geometry.Building.UnramifiedFiniteVertexFixerAssembly) proves FiniteVertexFixerApproximationStatement: for supplied C, g and nonempty bounded Omega_a, some nonempty finite set of vertices has the intersection of their one-stabilizers contained, normally and with finite index, in G(K)^1 ⊓ C.pointwiseFixer (g·Omega_a). Langlands.GroupScheme.IntegralModel.finiteIndexEnlargement (module Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargementProof) proves FiniteIndexEnlargementStatement, the finite-index part of KP Proposition A.7.1: over any Henselian discrete valuation ring with algebraically closed residue field, a smooth model M of a smooth affine group over the fraction field and a subgroup V of its rational points containing M.integralPoints as a normal subgroup of finite index give a smooth model with integral points V and an open immersion of M into it, extending the identity of the generic group and preserving relative identity components. Both were first published in Library commit 410c79471b79f65a02fb0f6070da7f2800793ff3. The other three were first published in Library commit b3a1bdaf15715f16a43643513b7cbb6cbb58ef3a: Langlands.Geometry.Building.MaximalUnramified.vertexOneStabilizerMaximalBounded (module Langlands.Geometry.Building.UnramifiedVertexMaximalBoundedProof) proves VertexOneStabilizerMaximalBoundedStatement, Langlands.GroupScheme.maximalBoundedIntegralModel (module Langlands.GroupScheme.IntegralModel.MaximalBoundedConstruction) proves MaximalBoundedIntegralModelStatement, and Langlands.GroupScheme.IntegralModel.smoothIntersection (module Langlands.GroupScheme.IntegralModel.SmoothIntersectionConstruction) proves SmoothIntersectionStatement. Applied to the five proofs, exists_relativeComponentModelData_of_vertexInputs therefore gives, for every supplied C, every g and every nonempty bounded Omega_a, a RelativeComponentModelData over O whose full model has integral points G(K)^1 ⊓ C.pointwiseFixer (g·Omega_a). No published declaration states this composite alone; it was checked with a separate Lean check run, and the proof of exists_unramifiedParahoricModel_of_torusInputs (next entry) makes the same application for g = 1. It also follows from UnramifiedParahoricModelStatement, which unramifiedParahoricModel proves (the entry after next). This route alone does not compare the neutral integral points with G(K)^0_Omega.",
        "Recorded Lean reduction of the whole statement: Langlands.BruhatTits.IntegralModels.unramifiedParahoricModel_of_torusInputs (module Langlands.BruhatTits.IntegralModels.UnramifiedParahoricModelConstruction, first published in Library commit af5d652c2f2ff5b35b4ce4dbbf7cbec8bbf3e99e) proves UnramifiedParahoricModelStatement from UnramifiedTorusIwahoriModelStatement and UnramifiedTorusConnectedBoundStatement. Its proof builds the full model of the previous entry on the untranslated apartment subset, identifies the neutral integral points with E.zeroPoints ⊓ C.pointwiseFixer (Omega_a) from the two torus statements together with published proved results (MaximalUnramified.simplyConnectedNormalizerAffineWeyl and the neutral-point assembly unramifiedNeutral_integralPoints_eq_zeroFixer), and transports both models along the inner automorphism of g. The two torus statements enter only through the neutral comparison; their further reduction is recorded in the Theorem 8.3.13 row.",
        "Recorded Lean proof: Langlands.BruhatTits.IntegralModels.unramifiedParahoricModel (module Langlands.BruhatTits.IntegralModels.UnramifiedParahoricModelProof, first published in Library commit c0c2e1210454ae2a1888a2989e3de794c1336819) proves UnramifiedParahoricModelStatement at arbitrary universe u, with no premise. Its proof applies unramifiedParahoricModel_of_torusInputs (previous entry) to UnramifiedTorusIwahoriModelStatement and UnramifiedTorusConnectedBoundStatement, which it obtains from the published assemblies unramifiedTorusNeutralSurjectivityAssembly, unramifiedTorusConnectedBoundAssembly and unramifiedTorusIwahoriModelAssembly and their published proved inputs, among them Langlands.GroupScheme.connectedGeneration (KP Lemma A.4.26); the Theorem 8.3.13 row records these proofs. Hence, for every nonarchimedean local field F, affine group scheme G over F, supplied building data C, datum E, point g of G(K) and nonempty bounded subset Omega_a of the apartment of C, some D : RelativeComponentModelData O K G_K has D.full.integralPoints = G(K)^1 ⊓ C.pointwiseFixer (g·Omega_a) and D.neutral.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (g·Omega_a).",
        "Open obligations: the building data C are supplied rather than constructed from the building of G_K; IntegralModelAxiomsStatement is not proved; the dagger model and the common relative identity component have no Lean statement. UnramifiedParahoricModelStatement is proved."
      ],
      "consumer_or_regression": "Actual integral-model input for the connected model, its reduction and compact/open integral points. The generally nonaffine full-fixer model of Remark 8.3.4 remains a different object.",
      "formal_status": "conditional",
      "publication_commits": [
        "cc5aa77fa8dbdc6e723091c7b710ab0d81162c4e",
        "7f43c3c930ff92f76dae6589da1678ad729017e5",
        "ed924aef420de137b4cbaa3b063a3618afcd73fd",
        "410c79471b79f65a02fb0f6070da7f2800793ff3",
        "b3a1bdaf15715f16a43643513b7cbb6cbb58ef3a",
        "af5d652c2f2ff5b35b4ce4dbbf7cbec8bbf3e99e",
        "c0c2e1210454ae2a1888a2989e3de794c1336819"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.UnramifiedParahoricModelStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit 451cce4c; kind definition; statement_returns_prop true; the module is byte-identical to commit cc5aa77f, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.exists_smoothFullModel_of_vertexInputs",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit aae8cb82; kind theorem; the module is byte-identical to commit 7f43c3c9, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.exists_relativeComponentModelData_of_vertexInputs",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit 451cce4c; kind theorem; the module is byte-identical to commit 7f43c3c9, its first publication."
        },
        {
          "declaration": "Langlands.Geometry.Building.IntegralModelAxiomsStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit eded01f2; kind definition; statement_returns_prop true; the module is byte-identical to commit ed924aef."
        },
        {
          "declaration": "Langlands.Geometry.Building.MaximalUnramified.finiteVertexFixerApproximation",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 20f83141; kind theorem; the module is byte-identical to commit 410c7947, its first publication."
        },
        {
          "declaration": "Langlands.GroupScheme.IntegralModel.finiteIndexEnlargement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 20f83141; kind theorem; the module is byte-identical to commit 410c7947, its first publication."
        },
        {
          "declaration": "Langlands.Geometry.Building.MaximalUnramified.vertexOneStabilizerMaximalBounded",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 70eca2e4; kind theorem; the module is byte-identical to commit b3a1bdaf, its first publication."
        },
        {
          "declaration": "Langlands.GroupScheme.maximalBoundedIntegralModel",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 70eca2e4; kind theorem; the module is byte-identical to commit b3a1bdaf, its first publication."
        },
        {
          "declaration": "Langlands.GroupScheme.IntegralModel.smoothIntersection",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 70eca2e4; kind theorem; the module is byte-identical to commit b3a1bdaf, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.unramifiedParahoricModel_of_torusInputs",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 70eca2e4; kind theorem; the module is byte-identical to commit af5d652c, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.unramifiedParahoricModel",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit 97101ec2; kind theorem; the module is byte-identical to commit c0c2e121, its first publication."
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
          "adaptation": "Adapted from the TakK section of the upstream file, which works over a field. The local module replaces the field by a commutative ring R with A and B flat over R, states the comultiplication hypothesis as membership in the range of the tensor-square inclusion, uses the current tensor-product induction principle and adds the bialgebra inclusion valBialgHom. Its Lean header carries the Anthropic copyright, Apache 2.0 and licenses/Anthropic-FLT references; its paired Markdown lists the changes and asserts no mathematical statement from an external source.",
          "use": "Implemented dependency of the proof: FiniteIndexEnlargementProof calls FiniteIndexEnlargement.Core.exists_hopf_enlargement, whose Hopf algebra of coordinates integral on V is SubHopf.hopfAlgebra (Enlarged.lean) and whose inclusion into the original coordinate Hopf algebra is SubHopf.valBialgHom (Core.lean).",
          "scope": "This is reuse of code already in the Library (first in Library commit 410c7947), not the adoption of a new external dependency by this ledger. SubHopf.lean and SubHopf.md are byte-identical at Library commits 410c7947 and 179f569b. The entry records the adapted code among the modules added with it; it is not a declaration-level audit of the transitive import closure, whose other modules, including earlier Library ports from Anthropic FLT and other projects with licence files under licenses/, are not enumerated here."
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
        "Recorded Lean scope (without the dagger model): UnramifiedParahoricModelStatement (module and setting as in the Theorem 8.3.2 row) asserts, for the same D, D.neutral.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (g·Omega_a), that is G(K)^0_Omega. The fields neutral_smooth, neutral_connectedFibres, inclusion and isRelativeComponent of RelativeComponentModelData make D.neutral a smooth affine O-model with connected fibres and generic fibre G_K that is the relative identity component of D.full. This is the conclusion of the theorem with three differences: D.neutral is stated to be the relative identity component of the G(K)^1_Omega model only, since the dagger model is absent; k is a nonarchimedean local field; and the building data C are supplied. The last sentence of the conclusion is a non-claim. Secondary, descended form: the clauses neutral_points (the neutral model of every index Omega has integral points zeroFixer P Omega, the pointwise fixer of Omega in P.zeroSubgroup) and facet_constancy (Axiom 4.1.20(1): a nonempty subset of a facet has a neutral model isomorphic to that of the facet) of IntegralModelAxiomsStatement, described in the Theorem 8.3.2 row. unramifiedParahoricModel (Theorem 8.3.2 row) proves UnramifiedParahoricModelStatement at arbitrary universe u, so this part holds for all supplied data; the row is therefore conditional. The status statement of this row covers only this part."
      ],
      "conclusion": "The common relative identity component G^0_Omega of the schematic models in 8.3.2 has G^0_Omega(O)=G(K)^0_Omega. It is the actual smooth affine connected-fibre parahoric model with generic fibre G_K. Its connectedness does not identify the parahoric with a full pointwise or setwise fixer.",
      "lean_declarations": [
        "Langlands.BruhatTits.IntegralModels.UnramifiedParahoricModelStatement",
        "Langlands.BruhatTits.IntegralModels.RelativeComponentModelData",
        "Langlands.Geometry.Building.IntegralModelAxiomsStatement",
        "Langlands.BruhatTits.IntegralModels.unramifiedParahoricModel_of_torusInputs",
        "Langlands.BruhatTits.IntegralModels.UnramifiedTorusIwahoriModelStatement",
        "Langlands.BruhatTits.IntegralModels.UnramifiedTorusConnectedBoundStatement",
        "Langlands.BruhatTits.IntegralModels.unramifiedTorusIwahoriModelAssembly",
        "Langlands.BruhatTits.IntegralModels.unramifiedTorusConnectedBoundAssembly",
        "Langlands.BruhatTits.IntegralModels.unramifiedTorusNeutralSurjectivityAssembly",
        "Langlands.GroupScheme.IntegralModel.smoothHomExtension",
        "Langlands.BruhatTits.IntegralModels.unramifiedTorusBoundedModel",
        "Langlands.BruhatTits.IntegralModels.unramifiedTorusIwahoriConnectedImage",
        "Langlands.BruhatTits.IntegralModels.unramifiedTorusNormPresentation",
        "Langlands.GroupScheme.ConnectedGenerationStatement",
        "Langlands.GroupScheme.TorusQuotientRationalSurjectivityStatement",
        "Langlands.BruhatTits.IntegralModels.UnramifiedTorusNeutralFiniteGenerationStatement",
        "Langlands.GroupScheme.TorusSurjectionIsogenySectionStatement",
        "Langlands.GroupScheme.torusQuotientRationalSurjectivity",
        "Langlands.BruhatTits.IntegralModels.unramifiedTorusNeutralFiniteGeneration",
        "Langlands.GroupScheme.torusSurjectionIsogenySection",
        "Langlands.GroupScheme.connectedGeneration",
        "Langlands.BruhatTits.IntegralModels.unramifiedTorusNeutralSurjectivity",
        "Langlands.BruhatTits.IntegralModels.unramifiedTorusConnectedBound",
        "Langlands.BruhatTits.IntegralModels.unramifiedTorusIwahoriModel",
        "Langlands.BruhatTits.IntegralModels.unramifiedParahoricModel"
      ],
      "modules": [
        "Langlands.BruhatTits.IntegralModels.UnramifiedParahoricModelStatement",
        "Langlands.BruhatTits.IntegralModels.RelativeComponent",
        "Langlands.Geometry.Building.IntegralModelAxiomsStatement",
        "Langlands.BruhatTits.IntegralModels.UnramifiedParahoricModelConstruction",
        "Langlands.BruhatTits.IntegralModels.UnramifiedTorusIwahoriModelStatement",
        "Langlands.BruhatTits.IntegralModels.UnramifiedTorusConnectedBoundStatement",
        "Langlands.BruhatTits.IntegralModels.UnramifiedTorusIwahoriModelAssembly",
        "Langlands.BruhatTits.IntegralModels.UnramifiedTorusConnectedBoundAssembly",
        "Langlands.BruhatTits.IntegralModels.UnramifiedTorusNeutralSurjectivityAssembly",
        "Langlands.GroupScheme.IntegralModel.SmoothHomExtensionProof",
        "Langlands.BruhatTits.IntegralModels.UnramifiedTorusBoundedModelProof",
        "Langlands.BruhatTits.IntegralModels.UnramifiedTorusIwahoriConnectedImageProof",
        "Langlands.BruhatTits.IntegralModels.UnramifiedTorusNormPresentationProof",
        "Langlands.GroupScheme.IntegralModel.ConnectedGeneration",
        "Langlands.GroupScheme.Torus.QuotientRationalSurjectivityStatement",
        "Langlands.BruhatTits.IntegralModels.UnramifiedTorusNeutralFiniteGenerationStatement",
        "Langlands.GroupScheme.Torus.SurjectionIsogenySectionStatement",
        "Langlands.GroupScheme.Torus.QuotientRationalSurjectivityProof",
        "Langlands.BruhatTits.IntegralModels.UnramifiedTorusNeutralFiniteGenerationProof",
        "Langlands.GroupScheme.Torus.SurjectionIsogenySectionProof",
        "Langlands.GroupScheme.IntegralModel.ConnectedGenerationProof",
        "Langlands.BruhatTits.IntegralModels.UnramifiedTorusNeutralSurjectivityProof",
        "Langlands.BruhatTits.IntegralModels.UnramifiedTorusConnectedBoundProof",
        "Langlands.BruhatTits.IntegralModels.UnramifiedTorusIwahoriModelProof",
        "Langlands.BruhatTits.IntegralModels.UnramifiedParahoricModelProof"
      ],
      "dependencies": [
        "Theorem 8.3.2; T is a maximal torus since G_K is quasi-split by 2.3.8. The connected Neron model has T^0(O)=T(K)^0 by B.8.7",
        "Sections 8.3.7–8.3.12 construct root models with prescribed integral points and connected fibres. Sections 2.10.10 and 2.10.19 extend the genuine generic-fibre inclusions",
        "Corrected connected-fibre argument: torus and root model maps factor through G^0_Omega; hence the generated G(K)^0_Omega lies in G^0_Omega(O). Proposition 7.7.1 gives openness and finite index there, and Lemma A.4.26 proves equality",
        "Proposition 8.3.14 gives the actual root-product open immersion",
        "For nonempty bounded Gamma-stable subsets, Section 9.2.5 constructs the descended smooth affine o-models using invariant coordinate rings and relative identity components; 9.2.6 identifies the parahoric o-points. Chapter 8 models alone do not give this descent.",
        "Recorded Lean reduction: unramifiedParahoricModel_of_torusInputs (Theorem 8.3.2 row) proves UnramifiedParahoricModelStatement, including D.neutral.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (g·Omega_a), from two general torus statements over K = inertiaFixedField F and O = fixedFieldIntegers F. UnramifiedTorusIwahoriModelStatement (module Langlands.BruhatTits.IntegralModels.UnramifiedTorusIwahoriModelStatement, first published in Library commit 73b1430a339b037d27e9096762b0400adb4fbd19) asserts that every affine commutative group scheme T over K with a finite Galois intermediate field L of the separable closure over K splitting T has a smooth O-model with geometrically connected fibres whose integral points are torusNormIwahori K L (intermediateValuation F L) T, KP's T(K)^0 (Definition 2.5.13, Corollary B.8.7). UnramifiedTorusConnectedBoundStatement (module Langlands.BruhatTits.IntegralModels.UnramifiedTorusConnectedBoundStatement, first published in Library commit db8d6b3d466f2fd453a4df4624ce6c90db8eed46) asserts that the integral points of every smooth O-model of such T with geometrically connected fibres lie in that subgroup (Corollary B.8.7 with the proof of Proposition B.8.8(3)).",
        "Further published reductions: unramifiedTorusIwahoriModelAssembly (module Langlands.BruhatTits.IntegralModels.UnramifiedTorusIwahoriModelAssembly, first published in Library commit db8d6b3d466f2fd453a4df4624ce6c90db8eed46) derives UnramifiedTorusIwahoriModelStatement from IntegralModel.SmoothHomExtensionStatement, UnramifiedTorusBoundedModelStatement, UnramifiedTorusConnectedBoundStatement and UnramifiedTorusIwahoriConnectedImageStatement. Three of these are proved: IntegralModel.smoothHomExtension (module Langlands.GroupScheme.IntegralModel.SmoothHomExtensionProof, first published in Library commit db8d6b3d466f2fd453a4df4624ce6c90db8eed46), unramifiedTorusBoundedModel (module Langlands.BruhatTits.IntegralModels.UnramifiedTorusBoundedModelProof, first published in Library commit af5d652c2f2ff5b35b4ce4dbbf7cbec8bbf3e99e) and unramifiedTorusIwahoriConnectedImage (module Langlands.BruhatTits.IntegralModels.UnramifiedTorusIwahoriConnectedImageProof, first published in Library commit b3a1bdaf15715f16a43643513b7cbb6cbb58ef3a). unramifiedTorusConnectedBoundAssembly (module Langlands.BruhatTits.IntegralModels.UnramifiedTorusConnectedBoundAssembly, first published in Library commit c40a01345b2f4172fa41e07ff31644b40e695003) derives UnramifiedTorusConnectedBoundStatement from UnramifiedTorusBoundedModelStatement, UnramifiedTorusNeutralSurjectivityStatement and UnramifiedTorusNormPresentationStatement; the last is proved by unramifiedTorusNormPresentation (module Langlands.BruhatTits.IntegralModels.UnramifiedTorusNormPresentationProof, first published in Library commit ba00e0970dd9ba6222ccc056ca2ee7f06bcc8181). unramifiedTorusNeutralSurjectivityAssembly (module Langlands.BruhatTits.IntegralModels.UnramifiedTorusNeutralSurjectivityAssembly, first published in Library commit b3a1bdaf15715f16a43643513b7cbb6cbb58ef3a) derives UnramifiedTorusNeutralSurjectivityStatement (KP Corollary B.8.6 over K) from four statements: Langlands.GroupScheme.ConnectedGenerationStatement (module Langlands.GroupScheme.IntegralModel.ConnectedGeneration, first published in Library commit 73b1430a339b037d27e9096762b0400adb4fbd19; KP Lemma A.4.26), and Langlands.GroupScheme.TorusQuotientRationalSurjectivityStatement, UnramifiedTorusNeutralFiniteGenerationStatement and Langlands.GroupScheme.TorusSurjectionIsogenySectionStatement (modules Langlands.GroupScheme.Torus.QuotientRationalSurjectivityStatement, Langlands.BruhatTits.IntegralModels.UnramifiedTorusNeutralFiniteGenerationStatement and Langlands.GroupScheme.Torus.SurjectionIsogenySectionStatement, published with the assembly). The last three are proved; their proofs were first published in Library commit 4abbe7aabd9c92005d91c9d5bba86b879e928bb3: Langlands.GroupScheme.torusQuotientRationalSurjectivity (module Langlands.GroupScheme.Torus.QuotientRationalSurjectivityProof) proves TorusQuotientRationalSurjectivityStatement, Langlands.BruhatTits.IntegralModels.unramifiedTorusNeutralFiniteGeneration (module Langlands.BruhatTits.IntegralModels.UnramifiedTorusNeutralFiniteGenerationProof) proves UnramifiedTorusNeutralFiniteGenerationStatement, and Langlands.GroupScheme.torusSurjectionIsogenySection (module Langlands.GroupScheme.Torus.SurjectionIsogenySectionProof) proves TorusSurjectionIsogenySectionStatement. Hence UnramifiedParahoricModelStatement follows from ConnectedGenerationStatement alone; the next entry records the published proofs.",
        "Recorded Lean proofs: Langlands.GroupScheme.connectedGeneration (module Langlands.GroupScheme.IntegralModel.ConnectedGenerationProof, first published in Library commit e9c05be9da1000900a43de75ec2ede66892aa158) proves ConnectedGenerationStatement (KP Lemma A.4.26) at arbitrary universe u: it applies connectedGeneration_of_greenbergPointModel, which combines connectedGeneration_of_prerequisites with connectedGenerationField and IntegralModel.henselianCongruenceLifting, to IntegralModel.greenbergPointModel. Langlands.BruhatTits.IntegralModels.unramifiedTorusNeutralSurjectivity (module Langlands.BruhatTits.IntegralModels.UnramifiedTorusNeutralSurjectivityProof, first published in Library commit a2dba61c0a2313b5533c11ee999bece88bb28845) proves UnramifiedTorusNeutralSurjectivityStatement by applying unramifiedTorusNeutralSurjectivityAssembly to connectedGeneration, torusQuotientRationalSurjectivity, unramifiedTorusNeutralFiniteGeneration and torusSurjectionIsogenySection (previous entry). Langlands.BruhatTits.IntegralModels.unramifiedTorusConnectedBound (module Langlands.BruhatTits.IntegralModels.UnramifiedTorusConnectedBoundProof, first published in Library commit a98af0ff45faf7905209f65d641389deee5d8392) proves UnramifiedTorusConnectedBoundStatement by applying unramifiedTorusConnectedBoundAssembly to unramifiedTorusBoundedModel, unramifiedTorusNeutralSurjectivity and unramifiedTorusNormPresentation. Langlands.BruhatTits.IntegralModels.unramifiedTorusIwahoriModel (module Langlands.BruhatTits.IntegralModels.UnramifiedTorusIwahoriModelProof, first published in Library commit a98af0ff45faf7905209f65d641389deee5d8392) proves UnramifiedTorusIwahoriModelStatement by applying unramifiedTorusIwahoriModelAssembly to IntegralModel.smoothHomExtension, unramifiedTorusBoundedModel, the connected bound given by the same assembly and unramifiedTorusIwahoriConnectedImage. unramifiedParahoricModel (Theorem 8.3.2 row) makes the same applications and proves UnramifiedParahoricModelStatement, so the neutral clause D.neutral.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (g·Omega_a), with D.neutral the relative identity component of D.full, holds for all supplied data.",
        "Open obligations: the building data C are supplied rather than constructed from the building of G_K; IntegralModelAxiomsStatement is not proved; the dagger model has no Lean statement. UnramifiedParahoricModelStatement, ConnectedGenerationStatement (KP Lemma A.4.26), the connected torus Iwahori models over the maximal unramified integers, KP B.8.7 (integral points of connected smooth torus models lie in the Iwahori subgroup) and KP B.8.6 (neutral integral-point lifting in exact sequences of unramified-field tori) are proved."
      ],
      "consumer_or_regression": "Connected parahoric construction for reduction, inflation and compact induction. Proving compactness and openness further uses the actual scheme-point topology.",
      "formal_status": "conditional",
      "publication_commits": [
        "cc5aa77fa8dbdc6e723091c7b710ab0d81162c4e",
        "ed924aef420de137b4cbaa3b063a3618afcd73fd",
        "af5d652c2f2ff5b35b4ce4dbbf7cbec8bbf3e99e",
        "73b1430a339b037d27e9096762b0400adb4fbd19",
        "db8d6b3d466f2fd453a4df4624ce6c90db8eed46",
        "c40a01345b2f4172fa41e07ff31644b40e695003",
        "b3a1bdaf15715f16a43643513b7cbb6cbb58ef3a",
        "ba00e0970dd9ba6222ccc056ca2ee7f06bcc8181",
        "4abbe7aabd9c92005d91c9d5bba86b879e928bb3",
        "e9c05be9da1000900a43de75ec2ede66892aa158",
        "a2dba61c0a2313b5533c11ee999bece88bb28845",
        "a98af0ff45faf7905209f65d641389deee5d8392",
        "c0c2e1210454ae2a1888a2989e3de794c1336819"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.UnramifiedParahoricModelStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit 451cce4c; kind definition; statement_returns_prop true; the module is byte-identical to commit cc5aa77f, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.RelativeComponentModelData",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit eded01f2; kind inductive; the module is byte-identical to commit ed924aef."
        },
        {
          "declaration": "Langlands.Geometry.Building.IntegralModelAxiomsStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit eded01f2; kind definition; statement_returns_prop true; the module is byte-identical to commit ed924aef."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.unramifiedParahoricModel_of_torusInputs",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 70eca2e4; kind theorem; the module is byte-identical to commit af5d652c, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.UnramifiedTorusIwahoriModelStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 70eca2e4; kind definition; statement_returns_prop true; the module is byte-identical to commit 73b1430a, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.UnramifiedTorusConnectedBoundStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 70eca2e4; kind definition; statement_returns_prop true; the module is byte-identical to commit db8d6b3d, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.unramifiedTorusIwahoriModelAssembly",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 70eca2e4; kind theorem; the module is byte-identical to commit db8d6b3d, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.unramifiedTorusConnectedBoundAssembly",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 70eca2e4; kind theorem; the module is byte-identical to commit c40a0134, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.unramifiedTorusNeutralSurjectivityAssembly",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 70eca2e4; kind theorem; the module is byte-identical to commit b3a1bdaf, its first publication."
        },
        {
          "declaration": "Langlands.GroupScheme.IntegralModel.smoothHomExtension",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 70eca2e4; kind theorem; the module is byte-identical to commit e5365902, not to commit db8d6b3d, which first published it."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.unramifiedTorusBoundedModel",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 70eca2e4; kind theorem; the module is byte-identical to commit af5d652c, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.unramifiedTorusIwahoriConnectedImage",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 70eca2e4; kind theorem; the module is byte-identical to commit b3a1bdaf, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.unramifiedTorusNormPresentation",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 70eca2e4; kind theorem; the module is byte-identical to commit ba00e097, its first publication."
        },
        {
          "declaration": "Langlands.GroupScheme.ConnectedGenerationStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 70eca2e4; kind definition; statement_returns_prop true; the module is byte-identical to commit 73b1430a, its first publication."
        },
        {
          "declaration": "Langlands.GroupScheme.TorusQuotientRationalSurjectivityStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 70eca2e4; kind definition; statement_returns_prop true; the module is byte-identical to commit b3a1bdaf, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.UnramifiedTorusNeutralFiniteGenerationStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 70eca2e4; kind definition; statement_returns_prop true; the module is byte-identical to commit b3a1bdaf, its first publication."
        },
        {
          "declaration": "Langlands.GroupScheme.TorusSurjectionIsogenySectionStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 70eca2e4; kind definition; statement_returns_prop true; the module is byte-identical to commit b3a1bdaf, its first publication."
        },
        {
          "declaration": "Langlands.GroupScheme.torusQuotientRationalSurjectivity",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 0b7bb3fd; kind theorem; the module is byte-identical to commit 4abbe7aa, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.unramifiedTorusNeutralFiniteGeneration",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 0b7bb3fd; kind theorem; the module is byte-identical to commit 4abbe7aa, its first publication."
        },
        {
          "declaration": "Langlands.GroupScheme.torusSurjectionIsogenySection",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 0b7bb3fd; kind theorem; the module is byte-identical to commit 4abbe7aa, its first publication."
        },
        {
          "declaration": "Langlands.GroupScheme.connectedGeneration",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit 97101ec2; kind theorem; the module is byte-identical to commit e9c05be9, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.unramifiedTorusNeutralSurjectivity",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit 97101ec2; kind theorem; the module is byte-identical to commit a2dba61c, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.unramifiedTorusConnectedBound",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit 97101ec2; kind theorem; the module is byte-identical to commit a98af0ff, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.unramifiedTorusIwahoriModel",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit 97101ec2; kind theorem; the module is byte-identical to commit a98af0ff, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.unramifiedParahoricModel",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit 97101ec2; kind theorem; the module is byte-identical to commit c0c2e121, its first publication."
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
        "Recorded Lean scope (the root-datum assertion for facets only): UnramifiedFacetRootDatumStatement (module Langlands.BruhatTits.IntegralModels.UnramifiedFacetRootDatumStatement, first published in Library commit 73b1430a339b037d27e9096762b0400adb4fbd19) is Axiom 4.1.22(6) for the descended building, in the form of Proposition 9.4.23. It quantifies over every nonarchimedean local field F, affine group scheme G over F and supplied P : ParahoricBuildingData G with a polysimplicial realization and an apartment splitting satisfying the seven Section 4.2 building predicates. It also takes supplied building data C of G_K for K = inertiaFixedField F, a semilinear Galois action A on C, a datum E computing G(K)^0, and an injective G(F)-equivariant map e from the building of P to that of C with an affine apartment map a, subject to eight descent premises: e is compatible with the apartment maps through a; it lands in and surjects onto the Galois-fixed points; it reflects special points; a matches the facets; and S(K)^1 fixes the image of the apartment. The models are D : RelativeComponentModelData over 𝒪[F] whose smooth neutral model has base change to the integers of K with integral points E.zeroPoints ⊓ C.pointwiseFixer (e(F)) = G(K)^0 ∩ G(K)_{e(F)} for the facet F concerned, together with any Q : SpecialFibreQuotientData D satisfying Q.IsReductiveQuotient. For a facet presented by an apartment facet Fa translated by g in G(F), an integral split torus 𝒯 of D with generic fibre S satisfying the torus clause of Axiom 4.1.20(3), and any relative root reflection data Droot, it asserts HasApartmentDerivativeRootDatum: the root datum of Q relative to the image of the special fibre of 𝒯 consists of the derivatives of the affine roots vanishing on Fa and their coroots in Droot, transported through 𝒯. It differs from the source in four ways: Omega is a facet; the open-cell product onto R_u(H_Omega), the plus-group images and the isomorphism of Ubar_{a,Omega,0}/U^+_{a,Omega,0} with the root group are not stated, nor is reducedness of Phi_Omega as a separate assertion; the root datum is the descended one over 𝒪[F], relative to an f-split torus, rather than the geometric one over fbar relative to Sbar; and the building data and models are supplied. Secondary: the clause derivative_root_data of IntegralModelAxiomsStatement (described in the Theorem 8.3.2 row) asserts the same predicate for the facets of its supplied model families. Langlands.BruhatTits.IntegralModels.unramifiedFacetRootDatum (module Langlands.BruhatTits.IntegralModels.UnramifiedFacetRootDatumProof, first published in Library commit af5d652c2f2ff5b35b4ce4dbbf7cbec8bbf3e99e) proves UnramifiedFacetRootDatumStatement at arbitrary universe u, so this part holds for all supplied data; the row is therefore conditional. The status statement of this row covers only this part."
      ],
      "conclusion": "For every choice of positive relative roots, open-cell multiplication is an isomorphism of schemes from the negative nondivisible U^+_{a,Omega,0} factors, T^+, and the positive nondivisible factors onto R_u(H_Omega). These plus groups are special-fibre images of the corresponding 0+ model maps. This is not a direct-product group decomposition. The root datum of Gred_Omega relative to Sbar is (X^*(S),Phi_Omega,X_*(S),Phi_Omega^vee), where Phi_Omega consists of gradients of affine roots vanishing identically on Omega. For a in Phi_Omega, Ubar_{a,Omega,0}/U^+_{a,Omega,0} maps isomorphically to its a-root group. Phi_Omega is reduced even when the ambient relative root system has multipliable roots.",
      "lean_declarations": [
        "Langlands.BruhatTits.IntegralModels.UnramifiedFacetRootDatumStatement",
        "Langlands.BruhatTits.IntegralModels.HasApartmentDerivativeRootDatum",
        "Langlands.Geometry.Building.IntegralModelAxiomsStatement",
        "Langlands.BruhatTits.IntegralModels.unramifiedFacetRootDatum",
        "Langlands.BruhatTits.IntegralModels.unramifiedFacetRootDatum_of_integralOppositeFactors"
      ],
      "modules": [
        "Langlands.BruhatTits.IntegralModels.UnramifiedFacetRootDatumStatement",
        "Langlands.BruhatTits.IntegralModels.FacetAxioms",
        "Langlands.Geometry.Building.IntegralModelAxiomsStatement",
        "Langlands.BruhatTits.IntegralModels.UnramifiedFacetRootDatumProof",
        "Langlands.BruhatTits.IntegralModels.UnramifiedFacetRootDatumReduction"
      ],
      "dependencies": [
        "Proposition 8.3.14, Corollary 8.4.5 and Proposition 8.4.8; Lemma 8.4.7 keeps the a-versus-2a alternatives",
        "Dynamic root groups and multiplication, Proposition 2.11.9 and Theorem 2.11.15; torus unipotent radical B.10.12",
        "For nonempty bounded Gamma-stable subsets, Section 9.2.5 constructs the descended smooth affine o-models using invariant coordinate rings and relative identity components; 9.2.6 identifies the parahoric o-points. Chapter 8 models alone do not give this descent.",
        "Section 9.5 uses perfectness to descend the geometric unipotent radical; the displayed split root datum is a geometric description over fbar, not an assertion of splitness over f",
        "Recorded Lean proof: unramifiedFacetRootDatum applies Langlands.BruhatTits.IntegralModels.unramifiedFacetRootDatum_of_integralOppositeFactors (module Langlands.BruhatTits.IntegralModels.UnramifiedFacetRootDatumReduction, first published in Library commit b3a1bdaf15715f16a43643513b7cbb6cbb58ef3a), which derives UnramifiedFacetRootDatumStatement from IntegralOppositeFactorsStatement, to the published proof integralOppositeFactors of the latter (Theorem 9.6.5 row). The reduction builds a root datum on the actual roots of the supplied quotient Q relative to the special fibre of the supplied integral torus and identifies its graph of root-coroot pairs with apartmentDerivativeRootCorootGraph for Fa.",
        "Open obligations: the parts of the conclusion that the Recorded Lean scope lists as not stated have no Lean statement, and the proved part concerns supplied building data and models. IntegralModelAxiomsStatement, whose clause derivative_root_data asserts the same predicate for its model families, is not proved."
      ],
      "consumer_or_regression": "Maximal reductive quotient for depth zero. Preserve the special-fibre distinction; the ramified SU_3 example of Remark 8.4.11 has quotient SO(3)=PGL_2 although the ambient group is simply connected.",
      "formal_status": "conditional",
      "publication_commits": [
        "73b1430a339b037d27e9096762b0400adb4fbd19",
        "ed924aef420de137b4cbaa3b063a3618afcd73fd",
        "af5d652c2f2ff5b35b4ce4dbbf7cbec8bbf3e99e",
        "b3a1bdaf15715f16a43643513b7cbb6cbb58ef3a"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.UnramifiedFacetRootDatumStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit 451cce4c; kind definition; statement_returns_prop true; the module is byte-identical to commit 73b1430a, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.HasApartmentDerivativeRootDatum",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit eded01f2; kind definition; the module is byte-identical to commit ed924aef."
        },
        {
          "declaration": "Langlands.Geometry.Building.IntegralModelAxiomsStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit eded01f2; kind definition; statement_returns_prop true; the module is byte-identical to commit ed924aef."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.unramifiedFacetRootDatum",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 70eca2e4; kind theorem; the module is byte-identical to commit af5d652c, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.unramifiedFacetRootDatum_of_integralOppositeFactors",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 70eca2e4; kind theorem; the module is byte-identical to commit b3a1bdaf, its first publication."
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
        "Recorded Lean scope (the Axiom 4.1.22(7) inclusion, which KP 4.1.28 derives from this corollary, and the identification of the radical preimage for nonempty subsets of one facet, with an unidentified torus factor): UnramifiedFacetPositiveRadicalStatement (module Langlands.BruhatTits.IntegralModels.UnramifiedFacetPositiveRadicalStatement, first published in Library commit 73b1430a339b037d27e9096762b0400adb4fbd19) has the setting of the Theorem 8.4.10 row. For facets F ≺ F' of the descended building, with characterized models D and D' and reductive quotients Q and Q', it asserts Q.positivePoints ≤ Q'.positivePoints. Here positivePoints is by definition the subgroup of G(F) of integral sections of the neutral model whose reduction projects into the unipotent radical, the descended analogue of the inverse image named in the corollary. The identification is stated in two forms. UnramifiedUpstairsRadicalRootGenerationStatement (module Langlands.BruhatTits.IntegralModels.UnramifiedUpstairsRadicalRootGenerationStatement, first published in Library commit b3a1bdaf15715f16a43643513b7cbb6cbb58ef3a) is the form over O, in the setting of the Theorem 8.3.2 row (K = inertiaFixedField F, O = fixedFieldIntegers F, supplied C : MaximalUnramified.BuildingData F G_K and E : UnramifiedZeroDatum). It asserts one subgroup H of G(K), contained in the image of the centralizer inclusion of C and in E.zeroPoints ⊓ C.pointwiseFixer of the whole apartment image, such that for every nonempty subset Omega of one facet of the apartment, every smooth O-model N of G_K with N.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (Omega) and every represented unipotent radical i : U ⟶ N.specialFibre, the image in G(K) of the integral points of N whose reduction lies in the rational points of U is the subgroup generated by H and the groups C.apartment.rootFixerPlus a Omega = U_{a,Omega,0+} for all relative roots a. UnramifiedRadicalRootGenerationStatement (module Langlands.BruhatTits.IntegralModels.UnramifiedRadicalRootGenerationStatement, first published in Library commit 4f6abf4c7e19610e4d89edc9bf64b34ba1db9ff2) is the descended form of Section 9.5 for an affine F-group G, with C and E for G_K: one H in the image of the centralizer inclusion such that for every nonempty subset Omega_a of one facet, every g in G(K), every D : RelativeComponentModelData over 𝒪[F] whose smooth neutral model has, after base change to O, the integral points E.zeroPoints ⊓ C.pointwiseFixer (g·Omega_a), and every reductive quotient Q of D, Q.positivePoints is the preimage under rationalExtend of the conjugate by g of the subgroup generated by H and the groups C.rootFixerPlus a Omega_a. In both forms H is chosen before Omega and only its existence is asserted: KP's torus factor, the image of T(K)^{mc}_{0+} for T = Z_G(S) (Lemma B.10.11), is not identified with H, no Lean declaration names G(K)_{Omega,0+} itself, and Omega ranges over nonempty subsets of one facet rather than all nonempty bounded subsets. The surjectivity of reduction used in the corollary is proved in general: Langlands.GroupScheme.IntegralModel.reduction_surjective (module Langlands.GroupScheme.IntegralModel.HenselianReduction, present in Library commit ed924aef420de137b4cbaa3b063a3618afcd73fd) says that the reduction map of a smooth integral model over a Henselian local ring is surjective, the role of 8.1.3. Secondary: the clause positive_radicals of IntegralModelAxiomsStatement (described in the Theorem 8.3.2 row) asserts SatisfiesPositiveRadicalClause for incident facets of its supplied families: both reductions are surjective and the same inclusion holds. unramifiedFacetPositiveRadical, unramifiedUpstairsRadicalRootGeneration and unramifiedRadicalRootGeneration (recorded in the dependencies) prove these three statements at arbitrary universe u, so these parts hold for all supplied data; the row is therefore conditional. The status statement of this row covers only these parts."
      ],
      "conclusion": "Under the natural surjective reduction G(K)^0_Omega=G^0_Omega(O)→H_Omega(fbar), the inverse image of R_u(H_Omega)(fbar) is G(K)_{Omega,0+}. Thus 0+ is the kernel of the composite to Gred_Omega(fbar); it is generally larger than the kernel of reduction to the whole special fibre.",
      "lean_declarations": [
        "Langlands.BruhatTits.IntegralModels.UnramifiedFacetPositiveRadicalStatement",
        "Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom.SatisfiesPositiveRadicalClause",
        "Langlands.GroupScheme.IntegralModel.reduction_surjective",
        "Langlands.Geometry.Building.IntegralModelAxiomsStatement",
        "Langlands.BruhatTits.IntegralModels.UnramifiedUpstairsRadicalRootGenerationStatement",
        "Langlands.BruhatTits.IntegralModels.unramifiedUpstairsRadicalRootGeneration",
        "Langlands.BruhatTits.IntegralModels.UnramifiedRadicalRootGenerationStatement",
        "Langlands.BruhatTits.IntegralModels.unramifiedRadicalRootGeneration",
        "Langlands.BruhatTits.IntegralModels.unramifiedFacetPositiveRadical"
      ],
      "modules": [
        "Langlands.BruhatTits.IntegralModels.UnramifiedFacetPositiveRadicalStatement",
        "Langlands.BruhatTits.IntegralModels.SpecialFibre",
        "Langlands.GroupScheme.IntegralModel.HenselianReduction",
        "Langlands.Geometry.Building.IntegralModelAxiomsStatement",
        "Langlands.BruhatTits.IntegralModels.UnramifiedUpstairsRadicalRootGenerationStatement",
        "Langlands.BruhatTits.IntegralModels.UnramifiedUpstairsRadicalRootGenerationProof",
        "Langlands.BruhatTits.IntegralModels.UnramifiedRadicalRootGenerationStatement",
        "Langlands.BruhatTits.IntegralModels.UnramifiedRadicalRootGenerationProof",
        "Langlands.BruhatTits.IntegralModels.UnramifiedFacetPositiveRadicalProof"
      ],
      "dependencies": [
        "Smooth Henselian reduction is surjective by 8.1.3; the integral-point identification is Theorem 8.3.13",
        "Theorem 8.4.10, Corollary 8.4.5(2), Lemma B.10.11 and Proposition 7.3.12 identify the inverse image",
        "Proposition 2.4.3 makes projection from smooth connected special-fibre rational points to the reductive quotient surjective; Lemma 2.4.2 supplies unipotent H^1 vanishing",
        "For nonempty bounded Gamma-stable subsets, Section 9.2.5 constructs the descended smooth affine o-models using invariant coordinate rings and relative identity components; 9.2.6 identifies the parahoric o-points. Chapter 8 models alone do not give this descent.",
        "Section 9.5 uses G(k)^0=G(K)^0 intersect G(k) from 9.3.24, descends the unipotent radical over perfect f and gives G(k)^0+_F=G(K)^0+_F intersect G(k), hence the kernel over k",
        "Recorded Lean proofs: Langlands.BruhatTits.IntegralModels.unramifiedUpstairsRadicalRootGeneration (module Langlands.BruhatTits.IntegralModels.UnramifiedUpstairsRadicalRootGenerationProof, first published in Library commit e9c05be9da1000900a43de75ec2ede66892aa158) proves UnramifiedUpstairsRadicalRootGenerationStatement at arbitrary universe u, with no premise. It applies unramifiedUpstairsRadicalRootGeneration_of_singleton, which uses the constancy of the zero fixer and of the positive root fixers on nonempty subsets of one facet, chooses H by unramifiedZeroFixerCommonCentralizerRadicalExistence (H is the intersection of every radical preimage with the centralizer image) and proves the singleton formula with unramifiedSingletonRadicalRootCentralizerGeneration. Langlands.BruhatTits.IntegralModels.unramifiedRadicalRootGeneration (module Langlands.BruhatTits.IntegralModels.UnramifiedRadicalRootGenerationProof, first published in Library commit a2dba61c0a2313b5533c11ee999bece88bb28845) proves UnramifiedRadicalRootGenerationStatement by applying unramifiedRadicalRootGeneration_of_upstairs, which passes through the actual radical of the base-changed special fibre (SpecialFibreQuotientData.exists_unramifiedRadical) and transports by conjugation with g, to unramifiedUpstairsRadicalRootGeneration. Langlands.BruhatTits.IntegralModels.unramifiedFacetPositiveRadical (module Langlands.BruhatTits.IntegralModels.UnramifiedFacetPositiveRadicalProof, first published in Library commit a98af0ff45faf7905209f65d641389deee5d8392) proves UnramifiedFacetPositiveRadicalStatement, the inclusion Q.positivePoints ≤ Q'.positivePoints, with no premise: it applies unramifiedRadicalRootGeneration with one H to both incident facets, written as translates of apartment facets Fa ≤ Ca by one g, and compares the positive root fixers of a '' Fa and a '' Ca through the facet closure. None of these proofs identifies H with the image of T(K)_{0+}.",
        "Open obligations: the building data and models are supplied; the common subgroup H is not identified with the image of T(K)^{mc}_{0+}, so the radical preimage is compared with G(K)_{Omega,0+} only up to the torus factor, and only for nonempty subsets of one facet; IntegralModelAxiomsStatement is not proved. UnramifiedFacetPositiveRadicalStatement is proved."
      ],
      "consumer_or_regression": "Use the actual reduction composite in the depth-zero quotient and inflation; neither an arbitrary map with an assumed kernel nor reduction to the entire special fibre meets the target.",
      "formal_status": "conditional",
      "publication_commits": [
        "73b1430a339b037d27e9096762b0400adb4fbd19",
        "ed924aef420de137b4cbaa3b063a3618afcd73fd",
        "b3a1bdaf15715f16a43643513b7cbb6cbb58ef3a",
        "e9c05be9da1000900a43de75ec2ede66892aa158",
        "4f6abf4c7e19610e4d89edc9bf64b34ba1db9ff2",
        "a2dba61c0a2313b5533c11ee999bece88bb28845",
        "a98af0ff45faf7905209f65d641389deee5d8392"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.UnramifiedFacetPositiveRadicalStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit 451cce4c; kind definition; statement_returns_prop true; the module is byte-identical to commit 73b1430a, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom.SatisfiesPositiveRadicalClause",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit eded01f2; kind definition; the module is byte-identical to commit ed924aef."
        },
        {
          "declaration": "Langlands.GroupScheme.IntegralModel.reduction_surjective",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit aae8cb82; kind theorem; the module is byte-identical to commit ed924aef."
        },
        {
          "declaration": "Langlands.Geometry.Building.IntegralModelAxiomsStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit eded01f2; kind definition; statement_returns_prop true; the module is byte-identical to commit ed924aef."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.UnramifiedUpstairsRadicalRootGenerationStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit 8f4a33d7; kind definition; statement_returns_prop true; the module is byte-identical to commit b3a1bdaf, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.unramifiedUpstairsRadicalRootGeneration",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit 8f4a33d7; kind theorem; the module is byte-identical to commit e9c05be9, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.UnramifiedRadicalRootGenerationStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit 8f4a33d7; kind definition; statement_returns_prop true; the module is byte-identical to commit 4f6abf4c, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.unramifiedRadicalRootGeneration",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit 8f4a33d7; kind theorem; the module is byte-identical to commit a2dba61c, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.unramifiedFacetPositiveRadical",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit 8f4a33d7; kind theorem; the module is byte-identical to commit a98af0ff, its first publication."
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
        "Recorded Lean scope (the smooth connected unipotent kernel of part (1), in the form of Proposition 8.4.15; parts (2)–(4) only through IntegralModelAxiomsStatement): UnramifiedModelKernelStatement (module Langlands.BruhatTits.IntegralModels.UnramifiedModelKernelStatement, first published in Library commit 51e4d8972659f1ffcf0ca89e8eee9540a30b52d3) has the setting of UnramifiedParahoricModelStatement (Theorem 8.3.2 row). For g in G(K) and subsets Omega_a and Omega_a' of the apartment of C with Omega_a nonempty, Omega_a' bounded and Omega_a contained in the closure of Omega_a', and for any smooth O-models N and N' with integral points G(K)^0 ∩ G(K)_{g·Omega_a} and G(K)^0 ∩ G(K)_{g·Omega_a'}, it asserts that every model homomorphism N' → N with identity generic fibre has a smooth, connected and unipotent scheme-theoretic kernel on special fibres. For facets F ≺ F' this is the first assertion of part (1). The product identification over all nondivisible roots is not stated, and neither is the false restricted index. At Library commit a0627c91 parts (2)–(4) had no statement in this unramified setting. Since Library commit 0c3f30c24701c74d5474fca3fbb5324a99aa1d58 three statements give them for the descended facet models over 𝒪[F], in the setting of the Theorem 8.4.10 row (supplied P with the seven building predicates, supplied C, A, e and a with the eight descent premises, a zero datum E, and pairs D whose smooth neutral model has integral points E.zeroPoints ⊓ C.pointwiseFixer (e(Fc)) after base change to O), for f-rational parabolics. UnramifiedFacetParabolicImageStatement (module Langlands.BruhatTits.IntegralModels.UnramifiedFacetParabolicImageStatement) asserts, for facets Fc ≺ Fc', such pairs D and D' and every model morphism φ : D' → D, φ.HasParabolicSpecialFibreImage and φ.HasParabolicReductionPreimage (Axiom 4.1.22(2) and (4), from parts (2) and (3)). UnramifiedFacetCommonTorusStatement (module Langlands.BruhatTits.IntegralModels.UnramifiedFacetCommonTorusStatement) asserts Axiom 4.1.22(3), the common maximal split torus and the signs of its Lie weights on the image (from part (2) and its proof), with maximality in the model of Fc' as a hypothesis. UnramifiedFacetParabolicOrderStatement (module Langlands.BruhatTits.IntegralModels.UnramifiedFacetParabolicOrderStatement) asserts Axiom 4.1.22(5), the order-preserving bijection from the facets Fc' with Fc ≺ Fc' onto the parabolic subgroups of the reductive quotient for Fc (from part (4)). The paired Markdown of each module states the exact form. UnramifiedFacetCommonTorusStatement and UnramifiedFacetParabolicOrderStatement are proved (recorded in the dependencies); UnramifiedFacetParabolicImageStatement follows from published proofs, but no published declaration proves it. IntegralModelAxiomsStatement (described in the Theorem 8.3.2 row) contains them for the descended supplied families over 𝒪[F], for f-rational parabolics rather than over fbar: its facet clauses assert HasParabolicSpecialFibreImage (the schematic image of the special-fibre map is a parabolic subgroup, Axiom 4.1.22(2)), HasParabolicReductionPreimage (the reduction preimage of the rational points of that image is the image of the integral points for F', Axiom 4.1.22(4)) and FacetModelData.HasFacetParabolicOrderBijection (an order-reversing bijection from all incident facets onto the f-parabolic subgroups of the quotient, Axiom 4.1.22(5)), and its general morphism clause asserts HasSmoothConnectedUnipotentKernel for the model map of every closure-ordered pair of subsets of a common apartment and every pair of incident facets (Axiom 4.1.22(1)). Containment of R_u(H_F) and the correspondence between facets in one apartment and parabolics containing the torus are not separate assertions. unramifiedModelKernel (recorded in the dependencies) proves UnramifiedModelKernelStatement at arbitrary universe u, so this part holds for all supplied data; the row is therefore conditional. The status statement of this row covers only this part."
      ],
      "conclusion": "By Proposition 8.4.15 specialized to these facets, the schematic kernel of rhobar is smooth connected unipotent, and open-cell multiplication identifies it as a scheme with the product of ker(Ubar_{a,F',0}→Ubar_{a,F,0}) over all nondivisible roots a in Phi(S,G_K). The restriction to Phi'_{F'} minus Psi_F(F') printed in Theorem 8.4.19(1) is false and is excluded as a formalization target: Example 8.3.5 gives a split SL_2 open chamber F' incident to a hyperspecial vertex F for which Phi'_{F'} is empty by 8.4.6, but ker(rhobar) is G_a. Theorem 8.4.19(2)–(4) supplies the remaining conclusions. The image p_F(F') is the parabolic of H_F associated to Psi_F(F') and contains R_u(H_F). The inverse image of p_F(F')(fbar) in G^0_F(O) is G^0_{F'}(O). The map F'↦p_F(F') is a bijection from all incident facets onto all parabolics of H_F, equivalently of Gred_F. Facets in A alone correspond to parabolics containing the chosen maximal torus. The kernel product is a scheme isomorphism, not a direct-product group decomposition.",
      "lean_declarations": [
        "Langlands.BruhatTits.IntegralModels.UnramifiedModelKernelStatement",
        "Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom.HasSmoothConnectedUnipotentKernel",
        "Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom.HasParabolicSpecialFibreImage",
        "Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom.HasParabolicReductionPreimage",
        "Langlands.BruhatTits.IntegralModels.FacetModelData.HasFacetParabolicOrderBijection",
        "Langlands.Geometry.Building.IntegralModelAxiomsStatement",
        "Langlands.BruhatTits.IntegralModels.UnramifiedFacetParabolicImageStatement",
        "Langlands.BruhatTits.IntegralModels.UnramifiedFacetParabolicOrderStatement",
        "Langlands.BruhatTits.IntegralModels.UnramifiedFacetCommonTorusStatement",
        "Langlands.BruhatTits.IntegralModels.unramifiedModelKernel_of_compatible",
        "Langlands.BruhatTits.IntegralModels.UnramifiedCompatibleModelKernelSmoothConnectedStatement",
        "Langlands.BruhatTits.IntegralModels.unramifiedModelKernel_of_smoothConnected",
        "Langlands.BruhatTits.IntegralModels.unramifiedFacetParabolicImage_of_generation_positive_modelKernel",
        "Langlands.BruhatTits.IntegralModels.UnramifiedUpstairsRadicalRootGenerationStatement",
        "Langlands.BruhatTits.IntegralModels.UnramifiedUpstairsSingletonRadicalRootGenerationStatement",
        "Langlands.BruhatTits.IntegralModels.unramifiedUpstairsRadicalRootGeneration_of_singleton",
        "Langlands.BruhatTits.IntegralModels.UnramifiedRootDepthKernelStatement",
        "Langlands.BruhatTits.IntegralModels.UnramifiedNoHigherRootDepthKernelStatement",
        "Langlands.BruhatTits.IntegralModels.unramifiedNoHigherRootDepthKernel",
        "Langlands.BruhatTits.IntegralModels.TorusRootModelFamilyData.smooth_connected_kernel_of_orderedCharts",
        "Langlands.BruhatTits.IntegralModels.TorusRootModelFamilyData.smooth_connected_kernel_of_orderedOpenCharts",
        "Langlands.BruhatTits.IntegralModels.unramifiedRootDepthKernel_of_multipliableCoordinates",
        "Langlands.Geometry.Building.MultipliableRootGroupCoordinatesExistenceStatement",
        "Langlands.BruhatTits.IntegralModels.UnramifiedOrderedIntegralOpenCellStatement",
        "Langlands.BruhatTits.IntegralModels.UnramifiedOrderedIntegralOpenCellReductionStatement",
        "Langlands.BruhatTits.IntegralModels.unramifiedOrderedIntegralOpenCellReduction",
        "Langlands.BruhatTits.IntegralModels.TorusRootModelFamilyData.closedPoint_mem_range_orderedChart",
        "Langlands.BruhatTits.IntegralModels.OrderedFixerFactorization",
        "Langlands.BruhatTits.IntegralModels.UnramifiedOrderedFixerFactorizationStatement",
        "Langlands.BruhatTits.IntegralModels.unramifiedOrderedFixerFactorization",
        "Langlands.BruhatTits.IntegralModels.matrixOrderModel",
        "Langlands.BruhatTits.IntegralModels.iwahoriMatrixHom",
        "Langlands.BruhatTits.IntegralModels.specialFibreKernelIso",
        "Langlands.BruhatTits.IntegralModels.iwahoriMatrixHom_specialFibreKernel_properties",
        "Langlands.BruhatTits.IntegralModels.matrixOrderModelData",
        "Langlands.BruhatTits.IntegralModels.iwahoriMatrixModelHom",
        "Langlands.BruhatTits.IntegralModels.specialFibreImageIso",
        "Langlands.BruhatTits.IntegralModels.iwahoriMatrixModelHom_hasSmoothConnectedUnipotentKernel",
        "Langlands.BruhatTits.IntegralModels.iwahoriMatrixModelHom_hasParabolicSpecialFibreImage",
        "Langlands.BruhatTits.IntegralModels.iwahoriMatrixModelHom_isBorelSubgroup_specialFibreImage",
        "Langlands.BruhatTits.IntegralModels.iwahoriMatrixModelHom_hasParabolicReductionPreimage",
        "Langlands.BruhatTits.IntegralModels.matrixOrderModelIso",
        "Langlands.BruhatTits.IntegralModels.iwahoriStandardModelHom",
        "Langlands.BruhatTits.IntegralModels.iwahoriStandardModelHom_hasSmoothConnectedUnipotentKernel",
        "Langlands.BruhatTits.IntegralModels.iwahoriStandardModelHom_hasParabolicSpecialFibreImage",
        "Langlands.BruhatTits.IntegralModels.iwahoriStandardModelHom_isBorelSubgroup_specialFibreImage",
        "Langlands.BruhatTits.IntegralModels.iwahoriStandardModelHom_hasParabolicReductionPreimage",
        "Langlands.BruhatTits.IntegralModels.iwahoriStandardModelHom_hasParabolicReductiveImage",
        "Langlands.BruhatTits.IntegralModels.iwahoriStandardModelHom_isBorelSubgroup_reductiveImage",
        "Langlands.BruhatTits.IntegralModels.generalLinearIwahori_satisfiesPositiveRadicalClause",
        "Langlands.Geometry.Building.multipliableRootGroupCoordinatesExistence",
        "Langlands.BruhatTits.IntegralModels.unramifiedRootDepthKernel",
        "Langlands.BruhatTits.IntegralModels.unramifiedOrderedIntegralOpenCell",
        "Langlands.BruhatTits.IntegralModels.unramifiedFacetCommonTorus",
        "Langlands.BruhatTits.IntegralModels.unramifiedFacetParabolicOrder",
        "Langlands.BruhatTits.IntegralModels.unramifiedFacetParabolicOrder_of_upstairs_rootGeneration",
        "Langlands.BruhatTits.IntegralModels.unramifiedModelKernel",
        "Langlands.BruhatTits.IntegralModels.unramifiedUpstairsRadicalRootGeneration",
        "Langlands.BruhatTits.IntegralModels.unramifiedFacetPositiveRadical"
      ],
      "modules": [
        "Langlands.BruhatTits.IntegralModels.UnramifiedModelKernelStatement",
        "Langlands.BruhatTits.IntegralModels.ModelMorphism",
        "Langlands.BruhatTits.IntegralModels.SpecialFibre",
        "Langlands.BruhatTits.IntegralModels.FacetParabolicOrder",
        "Langlands.Geometry.Building.IntegralModelAxiomsStatement",
        "Langlands.BruhatTits.IntegralModels.UnramifiedFacetParabolicImageStatement",
        "Langlands.BruhatTits.IntegralModels.UnramifiedFacetParabolicOrderStatement",
        "Langlands.BruhatTits.IntegralModels.UnramifiedFacetCommonTorusStatement",
        "Langlands.BruhatTits.IntegralModels.UnramifiedModelKernelReduction",
        "Langlands.BruhatTits.IntegralModels.UnramifiedModelKernelTorus",
        "Langlands.BruhatTits.IntegralModels.UnramifiedFacetParabolicImageReduction",
        "Langlands.BruhatTits.IntegralModels.UnramifiedUpstairsRadicalRootGenerationStatement",
        "Langlands.BruhatTits.IntegralModels.UnramifiedSingleFacetReduction",
        "Langlands.BruhatTits.IntegralModels.RootDepthKernelStatement",
        "Langlands.BruhatTits.IntegralModels.RootDepthKernelNoHigher",
        "Langlands.BruhatTits.IntegralModels.TorusRootModelKernel",
        "Langlands.BruhatTits.IntegralModels.TorusRootKernelOpenChart",
        "Langlands.BruhatTits.IntegralModels.RootDepthKernelMultipliable",
        "Langlands.Geometry.Building.MultipliableRootGroupCoordinates",
        "Langlands.BruhatTits.IntegralModels.OrderedIntegralOpenCell",
        "Langlands.BruhatTits.IntegralModels.OrderedIntegralOpenCellReduction",
        "Langlands.BruhatTits.IntegralModels.TorusRootKernelCell",
        "Langlands.BruhatTits.IntegralModels.OrderedFixerFactorizationStatement",
        "Langlands.BruhatTits.IntegralModels.OrderedFixerFactorizationProof",
        "Langlands.BruhatTits.IntegralModels.GeneralLinearIwahoriKernel",
        "Langlands.BruhatTits.IntegralModels.GeneralLinearIwahoriImage",
        "Langlands.BruhatTits.IntegralModels.GeneralLinearIwahoriStandard",
        "Langlands.Geometry.Building.MultipliableRootGroupCoordinatesExistenceProof",
        "Langlands.BruhatTits.IntegralModels.RootDepthKernel",
        "Langlands.BruhatTits.IntegralModels.OrderedIntegralOpenCellTheorem",
        "Langlands.BruhatTits.IntegralModels.UnramifiedFacetCommonTorusProof",
        "Langlands.BruhatTits.IntegralModels.UnramifiedFacetParabolicOrderProof",
        "Langlands.BruhatTits.IntegralModels.UnramifiedFacetParabolicOrderReduction",
        "Langlands.BruhatTits.IntegralModels.UnramifiedModelKernelProof",
        "Langlands.BruhatTits.IntegralModels.UnramifiedUpstairsRadicalRootGenerationProof",
        "Langlands.BruhatTits.IntegralModels.UnramifiedFacetPositiveRadicalProof"
      ],
      "dependencies": [
        "Corrected general morphism setup preceding Proposition 8.4.15; that proposition supplies the smooth connected unipotent kernel and the product over all nondivisible ambient roots, without the false restriction in 8.4.19(1)",
        "Derived source-discrepancy check from Example 8.3.5 and Section 8.4.6: the chamber model maps to the hyperspecial SL_2 model by c=pi*c'; on special fibres its kernel has a=d=1, b=0 and c' free, hence is G_a, whereas Phi'_{F'} and the printed product index are empty",
        "Root-filtration comparisons 6.3.21; Theorem 8.4.10, Proposition 8.4.8(2), Proposition 1.3.35 and Corollary 8.4.12; independence from the apartment and the use of all apartments through F",
        "For nonempty bounded Gamma-stable subsets, Section 9.2.5 constructs the descended smooth affine o-models using invariant coordinate rings and relative identity components; 9.2.6 identifies the parahoric o-points. Chapter 8 models alone do not give this descent.",
        "Section 9.3.2 descends the facet morphisms and identifies Gamma-facets through F with parabolic f-subgroups; Proposition 2.4.5 transfers these to the maximal reductive quotient",
        "Proposition 9.3.3 proves the exact inverse-image equality over o, using 8.1.3 smooth Henselian reduction and Lemma 2.4.2 for the smooth connected unipotent kernel. This does not assert that every geometric parabolic descends",
        "Recorded Lean reductions of the kernel statement: unramifiedModelKernel_of_compatible (module Langlands.BruhatTits.IntegralModels.UnramifiedModelKernelReduction, first published in Library commit db8d6b3d466f2fd453a4df4624ce6c90db8eed46) derives UnramifiedModelKernelStatement from UnramifiedQuasiSplitStatement, UnramifiedZeroPointsIndependenceStatement and UnramifiedCompatibleModelKernelStatement, its special case with g = 1 and a zero datum whose torus represents the centralizer of the maximal split torus C.i. unramifiedModelKernel_of_smoothConnected (module Langlands.BruhatTits.IntegralModels.UnramifiedModelKernelTorus, first published in Library commit 410c79471b79f65a02fb0f6070da7f2800793ff3) replaces the last input by UnramifiedCompatibleModelKernelSmoothConnectedStatement, which asks only that the kernel be smooth and connected; unipotence is proved in that module from the bounded split torus. The first two inputs are proved (unramifiedQuasiSplit_of_henselianDiscrete with henselianDiscreteQuasiSplit, Theorem 9.6.5 row; unramifiedZeroPointsIndependence, Definition 6.6.1 row), so UnramifiedModelKernelStatement follows from UnramifiedCompatibleModelKernelSmoothConnectedStatement alone. Langlands.BruhatTits.IntegralModels.unramifiedModelKernel (module Langlands.BruhatTits.IntegralModels.UnramifiedModelKernelProof, first published in Library commit 9e39a73d21bd6ed6fac00b01cc5e01c0db5d105b) proves UnramifiedModelKernelStatement at arbitrary universe u, with no premise. Its proof applies unramifiedModelKernel_of_smoothConnected to unramifiedQuasiSplit_of_henselianDiscrete (with henselianDiscreteQuasiSplitReduction, quasiSplitRegularClassRationalReduction and quasiSplitSteinbergQuotient) and unramifiedZeroPointsIndependence, and proves the smooth-connected input inside the proof (next entry).",
        "Recorded root-group kernel results (KP Lemma C.5.3, printed p. 705 / PDF p. 736, which KP's proof of Proposition 8.4.15 applies to each factor of the kernel product; the authors' corrections do not amend Appendix C): UnramifiedRootDepthKernelStatement (module Langlands.BruhatTits.IntegralModels.RootDepthKernelStatement, first published in Library commit 430cc03fe803c5dbf74bc3baf91e8f7a2c26ea9c) states the conclusion of Lemma C.5.3 over O on supplied root models. For x in the apartment of C, a relative root a, depths r ≤ s, RootFiltrationModelData U and V for a at x at depths r and s, and a generic map f of their root groups with f ≫ U.inclusion = V.inclusion, every model homomorphism from V.model to U.model with generic fibre f has a smooth, connected and unipotent kernel on special fibres. unramifiedNoHigherRootDepthKernel (module Langlands.BruhatTits.IntegralModels.RootDepthKernelNoHigher, first published in Library commit fab9caeae532b7a65e67e702bcab72d3194371ae) proves UnramifiedNoHigherRootDepthKernelStatement, the same assertion for relative roots a with RelativeRoot.HasNoHigherRoots C.i a, that is, no multiple n • a with n ≥ 2 is a relative root. This covers every relative root that is not multipliable, including divisible ones. unramifiedRootDepthKernel_of_multipliableCoordinates (module Langlands.BruhatTits.IntegralModels.RootDepthKernelMultipliable, first published in Library commit b3dcc8cc4c93f1140c6b34374f589ccc637a1a22) proves that MultipliableRootGroupCoordinatesExistenceStatement implies UnramifiedRootDepthKernelStatement. The hypothesis (module Langlands.Geometry.Building.MultipliableRootGroupCoordinates, first published in Library commit 0b7bb3fdbe6e0386b666b6b099a3bc9cd3ad7e18) is proved by multipliableRootGroupCoordinatesExistence (module Langlands.Geometry.Building.MultipliableRootGroupCoordinatesExistenceProof, first published in Library commit 2016a0d994180c702214a75514a08546aa930f07), which applies the published reduction multipliableRootGroupCoordinatesExistence_of_algebraicSU3 to the published theorems algebraicSU3RootCoordinatesExistence and Langlands.GroupScheme.RelativeRoot.unitaryChartUpgrade. It asserts that for supplied building data and every relative root b with 2 • b a relative root, the record ValuedUnitaryRootGroupCoordinates of b is nonempty: a finite separable extension E of the maximal unramified field K, a separable quadratic extension L of E, a homomorphism from R_{E/K} U_{L/E} to G that represents the root group U_b, and an apartment point at which b takes the value ω(v)/2 on the image of each unitary parameter (u, v), where ω is the valuation of L extending that of K with ω(K^×) = ℤ (KP Construction 2.9.16, display (2.9.3), printed p. 117, and Construction 6.1.17, printed pp. 205–206). For a multipliable root the proof follows KP Proposition C.5.1 (printed pp. 703–704): the root models are the canonical restricted lattice models R_{O_E/O} X_{r',2r'} (canonicalWeilLatticeModel), at a depth r' obtained after rescaling the valuation of E to have value group ℤ; their special-fibre transition kernels are smooth, connected and unipotent by canonicalWeilLatticeModel_kernel_properties, the Library form of KP Lemma C.4.4 (printed p. 701); and RootFiltrationModelData.specialFibreKernel_properties_of_presentation transfers this to arbitrary supplied presentations. The other roots have no higher multiples and are the case above. So UnramifiedRootDepthKernelStatement follows from MultipliableRootGroupCoordinatesExistenceStatement alone. unramifiedRootDepthKernel (module Langlands.BruhatTits.IntegralModels.RootDepthKernel, first published in Library commit 497ef49830025d23824f6b2e2b1d5d60b594f51e) proves UnramifiedRootDepthKernelStatement by applying unramifiedRootDepthKernel_of_multipliableCoordinates to multipliableRootGroupCoordinatesExistence, so this Lean form of KP Lemma C.5.3 on supplied root models holds for every relative root and all depths r ≤ s. TorusRootModelFamilyData.smooth_connected_kernel_of_orderedCharts (module Langlands.BruhatTits.IntegralModels.TorusRootModelKernel, first published in Library commit 410c79471b79f65a02fb0f6070da7f2800793ff3) takes UnramifiedRootDepthKernelStatement as a hypothesis and puts the factors together in chart form. Let N and N' be integral models of G over O, let A and B be supplied TorusRootModelFamilyData for N on Ω and N' on Ω' (a smooth torus model with geometrically connected fibres and integral points E.torusIwahori, a root model at each relative root at the root-fixer depth of Ω, resp. Ω', and model maps into N, resp. N'), with each root-fixer depth for Ω at most that for Ω', and let ψ : N' → N be a model homomorphism with identity generic fibre. Given a sequence e of torus and root indices, monomorphic ordered multiplication charts of both families along e, and a lift of the whole special-fibre kernel of ψ into the residue pullback of the source chart's product, that kernel is smooth and connected. The theorem also takes the hypothesis IntegralModel.HasSmoothHomExtension for O, which the Library proves (fixedField_hasSmoothHomExtension applied to smoothHomExtension). TorusRootModelFamilyData.smooth_connected_kernel_of_orderedOpenCharts (module Langlands.BruhatTits.IntegralModels.TorusRootKernelOpenChart, first published in Library commit 410c79471b79f65a02fb0f6070da7f2800793ff3) replaces the lift and the monomorphism of the source chart by three conditions: the source chart, of B, is an open immersion, N' is smooth, and every integral section of N' whose image under ψ reduces to 1 in N has its closed point in the range of the source chart; the target chart, of A, must still be a monomorphism. Published results construct such families and open charts and prove the range condition, under further hypotheses. unramifiedOrderedIntegralOpenCellReduction (module Langlands.BruhatTits.IntegralModels.OrderedIntegralOpenCellReduction, first published in Library commit e5365902d74534dbf1622c06e695dffdc128d723) proves UnramifiedOrderedIntegralOpenCellReductionStatement (same module): UnramifiedTorusConnectedBoundStatement and UnramifiedTorusIwahoriConnectedImageStatement together imply UnramifiedOrderedIntegralOpenCellStatement (module Langlands.BruhatTits.IntegralModels.OrderedIntegralOpenCell, first published in Library commit 410c79471b79f65a02fb0f6070da7f2800793ff3), the open-immersion clause of KP Proposition 8.3.14(3) (printed pp. 299–300 / PDF pp. 330–331; the authors' corrections do not amend Proposition 8.3.14) over O. For supplied building data C, a zero datum E whose torus represents the centralizer of the maximal split torus C.i, a point x of the apartment, a nonempty affine-bounded subset Ω of the apartment and a smooth integral model N with N.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (Ω), that statement asserts that some TorusRootModelFamilyData A for N on Ω exists whose ordered integral multiplication (negative indivisible roots, then the torus, then positive indivisible roots) is an open immersion for every generic cocharacter ν and all injective complete enumerations of the indivisible roots positive on −ν and on ν. Both of its hypotheses are proved: UnramifiedTorusIwahoriConnectedImageStatement by unramifiedTorusIwahoriConnectedImage and UnramifiedTorusConnectedBoundStatement by unramifiedTorusConnectedBound (both in the Theorem 8.3.13 row). Langlands.BruhatTits.IntegralModels.unramifiedOrderedIntegralOpenCell (module Langlands.BruhatTits.IntegralModels.OrderedIntegralOpenCellTheorem, first published in Library commit d210ab55a138c1f91b826ee47c6280ce6c6b90bc) applies unramifiedOrderedIntegralOpenCellReduction to these two proofs and proves UnramifiedOrderedIntegralOpenCellStatement at arbitrary universe u, so this construction holds for all supplied data. TorusRootModelFamilyData.closedPoint_mem_range_orderedChart (module Langlands.BruhatTits.IntegralModels.TorusRootKernelCell, first published in Library commit 410c79471b79f65a02fb0f6070da7f2800793ff3) proves the range condition for B's chart along e when A's chart along e is an open immersion, Ω and Ω' are nonempty and affine-bounded, N'.integralPoints ≤ E.zeroPoints ⊓ C.pointwiseFixer (Ω'), and OrderedFixerFactorization C E e Ω Ω' holds. That property (same module) says: whenever elements of the slot subgroups for Ω (the image of T(K)^0 for the torus slot, U_{a,Ω,0} for a root slot a) have their ordered product in E.zeroPoints ⊓ C.pointwiseFixer (Ω'), each lies in the slot subgroup for Ω'. unramifiedOrderedFixerFactorization (module Langlands.BruhatTits.IntegralModels.OrderedFixerFactorizationProof, first published in Library commit b3a1bdaf15715f16a43643513b7cbb6cbb58ef3a) proves UnramifiedOrderedFixerFactorizationStatement (module Langlands.BruhatTits.IntegralModels.OrderedFixerFactorizationStatement, first published in Library commit e5365902d74534dbf1622c06e695dffdc128d723): for a zero datum as above, a generic cocharacter ν and injective complete enumerations of the indivisible roots positive on −ν and on ν, OrderedFixerFactorization holds for the order negative roots, torus, positive roots, for all Ω and every nonempty affine-bounded Ω'. The proof of unramifiedModelKernel (previous entry) assembles these results for its smooth-connected input; UnramifiedCompatibleModelKernelSmoothConnectedStatement itself has no published named proof. For two closure-ordered subsets it chooses common ordered root data (a generic cocharacter and injective complete enumerations of the indivisible roots, by a private lemma of the module), applies unramifiedOrderedIntegralOpenCell to both models, unramifiedOrderedFixerFactorization, TorusRootModelFamilyData.closedPoint_mem_range_orderedChart, TorusRootModelFamilyData.rootDepth_le_of_subset_affineClosure and IntegralModel.fixedField_hasSmoothHomExtension with IntegralModel.smoothHomExtension, and concludes with TorusRootModelFamilyData.smooth_connected_kernel_of_orderedOpenCharts, whose root-group hypothesis unramifiedRootDepthKernel discharges. The product identification of Proposition 8.4.15 is not part of its target.",
        "Recorded Lean reduction of parts (2) and (3): unramifiedFacetParabolicImage_of_generation_positive_modelKernel (module Langlands.BruhatTits.IntegralModels.UnramifiedFacetParabolicImageReduction, first published in Library commit af5d652c2f2ff5b35b4ce4dbbf7cbec8bbf3e99e) derives UnramifiedFacetParabolicImageStatement from UnramifiedUpstairsRadicalRootGenerationStatement, UnramifiedFacetPositiveRadicalStatement (Corollary 8.4.12 row) and UnramifiedModelKernelStatement. UnramifiedUpstairsRadicalRootGenerationStatement (module Langlands.BruhatTits.IntegralModels.UnramifiedUpstairsRadicalRootGenerationStatement, first published in Library commit b3a1bdaf15715f16a43643513b7cbb6cbb58ef3a; derived from Corollary 8.4.12) asserts that one subgroup H serves every smooth O-model with integral points E.zeroPoints ⊓ C.pointwiseFixer (Omega) for a nonempty subset Omega of one apartment facet: the image of the reduction preimage of its unipotent radical is H joined with the positive root fixers of Omega. unramifiedUpstairsRadicalRootGeneration_of_singleton (module Langlands.BruhatTits.IntegralModels.UnramifiedSingleFacetReduction, first published in Library commit af5d652c2f2ff5b35b4ce4dbbf7cbec8bbf3e99e) derives it from its restriction to apartment singletons, UnramifiedUpstairsSingletonRadicalRootGenerationStatement. All three inputs are proved: by unramifiedUpstairsRadicalRootGeneration and unramifiedFacetPositiveRadical (both recorded in the Corollary 8.4.12 row) and by unramifiedModelKernel (above). Hence UnramifiedFacetParabolicImageStatement follows from published proofs: unramifiedFacetParabolicImage_of_generation_positive_modelKernel applied to these three theorems proves it, with the axioms propext, Classical.choice and Quot.sound, in a separate Lean check run at Library commit fcb85a7e. No published declaration states this composite.",
        "Recorded Lean proofs of Axiom 4.1.22(3) and (5): Langlands.BruhatTits.IntegralModels.unramifiedFacetCommonTorus (module Langlands.BruhatTits.IntegralModels.UnramifiedFacetCommonTorusProof, first published in Library commit aeb3911c4e1bf6e3a2f653e874e4ebc422d2a61a) proves UnramifiedFacetCommonTorusStatement at arbitrary universe u, with no premise. Maximality of the torus in the special fibre of the target model and in its reductive quotient comes from RelativeComponentModelHom.hasMaximalSplitTori_integer, and the sign formula for the Lie weights from unramifiedFacetLieWeightSignFormula_of_descent applied to unramifiedFacetLieWeightSign and Langlands.Geometry.Building.unramifiedDescendedApartmentTorus. Langlands.BruhatTits.IntegralModels.unramifiedFacetParabolicOrder (module Langlands.BruhatTits.IntegralModels.UnramifiedFacetParabolicOrderProof, first published in Library commit a2dba61c0a2313b5533c11ee999bece88bb28845) proves UnramifiedFacetParabolicOrderStatement at arbitrary universe u by applying Langlands.BruhatTits.IntegralModels.unramifiedFacetParabolicOrder_of_upstairs_rootGeneration (module Langlands.BruhatTits.IntegralModels.UnramifiedFacetParabolicOrderReduction, first published in Library commit a2dba61c0a2313b5533c11ee999bece88bb28845), a proof of UnramifiedFacetParabolicOrderReductionStatement, the implication from UnramifiedUpstairsRadicalRootGenerationStatement to UnramifiedFacetParabolicOrderStatement, to unramifiedUpstairsRadicalRootGeneration.",
        "Recorded GL_N regression instance (the standard alcove F' and its hyperspecial vertex F; no building point; the first assertion of part (1), parts (2) and (3), the parabolicity of the image ℘_F(F') in the maximal reductive quotient, and the Axiom 4.1.22(7) inclusion, which KP derive from Corollary 8.4.12). F is a nonarchimedean local field with integers 𝒪[F] and residue field 𝓀[F], and the Iwahori model iwahoriModel F N, its model data iwahoriModelData F N and quotient data iwahoriQuotientData F N are those of item (11) of the Section 13.2.6 row: the unit group scheme of the Iwahori order Λ (integral matrices whose strictly lower entries lie in the maximal ideal), with integral points the Iwahori subgroup I, the diagonal torus as reductive quotient and radical preimage I^+. Langlands.BruhatTits.IntegralModels.GeneralLinearIwahoriKernel (first published in Library commit 9ed11fc606807fab34c4852a4e88dbabebba69d1) defines matrixOrderModel F N, the unit group scheme of the order M_N(𝒪[F]) as an integral model of GL_N, and iwahoriMatrixHom F N, the model homomorphism from iwahoriModel F N induced by the inclusion Λ ⊆ M_N(𝒪[F]), with identity generic fibre. specialFibreKernelIso identifies the kernel of its special-fibre map with the unit group scheme 1 + J_-, where J_- is spanned by the classes of the scaled matrix units ϖE_ij (i > j) in 𝓀[F] ⊗ Λ, and iwahoriMatrixHom_specialFibreKernel_properties proves that this kernel is smooth, connected and unipotent. Langlands.BruhatTits.IntegralModels.GeneralLinearIwahoriImage (first published in Library commit 2016a0d994180c702214a75514a08546aa930f07) defines matrixOrderModelData F N (full and neutral model matrixOrderModel F N) and iwahoriMatrixModelHom : RelativeComponentModelHom (iwahoriModelData F N) (matrixOrderModelData F N). specialFibreImageIso identifies the schematic image of the special-fibre map with the upper triangular Borel subgroup scheme of GL_N over 𝓀[F] (the block parabolic for the weights −i), and the module proves HasSmoothConnectedUnipotentKernel, HasParabolicSpecialFibreImage, IsBorelSubgroup of the image and HasParabolicReductionPreimage for iwahoriMatrixModelHom F N: the sections of the hyperspecial model whose reduction lies in the rational points of the image are exactly the images of the sections of the Iwahori model. Langlands.BruhatTits.IntegralModels.GeneralLinearIwahoriStandard (first published in Library commit 497ef49830025d23824f6b2e2b1d5d60b594f51e) proves matrixOrderModelIso, an isomorphism over the identity of GL_N from matrixOrderModel F N to the Library's standard model GeneralLinear.standardIntegralModel 𝒪[F] F (Fin N), the neutral model of generalLinearModelData F N (module Langlands.BruhatTits.IntegralModels.GeneralLinearDepthZero), and defines iwahoriStandardModelHom : RelativeComponentModelHom (iwahoriModelData F N) (generalLinearModelData F N), iwahoriMatrixHom F N followed by that isomorphism. Transport along it proves the same four predicates and Borelness for iwahoriStandardModelHom F N. For the identity quotient data generalLinearQuotientData F N of the hyperspecial model, iwahoriStandardModelHom_hasParabolicReductiveImage and iwahoriStandardModelHom_isBorelSubgroup_reductiveImage prove that the image in the reductive quotient is parabolic, indeed Borel, and generalLinearIwahori_satisfiesPositiveRadicalClause proves SatisfiesPositiveRadicalClause (generalLinearQuotientData F N) (iwahoriQuotientData F N): the reductions of both models are surjective on integral sections, and the positive subgroup of the hyperspecial quotient data, the principal congruence subgroup of GL_N(𝒪[F]), lies in I^+. Here I, I^+, GL_N(𝒪[F]) and its principal congruence subgroup play the roles of G(k)^0_{F'}, G(k)^{0+}_{F'}, G(k)^0_F and G(k)^{0+}_F. Nothing identifies these models with KP's G^0_{F'} and G^0_F, and no facet appears. The product description of the kernel, Ψ_F(F'), the common torus of Axiom 4.1.22(3) and the bijection of part (4) are not formalized for GL_N. The proofs compute with the Iwahori order and do not use the unproved statements of this row.",
        "Open obligations: the parts of the conclusion that the Recorded Lean scope lists as not stated have no Lean statement, and the proved statements concern supplied building data and models. UnramifiedFacetParabolicImageStatement follows from published proofs (the entry on parts (2) and (3)); no theorem stating it was in Library commit fcb85a7e. IntegralModelAxiomsStatement is not proved. The smooth connected unipotent kernel of special-fibre maps between unramified parahoric models (KP Proposition 8.4.15), the parabolic order bijection (KP 4.1.22(5)) and the common maximal split tori and Lie-weight signs (KP 4.1.22(3)) for descended unramified facet models, and KP B.8.7 are proved."
      ],
      "consumer_or_regression": "Residue/facet correspondence and change-of-parahoric tests for depth-zero induction and double cosets; retain rational parabolics after Chapter 9 descent. The split SL_2 chamber-to-vertex kernel is a regression against the erroneous printed restricted index. The GL_N Iwahori-to-hyperspecial model map of the recorded regression instance is a positive regression for the first assertion of part (1), parts (2) and (3), the parabolicity of ℘_F(F') and the Axiom 4.1.22(7) inclusion.",
      "formal_status": "conditional",
      "publication_commits": [
        "51e4d8972659f1ffcf0ca89e8eee9540a30b52d3",
        "ed924aef420de137b4cbaa3b063a3618afcd73fd",
        "0c3f30c24701c74d5474fca3fbb5324a99aa1d58",
        "db8d6b3d466f2fd453a4df4624ce6c90db8eed46",
        "410c79471b79f65a02fb0f6070da7f2800793ff3",
        "af5d652c2f2ff5b35b4ce4dbbf7cbec8bbf3e99e",
        "b3a1bdaf15715f16a43643513b7cbb6cbb58ef3a",
        "430cc03fe803c5dbf74bc3baf91e8f7a2c26ea9c",
        "fab9caeae532b7a65e67e702bcab72d3194371ae",
        "b3dcc8cc4c93f1140c6b34374f589ccc637a1a22",
        "0b7bb3fdbe6e0386b666b6b099a3bc9cd3ad7e18",
        "e5365902d74534dbf1622c06e695dffdc128d723",
        "9ed11fc606807fab34c4852a4e88dbabebba69d1",
        "2016a0d994180c702214a75514a08546aa930f07",
        "497ef49830025d23824f6b2e2b1d5d60b594f51e",
        "d210ab55a138c1f91b826ee47c6280ce6c6b90bc",
        "aeb3911c4e1bf6e3a2f653e874e4ebc422d2a61a",
        "a2dba61c0a2313b5533c11ee999bece88bb28845",
        "9e39a73d21bd6ed6fac00b01cc5e01c0db5d105b",
        "e9c05be9da1000900a43de75ec2ede66892aa158",
        "a98af0ff45faf7905209f65d641389deee5d8392"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.UnramifiedModelKernelStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit 451cce4c; kind definition; statement_returns_prop true; the module is byte-identical to commit 51e4d897, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom.HasSmoothConnectedUnipotentKernel",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit eded01f2; kind definition; the module is byte-identical to commit ed924aef."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom.HasParabolicSpecialFibreImage",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit eded01f2; kind definition; the module is byte-identical to commit ed924aef."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom.HasParabolicReductionPreimage",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit eded01f2; kind definition; the module is byte-identical to commit ed924aef."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.FacetModelData.HasFacetParabolicOrderBijection",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit eded01f2; kind definition; the module is byte-identical to commit ed924aef."
        },
        {
          "declaration": "Langlands.Geometry.Building.IntegralModelAxiomsStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit eded01f2; kind definition; statement_returns_prop true; the module is byte-identical to commit ed924aef."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.UnramifiedFacetParabolicImageStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 70eca2e4; kind definition; statement_returns_prop true; the module is byte-identical to commit 0c3f30c2, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.UnramifiedFacetParabolicOrderStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 70eca2e4; kind definition; statement_returns_prop true; the module is byte-identical to commit 0c3f30c2, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.UnramifiedFacetCommonTorusStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 70eca2e4; kind definition; statement_returns_prop true; the module is byte-identical to commit 0c3f30c2, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.unramifiedModelKernel_of_compatible",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 70eca2e4; kind theorem; the module is byte-identical to commit db8d6b3d, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.UnramifiedCompatibleModelKernelSmoothConnectedStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 70eca2e4; kind definition; statement_returns_prop true; the module is byte-identical to commit 410c7947, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.unramifiedModelKernel_of_smoothConnected",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 70eca2e4; kind theorem; the module is byte-identical to commit 410c7947, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.unramifiedFacetParabolicImage_of_generation_positive_modelKernel",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 70eca2e4; kind theorem; the module is byte-identical to commit af5d652c, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.UnramifiedUpstairsRadicalRootGenerationStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 70eca2e4; kind definition; statement_returns_prop true; the module is byte-identical to commit b3a1bdaf, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.UnramifiedUpstairsSingletonRadicalRootGenerationStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 70eca2e4; kind definition; statement_returns_prop true; the module is byte-identical to commit af5d652c, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.unramifiedUpstairsRadicalRootGeneration_of_singleton",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 70eca2e4; kind theorem; the module is byte-identical to commit af5d652c, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.UnramifiedRootDepthKernelStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit b3dcc8cc; kind definition; statement_returns_prop true; the module is byte-identical to commit 430cc03f, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.UnramifiedNoHigherRootDepthKernelStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit b3dcc8cc; kind definition; statement_returns_prop true; the module is byte-identical to commit fab9caea, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.unramifiedNoHigherRootDepthKernel",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit b3dcc8cc; kind theorem; the module is byte-identical to commit fab9caea, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.TorusRootModelFamilyData.smooth_connected_kernel_of_orderedCharts",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit b3dcc8cc; kind theorem; the module is byte-identical to commit 410c7947, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.TorusRootModelFamilyData.smooth_connected_kernel_of_orderedOpenCharts",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit b3dcc8cc; kind theorem; the module is byte-identical to commit 410c7947, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.unramifiedRootDepthKernel_of_multipliableCoordinates",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit b3dcc8cc; kind theorem; that commit first published the module."
        },
        {
          "declaration": "Langlands.Geometry.Building.MultipliableRootGroupCoordinatesExistenceStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit b3dcc8cc; kind definition; statement_returns_prop true; the module is byte-identical to commit 0b7bb3fd, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.UnramifiedOrderedIntegralOpenCellStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit b3dcc8cc; kind definition; statement_returns_prop true; the module is byte-identical to commit 410c7947, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.UnramifiedOrderedIntegralOpenCellReductionStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit b3dcc8cc; kind definition; statement_returns_prop true; the module is byte-identical to commit e5365902, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.unramifiedOrderedIntegralOpenCellReduction",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit b3dcc8cc; kind theorem; the module is byte-identical to commit e5365902, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.TorusRootModelFamilyData.closedPoint_mem_range_orderedChart",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit b3dcc8cc; kind theorem; the module is byte-identical to commit 410c7947, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.OrderedFixerFactorization",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit b3dcc8cc; kind definition; the module is byte-identical to commit 410c7947, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.UnramifiedOrderedFixerFactorizationStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit b3dcc8cc; kind definition; statement_returns_prop true; the module is byte-identical to commit e5365902, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.unramifiedOrderedFixerFactorization",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit b3dcc8cc; kind theorem; the module is byte-identical to commit b3a1bdaf, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.matrixOrderModel",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 72480b70; kind definition; the module is byte-identical to commit 9ed11fc6, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.iwahoriMatrixHom",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 72480b70; kind definition; the module is byte-identical to commit 9ed11fc6, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.specialFibreKernelIso",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 72480b70; kind definition; the module is byte-identical to commit 9ed11fc6, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.iwahoriMatrixHom_specialFibreKernel_properties",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 72480b70; kind theorem; the module is byte-identical to commit 9ed11fc6, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.matrixOrderModelData",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 72480b70; kind definition; the module is byte-identical to commit 2016a0d9, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.iwahoriMatrixModelHom",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 72480b70; kind definition; the module is byte-identical to commit 2016a0d9, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.specialFibreImageIso",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 72480b70; kind definition; the module is byte-identical to commit 2016a0d9, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.iwahoriMatrixModelHom_hasSmoothConnectedUnipotentKernel",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 72480b70; kind theorem; the module is byte-identical to commit 2016a0d9, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.iwahoriMatrixModelHom_hasParabolicSpecialFibreImage",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 72480b70; kind theorem; the module is byte-identical to commit 2016a0d9, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.iwahoriMatrixModelHom_isBorelSubgroup_specialFibreImage",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 72480b70; kind theorem; the module is byte-identical to commit 2016a0d9, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.iwahoriMatrixModelHom_hasParabolicReductionPreimage",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 72480b70; kind theorem; the module is byte-identical to commit 2016a0d9, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.matrixOrderModelIso",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 72480b70; kind definition; the module is byte-identical to commit 497ef498, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.iwahoriStandardModelHom",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 72480b70; kind definition; the module is byte-identical to commit 497ef498, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.iwahoriStandardModelHom_hasSmoothConnectedUnipotentKernel",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 72480b70; kind theorem; the module is byte-identical to commit 497ef498, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.iwahoriStandardModelHom_hasParabolicSpecialFibreImage",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 72480b70; kind theorem; the module is byte-identical to commit 497ef498, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.iwahoriStandardModelHom_isBorelSubgroup_specialFibreImage",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 72480b70; kind theorem; the module is byte-identical to commit 497ef498, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.iwahoriStandardModelHom_hasParabolicReductionPreimage",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 72480b70; kind theorem; the module is byte-identical to commit 497ef498, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.iwahoriStandardModelHom_hasParabolicReductiveImage",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 72480b70; kind theorem; the module is byte-identical to commit 497ef498, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.iwahoriStandardModelHom_isBorelSubgroup_reductiveImage",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 72480b70; kind theorem; the module is byte-identical to commit 497ef498, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.generalLinearIwahori_satisfiesPositiveRadicalClause",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 72480b70; kind theorem; the module is byte-identical to commit 497ef498, its first publication."
        },
        {
          "declaration": "Langlands.Geometry.Building.multipliableRootGroupCoordinatesExistence",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 72480b70; kind theorem; the module is byte-identical to commit 2016a0d9, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.unramifiedRootDepthKernel",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 72480b70; kind theorem; the module is byte-identical to commit 497ef498, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.unramifiedOrderedIntegralOpenCell",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit 8f4a33d7; kind theorem; the module is byte-identical to commit d210ab55, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.unramifiedFacetCommonTorus",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit 8f4a33d7; kind theorem; the module is byte-identical to commit aeb3911c, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.unramifiedFacetParabolicOrder",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit 8f4a33d7; kind theorem; the module is byte-identical to commit a2dba61c, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.unramifiedFacetParabolicOrder_of_upstairs_rootGeneration",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit 8f4a33d7; kind theorem; the module is byte-identical to commit a2dba61c, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.unramifiedModelKernel",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit 8f4a33d7; kind theorem; the module is byte-identical to commit 9e39a73d, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.unramifiedUpstairsRadicalRootGeneration",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit 8f4a33d7; kind theorem; the module is byte-identical to commit e9c05be9, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.unramifiedFacetPositiveRadical",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit 8f4a33d7; kind theorem; the module is byte-identical to commit a98af0ff, its first publication."
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
        "Lean facet scope. F is a nonarchimedean local field of either characteristic, G is connected reductive over F, and x is a facet of a KPBuildingDatum D with D.SatisfiesGroupAxioms. Its parahoric, radical and represented connected reductive quotient come from the facet datum. Theorem bruhatTitsCompletionCertificate supplies such a group-valid datum for every F and G in this scope. The supplied-model lemmas below retain their own model, lifting and quotient hypotheses. The linear kernel correspondence takes finite-dimensional complex inducing representations.",
        "Recorded Lean scope: the published modules Langlands.BruhatTits.IntegralModels.DepthZeroReduction (first in Library commit 7047367a78583edbe335517824e30403414aa3f0) and Langlands.BruhatTits.IntegralModels.DepthZeroInduction (first in Library commit 7103f5282c4897716543f227940fdb2a0e12e70e) work over a domain R in universe u with fraction field K and a group scheme G over Spec K, with supplied D : RelativeComponentModelData R K G and Q : SpecialFibreQuotientData D. The smooth model D.neutral with connected fibres plays the role of G^0_x, Q.quotient that of Gred_x and Q.projection that of the quotient map; nothing identifies D.neutral with the actual parahoric model or D.neutral.integralPoints with P_{x,0}. The premises hrad : IsUnipotentRadical Q.radicalInclusion and hQ (Q.projection is the represented fppf quotient by that radical) are the first two conjuncts of Q.IsReductiveQuotient; reductivity of the quotient is not used. For a local domain R, ker_parahoricReduction hQ identifies the kernel of parahoricReduction : G^0(R) → Q.quotient(f) with Q.positivePoints.subgroupOf D.neutral.integralPoints, the radical preimage G(K)^{0+} of Axiom 4.1.22(7) inside G^0(R). For a Henselian local domain R with perfect residue field, parahoricReduction_surjective hrad hQ gives surjectivity and depthZeroQuotientEquiv hrad hQ is the induced group isomorphism from G^0(R) modulo that kernel onto Q.quotient(f). The integer rings of k and of K in the source are both such bases, so the source's assertion over K is the same declaration at another base; no instance is supplied. DepthZeroInduction adds the consumer test: inflation of a representation of Q.quotient(f) to G^0(R), the bijection between G^0(R)-maps from an inflation and Q.quotient(f)-maps into kernel invariants, and, for a topological-group structure on G(K) in which G^0(R) and its level-one congruence subgroup are open, compact induction from G^0(R) with Frobenius reciprocity (depthZeroInductionHomEquiv). For a nonarchimedean local field F, R = 𝒪[F] is proved Henselian and localFieldDepthZeroInductionHomEquiv, for affine G locally of finite type with rationalPointTopology, takes those openness premises from LocalFieldIntegralModel.CongruenceNeighborhoodBasisStatement. That statement is proved: congruenceNeighborhoodBasis_proof (module Langlands.GroupScheme.IntegralModel.CongruenceNeighborhoodBasisProof, first published in Library commit ba77b83f98d4cbe92842b4645577633e0541fdab) applies to every integral model over 𝒪[F] of an affine G, so localFieldDepthZeroInductionHomEquiv congruenceNeighborhoodBasis_proof needs only the supplied D, Q, hrad and hQ, and the first conjunct of congruenceNeighborhoodBasis_proof F G D.neutral says that D.neutral.integralPoints is compact in rationalPointTopology. The module Langlands.BruhatTits.IntegralModels.FiniteReductiveQuotient (first in Library commit cfedefb680f317b0ea5d351023e1c9dd886b2547) assumes a finite residue field. GroupScheme.finite_rationalPoints says that an affine group scheme locally of finite type over a finite commutative ring has finitely many points. For a local domain R and Q.quotient locally of finite type, finite_quotientPoints gives Finite (rationalPoints Q.quotient), as does IsConnectedReductive Q.quotient alone (finite_quotientPoints_of_isConnectedReductive); finiteQuotientGroup packages these points as a FiniteGrp, and positivePoints_subgroupOf_finiteIndex hQ says that Q.positivePoints.subgroupOf D.neutral.integralPoints has finite index. For a Henselian local domain, index_positivePoints_subgroupOf hrad hQ says that this index equals Nat.card (rationalPoints Q.quotient), and localField_index_positivePoints_subgroupOf is the case R = 𝒪[F]. For affine G locally of finite type with rationalPointTopology, localField_isOpen_ker_parahoricReduction says that the kernel of parahoricReduction is open in D.neutral.integralPoints. The module Langlands.BruhatTits.IntegralModels.DepthZeroCompactOpen (first in the same commit) proves, over a local domain, congruenceSubgroup_le_positivePoints (D.neutral.congruenceSubgroup ≤ Q.positivePoints) and positivePoints_subgroupOf_normal hQ. Over 𝒪[F], with G affine and locally of finite type and rationalPointTopology, localField_isOpen_positivePoints and localField_isCompact_positivePoints say that Q.positivePoints is open and compact in G(F) without hrad or hQ, localFieldPositiveOpenSubgroup bundles it as an OpenSubgroup, and RelativeComponentModelData.localFieldIntegralOpenSubgroup bundles D.neutral.integralPoints for affine G. The cokernel description of Gred_x is not formalized. The module Langlands.Representation.Induction.OpenIntertwiningStatement (first published in Library commit 79de65ce5fcd6dc5f182612988e1b529d49a63b4) states, for a subgroup H of a topological group G and representations of H over a commutative ring, CompactInductionIntertwiningStatement, the conjunction of three propositions. CompactInductionKernelStatement: for open H, the maps c-Ind_H^G A → c-Ind_H^G B between smooth representations correspond bijectively to intertwining kernels Φ : G → Hom(A, B) (IsIntertwiningKernel: Φ(hgh') = τ(h) ∘ Φ(g) ∘ σ(h'), and for each vector v only finitely many right cosets Hg have Φ(g)v ≠ 0), via Φ(g)v = T(unitFunction v)(g). CompactInductionDoubleCosetStatement: for compact open H, smooth σ and double-coset representatives s, restriction to the representatives is a bijection from intertwining kernels onto local intertwiner families (IsLocalIntertwinerFamily: φ(q) intertwines σ with h ↦ τ(s(q) h s(q)⁻¹) on H ∩ s(q)⁻¹ H s(q), and for each v only finitely many q have φ(q)v ≠ 0). CompactInductionFiniteTypeKernelStatement: for compact open H and finitely generated σ, the intertwining kernels are the covariant functions whose support meets finitely many double cosets HgH. With H = D.neutral.integralPoints and A, B two inflations Q.inflationSmoothRep, these describe the maps between the depth-zero compact inductions of DepthZeroInduction. Each conjunct is proved: Langlands.Induction.compactInductionKernel (module Langlands.Representation.Induction.OpenIntertwiningKernelProof), compactInductionDoubleCoset (module Langlands.Representation.Induction.OpenIntertwiningDoubleCosetProof) and compactInductionFiniteTypeKernel (module Langlands.Representation.Induction.OpenIntertwiningFiniteTypeProof), all first published in Library commit 730bd1f25b056b8106a2697e003c1ef1733a6b30; no separate theorem proves the conjunction. The module Langlands.BruhatTits.IntegralModels.DepthZeroIntertwining (first published in Library commit 73b1430a339b037d27e9096762b0400adb4fbd19) specializes them to H = D.neutral.integralPoints and two inflations, for a local domain R and a topological-group structure on G(K) in which H and the level-one congruence subgroup are open. depthZeroInductionKernelEquiv identifies the maps between the depth-zero compact inductions of σ and τ with the intertwining kernels of their inflations. For compact H and supplied double-coset representatives s, depthZeroInductionDoubleCosetEquiv identifies them with local intertwiner families on H\\G(K)/H. For σ on a finite k-module, depthZeroInductionKernel_finite_doubleCosetSupport says that the kernel of every such map is supported on finitely many double cosets. Over a nonarchimedean local field with G affine and rationalPointTopology, RelativeComponentModelData.localField_isOpen_congruenceSubgroup proves the congruence premise; for G also locally of finite type, localFieldDepthZeroInductionDoubleCosetEquiv and localField_depthZeroInductionKernel_finite_doubleCosetSupport need only the supplied D and Q. None of these uses hrad, hQ or a Henselian base. The double-coset representatives are supplied: no Bruhat or Iwahori decomposition of H\\G(K)/H, no Hecke-algebra multiplication and nothing about irreducibility or supercuspidality is stated.",
        "Recorded regression instances (split groups with their standard models; no building point): five published modules construct actual, not supplied, D and Q over R = 𝒪[F] for a nonarchimedean local field F whose residue field f has q elements. In each, D.full = D.neutral is a standard smooth model with connected fibres, obtained from the published criterion relativeComponentData_of_reductive_localField, the radical is the trivial subgroup, Q.quotient is the special fibre itself with the identity projection, and Q.IsReductiveQuotient is proved, so the theorems of the Recorded Lean scope apply with hrad and hQ discharged. (1) Langlands.BruhatTits.IntegralModels.MultiplicativeDepthZero (first published in Library commit 85c2fe719cf62e96f22aaf4ca03961c5814d086b): multiplicativeModelData on the published model IntegralModel.multiplicative, multiplicativeQuotientData and multiplicativeQuotientData_isReductiveQuotient; mem_multiplicative_positivePoints describes the radical preimage as the images of the units of 𝒪[F] with residue 1, that is 1 + 𝔪; multiplicative_index_positivePoints_subgroupOf gives index q − 1 in the integral points, and multiplicative_index_positivePoints_subgroupOf_eq_one gives index 1 when q = 2. (2) Langlands.BruhatTits.IntegralModels.SplitTorusDepthZero (first published in Library commit 85c2fe719cf62e96f22aaf4ca03961c5814d086b): for a finite index type I, Langlands.GroupScheme.IntegralModel.splitTorusModel is the split torus G_m^I over a domain, as a model of the split torus over its fraction field; splitTorusModelData, splitTorusQuotientData and splitTorusQuotientData_isReductiveQuotient are as in (1); mem_splitTorus_positivePoints gives (1 + 𝔪)^I and splitTorus_index_positivePoints_subgroupOf gives index (q − 1)^|I|. (3) Langlands.BruhatTits.IntegralModels.GeneralLinearDepthZero (first published in Library commit db8d6b3d466f2fd453a4df4624ce6c90db8eed46): for any D, SpecialFibreQuotientData.identityQuotient D is the quotient data with trivial radical and identity projection; identityQuotient_isReductiveQuotient proves that it is a reductive quotient when the neutral special fibre is connected reductive, and identityQuotient_positivePoints identifies its radical preimage with D.neutral.congruenceSubgroup, the image of the kernel of reduction. generalLinearModelData on the standard model GL_{N,𝒪[F]}, generalLinearQuotientData (the identity quotient) and generalLinearQuotientData_isReductiveQuotient; generalLinear_index_positivePoints_subgroupOf_eq_prod gives index ∏_{i<N} (q^N − q^i), the order of GL_N(f). For N = n + 1, generalLinear_integralPoints_map_eq_integralSubgroup and generalLinear_positivePoints_map_eq_principalLevelSubgroup map the integral points and the radical preimage onto the Library's concrete Conductor.integralSubgroup 𝒪[F] n and Conductor.principalLevelSubgroup F n 1, and generalLinear_principalLevelSubgroup_relIndex gives their relative index |GL_{n+1}(f)|. (4) Langlands.BruhatTits.IntegralModels.SymplecticDepthZero (first published in Library commit 410c79471b79f65a02fb0f6070da7f2800793ff3): symplecticModelData on the standard model Sp_{2l,𝒪[F]} (Langlands.GroupScheme.SymplecticMatrix.standardIntegralModel), symplecticQuotientData (the identity quotient) and symplecticQuotientData_isReductiveQuotient; symplectic_index_positivePoints_subgroupOf gives index |Sp_{2l}(f)|, and mem_symplectic_positivePoints_iff_generalLinear says that a point lies in the radical preimage exactly when its matrix in GL_{l⊕l}(F) is the image of an element of GL_{l⊕l}(𝒪[F]) with residue 1. (5) Langlands.BruhatTits.IntegralModels.SpecialLinearDepthZero (first published in Library commit 410c79471b79f65a02fb0f6070da7f2800793ff3): specialLinearModelData on the standard model SL_{n,𝒪[F]} (Langlands.GroupScheme.SpecialLinear.standardIntegralModel) for a nonempty finite index type n, specialLinearQuotientData (the identity quotient) and specialLinearQuotientData_isReductiveQuotient; specialLinear_index_positivePoints_subgroupOf_mul says that for n = Fin N the index times q − 1 is ∏_{i<N} (q^N − q^i), and specialLinear_positivePoints_eq_comap_principalLevelSubgroup identifies the radical preimage for n = Fin (m + 1) with the preimage of Conductor.principalLevelSubgroup F m 1. Each index theorem is derived from localField_index_positivePoints_subgroupOf (FiniteReductiveQuotient) through an identification of the residue-field points of the special fibre. Non-claims: no building and no point x appear. Nothing identifies these standard models with KP's G^0_x at a hyperspecial vertex (for G split over K, Proposition 8.4.14, printed p.306 / PDF p.337, says that G^0_x is reductive exactly when x is a hyperspecial vertex), D.neutral.integralPoints with P_{x,0}, or the radical preimage with P_{x,0+}; agreement with KP's values holds only through the explicit descriptions above. Every radical here is trivial, and every group is split.",
        "Recorded regression instances, second entry (non-split tori and the standard Iwahori subgroup of GL_N; no building point). F is a nonarchimedean local field whose residue field f = 𝓀[F] has q elements. (6) Langlands.BruhatTits.IntegralModels.NormOneTorusDepthZero (first published in Library commit e5365902d74534dbf1622c06e695dffdc128d723): for a finite separable field extension E/F and supplied integral data, namely a finite free 𝒪[F]-algebra B with eF : F ⊗[𝒪[F]] B ≃ₐ[F] E, a field k' with eκ : 𝓀[F] ⊗[𝒪[F]] B ≃ₐ[𝓀[F]] k' and hB stating that the norm-one kernel normOne 𝒪[F] B is smooth, normOneModel is that kernel R¹_{B/𝒪[F]} G_m as an integral model of the norm-one torus G = R¹_{E/F} G_m. normOneModelData (with D.full = D.neutral) and normOneQuotientData (the identity quotient) are actual D and Q, and normOneQuotientData_isReductiveQuotient proves Q.IsReductiveQuotient, the special fibre being the norm-one torus of k'/f. normOneQuotientData_positivePoints identifies the radical preimage with the congruence subgroup. normOne_index_positivePoints_subgroupOf gives its index in the integral points as the number of norm-one units of k', normOne_index_positivePoints_subgroupOf_mul says that this index times q − 1 is q^n − 1 for n = [k' : f], and normOne_index_positivePoints_subgroupOf_of_finrank_eq_two gives q + 1 for n = 2. normOne_isAnisotropic proves that G is anisotropic over F. WeilGm.normOne_smooth_of_decomposition proves hB when B becomes a finite nonempty product of copies of A' after a faithfully flat base change 𝒪[F] → A'. The module constructs no B. (7) Langlands.BruhatTits.IntegralModels.QuadraticNormOneDepthZero (first published in Library commit b3a1bdaf15715f16a43643513b7cbb6cbb58ef3a): UnramifiedQuadraticData F packages b, c ∈ 𝒪[F] such that b^2 − 4c is a unit and the reduction of X^2 + bX + c is irreducible over f. For such D, B = 𝒪[F][X]/(X^2 + bX + c) and E = F[X]/(X^2 + bX + c); UnramifiedQuadraticData.smooth proves hB through the splitting B ⊗[𝒪[F]] B ≃ B × B, and D.modelData, D.quotientData and D.quotientData_isReductiveQuotient are the instances of (6). D.index_positivePoints_subgroupOf gives index q + 1 and D.isAnisotropic proves anisotropy. UnramifiedQuadraticData.nonempty says that such data exist for every F, and exists_unramifiedQuadraticNormOne combines these: every nonarchimedean local field has an anisotropic norm-one torus with smooth model data, reductive identity quotient and depth-zero index q + 1. (8) Langlands.BruhatTits.IntegralModels.NormOneTraceSmoothness (first published in Library commit b3a1bdaf15715f16a43643513b7cbb6cbb58ef3a): HasTraceOne A B says that some element of B has trace 1 over A, and hasTraceOne_of_isUnit_finrank gives one (the inverse of the rank) when the rank of a finite free B is a unit of A. WeilGm.normOne_smooth_of_hasTraceOne proves that the norm-one kernel normOne A B is smooth over a noetherian ring A for every finite free A-algebra B with HasTraceOne A B. This gives hB for B that are not étale over 𝒪[F]. It gives only hB, not eκ: to apply (6), the special fibre 𝓀[F] ⊗[𝒪[F]] B must still be shown to be a field k'. (9) Langlands.BruhatTits.IntegralModels.GeneralLinearIwahoriComparison (first published in Library commit c40a01345b2f4172fa41e07ff31644b40e695003): on the standard model of (3), write K for (generalLinearModelData F N).neutral.integralPoints and K^+ for the radical preimage (generalLinearQuotientData F N).positivePoints. generalLinearReductionPreimage H is the preimage in K of a subgroup H of GL_N(f), as a subgroup of GL_N(F); the preimage of ⊤ is K, that of ⊥ is K^+, and relative indices are those in GL_N(f). generalLinearIwahoriPoints I and generalLinearIwahoriPositivePoints I^+ are the preimages of the upper triangular and upper unipotent groups of GL_N(f), so K^+ ≤ I^+ ≤ I ≤ K. generalLinearIwahoriPoints_relIndex gives [K : I] = [GL_N(f) : B(f)], generalLinearIwahoriPoints_relIndex_mul gives q^(N choose 2) (q − 1)^N [K : I] = ∏_{i<N} (q^N − q^i), generalLinearIwahoriPoints_relIndex_two gives [K : I] = q + 1 for N = 2, generalLinearIwahoriPositivePoints_relIndex gives [I : I^+] = (q − 1)^N, positivePoints_relIndex_generalLinearIwahoriPositivePoints gives [I^+ : K^+] = q^(N choose 2), and generalLinearIwahoriQuotientEquiv identifies I/I^+ with the diagonal torus (GL_1(f))^N. generalLinearIwahoriPoints_lt_integralPoints says that I < K for N ≥ 2, and generalLinearIwahoriPoints_of_le_one that I = K for N ≤ 1. The KP comparison values are Theorem 8.4.19(3) (printed p.309 / PDF p.340: the preimage of a parabolic of the special fibre is the parahoric of the larger facet) and Theorem 8.4.10(2) (printed p.305 / PDF p.336: for a chamber no affine root vanishes, so the maximal reductive quotient is a torus); KP state them over the maximal unramified extension, and the Lean statements are over F with its finite residue field. Model data for I are recorded in (11); nothing identifies I with P_{x,0} for x in a chamber or I^+ with P_{x,0+}. (10) Langlands.BruhatTits.IntegralModels.RamifiedQuadraticNormOne (first published in Library commit af5d652c2f2ff5b35b4ce4dbbf7cbec8bbf3e99e): RamifiedQuadraticData F is an irreducible element ϖ of 𝒪[F] (a uniformizer) together with the hypothesis that 2 is a unit of 𝒪[F], and RamifiedQuadraticData.nonempty_iff says that such data exist exactly when 2 is a unit. For such D, B = 𝒪[F][X]/(X^2 − ϖ) and E = F[X]/(X^2 − ϖ), and D.isAnisotropic proves that T = R¹_{E/F} G_m is anisotropic. D.smooth proves that the norm-one kernel of B is smooth, through (8). Its special fibre is disconnected: D.specialFibreSign sends a point x + yα of the special fibre (α^2 = 0, x^2 = 1) to x ∈ f^×, and index_ker_specialFibreSign gives its kernel index 2. D.componentPoints, the integral points whose reduction has sign 1, has relative index 2 in the integral points (relIndex_componentPoints) and contains the congruence subgroup (congruenceSubgroup_le_componentPoints). D.integralPoints_eq_top says that every point of T(F) is integral, and D.index_componentPoints gives index 2 in T(F). The module constructs no D or Q of the Recorded Lean scope; relativeComponentData_of_reductive_localField does not apply, the special fibre being disconnected. The comparison with corrected Remark 2.5.15 (corrections PDF pp.24–25: T(k)_0 ⊂ T(k)_1 = T(k) has index 2 for ramified ℓ/k, and T(k)_0 = (1 + p_ℓ) ∩ ℓ^1 when ℓ/k is tamely ramified) holds only through these values: componentPoints consists of the norm-one elements of 1 + α𝒪[F][α], and no Lean declaration identifies 𝒪[F][α] with the ring of integers of E or componentPoints with KP's T(F)_0. (11) Model data for I. Langlands.GroupScheme.FiniteFreeAlgebraUnits (first published in Library commit 7f5b5f04a855fc0b4671393213c87415a6ee2aaf): for R : CommRingCat and an R-algebra A, possibly noncommutative, with a finite basis b, FiniteFreeAlgebraUnits.groupScheme b is the affine group scheme over Spec R whose T-points are (Γ(T) ⊗[R] A)ˣ (pointsEquiv). It is smooth (smooth) with geometrically connected fibres; baseChangeIso compares its base change along R → R' with the unit group scheme of the base-changed basis, and generalLinearIso identifies the case A = M_N(R) with GL_N. Langlands.BruhatTits.IntegralModels.GeneralLinearIwahoriModel (first published in Library commit aeb3911c4e1bf6e3a2f653e874e4ebc422d2a61a): for a domain R with fraction field K, an R-algebra A with a finite basis and an injective φ : A →ₐ[R] M_N(K) such that every matrix has a nonzero multiple in its image, FiniteFreeAlgebraUnits.orderModel is this group scheme as an integral model of GL_N over K, with integral points φ(Aˣ) (mem_orderModel_integralPoints); orderModelData is D with D.full = D.neutral. iwahoriOrder F N is the 𝒪[F]-subalgebra of M_N(𝒪[F]) of matrices whose strictly lower entries lie in the maximal ideal. iwahoriModel F N is its order model, smooth (iwahoriModel_isSmooth), with integral points I (iwahoriModel_integralPoints); for iwahoriModelData, iwahoriModelData_neutralPoints gives D.neutral.integralPoints = I, and iwahoriModelData_neutralPoints_lt says that for N ≥ 2 this is a proper subgroup of the neutral integral points of the hyperspecial generalLinearModelData of (3). Langlands.GroupScheme.FiniteFreeAlgebraUnitsQuotient (first published in Library commit 4abbe7aabd9c92005d91c9d5bba86b879e928bb3): FiniteFreeAlgebraUnits.map is the homomorphism of unit group schemes induced by an algebra map f. Over a field, isFppfQuotient_map_of_section shows that it is an fppf quotient by its kernel when f has an algebra section, through SectionQuotient.isFppfQuotient_of_section for split homomorphisms. Langlands.GroupScheme.FiniteFreeAlgebraUnipotentUnits (first published in Library commit fab9caeae532b7a65e67e702bcab72d3194371ae): for an algebra map π : A →ₐ[R] B and a basis of A adapted to π whose kernel part spans a nilpotent ideal J, UnipotentPart.groupScheme is the smooth group scheme 1 + J with geometrically connected fibres, and kernelIso identifies it with the kernel of the unit-group map of π. Over a field, UnipotentPart.isUnipotent proves that it is unipotent when the basis of J carries weights at least 1 that add under multiplication, and UnipotentPart.isUnipotentRadical says that if moreover π has an algebra section and the unit group of B is a torus, then 1 + J is a unipotent radical and the unit-group map of π is an fppf quotient by it; isTorus_pi proves that the unit group of k^N is a torus. Langlands.BruhatTits.IntegralModels.GeneralLinearIwahoriQuotient (first published in Library commit 0b7bb3fdbe6e0386b666b6b099a3bc9cd3ad7e18): specialFibreIso identifies the special fibre of iwahoriModelData F N with the unit group scheme of 𝓀[F] ⊗[𝒪[F]] iwahoriOrder F N. iwahoriQuotientData is Q with radical 1 + J, for J spanned by the off-diagonal scaled matrix units (specialRadical_isUnipotentRadical), and quotient the diagonal split torus, the unit group of 𝓀[F]^N. iwahoriQuotientData_isReductiveQuotient proves Q.IsReductiveQuotient, and iwahoriQuotientData_positivePoints proves Q.positivePoints = generalLinearIwahoriPositivePoints F N, the group I^+ of (9). So the pair I^+ ≤ I of (9) is the pair of radical preimage and neutral integral points of actual D and Q, which for N ≥ 2 differ from the hyperspecial data of (3), with reductive quotient a torus, as KP Theorem 8.4.10(2) gives at a chamber. Nothing identifies iwahoriModelData with KP's G^0_x for x in a chamber. (12) Depth-zero theory for I. Langlands.BruhatTits.IntegralModels.GeneralLinearIwahoriDepthZero (first published in Library commit b3dcc8cc4c93f1140c6b34374f589ccc637a1a22) applies the general depth-zero results of the Recorded Lean scope to D = iwahoriModelData F N and Q = iwahoriQuotientData F N of (11). iwahoriModelData_integralPoints gives D.neutral.integralPoints = I. diagTorusPointsEquiv identifies the residue-field points of the quotient, the diagonal torus diagTorus F N, with (𝓀[F]ˣ)^N, and card_diagTorus_rationalPoints counts (q − 1)^N of them. singletonLevi_parahoricReduction says that on I the general reduction Q.parahoricReduction, read through singletonLevi as a Levi element of the singleton block shape, is the group-level projection generalLinearIwahoriDiagonal of (9), the diagonal of the residue matrix. iwahoriDepthZeroQuotientEquiv is the general depthZeroQuotientEquiv for D and Q followed by diagTorusPointsEquiv: I modulo the kernel of Q.parahoricReduction is (𝓀[F]ˣ)^N, and iwahoriQuotientData_ker_parahoricReduction identifies that kernel with I^+. iwahori_index_positivePoints_subgroupOf obtains [I : I^+] = (q − 1)^N from the general index theorem localField_index_positivePoints_subgroupOf, the value that (9) computes by finite group theory. isOpen_generalLinearIwahoriPoints, isCompact_generalLinearIwahoriPoints, isOpen_generalLinearIwahoriPositivePoints and isCompact_generalLinearIwahoriPositivePoints prove that I and I^+ are compact open in GL_N(F) with its canonical topology, from the general theorems for neutral integral points (isOpen_integralPoints_localField, isCompact_integralPoints_localField) and radical preimages (localField_isOpen_positivePoints, localField_isCompact_positivePoints). Non-claims: no building and no point x appear. Nothing identifies these models with KP's G^0_x, or their points with P_{x,0}, P_{x,0+} or the torus subgroups T(k)_1 and T(k)_0 of Proposition 2.5.8 and Definition 2.5.13; agreement with KP holds only through the explicit values above."
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
        "Langlands.BruhatTits.IntegralModels.specialLinear_positivePoints_eq_comap_principalLevelSubgroup",
        "Langlands.GroupScheme.WeilGm.normOne_smooth_of_decomposition",
        "Langlands.BruhatTits.IntegralModels.normOneModel",
        "Langlands.BruhatTits.IntegralModels.normOneModelData",
        "Langlands.BruhatTits.IntegralModels.normOneQuotientData",
        "Langlands.BruhatTits.IntegralModels.normOneQuotientData_isReductiveQuotient",
        "Langlands.BruhatTits.IntegralModels.normOneQuotientData_positivePoints",
        "Langlands.BruhatTits.IntegralModels.normOne_index_positivePoints_subgroupOf",
        "Langlands.BruhatTits.IntegralModels.normOne_index_positivePoints_subgroupOf_mul",
        "Langlands.BruhatTits.IntegralModels.normOne_index_positivePoints_subgroupOf_of_finrank_eq_two",
        "Langlands.BruhatTits.IntegralModels.normOne_isAnisotropic",
        "Langlands.BruhatTits.IntegralModels.UnramifiedQuadraticData",
        "Langlands.BruhatTits.IntegralModels.UnramifiedQuadraticData.smooth",
        "Langlands.BruhatTits.IntegralModels.UnramifiedQuadraticData.modelData",
        "Langlands.BruhatTits.IntegralModels.UnramifiedQuadraticData.quotientData",
        "Langlands.BruhatTits.IntegralModels.UnramifiedQuadraticData.quotientData_isReductiveQuotient",
        "Langlands.BruhatTits.IntegralModels.UnramifiedQuadraticData.index_positivePoints_subgroupOf",
        "Langlands.BruhatTits.IntegralModels.UnramifiedQuadraticData.isAnisotropic",
        "Langlands.BruhatTits.IntegralModels.UnramifiedQuadraticData.nonempty",
        "Langlands.BruhatTits.IntegralModels.exists_unramifiedQuadraticNormOne",
        "Langlands.Algebra.HasTraceOne",
        "Langlands.Algebra.hasTraceOne_of_isUnit_finrank",
        "Langlands.GroupScheme.WeilGm.normOne_smooth_of_hasTraceOne",
        "Langlands.BruhatTits.IntegralModels.generalLinearReductionPreimage",
        "Langlands.BruhatTits.IntegralModels.generalLinearIwahoriPoints",
        "Langlands.BruhatTits.IntegralModels.generalLinearIwahoriPositivePoints",
        "Langlands.BruhatTits.IntegralModels.generalLinearIwahoriPoints_relIndex",
        "Langlands.BruhatTits.IntegralModels.generalLinearIwahoriPoints_relIndex_mul",
        "Langlands.BruhatTits.IntegralModels.generalLinearIwahoriPoints_relIndex_two",
        "Langlands.BruhatTits.IntegralModels.generalLinearIwahoriPositivePoints_relIndex",
        "Langlands.BruhatTits.IntegralModels.positivePoints_relIndex_generalLinearIwahoriPositivePoints",
        "Langlands.BruhatTits.IntegralModels.generalLinearIwahoriQuotientEquiv",
        "Langlands.BruhatTits.IntegralModels.generalLinearIwahoriPoints_lt_integralPoints",
        "Langlands.BruhatTits.IntegralModels.generalLinearIwahoriPoints_of_le_one",
        "Langlands.BruhatTits.IntegralModels.RamifiedQuadraticData",
        "Langlands.BruhatTits.IntegralModels.RamifiedQuadraticData.smooth",
        "Langlands.BruhatTits.IntegralModels.RamifiedQuadraticData.isAnisotropic",
        "Langlands.BruhatTits.IntegralModels.RamifiedQuadraticData.specialFibreSign",
        "Langlands.BruhatTits.IntegralModels.RamifiedQuadraticData.index_ker_specialFibreSign",
        "Langlands.BruhatTits.IntegralModels.RamifiedQuadraticData.componentPoints",
        "Langlands.BruhatTits.IntegralModels.RamifiedQuadraticData.relIndex_componentPoints",
        "Langlands.BruhatTits.IntegralModels.RamifiedQuadraticData.congruenceSubgroup_le_componentPoints",
        "Langlands.BruhatTits.IntegralModels.RamifiedQuadraticData.integralPoints_eq_top",
        "Langlands.BruhatTits.IntegralModels.RamifiedQuadraticData.index_componentPoints",
        "Langlands.BruhatTits.IntegralModels.RamifiedQuadraticData.nonempty_iff",
        "Langlands.GroupScheme.FiniteFreeAlgebraUnits.groupScheme",
        "Langlands.GroupScheme.FiniteFreeAlgebraUnits.smooth",
        "Langlands.GroupScheme.FiniteFreeAlgebraUnits.pointsEquiv",
        "Langlands.GroupScheme.FiniteFreeAlgebraUnits.baseChangeIso",
        "Langlands.GroupScheme.FiniteFreeAlgebraUnits.generalLinearIso",
        "Langlands.GroupScheme.FiniteFreeAlgebraUnits.orderModel",
        "Langlands.GroupScheme.FiniteFreeAlgebraUnits.mem_orderModel_integralPoints",
        "Langlands.GroupScheme.FiniteFreeAlgebraUnits.orderModelData",
        "Langlands.BruhatTits.IntegralModels.iwahoriOrder",
        "Langlands.BruhatTits.IntegralModels.iwahoriModel",
        "Langlands.BruhatTits.IntegralModels.iwahoriModel_isSmooth",
        "Langlands.BruhatTits.IntegralModels.iwahoriModel_integralPoints",
        "Langlands.BruhatTits.IntegralModels.iwahoriModelData",
        "Langlands.BruhatTits.IntegralModels.iwahoriModelData_neutralPoints",
        "Langlands.BruhatTits.IntegralModels.iwahoriModelData_neutralPoints_lt",
        "Langlands.GroupScheme.FiniteFreeAlgebraUnits.map",
        "Langlands.GroupScheme.FiniteFreeAlgebraUnits.isFppfQuotient_map_of_section",
        "Langlands.GroupScheme.SectionQuotient.isFppfQuotient_of_section",
        "Langlands.GroupScheme.FiniteFreeAlgebraUnits.UnipotentPart.groupScheme",
        "Langlands.GroupScheme.FiniteFreeAlgebraUnits.UnipotentPart.kernelIso",
        "Langlands.GroupScheme.FiniteFreeAlgebraUnits.UnipotentPart.isUnipotent",
        "Langlands.GroupScheme.FiniteFreeAlgebraUnits.UnipotentPart.isUnipotentRadical",
        "Langlands.GroupScheme.FiniteFreeAlgebraUnits.isTorus_pi",
        "Langlands.BruhatTits.IntegralModels.specialFibreIso",
        "Langlands.BruhatTits.IntegralModels.specialRadical_isUnipotentRadical",
        "Langlands.BruhatTits.IntegralModels.iwahoriQuotientData",
        "Langlands.BruhatTits.IntegralModels.iwahoriQuotientData_isReductiveQuotient",
        "Langlands.BruhatTits.IntegralModels.iwahoriQuotientData_positivePoints",
        "Langlands.BruhatTits.IntegralModels.diagTorusPointsEquiv",
        "Langlands.BruhatTits.IntegralModels.card_diagTorus_rationalPoints",
        "Langlands.BruhatTits.IntegralModels.singletonLevi_parahoricReduction",
        "Langlands.BruhatTits.IntegralModels.iwahoriDepthZeroQuotientEquiv",
        "Langlands.BruhatTits.IntegralModels.iwahoriQuotientData_ker_parahoricReduction",
        "Langlands.BruhatTits.IntegralModels.iwahori_index_positivePoints_subgroupOf",
        "Langlands.BruhatTits.IntegralModels.isOpen_generalLinearIwahoriPoints",
        "Langlands.BruhatTits.IntegralModels.isCompact_generalLinearIwahoriPoints",
        "Langlands.BruhatTits.IntegralModels.isOpen_generalLinearIwahoriPositivePoints",
        "Langlands.BruhatTits.IntegralModels.isCompact_generalLinearIwahoriPositivePoints",
        "Langlands.Geometry.Building.DepthZeroConsumerStatement",
        "Langlands.Geometry.Building.depthZeroConsumer"
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
        "Langlands.BruhatTits.IntegralModels.SpecialLinearDepthZero",
        "Langlands.BruhatTits.IntegralModels.NormOneTorusDepthZero",
        "Langlands.BruhatTits.IntegralModels.QuadraticNormOneDepthZero",
        "Langlands.BruhatTits.IntegralModels.NormOneTraceSmoothness",
        "Langlands.BruhatTits.IntegralModels.GeneralLinearIwahoriComparison",
        "Langlands.BruhatTits.IntegralModels.RamifiedQuadraticNormOne",
        "Langlands.GroupScheme.FiniteFreeAlgebraUnits",
        "Langlands.BruhatTits.IntegralModels.GeneralLinearIwahoriModel",
        "Langlands.GroupScheme.FiniteFreeAlgebraUnitsQuotient",
        "Langlands.GroupScheme.FiniteFreeAlgebraUnipotentUnits",
        "Langlands.BruhatTits.IntegralModels.GeneralLinearIwahoriQuotient",
        "Langlands.BruhatTits.IntegralModels.GeneralLinearIwahoriDepthZero",
        "Langlands.Geometry.Building.DepthZero.Statement",
        "Langlands.Geometry.Building.DepthZero.Proof"
      ],
      "dependencies": [
        "Theorems 8.3.2 and 8.3.13 construct the actual models; Sections 9.2.5–9.2.6 descend them and identify integral points",
        "The first reduction arrow is surjective by 8.1.3. The second is surjective by Proposition 2.4.3 over perfect f, proved using Lemma 2.4.2 on split unipotent groups and H^1",
        "Corollary 8.4.12 and Section 9.5 identify the actual kernel over k; apply the group first isomorphism theorem",
        "The congruence models and their morphism come from Theorem 8.5.2 and Section 8.5.17, with Chapter 9 descent",
        "Section 13.2.2 separates facet-dependent 0 and 0+ from positive-depth variation, and 13.2.3 uses 9.8.3(2) for the Gamma-invariant group comparison",
        "Recorded Lean route: surjectivity composes the Henselian lifting theorem IntegralModel.reduction_surjective for the smooth model (the role of 8.1.3) with projectionPoints_surjective. Over a perfect residue field the latter uses a scheme section of the projection, obtained from the published perfectFieldUnipotentSplit and splitUnipotentAffineTorsorStatement, instead of the Galois cohomology of Lemma 2.4.2 and Proposition 2.4.3 (printed p.84 / PDF p.115). The kernel is the radical preimage by construction. Its identification with the Moy–Prasad group P_{x,0+} (Corollary 8.4.12, printed p.306 / PDF p.337, and Section 9.5) and the construction of the actual models, radical and quotient (Theorems 8.3.2 and 8.3.13, Sections 9.2.5–9.2.6) are not formalized.",
        "Intertwining source (outside KP): M.-F. Vignéras, Représentations ℓ-modulaires d'un groupe réductif p-adique avec ℓ ≠ p (1996), literature ID provided-74667a7cddb3bdafff85f01c658605ce7d929f6da73950d79457c46bcd761dd4, SHA-256 4d2daeee16515f994dfb04157915179b55b30d5bf2f874a16f13e7cb6fa7d657, I.8.5 at printed pp.67–68 / PDF pp.85–86, with I.8.1–I.8.2 at printed pp.64–65 / PDF pp.82–83 and the proof of I.8.3 at printed p.66 / PDF p.84. I.8.5 identifies Hom(ind_{G,K} σ, ind_{G,H} π), for open K and σ of finite type, with the covariant functions supported on finitely many double cosets HgK. The kernel statement drops finite type and compactness and uses the per-vector support condition of the source's proof; the double-coset statement parametrizes kernels by their values at double-coset representatives, as in the proof of I.8.3, with per-vector finiteness, a form derived for this unit; the finite-type statement recovers I.8.5 a) for compact open H. Only the case K = H is stated; compactness of H replaces compactness modulo the centre.",
        "The theorem Langlands.Geometry.Building.depthZeroConsumer proves DepthZeroConsumerStatement. It uses the neutral facet model and its quotient, with the model point topology and the perfect finite residue field. It identifies the parahoric with the zero-fixer, proves compact openness, and gives the normal compact open kernel, the surjective reduction and the quotient equivalence respecting representatives. Inflation and compact induction use that reduction, and the linear kernel map is injective with image the equivariant functions of finite double-coset support. The completion certificate supplies the group axioms through IsAvailableFor.groupAxioms."
      ],
      "consumer_or_regression": "The facet consumer handles finite reductive points, smooth inflation and compact induction, and finite-dimensional intertwiners. Its GL_N vertex and chamber targets compare the facet quotients with the standard integral model and the Iwahori model respectively. The stated Lean proof covers the local-field rational-point and representation conclusions. The source also describes the group-scheme cokernel and the rational-point comparison over K.",
      "formal_status": "proved",
      "publication_commits": [
        "7047367a78583edbe335517824e30403414aa3f0",
        "7103f5282c4897716543f227940fdb2a0e12e70e",
        "79de65ce5fcd6dc5f182612988e1b529d49a63b4",
        "cfedefb680f317b0ea5d351023e1c9dd886b2547",
        "730bd1f25b056b8106a2697e003c1ef1733a6b30",
        "73b1430a339b037d27e9096762b0400adb4fbd19",
        "85c2fe719cf62e96f22aaf4ca03961c5814d086b",
        "db8d6b3d466f2fd453a4df4624ce6c90db8eed46",
        "410c79471b79f65a02fb0f6070da7f2800793ff3",
        "e5365902d74534dbf1622c06e695dffdc128d723",
        "b3a1bdaf15715f16a43643513b7cbb6cbb58ef3a",
        "c40a01345b2f4172fa41e07ff31644b40e695003",
        "af5d652c2f2ff5b35b4ce4dbbf7cbec8bbf3e99e",
        "7f5b5f04a855fc0b4671393213c87415a6ee2aaf",
        "aeb3911c4e1bf6e3a2f653e874e4ebc422d2a61a",
        "4abbe7aabd9c92005d91c9d5bba86b879e928bb3",
        "fab9caeae532b7a65e67e702bcab72d3194371ae",
        "0b7bb3fdbe6e0386b666b6b099a3bc9cd3ad7e18",
        "b3dcc8cc4c93f1140c6b34374f589ccc637a1a22",
        "be45b656851f6de76d62d52bac606a01769d968c"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.depthZeroQuotientEquiv",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-11 at Library commit 389dbc16; a definition."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.parahoricReduction_surjective",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-11 at Library commit 389dbc16; kind theorem."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.ker_parahoricReduction",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-11 at Library commit 389dbc16; kind theorem."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.depthZeroInductionHomEquiv",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-11 at Library commit 389dbc16; a definition."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.localFieldDepthZeroInductionHomEquiv",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-11 at Library commit 389dbc16; a definition."
        },
        {
          "declaration": "Langlands.Induction.CompactInductionIntertwiningStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-12 at Library commit 9951a27f; kind definition; statement_returns_prop true; the module is byte-identical to commit 79de65ce."
        },
        {
          "declaration": "Langlands.Induction.CompactInductionKernelStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-12 at Library commit 9951a27f; kind definition; statement_returns_prop true; the module is byte-identical to commit 79de65ce."
        },
        {
          "declaration": "Langlands.Induction.CompactInductionDoubleCosetStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-12 at Library commit 9951a27f; kind definition; statement_returns_prop true; the module is byte-identical to commit 79de65ce."
        },
        {
          "declaration": "Langlands.Induction.CompactInductionFiniteTypeKernelStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-12 at Library commit 9951a27f; kind definition; statement_returns_prop true; the module is byte-identical to commit 79de65ce."
        },
        {
          "declaration": "Langlands.GroupScheme.finite_rationalPoints",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit cfedefb6, the commit of first publication; kind theorem."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.finite_quotientPoints_of_isConnectedReductive",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit cfedefb6, the commit of first publication; kind theorem."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.finiteQuotientGroup",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit cfedefb6, the commit of first publication; kind definition."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.index_positivePoints_subgroupOf",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit cfedefb6, the commit of first publication; kind theorem."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.localField_index_positivePoints_subgroupOf",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit cfedefb6, the commit of first publication; kind theorem."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.localField_isOpen_ker_parahoricReduction",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit cfedefb6, the commit of first publication; kind theorem."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.positivePoints_subgroupOf_normal",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit cfedefb6, the commit of first publication; kind theorem."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.localField_isOpen_positivePoints",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit cfedefb6, the commit of first publication; kind theorem."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.localField_isCompact_positivePoints",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit cfedefb6, the commit of first publication; kind theorem."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.localFieldPositiveOpenSubgroup",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit cfedefb6, the commit of first publication; kind definition."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.RelativeComponentModelData.localFieldIntegralOpenSubgroup",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit cfedefb6, the commit of first publication; kind definition."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.depthZeroInductionKernelEquiv",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit aae8cb82; kind definition; the module is byte-identical to commit 73b1430a, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.depthZeroInductionDoubleCosetEquiv",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit aae8cb82; kind definition; the module is byte-identical to commit 73b1430a, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.depthZeroInductionKernel_finite_doubleCosetSupport",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit aae8cb82; kind theorem; the module is byte-identical to commit 73b1430a, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.localFieldDepthZeroInductionDoubleCosetEquiv",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit aae8cb82; kind definition; the module is byte-identical to commit 73b1430a, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.localField_depthZeroInductionKernel_finite_doubleCosetSupport",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit aae8cb82; kind theorem; the module is byte-identical to commit 73b1430a, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.RelativeComponentModelData.localField_isOpen_congruenceSubgroup",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit aae8cb82; kind theorem; the module is byte-identical to commit 73b1430a, its first publication."
        },
        {
          "declaration": "Langlands.Induction.compactInductionKernel",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit aae8cb82; kind theorem, proving CompactInductionKernelStatement; the module is byte-identical to commit 730bd1f2, its first publication."
        },
        {
          "declaration": "Langlands.Induction.compactInductionDoubleCoset",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit aae8cb82; kind theorem, proving CompactInductionDoubleCosetStatement; the module is byte-identical to commit 730bd1f2, its first publication."
        },
        {
          "declaration": "Langlands.Induction.compactInductionFiniteTypeKernel",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit aae8cb82; kind theorem, proving CompactInductionFiniteTypeKernelStatement; the module is byte-identical to commit 730bd1f2, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.multiplicativeModelData",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 3489c503; kind definition; the module is byte-identical to commit 85c2fe71, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.multiplicativeQuotientData",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 410c7947; kind definition; the module is byte-identical to commit 85c2fe71, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.multiplicativeQuotientData_isReductiveQuotient",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 410c7947; kind theorem; the module is byte-identical to commit 85c2fe71, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.multiplicative_index_positivePoints_subgroupOf",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 410c7947; kind theorem; the module is byte-identical to commit 85c2fe71, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.multiplicative_index_positivePoints_subgroupOf_eq_one",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 410c7947; kind theorem; the module is byte-identical to commit 85c2fe71, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.mem_multiplicative_positivePoints",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 410c7947; kind theorem; the module is byte-identical to commit 85c2fe71, its first publication."
        },
        {
          "declaration": "Langlands.GroupScheme.IntegralModel.splitTorusModel",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 410c7947; kind definition; the module is byte-identical to commit 85c2fe71, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.splitTorusModelData",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 410c7947; kind definition; the module is byte-identical to commit 85c2fe71, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.splitTorusQuotientData",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 410c7947; kind definition; the module is byte-identical to commit 85c2fe71, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.splitTorusQuotientData_isReductiveQuotient",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 410c7947; kind theorem; the module is byte-identical to commit 85c2fe71, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.splitTorus_index_positivePoints_subgroupOf",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 410c7947; kind theorem; the module is byte-identical to commit 85c2fe71, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.mem_splitTorus_positivePoints",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 410c7947; kind theorem; the module is byte-identical to commit 85c2fe71, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.identityQuotient",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 410c7947; kind definition; the module is byte-identical to commit db8d6b3d, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.identityQuotient_isReductiveQuotient",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 410c7947; kind theorem; the module is byte-identical to commit db8d6b3d, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.identityQuotient_positivePoints",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 410c7947; kind theorem; the module is byte-identical to commit db8d6b3d, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.generalLinearModelData",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 410c7947; kind definition; the module is byte-identical to commit db8d6b3d, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.generalLinearQuotientData",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 410c7947; kind definition; the module is byte-identical to commit db8d6b3d, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.generalLinearQuotientData_isReductiveQuotient",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 410c7947; kind theorem; the module is byte-identical to commit db8d6b3d, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.generalLinear_index_positivePoints_subgroupOf_eq_prod",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 410c7947; kind theorem; the module is byte-identical to commit db8d6b3d, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.generalLinear_integralPoints_map_eq_integralSubgroup",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 410c7947; kind theorem; the module is byte-identical to commit db8d6b3d, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.generalLinear_positivePoints_map_eq_principalLevelSubgroup",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 410c7947; kind theorem; the module is byte-identical to commit db8d6b3d, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.generalLinear_principalLevelSubgroup_relIndex",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 410c7947; kind theorem; the module is byte-identical to commit db8d6b3d, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.symplecticModelData",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 410c7947; kind definition; the module is byte-identical to commit 410c7947, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.symplecticQuotientData",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 410c7947; kind definition; the module is byte-identical to commit 410c7947, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.symplecticQuotientData_isReductiveQuotient",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 410c7947; kind theorem; the module is byte-identical to commit 410c7947, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.symplectic_index_positivePoints_subgroupOf",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 410c7947; kind theorem; the module is byte-identical to commit 410c7947, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.mem_symplectic_positivePoints_iff_generalLinear",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 410c7947; kind theorem; the module is byte-identical to commit 410c7947, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.specialLinearModelData",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 410c7947; kind definition; the module is byte-identical to commit 410c7947, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.specialLinearQuotientData",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 410c7947; kind definition; the module is byte-identical to commit 410c7947, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.specialLinearQuotientData_isReductiveQuotient",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 410c7947; kind theorem; the module is byte-identical to commit 410c7947, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.specialLinear_index_positivePoints_subgroupOf_mul",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 410c7947; kind theorem; the module is byte-identical to commit 410c7947, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.specialLinear_positivePoints_eq_comap_principalLevelSubgroup",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 410c7947; kind theorem; the module is byte-identical to commit 410c7947, its first publication."
        },
        {
          "declaration": "Langlands.GroupScheme.WeilGm.normOne_smooth_of_decomposition",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit c40a0134; kind theorem; the module is byte-identical to commit e5365902, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.normOneModel",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit c40a0134; kind definition; the module is byte-identical to commit e5365902, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.normOneModelData",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit c40a0134; kind definition; the module is byte-identical to commit e5365902, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.normOneQuotientData",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit c40a0134; kind definition; the module is byte-identical to commit e5365902, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.normOneQuotientData_isReductiveQuotient",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit c40a0134; kind theorem; the module is byte-identical to commit e5365902, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.normOneQuotientData_positivePoints",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit c40a0134; kind theorem; the module is byte-identical to commit e5365902, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.normOne_index_positivePoints_subgroupOf",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit c40a0134; kind theorem; the module is byte-identical to commit e5365902, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.normOne_index_positivePoints_subgroupOf_mul",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit c40a0134; kind theorem; the module is byte-identical to commit e5365902, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.normOne_index_positivePoints_subgroupOf_of_finrank_eq_two",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit c40a0134; kind theorem; the module is byte-identical to commit e5365902, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.normOne_isAnisotropic",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit c40a0134; kind theorem; the module is byte-identical to commit e5365902, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.UnramifiedQuadraticData",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 457e31a2; kind inductive; the module is byte-identical to commit b3a1bdaf, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.UnramifiedQuadraticData.smooth",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 457e31a2; kind theorem; the module is byte-identical to commit b3a1bdaf, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.UnramifiedQuadraticData.modelData",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 457e31a2; kind definition; the module is byte-identical to commit b3a1bdaf, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.UnramifiedQuadraticData.quotientData",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 457e31a2; kind definition; the module is byte-identical to commit b3a1bdaf, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.UnramifiedQuadraticData.quotientData_isReductiveQuotient",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 457e31a2; kind theorem; the module is byte-identical to commit b3a1bdaf, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.UnramifiedQuadraticData.index_positivePoints_subgroupOf",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 457e31a2; kind theorem; the module is byte-identical to commit b3a1bdaf, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.UnramifiedQuadraticData.isAnisotropic",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 457e31a2; kind theorem; the module is byte-identical to commit b3a1bdaf, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.UnramifiedQuadraticData.nonempty",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 457e31a2; kind theorem; the module is byte-identical to commit b3a1bdaf, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.exists_unramifiedQuadraticNormOne",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 457e31a2; kind theorem; the module is byte-identical to commit b3a1bdaf, its first publication."
        },
        {
          "declaration": "Langlands.Algebra.HasTraceOne",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 457e31a2; kind definition; the module is byte-identical to commit b3a1bdaf, its first publication."
        },
        {
          "declaration": "Langlands.Algebra.hasTraceOne_of_isUnit_finrank",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 457e31a2; kind theorem; the module is byte-identical to commit b3a1bdaf, its first publication."
        },
        {
          "declaration": "Langlands.GroupScheme.WeilGm.normOne_smooth_of_hasTraceOne",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 457e31a2; kind theorem; the module is byte-identical to commit b3a1bdaf, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.generalLinearReductionPreimage",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit c40a0134; kind definition; the module is byte-identical to commit c40a0134, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.generalLinearIwahoriPoints",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit c40a0134; kind definition; the module is byte-identical to commit c40a0134, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.generalLinearIwahoriPositivePoints",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit c40a0134; kind definition; the module is byte-identical to commit c40a0134, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.generalLinearIwahoriPoints_relIndex",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit c40a0134; kind theorem; the module is byte-identical to commit c40a0134, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.generalLinearIwahoriPoints_relIndex_mul",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit c40a0134; kind theorem; the module is byte-identical to commit c40a0134, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.generalLinearIwahoriPoints_relIndex_two",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit c40a0134; kind theorem; the module is byte-identical to commit c40a0134, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.generalLinearIwahoriPositivePoints_relIndex",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit c40a0134; kind theorem; the module is byte-identical to commit c40a0134, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.positivePoints_relIndex_generalLinearIwahoriPositivePoints",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit c40a0134; kind theorem; the module is byte-identical to commit c40a0134, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.generalLinearIwahoriQuotientEquiv",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit c40a0134; kind definition; the module is byte-identical to commit c40a0134, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.generalLinearIwahoriPoints_lt_integralPoints",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit c40a0134; kind theorem; the module is byte-identical to commit c40a0134, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.generalLinearIwahoriPoints_of_le_one",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit c40a0134; kind theorem; the module is byte-identical to commit c40a0134, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.RamifiedQuadraticData",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 70eca2e4; kind inductive; the module is byte-identical to commit af5d652c, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.RamifiedQuadraticData.smooth",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 70eca2e4; kind theorem; the module is byte-identical to commit af5d652c, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.RamifiedQuadraticData.isAnisotropic",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 70eca2e4; kind theorem; the module is byte-identical to commit af5d652c, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.RamifiedQuadraticData.specialFibreSign",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 70eca2e4; kind definition; the module is byte-identical to commit af5d652c, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.RamifiedQuadraticData.index_ker_specialFibreSign",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 70eca2e4; kind theorem; the module is byte-identical to commit af5d652c, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.RamifiedQuadraticData.componentPoints",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 70eca2e4; kind definition; the module is byte-identical to commit af5d652c, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.RamifiedQuadraticData.relIndex_componentPoints",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 70eca2e4; kind theorem; the module is byte-identical to commit af5d652c, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.RamifiedQuadraticData.congruenceSubgroup_le_componentPoints",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 70eca2e4; kind theorem; the module is byte-identical to commit af5d652c, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.RamifiedQuadraticData.integralPoints_eq_top",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 70eca2e4; kind theorem; the module is byte-identical to commit af5d652c, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.RamifiedQuadraticData.index_componentPoints",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 70eca2e4; kind theorem; the module is byte-identical to commit af5d652c, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.RamifiedQuadraticData.nonempty_iff",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 70eca2e4; kind theorem; the module is byte-identical to commit af5d652c, its first publication."
        },
        {
          "declaration": "Langlands.GroupScheme.FiniteFreeAlgebraUnits.groupScheme",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 0b7bb3fd; kind definition; the module is byte-identical to commit 7f5b5f04, its first publication."
        },
        {
          "declaration": "Langlands.GroupScheme.FiniteFreeAlgebraUnits.smooth",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 0b7bb3fd; kind theorem; the module is byte-identical to commit 7f5b5f04, its first publication."
        },
        {
          "declaration": "Langlands.GroupScheme.FiniteFreeAlgebraUnits.pointsEquiv",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 0b7bb3fd; kind definition; the module is byte-identical to commit 7f5b5f04, its first publication."
        },
        {
          "declaration": "Langlands.GroupScheme.FiniteFreeAlgebraUnits.baseChangeIso",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 0b7bb3fd; kind definition; the module is byte-identical to commit 7f5b5f04, its first publication."
        },
        {
          "declaration": "Langlands.GroupScheme.FiniteFreeAlgebraUnits.generalLinearIso",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 0b7bb3fd; kind definition; the module is byte-identical to commit 7f5b5f04, its first publication."
        },
        {
          "declaration": "Langlands.GroupScheme.FiniteFreeAlgebraUnits.orderModel",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 0b7bb3fd; kind definition; the module is byte-identical to commit aeb3911c, its first publication."
        },
        {
          "declaration": "Langlands.GroupScheme.FiniteFreeAlgebraUnits.mem_orderModel_integralPoints",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 0b7bb3fd; kind theorem; the module is byte-identical to commit aeb3911c, its first publication."
        },
        {
          "declaration": "Langlands.GroupScheme.FiniteFreeAlgebraUnits.orderModelData",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 0b7bb3fd; kind definition; the module is byte-identical to commit aeb3911c, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.iwahoriOrder",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 0b7bb3fd; kind definition; the module is byte-identical to commit aeb3911c, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.iwahoriModel",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 0b7bb3fd; kind definition; the module is byte-identical to commit aeb3911c, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.iwahoriModel_isSmooth",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 0b7bb3fd; kind theorem; the module is byte-identical to commit aeb3911c, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.iwahoriModel_integralPoints",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 0b7bb3fd; kind theorem; the module is byte-identical to commit aeb3911c, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.iwahoriModelData",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 0b7bb3fd; kind definition; the module is byte-identical to commit aeb3911c, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.iwahoriModelData_neutralPoints",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 0b7bb3fd; kind theorem; the module is byte-identical to commit aeb3911c, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.iwahoriModelData_neutralPoints_lt",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 0b7bb3fd; kind theorem; the module is byte-identical to commit aeb3911c, its first publication."
        },
        {
          "declaration": "Langlands.GroupScheme.FiniteFreeAlgebraUnits.map",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 0b7bb3fd; kind definition; the module is byte-identical to commit 4abbe7aa, its first publication."
        },
        {
          "declaration": "Langlands.GroupScheme.FiniteFreeAlgebraUnits.isFppfQuotient_map_of_section",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 0b7bb3fd; kind theorem; the module is byte-identical to commit 4abbe7aa, its first publication."
        },
        {
          "declaration": "Langlands.GroupScheme.SectionQuotient.isFppfQuotient_of_section",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 0b7bb3fd; kind theorem; the module is byte-identical to commit 4abbe7aa, its first publication."
        },
        {
          "declaration": "Langlands.GroupScheme.FiniteFreeAlgebraUnits.UnipotentPart.groupScheme",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 0b7bb3fd; kind definition; the module is byte-identical to commit fab9caea, its first publication."
        },
        {
          "declaration": "Langlands.GroupScheme.FiniteFreeAlgebraUnits.UnipotentPart.kernelIso",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 0b7bb3fd; kind definition; the module is byte-identical to commit fab9caea, its first publication."
        },
        {
          "declaration": "Langlands.GroupScheme.FiniteFreeAlgebraUnits.UnipotentPart.isUnipotent",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 0b7bb3fd; kind theorem; the module is byte-identical to commit fab9caea, its first publication."
        },
        {
          "declaration": "Langlands.GroupScheme.FiniteFreeAlgebraUnits.UnipotentPart.isUnipotentRadical",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 0b7bb3fd; kind theorem; the module is byte-identical to commit fab9caea, its first publication."
        },
        {
          "declaration": "Langlands.GroupScheme.FiniteFreeAlgebraUnits.isTorus_pi",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 0b7bb3fd; kind theorem; the module is byte-identical to commit fab9caea, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.specialFibreIso",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 0b7bb3fd; kind definition; the module is byte-identical to commit 0b7bb3fd, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.specialRadical_isUnipotentRadical",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 0b7bb3fd; kind theorem; the module is byte-identical to commit 0b7bb3fd, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.iwahoriQuotientData",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 0b7bb3fd; kind definition; the module is byte-identical to commit 0b7bb3fd, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.iwahoriQuotientData_isReductiveQuotient",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 0b7bb3fd; kind theorem; the module is byte-identical to commit 0b7bb3fd, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.iwahoriQuotientData_positivePoints",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit 0b7bb3fd; kind theorem; the module is byte-identical to commit 0b7bb3fd, its first publication."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.diagTorusPointsEquiv",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit b3dcc8cc; kind definition; that commit first published the module."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.card_diagTorus_rationalPoints",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit b3dcc8cc; kind theorem; that commit first published the module."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.singletonLevi_parahoricReduction",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit b3dcc8cc; kind theorem; that commit first published the module."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.iwahoriDepthZeroQuotientEquiv",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit b3dcc8cc; kind definition; that commit first published the module."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.iwahoriQuotientData_ker_parahoricReduction",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit b3dcc8cc; kind theorem; that commit first published the module."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.iwahori_index_positivePoints_subgroupOf",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit b3dcc8cc; kind theorem; that commit first published the module."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.isOpen_generalLinearIwahoriPoints",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit b3dcc8cc; kind theorem; that commit first published the module."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.isCompact_generalLinearIwahoriPoints",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit b3dcc8cc; kind theorem; that commit first published the module."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.isOpen_generalLinearIwahoriPositivePoints",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit b3dcc8cc; kind theorem; that commit first published the module."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.isCompact_generalLinearIwahoriPositivePoints",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-15 at Library commit b3dcc8cc; kind theorem; that commit first published the module."
        },
        {
          "declaration": "Langlands.Geometry.Building.depthZeroConsumer",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Declaration inspection on 2026-11-27 at Library commit 2f86a99eb5616254ac5b9c399603c9bbbea15f7a. The theorem has universe parameter u and type DepthZeroConsumerStatement.{u}."
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
        "Recorded Lean scope: MoyPrasadFiltrationStatement (module Langlands.Geometry.Building.KPMoyPrasadFiltrationStatement) is the conjunction of MoyPrasadSeparatedStatement, MoyPrasadBoundedOpenStatement, MoyPrasadCovarianceStatement and MoyPrasadCommutatorStatement. Each quantifies over every nonarchimedean local field F of either characteristic in universe u, every G with [IsAffineHom G.X.hom], supplied P : ParahoricBuildingData G with P.SatisfiesApartmentAxioms (V 6 in the data, V 7 and AS 2–AS 5) and a supplied Zf : P.CentralizerFiltration: subgroups Z(F)_r of Z(F) for real r ≥ 0, decreasing and separated, with Z(F)_0 = Z(F)^0. The premise Zf.SatisfiesFiltrationAxioms requires the commutator clause of Definition 7.2.1 (with the Z-component of Definition 7.1.3), N(F)-stability, [Z(F)_r, Z(F)_s] ⊆ Z(F)_{r+s} and [Z(F)_r, U_{a,x,s}] ⊆ U_{a,x,r+s} U_{2a,x,r+s}. The last three are derived properties of the Section 9.8 filtration; for every supplied P satisfying the apartment axioms, the published proof centralizerFiltrationDoubleRootExistence (Lemma 9.8.1 row) provides a filtration with all four that is also open and double-root commutator friendly. P_{x,r} = Zf.moyPrasad x r, for x in the apartment A(S), is generated by the image of Z(F)_r and the blocks U_{a,x,r} U_{2a,x,r} (Definitions 13.2.1 and 7.3.3); at depth 0 it is the published parahoricAt. The targets are: the infimum over real r ≥ 0 of P_{x,r} is trivial; under the extra premise Zf.IsOpenFiltration (each Z(F)_r open in Z(F)), P_{x,r} is open and algebraically bounded in rationalPointTopology F G.X for every real r ≥ 0; parts (1) and (2) as uniqueness of g P_{x,r} g⁻¹ over all presentations g·x = y of a point y of the reduced building (IsMoyPrasadAt), which gives apartment independence, covariance and normality in the point stabilizer; and part (4) for all real r, s ≥ 0. The strict-depth groups P_{x,r+} are defined (moyPrasadPlus) but appear in no target. MoyPrasadProductStatement (module Langlands.Geometry.Building.KPMoyPrasadProductStatement) states part (3) with indivisible-root blocks under the same premises. For r > 0, a cocharacter ν with IsGenericCocharacter P.i ν, and injective lists aneg and apos whose ranges are RelativeRoot.indivisiblePositiveRoots P.i (-ν) and RelativeRoot.indivisiblePositiveRoots P.i ν, it asserts that Zf.orderedMoyPrasadProduct x r aneg apos is injective with range P_{x,r}. That map multiplies, in the listed orders, one element of each block U_{a,x,r} U_{2a,x,r} for aneg, then the image under j of an element of Z(F)_r, then one element of each block for apos. Its middle factor is the full Z(F)_r, not the Z♯_{x,r} of Proposition 7.3.12(5). MoyPrasadLeviStatement (module Langlands.Geometry.Building.KPMoyPrasadLeviStatement) is the conjunction of MoyPrasadIwahoriDecompositionStatement (part (5)) and MoyPrasadLeviIntersectionStatement (part (6)) under the same premises, for r > 0 and the standard parabolic subgroups containing S: a generic cocharacter ν and J ⊆ simpleRelativeRoots P.i ν give the Levi M_J, the radical N_J and the opposite radical N_J⁻ (standardLeviPoints, standardUnipotentPoints and standardOppositeUnipotentPoints in G(F)). Part (5) asserts that the ordered product (P_{x,r} ∩ N_J⁻(F)) × (P_{x,r} ∩ M_J(F)) × (P_{x,r} ∩ N_J(F)) → P_{x,r} is a homeomorphism (IsTopologicalIwahoriDecomposition) and, for every A and q : A → S with IsCompatibleStandardSplitComponent, WeakChamberContraction for the elements a of A(F) with |α(a)| ≤ 1 on the roots α of N_J (standardComponentNonnegativePart): a (P_{x,r} ∩ N_J(F)) a⁻¹ ⊆ P_{x,r} ∩ N_J(F) and a⁻¹ (P_{x,r} ∩ N_J⁻(F)) a ⊆ P_{x,r} ∩ N_J⁻(F). Part (6) asserts, for the closed Levi Standard.leviScheme, all apartment data DM of (M_J, S) and every point xM with IsLeviRestriction (the map π_S of Section 6.7), that the image of Zf.leviMoyPrasad (generated by the preimage of Z(F)_r and the blocks of DM at xM) is P_{x,r} ∩ M_J(F). Part (6) at r = 0 (Corollary 9.7.3), the groups P_{x,r+}, the building B(M) and the bijection (9.7.1) are not formalized. MoyPrasadDoubleRootStatement (module Langlands.Geometry.Building.KPMoyPrasadDoubleRootStatement) is the conjunction of MoyPrasadDoubleRootCovarianceStatement and MoyPrasadDoubleRootCommutatorStatement: the published covariance and commutator statements with the extra premise Zf.IsDoubleRootCommutatorFriendly. That predicate has the hypotheses of IsCommutatorFriendly together with u ∈ U_{2a}(F) or u' ∈ U_{-2a}(F), and it concludes that the Z-component lies in Z(F)_{2r}, where r = x_a(u) + x_{-a}(u') and IsCommutatorFriendly gives Z(F)_r. It is not a clause of Definition 7.2.1, and for a reduced root system it adds nothing. The source's Henselian discretely valued generality is not formalized; existence of the data is not asserted."
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
        "One statement per conjunct: MoyPrasadSeparatedStatement; MoyPrasadBoundedOpenStatement; MoyPrasadCovarianceStatement; MoyPrasadCommutatorStatement. The conjunction needs no further mathematics once the four are proved. Part (3) is MoyPrasadProductStatement. Parts (5) and (6) are MoyPrasadLeviStatement. The double-root statements are MoyPrasadDoubleRootCovarianceStatement and MoyPrasadDoubleRootCommutatorStatement; MoyPrasadCovarianceStatement and MoyPrasadCommutatorStatement are kept as stated. The published iInf_moyPrasad_eq_bot, orderedMoyPrasadProduct_injective and range_orderedMoyPrasadProduct_eq (Library commit cd03c104) take only the apartment axioms and IsCommutatorFriendly. The published isMoyPrasadAt_unique_of_double_opposite_bound (module Langlands.Geometry.Building.MoyPrasadCovarianceReduction, Library commit 297a8ef0) derives the conclusion of MoyPrasadCovarianceStatement from the apartment axioms, SatisfiesFiltrationAxioms and one further hypothesis: conjugation of U_{-2a,x,r} by U_{a,x,0} stays in P_{x,r}. conjugate_double_opposite_mem_moyPrasad_of_central_bound (module Langlands.Geometry.Building.MoyPrasadMixedConjugation, same commit) reduces that hypothesis to a bound on the Z-component, the bound that IsDoubleRootCommutatorFriendly supplies. Every one of these statements except MoyPrasadCovarianceStatement and MoyPrasadCommutatorStatement is proved (the two entries on proved conjuncts and proved parts below).",
        "Proved conjuncts (13 November 2026): moyPrasadSeparated (module KPMoyPrasadSeparatedProof) proves MoyPrasadSeparatedStatement by applying iInf_moyPrasad_eq_bot to the first clause IsCommutatorFriendly of SatisfiesFiltrationAxioms; moyPrasadBoundedOpen (module MoyPrasadBoundedOpenProof) proves MoyPrasadBoundedOpenStatement from isOpen_moyPrasad (V 7 and IsOpenFiltration, through the proved Corollary 8.2.6) and the published boundedness lemma of MoyPrasadTopology. Both are present in Library commit 17dd94ea3f677b20fb5ab95b285cbc3fd7cde03e; Lean inspections at Library commit 8ff9abe9 report kind theorem and only propext, Classical.choice and Quot.sound. Both modules are first in Library commit 17dd94ea.",
        "Proved parts (13 November 2026): the theorem moyPrasadProduct (module KPMoyPrasadProductProof, first in Library commit cfedefb680f317b0ea5d351023e1c9dd886b2547) proves MoyPrasadProductStatement by combining orderedMoyPrasadProduct_injective and range_orderedMoyPrasadProduct_eq; of SatisfiesFiltrationAxioms it uses only the first clause IsCommutatorFriendly. The theorem moyPrasadLevi (module KPMoyPrasadLeviProof, first in Library commit cc5aa77fa8dbdc6e723091c7b710ab0d81162c4e) proves MoyPrasadLeviStatement by pairing the theorems moyPrasadIwahoriDecomposition and moyPrasadLeviIntersection of the same module. It takes the ordered covering of P_{x,r} from range_orderedMoyPrasadProduct_eq, not from MoyPrasadProductStatement, and the homeomorphism from the open cell on rational points. The theorem moyPrasadDoubleRootCovariance (module KPMoyPrasadDoubleRootCovarianceProof, first in Library commit cfedefb680f317b0ea5d351023e1c9dd886b2547) proves MoyPrasadDoubleRootCovarianceStatement by applying isMoyPrasadAt_unique_of_doubleRootCommutatorFriendly (module MoyPrasadDoubleRootConjugation). The theorem moyPrasadDoubleRootCommutator (module KPMoyPrasadDoubleRootCommutatorProof, same commit) proves MoyPrasadDoubleRootCommutatorStatement by applying commutator_moyPrasad_le from the module MoyPrasadCommutatorGenerators of the same unit. No published theorem has MoyPrasadDoubleRootStatement, the conjunction of the two double-root statements, as its type; it follows from the two proofs by pairing. Every one of these theorems keeps the supplied P and Zf and their premises, so the row is conditional: the building data and the Section 9.8 filtration are not constructed, and CentralizerFiltrationDoubleRootExistenceStatement (Lemma 9.8.1 row) is not proved. MoyPrasadCovarianceStatement, MoyPrasadCommutatorStatement and MoyPrasadFiltrationStatement, the conjunction of the four original statements, are not proved; the next entry refutes them on paper. Lean inspections of the four theorems are listed in the axiom reports. Follow-up (thirty-third update, Library commit b369a8f2): the theorem centralizerFiltrationDoubleRootExistence (Lemma 9.8.1 row) proves CentralizerFiltrationDoubleRootExistenceStatement. So for every supplied P satisfying the apartment axioms some filtration Zf satisfies SatisfiesFiltrationAxioms, IsOpenFiltration and IsDoubleRootCommutatorFriendly, which are all the premises on the filtration of the six published proofs of this row: moyPrasadSeparated, moyPrasadBoundedOpen (previous entry), moyPrasadProduct, moyPrasadLevi, moyPrasadDoubleRootCovariance and moyPrasadDoubleRootCommutator. A separate Lean check showed that all six, including both conjuncts of moyPrasadLevi, apply to the filtration provided by centralizerFiltrationDoubleRootExistence for every such P (Library commit fcb85a7e, only propext, Classical.choice and Quot.sound). The supplied filtration of these proofs can therefore be discharged, but the building data P are still supplied, so the row stays conditional. MoyPrasadCovarianceStatement, MoyPrasadCommutatorStatement and MoyPrasadFiltrationStatement remain unproved. The module KPDoubleRootFiltrationExistence is byte-identical between commit 9e39a73d and Library commit b369a8f2, and the six proof modules between their first commits and Library commit b369a8f2.",
        "Supplied-filtration counterexample (an unformalized paper argument, found in an attempt to prove MoyPrasadCommutatorStatement): take ramified quasi-split SU(3) over Q_2 split by E = Q_2(√2), assume its actual building data realized as P with P.SatisfiesApartmentAxioms, and let Z' be the smallest centralizer filtration (decreasing, separated, Z'_0 = Z(F)^0) satisfying the four clauses of SatisfiesFiltrationAxioms. Then u(0,√2) ∈ U_{2a,x,1/2} and u⁻(2,−2) ∈ U_{−a,x,1/2} have a commutator whose Z-component t(1−2√2) is not in Z'_1, refuting MoyPrasadCommutatorStatement. With u'' = u⁻(√2,1) ∈ U_{−a,x,0}, which fixes x, the conjugate u''⁻¹ u(0,√2) u'' has Z-component t(1+√2) ∉ Z'_{1/2}, so it is not in P'_{x,1/2}; then P'_{x,1/2} and u'' P'_{x,1/2} u''⁻¹ are distinct subgroups that are both Moy–Prasad at x of depth 1/2, refuting MoyPrasadCovarianceStatement and hence MoyPrasadFiltrationStatement. The same pair violates the hypothesis hmixed of sharpFixer_le_normalizer_moyPrasad_of_double_opposite_bound (module MoyPrasadCovarianceReduction) at the root −a with r = 1/2. Z' violates IsDoubleRootCommutatorFriendly, so MoyPrasadDoubleRootCovarianceStatement and MoyPrasadDoubleRootCommutatorStatement are unaffected, and KP's chosen filtration is not refuted (for odd p the forced filtration agrees with the actual one). The argument is the note notes/bruhat-tits/moy-prasad-supplied-filtration-counterexample.md, present in Library commit 4b619cdd61c537ff5ee2587fda415e0adb66e5ef. It is an unformalized paper argument; no Lean declaration refutes either statement. The Markdown of KPMoyPrasadFiltrationStatement, KPMoyPrasadDoubleRootStatement, CentralizerFiltrationExistenceStatement and KPMoyPrasadFiltration records this status (a Markdown-only change, present in Library commit cc5aa77fa8dbdc6e723091c7b710ab0d81162c4e; the Lean files are unchanged). Consequently MoyPrasadCovarianceStatement and MoyPrasadCommutatorStatement have no proofs, the two refuted statements stay in the Library as recorded targets, and the double-root variants (MoyPrasadDoubleRootCovarianceStatement and MoyPrasadDoubleRootCommutatorStatement) carry the covariance and commutator content."
      ],
      "consumer_or_regression": "Regression: a nonsplit group with a multipliable root must detect overlapping a/2a scalar factors and test the separately proved block formulation. Check finite r/r+ openness separately from the non-open infinite term for G_m(Q_2), point variation inside a facet, full-stabilizer normality and the actual Levi embedding. Boundedness alone is not compactness over general Henselian k. For the part (3) central factor: for G = G_m there are no roots, so G(k)♯_{x,r} = Z♯_{x,r} = {1}, while Z(k)_r = P_{x,r} is a nontrivial congruence subgroup; the middle factor must be the full filtration. Consumer: the positive-depth Iwahori factorization behind the special-compact properties on valid KP data; the published regrouping in Langlands.BruhatTits.SpecialCompact.MoyPrasadParabolicProduct takes ordered-root covering as a hypothesis. Parts (5) and (6): consumer is the positive-depth Iwahori decomposition (HasIwahoriIntersectionDecomposition and WeakChamberContraction) behind the special-compact properties on valid KP data. Double-root regression: for the unramified quasi-split SU_3 (relative root system BC_1) and u ∈ U_{2a}(k), the Z-component of (u, u') has depth 2(φ_a(u) + φ_{-a}(u')), twice the bound of Definition 7.2.1; for a reduced root system the premise IsDoubleRootCommutatorFriendly is implied by IsCommutatorFriendly.",
      "formal_status": "conditional",
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
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-11 at Library commit 389dbc16; kind definition; statement_returns_prop true; the pair is byte-identical to commit 642008d6."
        },
        {
          "declaration": "Langlands.Geometry.Building.MoyPrasadSeparatedStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-11 at Library commit 389dbc16; kind definition; statement_returns_prop true; the pair is byte-identical to commit 642008d6."
        },
        {
          "declaration": "Langlands.Geometry.Building.MoyPrasadBoundedOpenStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-11 at Library commit 389dbc16; kind definition; statement_returns_prop true; the pair is byte-identical to commit 642008d6."
        },
        {
          "declaration": "Langlands.Geometry.Building.MoyPrasadCovarianceStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-11 at Library commit 389dbc16; kind definition; statement_returns_prop true; the pair is byte-identical to commit 642008d6."
        },
        {
          "declaration": "Langlands.Geometry.Building.MoyPrasadCommutatorStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-11 at Library commit 389dbc16; kind definition; statement_returns_prop true; the pair is byte-identical to commit 642008d6."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.CentralizerFiltration.moyPrasad",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-11 at Library commit 389dbc16; a definition; the pair is byte-identical to commit 642008d6."
        },
        {
          "declaration": "Langlands.Geometry.Building.MoyPrasadProductStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-11 at Library commit 8964b41f; kind definition; statement_returns_prop true; the module is byte-identical to commit 63d9b857."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.CentralizerFiltration.orderedMoyPrasadProduct",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-11 at Library commit 8964b41f; kind definition; statement_returns_prop false; the module is byte-identical to commit 63d9b857."
        },
        {
          "declaration": "Langlands.Geometry.Building.MoyPrasadLeviStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-12 at Library commit 4ed6d979; kind definition; statement_returns_prop true; the module is byte-identical to commit 6bff2655."
        },
        {
          "declaration": "Langlands.Geometry.Building.MoyPrasadIwahoriDecompositionStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-12 at Library commit 14c08c22; kind definition; statement_returns_prop true; the module is byte-identical to commit 6bff2655."
        },
        {
          "declaration": "Langlands.Geometry.Building.MoyPrasadLeviIntersectionStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-12 at Library commit 14c08c22; kind definition; statement_returns_prop true; the module is byte-identical to commit 6bff2655."
        },
        {
          "declaration": "Langlands.Geometry.Building.MoyPrasadDoubleRootStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-12 at Library commit 16c60abd; kind definition; statement_returns_prop true; the module is byte-identical to commit 297a8ef0."
        },
        {
          "declaration": "Langlands.Geometry.Building.MoyPrasadDoubleRootCovarianceStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-12 at Library commit 16c60abd; kind definition; statement_returns_prop true; the module is byte-identical to commit 297a8ef0."
        },
        {
          "declaration": "Langlands.Geometry.Building.MoyPrasadDoubleRootCommutatorStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-12 at Library commit 16c60abd; kind definition; statement_returns_prop true; the module is byte-identical to commit 297a8ef0."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.CentralizerFiltration.IsDoubleRootCommutatorFriendly",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-12 at Library commit 16c60abd; kind definition; statement_returns_prop true (a Prop-valued predicate); the module is byte-identical to commit 297a8ef0."
        },
        {
          "declaration": "Langlands.Geometry.Building.moyPrasadSeparated",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit 8ff9abe9; a theorem proving MoyPrasadSeparatedStatement. It first appeared in Library commit 17dd94ea."
        },
        {
          "declaration": "Langlands.Geometry.Building.moyPrasadBoundedOpen",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit 8ff9abe9; a theorem proving MoyPrasadBoundedOpenStatement. It first appeared in Library commit 17dd94ea."
        },
        {
          "declaration": "Langlands.Geometry.Building.moyPrasadProduct",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit 0f84a0d8; kind theorem, proving MoyPrasadProductStatement; the module is byte-identical to commit cfedefb6."
        },
        {
          "declaration": "Langlands.Geometry.Building.moyPrasadLevi",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit 0f84a0d8; kind theorem, proving MoyPrasadLeviStatement; the module is byte-identical to commit cc5aa77f."
        },
        {
          "declaration": "Langlands.Geometry.Building.moyPrasadDoubleRootCovariance",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit 0f84a0d8; kind theorem, proving MoyPrasadDoubleRootCovarianceStatement; the module is byte-identical to commit cfedefb6."
        },
        {
          "declaration": "Langlands.Geometry.Building.moyPrasadDoubleRootCommutator",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit 0f84a0d8; kind theorem, proving MoyPrasadDoubleRootCommutatorStatement; the module is byte-identical to commit cfedefb6."
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
        "The smooth congruence models and their morphisms come from Section 8.5, with the actual Chapter 9 descent over o. Parahorics, full stabilizers, the whole special fibre H_x and its maximal reductive quotient Gred_x retain distinct meanings. Chapter 8 models over O alone do not supply the descended construction.",
        "Recorded Lean scope (the lattice assertion of the first sentence only, for an arbitrary supplied smooth integral model in place of G_{x,r}): the module Langlands.GroupScheme.IntegralModel.LieLattice, first published in Library commit c9fdbede045511865f0ea27259a1e1a35f442905, works with a commutative domain R with fraction field K, an affine group scheme G over Spec K and an integral model M : IntegralModel R K G. Langlands.GroupScheme.GenericLie R G is the Lie algebra Lie(G) of G over K, the Library's dual-number identity kernel, viewed as an R-module. Langlands.GroupScheme.IntegralModel.lieMap is the R-linear map from the Lie algebra of the model M.group to GenericLie R G given by change of coefficients from R to K followed by the identification of the generic fibre with G; Langlands.GroupScheme.IntegralModel.lieMap_injective proves that it is injective for every model, and Langlands.GroupScheme.IntegralModel.lieLattice is its range. Langlands.GroupScheme.IntegralModel.lieLattice_isLattice proves that for smooth M this range is a lattice in the sense of Mathlib's Submodule.IsLattice K: a finitely generated R-submodule that spans Lie(G) over K, matching KP's definition of an o-lattice (printed p.515 / PDF p.546). Langlands.GroupScheme.IntegralModel.Hom.map_lieLattice_le proves that a model homomorphism over a K-homomorphism f maps the Lie lattice of its source into that of its target under the Lie map of f. With R = o, K = k and M a smooth model of G this is the first assertion, that the Lie algebra of the model, identified with its image in g(k) as in KP Remark 2.10.8 (printed p.123 / PDF p.154), is an o-lattice in g(k); no Lean declaration constructs the congruence model G_{x,r}. The row's conditional status refers to lieLattice_isLattice, proved for every supplied smooth integral model, and to the results on supplied lattices recorded in the next entry.",
        "Recorded Lean scope (the filtration, the extension to real depths and the dual lattices, for the supplied lattices g_{x,r}, r >= 0, of the Section 13.3.3 row): in the module Langlands.Geometry.Building.KPLieFiltration, first published in Library commit fd643ecec6997ef17c8356ddbc924138631307d9, Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.lieFiltration x r is g_{x,r} for supplied L : P.LieFiltrationData, x : P.Apartment and r : NNReal (see that row); lieFiltration_antitone proves that it is decreasing in r, and lieFiltrationPlus x r is g_{x,r+}, the supremum of the g_{x,s} over s > r. In the module Langlands.Geometry.Building.KPLieFiltrationDual, first published in Library commit b86269dd36757fdbea2e51976499d645ca61a625, Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.IsPeriodic L is the predicate g_{x,r+1} = m • g_{x,r} for all x and all r >= 0, the case n = 1 of the identity that KP take from Proposition 8.5.16; it is a hypothesis here, not a theorem. Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.lieFiltrationReal x r, for real r, is the submodule of the X with a • X in g_{x,r+n} for every a in m^n, where n = ⌈-r⌉₊; this is KP's m^{-n} g_{x,r+n} written without a uniformizer. lieFiltrationReal_coe proves that it equals g_{x,r} for r >= 0, and lieFiltrationReal_antitone proves, under IsPeriodic, that it is decreasing in r; lieFiltrationPlusReal x r is the supremum over s > r, and mem_lieFiltrationPlusReal proves, under IsPeriodic, that it is KP's union of the lattices at s > r (without a hypothesis that makes the real family decreasing, the supremum can be larger than the union). Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.dualLieFiltration x r is g^*_{x,r}, the 𝒪[F]-submodule of Module.Dual F (GenericLie 𝒪[F] G) of the X with X(Y) in m for every Y in lieFiltrationPlusReal x (-r); mem_dualLieFiltration states this membership condition with the supremum unfolded (for every s > -r and every Y in the real-depth lattice at s, X(Y) is in m), keeping m, the minus sign and the strict plus, and dualLieFiltration_antitone proves g^*_{x,r} decreasing in r; dualLieFiltrationPlus x r is the supremum of the g^*_{x,s} over s > r, and mem_dualLieFiltrationPlus proves with no hypothesis that it is the union. The supplied lattices are arbitrary 𝒪[F]-submodules: their lattice property, openness and separatedness, the identity m^n g_{x,r} = g_{x,r+n} for negative r, the independence of the extension from the choice of n, the identification of lieFiltrationPlus (r >= 0) with a union, and the identification of lieFiltrationPlusReal with the union without IsPeriodic are not formalized.",
        "Recorded Lean scope (derived residue pairing, KPLieGradedPairing): for the supplied L : P.LieFiltrationData, apartment point x and real r, IsPeriodic is used to make evaluation of X in g^*_{x,r} on Y in g_{x,-r} integral. Reduction of X(Y) gives an 𝒪[F]-bilinear pairing into the residue field. gradedLieDualPairing quotients the Lie input by g_{x,(-r)+}; g^*_{x,r+} pairs to zero. With Submodule.IsLattice F on the lattice at -r, gradedLieDualPairing_surjective gives all 𝒪[F]-linear forms of its graded piece into the residue field, and ker_gradedLieDualPairing_flip is trivial. With IsLeftContinuousAt x (-r) instead, ker_gradedLieDualPairing identifies the left kernel with the comap of g^*_{x,r+}. The two hypotheses concern different sides. This module declares no perfect-pairing identification of full lattices; the graded linear equivalence obtained from these results is recorded in the next item.",
        "Recorded Lean scope (derived residue duality, KPLieGradedResidue): dualGradedLieProjection maps g^*_{x,r} onto dualGradedLie x r, and ker_dualGradedLieProjection identifies its kernel with the comap of g^*_{x,r+}. Under IsPeriodic, gradedLieResidueModule and dualGradedLieResidueModule make the Lie and dual grades modules over the residue field 𝓀[F], through which the 𝒪[F]-action factors. finite_gradedLie proves that the Lie grade at r is finite when g_{x,r} is finitely generated over 𝒪[F]. Assume IsPeriodic, IsLeftContinuousAt x (-r) and Submodule.IsLattice F for g_{x,-r}. Then dualGradedLieLinearEquiv is an 𝒪[F]-linear equivalence from g^*_{x,r}/g^*_{x,r+} to the 𝒪[F]-linear forms on g_{x,-r}/g_{x,(-r)+} with values in the residue field. dualGradedLieResidueEquiv is the same map as an 𝓀[F]-linear equivalence onto the residue-field dual, and finite_dualGradedLie proves that the dual grade is finite. All of this concerns the supplied lattices.",
        "Recorded Lean scope (derived jump finiteness, KPLieJumpDepths): lieJumpDepths x is the set of real r with g_{x,r+} < g_{x,r}. Assume IsPeriodic and that g_{x,0} is finitely generated over 𝒪[F]. Then finite_lieFiltrationReal_image_Icc shows that the real-depth lattices at x take finitely many values on each closed bounded interval, and finite_lieJumpDepths_inter_Icc gives finitely many jumps there. For a finite set X of apartment points with this finite generation at each member, isClosed_and_isDiscrete_biUnion_lieJumpDepths proves that the union of their jump sets is closed and discrete in ℝ. Rationality of jumps, the set of all optimal points and the building-wide set O are not involved.",
        "Recorded Lean scope (derived left continuity, KPLieFiltrationLeftContinuity): IsCentralizerLieLeftContinuous assumes a left interval of constancy for z_r at each positive nonnegative-real endpoint. Under this premise, IsPeriodic and RelativeRoot.HasOppositeFactorPairs P.i, isLeftContinuousAt_of_oppositePairs proves IsLeftContinuousAt at all real depths in the supplied apartment. The left-interval inclusion is equality by antitonicity. None of the three premises is discharged for constructed descended Lie models here."
      ],
      "conclusion": "For r>=0, g_{x,r}=Lie(G_{x,r}) is an o-lattice in g(k). The identity g_{x,r+n}=m^n g_{x,r} for nonnegative integers n extends the definition consistently to every real depth. The resulting open additive subgroups form a separated descending filtration, with g_{x,r+}=union_{s>r} g_{x,s}. The dual lattice is exactly g^*_{x,r}={X in g^* : X(Y) in m for every Y in g_{x,(-r)+}}. The maximal ideal m, the minus sign and the strict plus in this annihilator convention are retained.",
      "lean_declarations": [
        "Langlands.GroupScheme.GenericLie",
        "Langlands.GroupScheme.IntegralModel.lieMap",
        "Langlands.GroupScheme.IntegralModel.lieMap_injective",
        "Langlands.GroupScheme.IntegralModel.lieLattice",
        "Langlands.GroupScheme.IntegralModel.lieLattice_isLattice",
        "Langlands.GroupScheme.IntegralModel.Hom.map_lieLattice_le",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.lieFiltration",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.lieFiltration_antitone",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.lieFiltrationPlus",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.IsPeriodic",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.lieFiltrationReal",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.lieFiltrationReal_coe",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.lieFiltrationReal_antitone",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.lieFiltrationPlusReal",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.mem_lieFiltrationPlusReal",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.dualLieFiltration",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.mem_dualLieFiltration",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.dualLieFiltration_antitone",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.dualLieFiltrationPlus",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.mem_dualLieFiltrationPlus",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.gradedLieDualPairing",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.gradedLieDualPairing_surjective",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.ker_gradedLieDualPairing_flip",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.ker_gradedLieDualPairing",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.IsCentralizerLieLeftContinuous",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.isLeftContinuousAt_of_oppositePairs",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.dualGradedLieProjection",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.ker_dualGradedLieProjection",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.gradedLieResidueModule",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.finite_gradedLie",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.dualGradedLieResidueModule",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.dualGradedLieLinearEquiv",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.dualGradedLieResidueEquiv",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.finite_dualGradedLie",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.finite_lieFiltrationReal_image_Icc",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.lieJumpDepths",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.finite_lieJumpDepths_inter_Icc",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.isClosed_and_isDiscrete_biUnion_lieJumpDepths"
      ],
      "modules": [
        "Langlands.GroupScheme.IntegralModel.LieLattice",
        "Langlands.Geometry.Building.KPLieFiltration",
        "Langlands.Geometry.Building.KPLieFiltrationDual",
        "Langlands.Geometry.Building.KPLieGradedPairing",
        "Langlands.Geometry.Building.KPLieFiltrationLeftContinuity",
        "Langlands.Geometry.Building.KPLieGradedResidue",
        "Langlands.Geometry.Building.KPLieJumpDepths"
      ],
      "dependencies": [
        "Section 8.5 constructs the actual constant-concave-function models; Proposition 8.5.16 proves their Lie-lattice periodicity",
        "The smooth congruence models and their morphisms come from Section 8.5, with the actual Chapter 9 descent over o. Parahorics, full stabilizers, the whole special fibre H_x and its maximal reductive quotient Gred_x retain distinct meanings. Chapter 8 models over O alone do not supply the descended construction.",
        "Section 1.6 supplies the real-depth-plus convention; well-defined extension to negative depths is a proof obligation, not a separately assumed lattice family",
        "Recorded Lean construction: the proofs in the module LieLattice use Lie.affineMap_jointly_injective for the injectivity of lieMap, Lie.finite_lieKernel_of_smooth for finite generation, and the scalar-extension isomorphism of Lie algebras of smooth models (Lie.smoothKernelScalarExtension, packaged as IntegralModel.lieBaseChangeEquiv) for the K-span.",
        "Recorded Lean construction (module KPLieFiltrationDual): lieFiltrationReal is an infimum of comaps of g_{x,r+n} under multiplication by the elements of m^n; lieFiltrationReal_antitone uses smul_lieFiltration_le, m^k • g_{x,t} ≤ g_{x,t+k} under IsPeriodic, proved by induction on k with Submodule.mul_smul; dualLieFiltration has as carrier the X such that g_{x,(-r)+} lies in the comap under X of m, viewed as an 𝒪[F]-submodule of F (dualPairingSubmodule).",
        "Recorded Lean proof: the shift by one and the maximal-ideal-valued dual test make evaluation integral by cancellation of a uniformizer. Lifting through residue reduction and extending an integral lattice basis over F gives surjectivity. Left continuity gives a shallower strict Lie lattice contained in g_{x,-r}, yielding the left-kernel comparison.",
        "Recorded Lean proof: bounded finiteness of root evaluations under opposite factor pairs gives a gap immediately below the cutoff; combine it with the centralizer gap and use periodicity at the change of the natural-ceiling shift to propagate left continuity.",
        "Recorded Lean proof (residue duality): periodicity makes the maximal ideal kill both grades, so Module.IsTorsionBySet.module gives the residue structures. The equivalence is LinearEquiv.ofBijective applied to the pairing of chosen representatives. Injectivity comes from the published kernel description under left continuity and surjectivity from the published surjectivity under the lattice premise. Scalars extend along the surjection of 𝒪[F] onto the residue field.",
        "Recorded Lean proof (jump finiteness): with A = g_{x,0}, the shifted nonnegative lattices over a bounded interval lie between 𝔪^N A and A. Since A/𝔪^N A is finite over the finite ring 𝒪[F]/𝔪^N, only finitely many intermediate submodules occur. A jump at r < s forces g_{x,s} < g_{x,r}, so jumps inject into lattice values.",
        "Open obligations: construct the descended congruence models G_{x,r} of Section 8.5 and Chapter 9; identify their Lie lattices with the supplied span; prove their lattice property, openness, separatedness, Proposition 8.5.16 periodicity and the consistency of the negative-depth extension with all shifts. The derived residue pairing, graded residue duality, jump finiteness and left continuity do not supply these hypotheses or a full-lattice duality theorem.",
        "Release 1 constructions, the corrected Theorem 9.2.7 certificate and the inflation/compact-induction consumer remain prerequisites for positive-depth implementation. A source row supplies no release or formal acceptance."
      ],
      "consumer_or_regression": "Check positive and negative integer shifts and the exact dual annihilator pairing in equal and mixed characteristic. The general lattice construction requires no quasi-splitness of G.",
      "formal_status": "conditional",
      "publication_commits": [
        "c9fdbede045511865f0ea27259a1e1a35f442905",
        "fd643ecec6997ef17c8356ddbc924138631307d9",
        "b86269dd36757fdbea2e51976499d645ca61a625",
        "6e9e589baa721ce995563f73f648b6f4e45718a1",
        "2d12bd934a2a0da7808014bfe52c6d67fde3eb62"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.GroupScheme.GenericLie",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit 8f4a33d7; kind definition; the module is byte-identical to commit c9fdbede, its first publication."
        },
        {
          "declaration": "Langlands.GroupScheme.IntegralModel.lieMap",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit 8f4a33d7; kind definition; the module is byte-identical to commit c9fdbede, its first publication."
        },
        {
          "declaration": "Langlands.GroupScheme.IntegralModel.lieMap_injective",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit fcb85a7e; kind theorem; the module is byte-identical to commit c9fdbede, its first publication."
        },
        {
          "declaration": "Langlands.GroupScheme.IntegralModel.lieLattice",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit fcb85a7e; kind definition; the module is byte-identical to commit c9fdbede, its first publication."
        },
        {
          "declaration": "Langlands.GroupScheme.IntegralModel.lieLattice_isLattice",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit fcb85a7e; kind theorem; the module is byte-identical to commit c9fdbede, its first publication."
        },
        {
          "declaration": "Langlands.GroupScheme.IntegralModel.Hom.map_lieLattice_le",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit fcb85a7e; kind theorem; the module is byte-identical to commit c9fdbede, its first publication."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.lieFiltration",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit fd643ece; kind definition; that commit first published the module."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.lieFiltration_antitone",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit fd643ece; kind theorem; that commit first published the module."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.lieFiltrationPlus",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit fd643ece; kind definition; that commit first published the module."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.IsPeriodic",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-18 at Library commit ba9d1e9a; kind definition; statement_returns_prop true; the module is byte-identical to commit b86269dd, its first publication."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.lieFiltrationReal",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-18 at Library commit ba9d1e9a; kind definition; the module is byte-identical to commit b86269dd, its first publication."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.lieFiltrationReal_coe",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-18 at Library commit ba9d1e9a; kind theorem; the module is byte-identical to commit b86269dd, its first publication."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.lieFiltrationReal_antitone",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-18 at Library commit ba9d1e9a; kind theorem; the module is byte-identical to commit b86269dd, its first publication."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.lieFiltrationPlusReal",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-18 at Library commit ba9d1e9a; kind definition; the module is byte-identical to commit b86269dd, its first publication."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.mem_lieFiltrationPlusReal",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-18 at Library commit ba9d1e9a; kind theorem; the module is byte-identical to commit b86269dd, its first publication."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.dualLieFiltration",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-18 at Library commit ba9d1e9a; kind definition; the module is byte-identical to commit b86269dd, its first publication."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.mem_dualLieFiltration",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-18 at Library commit ba9d1e9a; kind theorem; the module is byte-identical to commit b86269dd, its first publication."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.dualLieFiltration_antitone",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-18 at Library commit ba9d1e9a; kind theorem; the module is byte-identical to commit b86269dd, its first publication."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.dualLieFiltrationPlus",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-18 at Library commit ba9d1e9a; kind definition; the module is byte-identical to commit b86269dd, its first publication."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.mem_dualLieFiltrationPlus",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-18 at Library commit ba9d1e9a; kind theorem; the module is byte-identical to commit b86269dd, its first publication."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.gradedLieDualPairing",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection; kind definition; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 6e9e589b."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.gradedLieDualPairing_surjective",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection; kind theorem; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 6e9e589b."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.ker_gradedLieDualPairing_flip",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection; kind theorem; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 6e9e589b."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.ker_gradedLieDualPairing",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection; kind theorem; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 6e9e589b."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.IsCentralizerLieLeftContinuous",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection; kind definition; statement_returns_prop true; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 6e9e589b."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.isLeftContinuousAt_of_oppositePairs",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection; kind theorem; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 6e9e589b."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.dualGradedLieProjection",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful #print axioms check; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 2d12bd93."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.ker_dualGradedLieProjection",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful #print axioms check; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 2d12bd93."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.gradedLieResidueModule",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful #print axioms check; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 2d12bd93."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.finite_gradedLie",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful #print axioms check; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 2d12bd93."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.dualGradedLieResidueModule",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful #print axioms check; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 2d12bd93."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.dualGradedLieLinearEquiv",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful #print axioms check; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 2d12bd93."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.dualGradedLieResidueEquiv",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection; kind definition; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 2d12bd93."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.finite_dualGradedLie",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful #print axioms check; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 2d12bd93."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.finite_lieFiltrationReal_image_Icc",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful #print axioms check; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 2d12bd93."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.lieJumpDepths",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection; kind definition; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 2d12bd93."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.finite_lieJumpDepths_inter_Icc",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful #print axioms check; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 2d12bd93."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.isClosed_and_isDiscrete_biUnion_lieJumpDepths",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection; kind theorem; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 2d12bd93."
        }
      ],
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
        "Gred_x is the maximal reductive quotient of H_x, the special fibre of the connected parahoric model. The Lie lattices and their 0+ term are the constructions of 13.3.1.",
        "Recorded Lean scope (the identification for supplied integral-model and reductive-quotient data, with g_{x,0+} defined intrinsically and identified with the Lie lattice of a supplied model only under hypotheses): the module Langlands.BruhatTits.IntegralModels.ReductiveQuotientLie, first published in Library commit fd643ecec6997ef17c8356ddbc924138631307d9, and its companion module Langlands.GroupScheme.IntegralModel.LieLatticeReduction (same commit) work with a local domain R with fraction field K, maximal ideal m and residue field f, a group scheme G over Spec K, supplied D : RelativeComponentModelData R K G, whose neutral model D.neutral is smooth with connected fibres and plays the role of G_{x,0}, and supplied Q : SpecialFibreQuotientData D with Q.IsReductiveQuotient: a closed subgroup R_u, the unipotent radical of the special fibre H of D.neutral, and an fppf quotient H → Gred by its image, with Gred connected reductive. Langlands.GroupScheme.IntegralModel.lieReduction is the R-linear reduction map from the Lie algebra of a model to that of its special fibre, and Langlands.GroupScheme.IntegralModel.ker_lieReduction proves that its kernel is m • Lie(M) for a smooth model M. Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.specialFibreLieQuotientEquiv is the f-linear isomorphism Lie(H)/Lie(R_u) ≃ Lie(Gred) induced by the differential of the projection, the case of KP Section 2.4(a)(3) for the radical inclusion. Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.positiveLieLattice is the R-submodule g_0+ of GenericLie R G formed by the images under the Lie map of the X in Lie(D.neutral) whose reduction lies in Lie(R_u); positiveLieLattice_le and smul_lieLattice_le_positiveLieLattice prove m • g_0 ≤ g_0+ ≤ g_0 for g_0 = D.neutral.lieLattice, and Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.reductiveQuotientLieEquiv is an R-linear isomorphism g_0/g_0+ ≃ Lie(Gred), for all such D and Q. For a supplied smooth model N with a model homomorphism to D.neutral over the identity of G whose special-fibre map factors through the radical inclusion by a smooth morphism, and with m • g_0 ≤ N.lieLattice, Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.positiveLieLattice_eq proves g_0+ = N.lieLattice, and Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.lieLatticeQuotientEquiv is the R-linear isomorphism g_0/N.lieLattice ≃ Lie(Gred). These hypotheses stand for KP's map G_{x,0+} → G_{x,0}, the identification of Section 13.2.6, the smooth kernel of Proposition 8.5.18 and the inclusion m g_{x,0} ⊂ g_{x,0+}. All isomorphisms are of modules; the Lie bracket and the f-module structure on g_0/g_0+ are not treated. No Lean declaration constructs G_{x,0} or G_{x,0+} from the building. The row's conditional status refers to reductiveQuotientLieEquiv and positiveLieLattice_eq, proved for all supplied data satisfying their hypotheses."
      ],
      "conclusion": "There is an identification of f-Lie algebras Lie(Gred_x)=cok(g_{x,0+} tensor_o f to g_{x,0} tensor_o f)=g_{x,0}/g_{x,0+}. It uses m g_{x,0} contained in g_{x,0+} contained in g_{x,0}; it identifies the maximal reductive quotient's Lie algebra, rather than the Lie algebra of the whole special fibre.",
      "lean_declarations": [
        "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.specialFibreLieQuotientEquiv",
        "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.positiveLieLattice",
        "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.positiveLieLattice_le",
        "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.smul_lieLattice_le_positiveLieLattice",
        "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.reductiveQuotientLieEquiv",
        "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.positiveLieLattice_eq",
        "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.lieLatticeQuotientEquiv",
        "Langlands.GroupScheme.IntegralModel.lieReduction",
        "Langlands.GroupScheme.IntegralModel.ker_lieReduction"
      ],
      "modules": [
        "Langlands.BruhatTits.IntegralModels.ReductiveQuotientLie",
        "Langlands.GroupScheme.IntegralModel.LieLatticeReduction"
      ],
      "dependencies": [
        "Section 13.2.6 identifies Gred_x with the group-scheme cokernel of the special-fibre morphism G_{x,0+} to G_{x,0}",
        "Proposition 8.5.18 proves smoothness of that morphism's kernel; Section 2.4(a) then supplies exactness on Lie algebras",
        "Use the actual descended models and Lie maps, not an arbitrary quotient equipped with an assumed identification",
        "Recorded Lean construction: specialFibreLieQuotientEquiv combines the Library's ker_projection_eq_radical_lie and projection_smooth (module ReductiveQuotientRoots) with SubgroupFunctor.lie_eq_range and Lie.targetMapLinear_surjective_of_smooth; reductiveQuotientLieEquiv is the first isomorphism theorem for reduction followed by the differential of the projection, surjective by lieReduction_surjective (smoothness of D.neutral); positiveLieLattice_eq lifts through the smooth factorization and the smooth model N (exists_lieReduction_eq) and uses ker_lieReduction. In the published module LieLatticeReduction the auxiliary isomorphism specialFibreBaseChangeIso of the earlier file was renamed specialFibreAlgebraBaseIso when the module entered the Library, avoiding a name collision; no recorded declaration is affected.",
        "Open obligations: the descended models G_{x,0} and G_{x,0+} and the map between them are not constructed in Lean, so KP's g_{x,0+} = Lie(G_{x,0+}) is identified with positiveLieLattice only under the supplied hypotheses; Proposition 8.5.18, the cokernel identification of Section 13.2.6 for those models and the inclusion m g_{x,0} ⊂ g_{x,0+} have no Lean proof, and the compatibility of the identification with Lie brackets has no Lean statement.",
        "Release 1 constructions, the corrected Theorem 9.2.7 certificate and the inflation/compact-induction consumer remain prerequisites for positive-depth implementation. A source row supplies no release or formal acceptance."
      ],
      "consumer_or_regression": "Depth-zero Lie comparison and graded-action tests. Keep distinct the rational-point quotient of 13.2.6 and this Lie-algebra cokernel calculation; neither alone proves the other.",
      "formal_status": "conditional",
      "publication_commits": [
        "fd643ecec6997ef17c8356ddbc924138631307d9"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.specialFibreLieQuotientEquiv",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit fd643ece; kind definition; that commit first published the module."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.positiveLieLattice",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit fd643ece; kind definition; that commit first published the module."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.positiveLieLattice_le",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit fd643ece; kind theorem; that commit first published the module."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.smul_lieLattice_le_positiveLieLattice",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit fd643ece; kind theorem; that commit first published the module."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.reductiveQuotientLieEquiv",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit fd643ece; kind definition; that commit first published the module."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.positiveLieLattice_eq",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit fd643ece; kind theorem; that commit first published the module."
        },
        {
          "declaration": "Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData.lieLatticeQuotientEquiv",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit fd643ece; kind definition; that commit first published the module."
        },
        {
          "declaration": "Langlands.GroupScheme.IntegralModel.lieReduction",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit fd643ece; kind definition; that commit first published the module."
        },
        {
          "declaration": "Langlands.GroupScheme.IntegralModel.ker_lieReduction",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit fd643ece; kind theorem; that commit first published the module."
        }
      ],
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
        "r is real.",
        "Recorded Lean scope (partial definition: the intrinsic span description of g_{x,r}, r >= 0, from supplied lattices z_r and u_psi): the module Langlands.Geometry.Building.KPLieFiltration, first published in Library commit fd643ecec6997ef17c8356ddbc924138631307d9, works with a group scheme G over a nonarchimedean local field F with ring of integers 𝒪[F] and supplied P : ParahoricBuildingData G; GenericLie 𝒪[F] G is Lie(G) as an 𝒪[F]-module. Langlands.Geometry.Building.ParahoricBuildingData.rootLieSpace a is u_a = Lie(U_a), the 𝒪[F]-submodule underlying the span of the weight spaces g_{na}, n >= 1, of the relative root a (RelativeRoot.positiveWeightSpan). The structure Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData P supplies a decreasing family z_r, r : NNReal, of 𝒪[F]-submodules of Lie(Z) for the centralizer Z = P.centralizer.Z (centralizerLie), and for each affine root psi of P.affineRoots an 𝒪[F]-submodule u_psi (affineRootLie) contained in u_a for the gradient a of psi. Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.rootLie x a r is the supremum of the u_psi with gradient a and psi(x) >= r, and Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.lieFiltration x r is the supremum, that is the 𝒪[F]-span, of the image of z_r in Lie(G) and of the u_psi with psi(x) >= r: KP's description of g_{x,r} as the o-span of z_r and the u_psi for psi in Psi_{x,r}. lieFiltration_eq_sup_rootLie regroups it as the image of z_r plus the supremum over a of rootLie x a r, lieFiltration_antitone proves it decreasing in r, and lieFiltrationPlus x r is the supremum over s > r. The supplied z_r and u_psi are not shown to be the Lie lattice of the S-fixed subgroup scheme of G_{x,r} or Lie(U_psi) = g_z ∩ u_a(k), and lieFiltration is not shown to be Lie(G_{x,r}). The identity g_{x,r} = g(K)_{x,r}^Gamma and the Chevalley–Steinberg basis formula are not formalized. The definition status covers only the span description on supplied lattices.",
        "Recorded Lean regression (derived split-torus calculation, KPSplitTorusLieFiltration): for the actual split torus T = G_m^I over F, with I finite and no characteristic restriction, and the published ParahoricBuildingData.ofTorus datum, splitTorusLieFiltration constructs LieFiltrationData. Its centralizer input at r >= 0 is 𝔪^⌈r⌉₊ A₀, where A₀ is the Lie lattice of the smooth standard model splitTorusModel. There are no affine-root inputs because the relative roots are empty. The theorems give g_{x,r} = 𝔪^⌈r⌉₊ A₀ at every apartment point (splitTorus_lieFiltration) and the unit shift (splitTorus_lieFiltration_isPeriodic). At every real r they give g_{x,r} = π^⌈r⌉ A₀ (splitTorus_lieFiltrationReal), g_{x,r+} = π^(⌊r⌋+1) A₀ (splitTorus_lieFiltrationPlusReal) and the lattice property (splitTorus_lieFiltrationReal_isLattice). By splitTorus_lieFiltrationPlusReal_lt_iff, jumps occur exactly at integers when I is nonempty and never when I is empty. The centralizer input is the Section 8.5.20 torus formula in this case; the positive-depth models of Section 8.5 are not constructed or compared."
      ],
      "conclusion": "Let g(K)_{x,r} be the O-Lie lattice of the base-changed actual model. Then g_{x,r}=g(K)_{x,r}^Gamma. The Chevalley-Steinberg basis formula of 8.5.20 describes the O-lattice over K and works over o when G is quasi-split. There is also an intrinsic description over o: choose a maximal k-split S with x in its apartment; let z_r be the Lie lattice of the S-fixed subgroup scheme of G_{x,r}, with generic fibre Z_G(S). For an affine root psi, let u_psi=Lie(U_psi)=g_z intersect u_a(k), for any z on H_psi and a the derivative of psi. Then g_{x,r} is the o-span of z_r and the u_psi for psi(x)>=r. The quasi-split hypothesis belongs to the explicit basis formula over o, not to the general lattice or its intrinsic span description.",
      "lean_declarations": [
        "Langlands.Geometry.Building.ParahoricBuildingData.rootLieSpace",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.rootLie",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.lieFiltration",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.lieFiltration_eq_sup_rootLie",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.lieFiltration_antitone",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.lieFiltrationPlus",
        "Langlands.Geometry.Building.ParahoricBuildingData.splitTorusLieFiltration",
        "Langlands.Geometry.Building.ParahoricBuildingData.splitTorus_lieFiltration",
        "Langlands.Geometry.Building.ParahoricBuildingData.splitTorus_lieFiltration_isPeriodic",
        "Langlands.Geometry.Building.ParahoricBuildingData.splitTorus_lieFiltrationReal",
        "Langlands.Geometry.Building.ParahoricBuildingData.splitTorus_lieFiltrationPlusReal",
        "Langlands.Geometry.Building.ParahoricBuildingData.splitTorus_lieFiltrationReal_isLattice",
        "Langlands.Geometry.Building.ParahoricBuildingData.splitTorus_lieFiltrationPlusReal_lt_iff"
      ],
      "modules": [
        "Langlands.Geometry.Building.KPLieFiltration",
        "Langlands.Geometry.Building.KPSplitTorusLieFiltration"
      ],
      "dependencies": [
        "Section 8.5.20 gives the explicit Chevalley-Steinberg lattice over O; the actual model descent gives the invariant lattice",
        "Section 9.4.5 constructs U_psi; Proposition 9.8.3 supplies the standard integral S-model action and its centralizer filtration. Section 13.2.1 defines Psi_{x,r} by psi(x)>=r",
        "The model construction and the root-space span formula must be proved for the constructed objects; a chosen basis or an assumed Gamma-invariant lattice is insufficient",
        "Recorded Lean construction: rootLieSpace is the comap of RelativeRoot.positiveWeightSpan (module Langlands.GroupScheme.Rational.RootSubgroupStructureStatement) under GenericLie.equiv, with scalars restricted to 𝒪[F]; lieFiltration_eq_sup_rootLie uses that every element of P.affineRoots has a relative root as gradient.",
        "Recorded Lean proof (split torus): the empty root summands vanish and the identity centralizer inclusion has identity differential. The real-depth piece is computed by testing the generator π^n of 𝔪^n and cancelling. The strict supremum is attained at ⌊r⌋+1. At an integer, Nakayama for the finitely generated nonzero A₀ gives 𝔪A₀ ≠ A₀; for empty I the infinitesimal-coordinate equivalence makes the Lie space zero.",
        "Open obligations: the models G_{x,r}, their base change to O and the Gamma-invariants are not constructed in Lean, so g_{x,r} = g(K)_{x,r}^Gamma has no Lean statement; the lattices z_r and u_psi are supplied rather than constructed from Section 9.4.5 and Proposition 9.8.3, and the basis formula of 8.5.20 has no Lean statement.",
        "Release 1 constructions, the corrected Theorem 9.2.7 certificate and the inflation/compact-induction consumer remain prerequisites for positive-depth implementation. A source row supplies no release or formal acceptance."
      ],
      "consumer_or_regression": "Compare split basis calculations with a non-quasi-split descended lattice and a multipliable-root case. Retain the actual maximal split torus, centralizer and affine-root valuation conventions. The root-free split-torus case is now a Lean regression on the actual standard depth-zero torus model; the descended non-quasi-split and multipliable-root comparisons remain open.",
      "formal_status": "definition",
      "publication_commits": [
        "fd643ecec6997ef17c8356ddbc924138631307d9",
        "2d12bd934a2a0da7808014bfe52c6d67fde3eb62"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.rootLieSpace",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit fd643ece; kind definition; that commit first published the module."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit fd643ece; kind inductive; that commit first published the module."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.rootLie",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit fd643ece; kind definition; that commit first published the module."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.lieFiltration",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit fd643ece; kind definition; that commit first published the module."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.lieFiltration_eq_sup_rootLie",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit fd643ece; kind theorem; that commit first published the module."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.lieFiltration_antitone",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit fd643ece; kind theorem; that commit first published the module."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.lieFiltrationPlus",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit fd643ece; kind definition; that commit first published the module."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.splitTorusLieFiltration",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection; kind definition; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 2d12bd93."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.splitTorus_lieFiltration",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful #print axioms check; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 2d12bd93."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.splitTorus_lieFiltration_isPeriodic",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful #print axioms check; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 2d12bd93."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.splitTorus_lieFiltrationReal",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful #print axioms check; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 2d12bd93."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.splitTorus_lieFiltrationPlusReal",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful #print axioms check; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 2d12bd93."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.splitTorus_lieFiltrationReal_isLattice",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful #print axioms check; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 2d12bd93."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.splitTorus_lieFiltrationPlusReal_lt_iff",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection; kind theorem; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 2d12bd93."
        }
      ],
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
        "r is real. Gred_x is the actual maximal reductive quotient of the parahoric special fibre; both Lie and dual lattices use Section 13.3.1's conventions.",
        "Recorded Lean scope (preservation of the Lie lattice by the integral points of a supplied integral model, the case r = 0 of the first sentence at the level of points): the module Langlands.GroupScheme.IntegralModel.LieLatticeAdjoint, first published in Library commit 9e39a73d21bd6ed6fac00b01cc5e01c0db5d105b, has the setting of the Section 13.3.1 row (a commutative domain R with fraction field K, an affine K-group G and an integral model M), with no smoothness hypothesis. Langlands.GroupScheme.GenericLie.adjoint R g is the adjoint action of g in G(K) on GenericLie R G, as an R-linear map (the Library's adjoint action, conjugation by a constant dual-number point, applied through AffineWeil.sectionsCoeffEquiv). Langlands.GroupScheme.IntegralModel.map_adjoint_lieLattice proves M.lieLattice.map (GenericLie.adjoint R g) = M.lieLattice for every g in M.integralPoints, and Langlands.GroupScheme.IntegralModel.lieLatticeAdjoint is the resulting representation M.integralPoints →* Module.End R M.lieLattice. With M the connected parahoric model G_{x,0} this would be the action of its o-points on g_{x,0}; no Lean declaration constructs that model. This integral-model theorem alone does not give a group-scheme action at all depths or its factorization through Gred_x.",
        "Recorded Lean scope (rational points, KPLieGradedAction): on supplied L : P.LieFiltrationData, filtrationStabilizer x consists of rational points preserving every nonnegative-depth Lie submodule under the adjoint action. It acts by adjoint and coadjoint on the respective real-depth pieces. gradedLie quotients the real lattice by the inverse image of the strict supremum (it is KP's strict quotient under IsPeriodic); dualGradedLie is the image of the dual lattice in the quotient by its deeper piece. For H contained in this stabilizer, quotientGradedAdjoint and quotientDualGradedAdjoint give 𝒪[F]-linear representations of H/(N.subgroupOf H) assuming normality of that subgroup and the respective triviality on the full graded piece. Taking H as the connected parahoric and N as its positive radical preimage requires these hypotheses. This is not a group-scheme representation of Gred_x.",
        "Recorded Lean scope (residue equivariance, KPLieGradedResidue): under the hypotheses of the graded residue equivalence in the Section 13.3.1 row, dualGradedLieLinearEquiv_dualGradedAdjoint shows that for g in filtrationStabilizer x the equivalence carries the coadjoint action on the dual grade at r to the contragredient of the graded adjoint action at -r. This is equivariance for the rational-point stabilizer only.",
        "Recorded Lean scope (dual transfer and invariance): actsTriviallyOnDualGraded_of_lieFiltrationPlusReal_le transfers N-triviality at Lie depth -r to dual depth r if g_{x,s+} ≤ g_{x,-r} for some s < -r. Periodicity and IsLeftContinuousAt at -r suffice; actsTriviallyOnDualGraded_of_oppositePairs obtains that premise by the Section 13.3.1 criterion. The residue pairing obeys gradedLieDualPairing_gradedAdjoint under IsPeriodic for elements of filtrationStabilizer x acting coadjointly on g^*_{x,r} and adjointly on the opposite-depth graded Lie piece. No triviality for the actual radical or scheme-level equivariance is inferred."
      ],
      "conclusion": "Conjugation by the connected parahoric model induces actions on the Lie and dual lattices. On their strict graded pieces g_{x,r}/g_{x,r+} and g^*_{x,r}/g^*_{x,r+}, these induce genuine f-rational representations of Gred_x. Factorization through the reductive quotient and preservation of the lattices are part of the conclusion, not structure fields to assume.",
      "lean_declarations": [
        "Langlands.GroupScheme.GenericLie.adjoint",
        "Langlands.GroupScheme.IntegralModel.map_adjoint_lieLattice",
        "Langlands.GroupScheme.IntegralModel.lieLatticeAdjoint",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.gradedAdjoint",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.dualGradedAdjoint",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.quotientGradedAdjoint",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.quotientDualGradedAdjoint",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.IsLeftContinuousAt",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.actsTriviallyOnDualGraded_of_lieFiltrationPlusReal_le",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.actsTriviallyOnDualGraded_of_oppositePairs",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.gradedLieDualPairing_gradedAdjoint",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.dualGradedLieLinearEquiv_dualGradedAdjoint"
      ],
      "modules": [
        "Langlands.GroupScheme.IntegralModel.LieLatticeAdjoint",
        "Langlands.Geometry.Building.KPLieGradedAction",
        "Langlands.Geometry.Building.KPLieFiltrationLeftContinuity",
        "Langlands.Geometry.Building.KPLieGradedPairing",
        "Langlands.Geometry.Building.KPLieGradedResidue"
      ],
      "dependencies": [
        "Proposition 13.2.5 gives normality over K; Corollary 2.10.10 extends the actual conjugation action to integral models",
        "Apply the Lie functor, dual action and reduction, with periodicity for all real depths, then prove the action factors through Gred_x on both strict graded pieces",
        "Sections 13.3.1-3 and the actual Chapter 9 model descent",
        "Recorded Lean construction: the proof of map_adjoint_lieLattice identifies the generic points of integral sections (IntegralModel.sectionsCoeffEquiv_integralPointMap) and proves IntegralModel.lieMap_adjoint, that lieMap intertwines the adjoint action of an integral section on the Lie algebra of the model with GenericLie.adjoint of its generic point; IntegralModel.adjoint_mem_lieLattice and the inverse point give both inclusions.",
        "Recorded Lean construction: restriction and descent of GenericLie.adjoint and the inverse-transpose coadjoint dual to the grade use the stabilizer inclusion. QuotientGroup.lift uses the respective normal-subgroup kernel premise. The dual transfer evaluates X on Ad(n^{-1})Y - Y and uses the maximal-ideal pairing on g_{x,(-r)+}. The pairing invariance uses cancellation of Ad(g^{-1}) with Ad(g).",
        "Open obligations: construct the descended models and their conjugation morphisms, prove their parahoric stabilizer and radical triviality premises and produce the genuine f-rational action of Gred_x with a comparison to the points-level actions. The abstract quotient construction is not the scheme-level descent or the algebraic instability input.",
        "Release 1 constructions, the corrected Theorem 9.2.7 certificate and the inflation/compact-induction consumer remain prerequisites for positive-depth implementation. A source row supplies no release or formal acceptance."
      ],
      "consumer_or_regression": "Graded adjoint/coadjoint action and pairing-equivariance tests; this rational reductive-quotient action is the one used for later algebraic instability, not a valuation-topology orbit action.",
      "formal_status": "conditional",
      "publication_commits": [
        "9e39a73d21bd6ed6fac00b01cc5e01c0db5d105b",
        "5f5d3a914cd43b9dc1cd32c07887a973f561df96",
        "6e9e589baa721ce995563f73f648b6f4e45718a1",
        "2d12bd934a2a0da7808014bfe52c6d67fde3eb62"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.GroupScheme.GenericLie.adjoint",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit fcb85a7e; kind definition; the module is byte-identical to commit 9e39a73d, its first publication."
        },
        {
          "declaration": "Langlands.GroupScheme.IntegralModel.map_adjoint_lieLattice",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit fcb85a7e; kind theorem; the module is byte-identical to commit 9e39a73d, its first publication."
        },
        {
          "declaration": "Langlands.GroupScheme.IntegralModel.lieLatticeAdjoint",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-17 at Library commit fcb85a7e; kind definition; the module is byte-identical to commit 9e39a73d, its first publication."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.gradedAdjoint",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection; kind definition; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 5f5d3a91."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.dualGradedAdjoint",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful #print axioms check; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 5f5d3a91."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.quotientGradedAdjoint",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection; kind definition; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 5f5d3a91."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.quotientDualGradedAdjoint",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection; kind definition; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 5f5d3a91."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.IsLeftContinuousAt",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful #print axioms check; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 5f5d3a91."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.actsTriviallyOnDualGraded_of_lieFiltrationPlusReal_le",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful #print axioms check; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 5f5d3a91."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.actsTriviallyOnDualGraded_of_oppositePairs",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful #print axioms check; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 6e9e589b."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.gradedLieDualPairing_gradedAdjoint",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection; kind theorem; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 6e9e589b."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.dualGradedLieLinearEquiv_dualGradedAdjoint",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful #print axioms check; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 2d12bd93."
        }
      ],
      "external_code": []
    },
    {
      "source_item": "Definition 13.4.1",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.472 / PDF p.503, including the preceding positivity and indecomposability definitions; compare Definition 1.3.19, printed p.22 / PDF p.53 for wall roots"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.49, Chapter 13",
        "change": "No correction to Section 13.4 is listed."
      },
      "hypotheses": [
        "The apartment of a fixed maximal k-split torus, with its actual affine roots Ψ, and a fixed chamber C. The source calls a positive affine root simple if it is not the sum of two positive affine roots.",
        "Recorded Lean scope (KPOptimalPoints): for any real affine torsor A with a set Ψ of affine functionals, IsRationalPoint means all root values are in the image of ℚ → ℝ. IsRationalAffineFunctional requires a regular representative c, and membership in the finite rational span of indecomposablePositiveRoots Ψ (facet Ψ c); these are exactly the positive roots not expressible as a sum of two positive roots. No affine-root axioms are needed to state these predicates."
      ],
      "conclusion": "A functional is rational if it is a rational linear combination of the specified simple affine roots. A point is rational if every affine root takes a rational value there. The Lean evaluation lemma proves that such a functional has rational value at each rational point.",
      "lean_declarations": [
        "Langlands.Geometry.Building.AffineRootSystem.IsRationalPoint",
        "Langlands.Geometry.Building.AffineRootSystem.indecomposablePositiveRoots",
        "Langlands.Geometry.Building.AffineRootSystem.IsRationalAffineFunctional",
        "Langlands.Geometry.Building.AffineRootSystem.IsRationalAffineFunctional.apply_mem_range"
      ],
      "modules": [
        "Langlands.Geometry.Building.KPOptimalPoints"
      ],
      "dependencies": [
        "KPOptimalPoints uses the existing chamber and positive-root conventions of AffineRootSystem and implements the rational span by a finite sum. At a rational point, evaluation carries each summand into the image of Rat.castHom ℝ.",
        "The literal generator rule is distinct from the Chapter 1 positive indivisible wall roots (Definition 1.3.19). In reduced affine A₁, two slopes ±1 cannot sum to an allowed slope, so all positive affine roots are indecomposable. The set is not asserted to be a finite basis and no generator comparison is proved."
      ],
      "consumer_or_regression": "Rationality predicate for Definition 13.4.2 and later rational optimization; keep the two generator conventions separate.",
      "formal_status": "definition",
      "publication_commits": [
        "032961776f43ccd672c6266d265a9c644faeba13"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.AffineRootSystem.IsRationalPoint",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful #print axioms check; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 03296177."
        },
        {
          "declaration": "Langlands.Geometry.Building.AffineRootSystem.indecomposablePositiveRoots",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful #print axioms check; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 03296177."
        },
        {
          "declaration": "Langlands.Geometry.Building.AffineRootSystem.IsRationalAffineFunctional",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful #print axioms check; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 03296177."
        },
        {
          "declaration": "Langlands.Geometry.Building.AffineRootSystem.IsRationalAffineFunctional.apply_mem_range",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful #print axioms check; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 03296177."
        }
      ],
      "external_code": []
    },
    {
      "source_item": "Definition 13.4.2",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.472 / PDF p.503, including the definitions of ℓ and Σ in the preceding paragraphs"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.49, Chapter 13",
        "change": "No correction to Section 13.4 is listed."
      },
      "hypotheses": [
        "Fix an apartment, an open chamber C and the least positive rational period ℓ of its nonempty affine-root set. Σ consists of the roots ψ positive on C with ψ - ℓ negative on C. Take a nonempty subset S of the finite set Σ.",
        "Recorded Lean scope (KPOptimalPoints): on an abstract real affine torsor, IsOptimalPointFor Ψ c S x requires IsRegular Ψ c, a nonempty Finset S contained in positiveRootsBelowPeriod Ψ c, x in facetClosure Ψ c, maximality of min_{ψ∈S} ψ(x) over that closure, and IsRationalPoint Ψ x. AffineRootSystem.IsOptimalPoint existentially chooses c and S. ValuationBuildingData.IsOptimalPoint on the reduced building is the existence of a rational-point translate of an apartment optimum under a chart. The chamber and lattice geometry remain supplied.",
        "For the period lemmas the abstract finiteness argument uses nonempty roots, bounded-finite derivative fibres and a positive rational period. The abstract strip finiteness holds under IsAffineRootSystemWithRankZero; strip nonemptiness also uses regularity, nonempty roots and membership of rootPeriod in rationalRootPeriods. For the supplied nonarchimedean local-field valuation apartment, period 2 is proved, so nonempty actual affine roots suffice for a least positive rational period; with regular c, Σ is finite and nonempty. The empty-root obstruction for building optimality is proved separately."
      ],
      "conclusion": "An optimal point for S in the closed chamber attains the maximum of the finite minimum and is rational on every root. A building point is optimal if it is such a point in some apartment and chamber for some nonempty S.",
      "lean_declarations": [
        "Langlands.Geometry.Building.AffineRootSystem.rationalRootPeriods",
        "Langlands.Geometry.Building.AffineRootSystem.rootPeriod",
        "Langlands.Geometry.Building.AffineRootSystem.positiveRootsBelowPeriod",
        "Langlands.Geometry.Building.AffineRootSystem.IsOptimalPointFor",
        "Langlands.Geometry.Building.AffineRootSystem.IsOptimalPoint",
        "Langlands.Geometry.Building.ValuationBuildingData.isLeast_rootPeriod_affineRoots",
        "Langlands.Geometry.Building.ValuationBuildingData.positiveRootsBelowPeriod_affineRoots_finite_nonempty",
        "Langlands.Geometry.Building.ValuationBuildingData.IsOptimalPoint",
        "Langlands.Geometry.Building.ValuationBuildingData.not_isOptimalPoint_of_affineRoots_eq_empty"
      ],
      "modules": [
        "Langlands.Geometry.Building.KPOptimalPoints"
      ],
      "dependencies": [
        "Section 13.4.1 rational points; KPOptimalPoints uses the root period as an infimum, identifies it as the least period under the given hypotheses, and uses weak signs for the closed chamber. Root stability under normalizer action and the translation by 2 yield the supplied valuation-apartment period. The existing rational-point translate charts give the building predicate.",
        "Open in this row: optimal-point existence for the nonempty subsets, the chosen family x_S and the set O of its rational-point translates for Lemma 13.4.4. A predicate on all optimal points is not that choice family. Example 13.4.3 and discreteness of optimal depths are not asserted."
      ],
      "consumer_or_regression": "The first clause of Proposition 13.6.7; the empty-root boundary for G_m. The instability clause is independent of this requirement.",
      "formal_status": "definition",
      "publication_commits": [
        "032961776f43ccd672c6266d265a9c644faeba13"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.AffineRootSystem.rationalRootPeriods",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful #print axioms check; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 03296177."
        },
        {
          "declaration": "Langlands.Geometry.Building.AffineRootSystem.rootPeriod",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful #print axioms check; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 03296177."
        },
        {
          "declaration": "Langlands.Geometry.Building.AffineRootSystem.positiveRootsBelowPeriod",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful #print axioms check; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 03296177."
        },
        {
          "declaration": "Langlands.Geometry.Building.AffineRootSystem.IsOptimalPointFor",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection; kind definition; statement_returns_prop true; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 03296177."
        },
        {
          "declaration": "Langlands.Geometry.Building.AffineRootSystem.IsOptimalPoint",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful #print axioms check; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 03296177."
        },
        {
          "declaration": "Langlands.Geometry.Building.ValuationBuildingData.isLeast_rootPeriod_affineRoots",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful #print axioms check; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 03296177."
        },
        {
          "declaration": "Langlands.Geometry.Building.ValuationBuildingData.positiveRootsBelowPeriod_affineRoots_finite_nonempty",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful #print axioms check; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 03296177."
        },
        {
          "declaration": "Langlands.Geometry.Building.ValuationBuildingData.IsOptimalPoint",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful #print axioms check; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 03296177."
        },
        {
          "declaration": "Langlands.Geometry.Building.ValuationBuildingData.not_isOptimalPoint_of_affineRoots_eq_empty",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful #print axioms check; the inspected module source is byte-identical to the file at Library commit b47a2385 and to the version first published at 03296177."
        }
      ],
      "external_code": []
    },
    {
      "source_item": "Lemma A.5.13(4)",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.636–637 / PDF pp.667–668, Lemma A.5.13(4)"
      },
      "erratum": null,
      "hypotheses": [
        "The source uses an affine integral model over the discretely valued base o. In Lean the base R is a discrete valuation ring with fraction field K, M is an integral model of an affine group scheme over K, ϖ is an irreducible element of R and n is a natural number."
      ],
      "conclusion": "The Lie lattice of the actual congruence group scheme M.congruenceModel hϖ n is 𝔪ⁿ times M.lieLattice in the generic Lie module. The statement includes level zero.",
      "lean_declarations": [
        "Langlands.GroupScheme.IntegralModel.CongruenceModelLieLatticeStatement",
        "Langlands.GroupScheme.IntegralModel.CongruenceLiePropertiesStatement"
      ],
      "modules": [
        "Langlands.GroupScheme.IntegralModel.CongruenceLieStatements"
      ],
      "dependencies": [
        "The dilatation construction supplies the actual congruence model. On dual numbers the source calculates the Lie functor as the kernel of reduction modulo 𝔪ⁿ and identifies it with the corresponding scaled lattice."
      ],
      "consumer_or_regression": "This formula identifies the target Lie lattices when the group filtration comes from the congruence models, including the base lattice at level zero.",
      "formal_status": "statement",
      "publication_commits": [
        "db940683e1d682d84831e8365720f1c79b5c9b0c"
      ],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Proposition A.5.19",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.641–643 / PDF pp.672–674, part (3) and Remark A.5.20"
      },
      "erratum": null,
      "hypotheses": [
        "In part (3), G is a smooth affine group scheme over the valuation ring o, R is a flat o-algebra and 0 < n ≤ m ≤ 2n. Surjectivity uses the local Henselian hypothesis with maximal ideal 𝔪R.",
        "The Lean construction takes a commutative local domain R with fraction field K and a smooth affine integral model M of an affine group scheme over K. It uses powers of the maximal ideal of R at positive levels n ≤ m ≤ 2n. The surjectivity statement takes a Henselian local R. The unramified comparison uses the integers of a nonarchimedean local field and those of the separable inertia fixed field."
      ],
      "conclusion": "The homomorphism on the level-n congruence subgroup takes values in the additive group of 𝔪ⁿL/𝔪ᵐL, where L is the integral Lie lattice. The construction induces a map on the quotient by level m. The companion propositions state injectivity, Henselian surjectivity, model functoriality, integral conjugation equivariance and compatibility with maximal unramified extension. The scheme isomorphism and Weil restriction comparison of parts (1) and (2) have their own scope.",
      "lean_declarations": [
        "Langlands.GroupScheme.IntegralModel.congruenceLieHom",
        "Langlands.GroupScheme.IntegralModel.congruenceLieQuotientHom",
        "Langlands.GroupScheme.IntegralModel.CongruenceLieInjectivityStatement",
        "Langlands.GroupScheme.IntegralModel.CongruenceLieSurjectivityStatement",
        "Langlands.GroupScheme.IntegralModel.CongruenceLieFunctorialityStatement",
        "Langlands.GroupScheme.IntegralModel.CongruenceLieAdjointEquivarianceStatement",
        "Langlands.GroupScheme.IntegralModel.CongruenceLieUnramifiedCompatibilityStatement"
      ],
      "modules": [
        "Langlands.GroupScheme.IntegralModel.LieLatticeBaseChange",
        "Langlands.GroupScheme.IntegralModel.CongruenceLie",
        "Langlands.GroupScheme.IntegralModel.CongruenceLieStatements",
        "Langlands.GroupScheme.IntegralModel.CongruenceLieUnramified"
      ],
      "dependencies": [
        "The coefficient ideal 𝔪ⁿ/𝔪ᵐ in R/𝔪ᵐ is square-zero by m ≤ 2n. Reduction takes the level-n subgroup to the square-zero kernel, where the augmentation derivation lands in the tensor of this ideal with the integral Lie module. Smoothness gives flatness of the Lie module for the comparison with the Lie-lattice quotient. Remark A.5.20 explains this direct construction.",
        "The surjectivity target uses Henselian lifting of residue-ring points. For the maximal unramified comparison, GenericLie.baseChange extends tangent points and IntegralModel.baseChange_mem_lieLattice proves preservation of the lattice. The coefficient map preserves powers of the maximal ideals."
      ],
      "consumer_or_regression": "The congruence–Lie map provides the integral-model comparison for the torus and parahoric maps in Appendix B and Theorem 13.5.1. Comparison there also requires identifying the particular models and their depths.",
      "formal_status": "statement",
      "publication_commits": [
        "db940683e1d682d84831e8365720f1c79b5c9b0c"
      ],
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
        "(3) 0<r<=s<=2r<=r+1.",
        "Recorded Lean scope (part (1) without the compatibility with unramified extensions, on supplied data): MoyPrasadIsomorphismStatement (module Langlands.Geometry.Building.KPMoyPrasadIsomorphismStatement) quantifies over every nonarchimedean local field F, every G over Spec F with [IsAffineHom G.X.hom], every ParahoricBuildingData P of G satisfying the apartment axioms, every CentralizerFiltration Zf of Z(F) satisfying the filtration axioms and IsDoubleRootCommutatorFriendly, every LieFiltrationData L (supplied lattices z_r in Lie(Z) and u_psi in the root spaces, module Langlands.Geometry.Building.KPLieFiltration), every point x of the apartment and every r, s in NNReal with 0 < r <= s and MoyPrasadAlternative F G r s. MoyPrasadAlternative states the three alternatives above, the torus clause of (1) as HasWeaklyInducedMaximallySplitTorus F G (module Langlands.Geometry.Building.KPWeaklyInducedTorus: a maximally split maximal torus of G over the maximal unramified extension K becomes induced over a finite tamely ramified extension of K inside a separable closure, KP Definition B.6.2). Assuming Z(F)_r/Z(F)_s = z_r/z_s and, for every non-divisible relative root a, U_{a,x,r}U_{2a,x,r}/U_{a,x,s}U_{2a,x,s} = (u_{a,x,r}+u_{2a,x,r})/(u_{a,x,s}+u_{2a,x,s}) (rootBlockLie), it asserts P_{x,r}/P_{x,s} = g_{x,r}/g_{x,s} for Zf.moyPrasad and L.lieFiltration. Each = is HasMoyPrasadQuotientIso: a surjective homomorphism from the larger group onto the additive quotient, whose kernel is the smaller group, so an isomorphism of abstract groups. The component isomorphisms are hypotheses because the Library has neither the minimal congruent torus filtration nor the Lie algebras of KP's integral models; Zf and L are supplied and nothing else ties them together. Automorphism equivariance, agreement of alternatives (1) and (2), and parts (2) and (3) are not stated."
      ],
      "conclusion": "There exists an isomorphism of abstract abelian groups MP_{x,r,s}:P_{x,r}/P_{x,s} to g_{x,r}/g_{x,s}, compatible with unramified algebraic extensions of k. Under alternative (1) or (2), it can be chosen so that, for every k-rational automorphism theta of G, dtheta composed with MP_{x,r,s} composed with theta^-1 equals MP_{theta(x),r,s}. The theorem does not assert this general automorphism equivariance under (3) alone. When (1) and (2) both hold, their constructions coincide. This is not an unconditional exponential map or a k-linear group map.",
      "lean_declarations": [
        "Langlands.Geometry.Building.MoyPrasadIsomorphismStatement",
        "Langlands.Geometry.Building.HasMoyPrasadQuotientIso",
        "Langlands.Geometry.Building.MoyPrasadAlternative",
        "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.rootBlockLie",
        "Langlands.Geometry.Building.HasWeaklyInducedMaximallySplitTorus"
      ],
      "modules": [
        "Langlands.Geometry.Building.KPMoyPrasadIsomorphismStatement",
        "Langlands.Geometry.Building.KPWeaklyInducedTorus"
      ],
      "dependencies": [
        "Alternative (2): Proposition A.5.19 on the actual congruence models and its functoriality for their morphisms",
        "Alternatives (1)/(3) over K: indivisible-root quotient products, C.5.1 root-model congruence and A.5.19; torus comparison B.6.9 under (1), and possibly nonfunctorial B.10.17 under (3). Resolve 13.2.5's indexing against its cited 7.3.3/7.3.12 construction before relying on it",
        "Descent: Lemma 8.1.4, smooth connected unipotent special fibres from 8.5.14 and perfect-residue H^1 vanishing from 2.4.2, for both group and Lie lattices",
        "Agreement under (1)/(2): A.5.19 functoriality and B.10.16 compatibility of the torus comparisons",
        "Corrected B.10.8 and added B.10.15 establish the minimal congruent torus filtration over k, Gamma-stability and smooth model descent. Functoriality of the filtration does not imply unrestricted functoriality of its Moy-Prasad isomorphisms at every positive depth",
        "Release 1 constructions, the corrected Theorem 9.2.7 certificate and the inflation/compact-induction consumer remain prerequisites for positive-depth implementation. A source row supplies no release or formal acceptance.",
        "Recorded statement (thirty-fourth update, Library commit ba9d1e9a): MoyPrasadIsomorphismStatement (a statement), first in Library commit b86269dd36757fdbea2e51976499d645ca61a625; the torus clause HasWeaklyInducedMaximallySplitTorus with IsWeaklyInducedTorus (a definition), first in Library commit fd643ecec6997ef17c8356ddbc924138631307d9. The premise Zf.IsDoubleRootCommutatorFriendly is the one under which the Library proves [P_{x,r}, P_{x,s}] in P_{x,r+s} (moyPrasadDoubleRootCommutator, Proposition 13.2.5 row); a statement without it fails for the ramified quasi-split SU(3) over Q_2 example of the Library note notes/bruhat-tits/moy-prasad-supplied-filtration-counterexample.md, in which P_{x,1/2}/P_{x,1} is not abelian. With the component isomorphisms and that premise assumed, the expected proof assembles the ordered products of MoyPrasadProductStatement (proved on supplied data by moyPrasadProduct, Proposition 13.2.5 row) at depths r and s and uses only the consequence s <= 2r of the alternatives. The statement has no proof."
      ],
      "consumer_or_regression": "Positive-depth acceptance requires actual finite abelian graded quotients over local fields, character transport through this proved map and a nontrivial calculation. Test each applicable alternative separately and the (1)/(2) overlap; do not impose a global tame or large-residue-characteristic hypothesis.",
      "formal_status": "statement",
      "publication_commits": [
        "b86269dd36757fdbea2e51976499d645ca61a625",
        "fd643ecec6997ef17c8356ddbc924138631307d9"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.MoyPrasadIsomorphismStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-18 at Library commit ba9d1e9a; kind definition, at universe level u, statement_returns_prop true; the module was first published in Library commit b86269dd and is byte-identical between that commit and Library commit ba9d1e9a."
        },
        {
          "declaration": "Langlands.Geometry.Building.HasMoyPrasadQuotientIso",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-18 at Library commit ba9d1e9a; kind definition, at universe levels u_1 and u_2, statement_returns_prop true; the module was first published in Library commit b86269dd and is byte-identical between that commit and Library commit ba9d1e9a."
        },
        {
          "declaration": "Langlands.Geometry.Building.MoyPrasadAlternative",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-18 at Library commit ba9d1e9a; kind definition, at universe level u, statement_returns_prop true; the module was first published in Library commit b86269dd and is byte-identical between that commit and Library commit ba9d1e9a."
        },
        {
          "declaration": "Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData.rootBlockLie",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-18 at Library commit ba9d1e9a; kind definition, at universe level u, a submodule-valued definition; the module was first published in Library commit b86269dd and is byte-identical between that commit and Library commit ba9d1e9a."
        },
        {
          "declaration": "Langlands.Geometry.Building.HasWeaklyInducedMaximallySplitTorus",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-18 at Library commit ba9d1e9a; kind definition, at universe level u, statement_returns_prop true; the module was first published in Library commit fd643ece and is byte-identical between that commit and Library commit ba9d1e9a."
        }
      ],
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
        "Recorded Lean scope: Langlands.BruhatTits.MaximalProP.AvailableMaximalProPStatement (module Langlands.BruhatTits.MaximalProP.AvailableStatement) quantifies over every nonarchimedean local field F of either characteristic in universe u, every connected reductive group scheme G over Spec F and every KPBuildingAssignment 𝔅 with 𝔅.IsAvailableFor F G hG, and asserts MaximalProPConclusions (𝔅.datum F G hG). The four conclusions are stated for facets of B(G) rather than points: P_{x,0+} is facetPositiveSubgroup D Fa for the facet Fa containing x, the points of the integral sections of the neutral facet model whose reduction lies in the residue-field points of the supplied radical of its special fibre (Axiom 4.1.22(7), Corollary 8.4.12), and P_{x,0} for a chamber is facetZeroFixer D C, the pointwise fixer of C in G(F)^0 = D.base.zeroSubgroup. With the point topology of G(F) and p = ringChar of the residue field: (1) every facetPositiveSubgroup lies in G(F)^0 and is open and pro-p; (2) it satisfies IsMaximalOpenProPIn p G(F)^0 (maximal among open pro-p subgroups of G(F) contained in G(F)^0) exactly when the facet is a chamber; (3) every such maximal subgroup is facetPositiveSubgroup D C for a chamber C; (4) for a chamber C, the normalizer of facetPositiveSubgroup D C intersected with G(F)^0 equals facetZeroFixer D C. This is the corrected ambient group G(k)^0 of both parts. The theorem availableMaximalProP proves AvailableMaximalProPStatement at arbitrary universe u. The completion certificate supplies IsAvailableFor on its own assignment, which gives all four facet conclusions for each F and G in the stated scope."
      ],
      "conclusion": "For every x, P_{x,0+} is an open pro-p subgroup of G(k)^0. It is maximal among open pro-p subgroups there exactly when x lies in a chamber, equivalently P_{x,0} is Iwahori. Every maximal open pro-p subgroup of G(k)^0 is P_{x,0+} for an Iwahori P_{x,0}, and its normalizer in G(k)^0 is P_{x,0}. Neither the maximality claim nor the normalizer identity is extended to the full G(k).",
      "lean_declarations": [
        "Langlands.BruhatTits.MaximalProP.AvailableMaximalProPStatement",
        "Langlands.BruhatTits.MaximalProP.MaximalProPConclusions",
        "Langlands.BruhatTits.MaximalProP.IsMaximalOpenProPIn",
        "Langlands.BruhatTits.MaximalProP.facetPositiveSubgroup",
        "Langlands.BruhatTits.MaximalProP.facetZeroFixer",
        "Langlands.BruhatTits.MaximalProP.availableMaximalProP",
        "Langlands.Geometry.Building.bruhatTitsCompletionCertificate"
      ],
      "modules": [
        "Langlands.BruhatTits.MaximalProP.AvailableStatement",
        "Langlands.BruhatTits.MaximalProP.AvailableProof",
        "Langlands.Geometry.Building.BruhatTitsCompletionCertificateProof"
      ],
      "dependencies": [
        "Proof: the theorem availableMaximalProP (module Langlands.BruhatTits.MaximalProP.AvailableProof, first in Library commit 410c79471b79f65a02fb0f6070da7f2800793ff3) proves AvailableMaximalProPStatement. Its Markdown describes the route. IsAvailableFor.groupAxioms gives the single-group axioms D.SatisfiesGroupAxioms of the available datum, and maximalProPConclusions_of_groupAxioms derives the four conclusions from them. The classification theorems of the module AvailableClassification give clauses (1)–(3) from the proved local-model pro-p result, the facet quotient comparisons and the finite-field Sylow and Borel theorems. For clause (4) the proof chooses an apartment chamber from a regular point of the affine reflection arrangement and a generic cocharacter of the maximal split torus. isProP_chamber_unipotent_factor gives the pro-p property of the two unipotent factors, for the cocharacter and its negative, and the Iwahori factorization with the split Tits-system normalizer theorem gives the normalizer identity at that chamber. chamber_normalizer_eq_of_one_apartment_chamber transports the identity to every chamber by conjugation inside G(F)^0. A Lean inspection on 2026-11-14 at Library commit 410c7947 reports kind theorem, a type that is exactly AvailableMaximalProPStatement.{u}, and only propext, Classical.choice and Quot.sound. The statement is present in Library commit ed924aef420de137b4cbaa3b063a3618afcd73fd. The completion certificate yields B.IsValid for the same assignment B that satisfies unramified descent. For a connected reductive G, availableMaximalProP F G hG B hB.isAvailableFor, with the affineness instance from hG.isAffineHom, gives MaximalProPConclusions (B.datum F G hG). This application has been checked in Lean.",
        "Intermediate statements of this proof (on 13 November 2026 none was proved): FacetReductiveComparisonStatement (module Langlands.BruhatTits.MaximalProP.FacetReductiveComparisonStatement, Library commit 7f43c3c930ff92f76dae6589da1678ad729017e5), the chamber, Borel and radical-preimage comparisons under the single-group Bruhat–Tits axioms; LocalFieldPositiveProPStatement (module Langlands.BruhatTits.IntegralModels.PositiveProPStatement, Library commit 73b1430a339b037d27e9096762b0400adb4fbd19), that the radical preimage of a supplied smooth neutral model with connected fibres is pro-p; FiniteFieldSylowBorelStatement and FiniteFieldNormalSylowTorusStatement (modules Langlands.GroupScheme.Rational.FiniteFieldSylowBorelStatement and Langlands.GroupScheme.Rational.FiniteFieldNormalSylowStatement, Library commit 7f43c3c930ff92f76dae6589da1678ad729017e5), on maximal p-subgroups of the rational points of a connected reductive group over a finite field; and BoundedOpenNormalizerStatement (module Langlands.BruhatTits.RationalPoints.BoundedOpenNormalizerStatement, Library commit 7f43c3c930ff92f76dae6589da1678ad729017e5), the local-field case of KP Proposition 2.2.16. The modules Langlands.BruhatTits.MaximalProP.AvailableFacetInputs and Langlands.BruhatTits.MaximalProP.AvailableNormalizerQuotient prove consequences that take some of these statements as hypotheses. At Library commit 410c7947 four of the five were proved. The theorems Langlands.GroupScheme.finiteFieldSylowBorel and Langlands.GroupScheme.finiteFieldNormalSylowTorus (module Langlands.GroupScheme.Rational.FiniteFieldBorelSylow, first in Library commit db8d6b3d466f2fd453a4df4624ce6c90db8eed46) prove FiniteFieldSylowBorelStatement and FiniteFieldNormalSylowTorusStatement; a Lean inspection on 2026-11-14 at Library commit 410c7947 reports kind theorem, a type that is exactly FiniteFieldSylowBorelStatement.{u}, and only propext, Classical.choice and Quot.sound, and an inspection reports the same for FiniteFieldNormalSylowTorusStatement.{u}. The theorem Langlands.BruhatTits.IntegralModels.localFieldPositiveProP (module Langlands.BruhatTits.IntegralModels.PositiveProP, first in Library commit 85c2fe719cf62e96f22aaf4ca03961c5814d086b) proves LocalFieldPositiveProPStatement; an inspection reports the same. The theorem Langlands.BruhatTits.MaximalProP.facetReductiveComparisonStatement (module Langlands.BruhatTits.MaximalProP.FacetRadicalPreimage, first in Library commit db8d6b3d466f2fd453a4df4624ce6c90db8eed46) proves FacetReductiveComparisonStatement; an inspection reports the same. Follow-up (twenty-second update, Library commit 58ad0f79): the fifth intermediate statement, BoundedOpenNormalizerStatement, is proved as well. The theorem Langlands.BruhatTits.RationalPoints.boundedOpenNormalizer (module Langlands.BruhatTits.RationalPoints.BoundedOpenNormalizerProof, first in Library commit af5d652c2f2ff5b35b4ce4dbbf7cbec8bbf3e99e) proves BoundedOpenNormalizerStatement; a Lean inspection on 2026-11-14 at Library commit 58ad0f79 reports kind theorem, a type that is exactly BoundedOpenNormalizerStatement.{u}, and only propext, Classical.choice and Quot.sound. Each module cited in this entry with a first commit is byte-identical between that commit and Library commit 58ad0f79.",
        "Actual model point topology and local compactness turn bounded open subgroups into compact ones. Realize P_{x,0+} as the inverse limit of its finite p-group filtration quotients, using 13.5.1 for their steps",
        "Fixed points 4.2.14, type preservation 1.5.13(3), the actual reduction and incident-facet/parabolic correspondence 8.4.19 with Chapter 9 descent; finite-field p-subgroup structure and the Iwahori-Tits system in G(k)^0",
        "The normalizer argument uses 2.2.16 and 6.3.21"
      ],
      "consumer_or_regression": "Check the exact ambient group in both maximality and normalization, including a case with nontrivial component or length-zero data. An abstract pro-p predicate does not supply the compactness, inverse limit or building fixed-point proof.",
      "formal_status": "proved",
      "publication_commits": [
        "ed924aef420de137b4cbaa3b063a3618afcd73fd",
        "410c79471b79f65a02fb0f6070da7f2800793ff3",
        "db940683e1d682d84831e8365720f1c79b5c9b0c"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.BruhatTits.MaximalProP.AvailableMaximalProPStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-13 at Library commit ed924aef; kind definition; statement_returns_prop true."
        },
        {
          "declaration": "Langlands.BruhatTits.MaximalProP.availableMaximalProP",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-14 at Library commit 410c7947; kind theorem, at universe level u, whose type is exactly AvailableMaximalProPStatement.{u}; the module was first published in this commit."
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
        "Later target: implement only after positive-depth acceptance has constructed finite abelian graded quotients, transported characters through the proved comparison and verified a nontrivial filtration calculation. No minimal K-type or supercuspidality theorem follows from this source row.",
        "Library status (thirty-seventh update): Definition 13.6.5 for g is published as IsCocharacterNilpotent and IsDegenerateLieCoset (KPNilpotentCoset, recorded in the Proposition 13.7.4 row). Definition 13.4.2 now has the predicate ValuationBuildingData.IsOptimalPoint on the reduced building (KPOptimalPoints, first published at 032961776f43ccd672c6266d265a9c644faeba13); it does not prove existence or Lemma 13.4.4. This row records no statement of Proposition 13.6.7. For the instability clause, KPLieGradedAction acts on graded pieces by a subgroup of G(F), with abstract normal-quotient factorizations under explicit hypotheses; it does not supply the algebraic Gred_x-action."
      ],
      "consumer_or_regression": "After positive-depth acceptance, test full-coset containment, the strict s>r inequality, the G_m/Q_2 zero coset at r=1 (degenerate, no literal optimal point, contained at depth 2, unstable), and the explicit contraction of the printed characteristic-two matrix. Use the k-cocharacter definition; any comparison with Jordan nilpotence needs a separate proof.",
      "formal_status": null,
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
        "r is real and Xi is a Lie coset in g_{x,r}/g_{x,r+}. Nilpotent means algebraically contracted to zero by a k-defined cocharacter G_m to G, as in 13.6.5. Degenerate means containing such an element. Instability refers to the algebraic Gred_x-orbit closure in the f-rational graded representation of 13.3.4. This is distinct from valuation-topology closure of a G(k)-orbit in g.",
        "Recorded Lean scope (part (1) for points of one apartment, on supplied Lie lattices): DegenerateCosetOfDeeperIntersectionStatement (module Langlands.Geometry.Building.KPDegenerateCosetStatement) quantifies over every nonarchimedean local field F, every G over Spec F with [IsAffineHom G.X.hom], every ParahoricBuildingData P of G, every LieFiltrationData L (supplied lattices z_r in Lie(Z) and u_psi in the root spaces, module Langlands.Geometry.Building.KPLieFiltration), all points x and y of the apartment and all real r < s. Neither the apartment axioms nor periodicity of L is assumed. For X in g_{x,r} (lieFiltrationReal, the real-depth extension of the Section 13.3.1 row), if some Y in g_{y,s} satisfies Y - X in g_{x,r+} (lieFiltrationPlusReal, the supremum of the g_{x,t} with t > r), it asserts IsDegenerateLieCoset g_{x,r+} X: some Y' with Y' - X in g_{x,r+} satisfies IsCocharacterNilpotent, that is, Y' lies in cocharacterPositiveLie nu, the sum of the weight spaces of Ad o nu with positive weight, for some homomorphism nu from G_m to G over F (KP Definition 13.6.5, module Langlands.Geometry.Building.KPNilpotentCoset). Under IsPeriodic, g_{x,r+} lies in g_{x,r} and X + g_{x,r+} is KP's coset in g_{x,r}/g_{x,r+}. For arbitrary L that inclusion can fail (the module's Markdown gives a G_m example), and the statement concerns the translate X + g_{x,r+} in Lie(G). Points y off the apartment and part (2), instability under the algebraic Gred_x-action, are not stated."
      ],
      "conclusion": "If there exist y in B(G) and real s>r with Xi intersect g_{y,s} nonempty, then Xi is degenerate. Also, Xi is unstable under the algebraic Gred_x-action if and only if Xi is degenerate. The first implication needs only an intersection, whereas the depth-raising clause printed in 13.6.7 asks for whole-coset containment and has the separate empty-root optimality obstruction recorded in its row. No local compactness or perfect-k hypothesis is added to this result; the perfect-residue/Henselian Chapter 13 setup is retained.",
      "lean_declarations": [
        "Langlands.Geometry.Building.DegenerateCosetOfDeeperIntersectionStatement",
        "Langlands.Geometry.Building.IsDegenerateLieCoset",
        "Langlands.Geometry.Building.IsCocharacterNilpotent",
        "Langlands.Geometry.Building.cocharacterPositiveLie"
      ],
      "modules": [
        "Langlands.Geometry.Building.KPDegenerateCosetStatement",
        "Langlands.Geometry.Building.KPNilpotentCoset"
      ],
      "dependencies": [
        "Lemma 13.7.3 proves g_{y,s} contained in g_{x,s}+N using an apartment displacement and its root-space decomposition, with N the cocharacter-defined nilpotent set",
        "Use only the separate instability clause of Proposition 13.6.7 for degenerate implies unstable, not its optimal-point assertion or an empty-root use of 13.4.4",
        "For unstable implies degenerate, Kempf's rational cocharacter theorem over perfect f gives a contracting f-cocharacter. Conjugacy of maximal f-split tori and the actual surjection P_x to Gred_x(f) lift it through a split o-torus. A small apartment translation raises the depth, and part (1) applies",
        "The additional perfect-k or locally compact hypotheses of nearby 13.7.2 concern the valuation-topology set N' and N=N', not the algebraic instability equivalence of 13.7.4. Register and read Kempf's original before a proof relies on that theorem directly",
        "Later target: implement only after positive-depth acceptance has constructed finite abelian graded quotients, transported characters through the proved comparison and verified a nontrivial filtration calculation. No minimal K-type or supercuspidality theorem follows from this source row.",
        "Recorded statement (thirty-sixth update, Library commit 5f5d3a91): DegenerateCosetOfDeeperIntersectionStatement (a statement), first in Library commit 5f5d3a914cd43b9dc1cd32c07887a973f561df96; the Definition 13.6.5 predicates IsCocharacterNilpotent and IsDegenerateLieCoset with cocharacterPositiveLie (a definition), first in Library commit b86269dd36757fdbea2e51976499d645ca61a625. The lattices lieFiltrationReal and lieFiltrationPlusReal are recorded in the Section 13.3.1 row. The expected proof follows Lemma 13.7.3 inside one apartment: it splits an element of g_{y,s} into a part in g_{x,s}, hence in g_{x,r+}, and root-space terms that a cocharacter of S near a lift of y - x contracts; the module's Markdown gives the argument, including negative depths. The statement has no proof; the positive-depth gate of the entry above applies to any proof."
      ],
      "consumer_or_regression": "After positive-depth acceptance, test intersection versus containment and distinguish algebraic residue-field orbit closure from valuation-topology G(k)-orbit closure. Preserve the actual reduction surjectivity used in lifting cocharacters.",
      "formal_status": "statement",
      "publication_commits": [
        "5f5d3a914cd43b9dc1cd32c07887a973f561df96",
        "b86269dd36757fdbea2e51976499d645ca61a625"
      ],
      "axiom_reports": [
        {
          "declaration": "Langlands.Geometry.Building.DegenerateCosetOfDeeperIntersectionStatement",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-19 at Library commit 5f5d3a91; kind definition, at universe level u, statement_returns_prop true; that commit first published the module."
        },
        {
          "declaration": "Langlands.Geometry.Building.IsDegenerateLieCoset",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-19 at Library commit 5f5d3a91; kind definition, at universe level u, statement_returns_prop true; the module was first published in Library commit b86269dd and is byte-identical between that commit and Library commit 5f5d3a91."
        },
        {
          "declaration": "Langlands.Geometry.Building.IsCocharacterNilpotent",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-19 at Library commit 5f5d3a91; kind definition, at universe level u, statement_returns_prop true; the module was first published in Library commit b86269dd and is byte-identical between that commit and Library commit 5f5d3a91."
        },
        {
          "declaration": "Langlands.Geometry.Building.cocharacterPositiveLie",
          "axioms": ["propext", "Classical.choice", "Quot.sound"],
          "scope": "Successful local declaration inspection on 2026-11-19 at Library commit 5f5d3a91; kind definition, at universe level u, a submodule-valued definition; the module was first published in Library commit b86269dd and is byte-identical between that commit and Library commit 5f5d3a91."
        }
      ],
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
        "Proposition 1.1.20 needs a complete NPC geodesic space and a nonempty closed convex base building. Its projection is unique, continuous and equivariant for isometries preserving that subset setwise. Corrections PDF p.2 prints the insufficient minimizing-sequence estimate d(y1,y2)^2<=2 epsilon(2r+epsilon), contradicted already by X=Y=R, x=0, r=0, epsilon=1 and y1,y2=+-3/4. Independently derive the sufficient bound with coefficient4 from the midpoint inequality. The added continuity proof needs the zero-distance case separately; the division-free bound d(pi(x_n),pi(x))^2<=2(q_n^2-r^2), with q_n=d(x,pi(x_n))->r=d(x,pi(x)), covers that case. These independently derived repairs are implemented in the published nearestPointProjection proof recorded in the Proposition 1.1.20 row. They are not authors' errata and do not construct the required building instance.",
        "For general k, 14.5.6 proves closedness and segment containment of the adapted-y locus. 14.7.1 makes the space of embeddings complete and NPC with evaluation-independent metric; 14.7.2 obtains an equivariant embedding assuming nonemptiness; 14.7.3 applies this to the maximal unramified extension and Chapter 9 descent. Neither convexity alone nor an assumed fixed point proves the needed nonemptiness",
        "Passing from a subgroup to a general homomorphism requires the 14.0 simple-factor lift condition: on every relevant simple factor the lift from G_sc to the simply connected cover of the image is trivial or an isomorphism onto its image. Use the faithfully flat quotient step of 14.1.1 and then the subgroup embedding. This does not give an injective or canonical map for every homomorphism.",
        "Release 1 constructions and its representation consumer, then positive-depth acceptance, precede Bundle F implementation. A source-only row is no formal or release acceptance."
      ],
      "consumer_or_regression": "Test all-translate full stabilizers after projection and after unramified descent, the induced metric choice and central-translation nonuniqueness. No arbitrary positive-depth filtration compatibility or canonical functor on all homomorphisms is claimed.",
      "formal_status": null,
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    }
  ]
}
```

## Bundle B: the complete certificate and its source map

The following table maps the ten axioms of corrected Definition 4.1.26
and the descent axiom to the source assembly in §9.5 and its supporting
results. Theorem `bruhatTitsCompletionCertificate` certifies these
conclusions in the nonarchimedean local-field scope of the structured row.

| Certificate item | Source route and boundary |
| --- | --- |
| 4.1.1 | Theorem 9.3.21, with apartments and facets constructed in §9.2. |
| 4.1.2 | The corresponding assertion for the constructed quasi-split group G_K. |
| 4.1.4 | Proposition 9.3.16. |
| 4.1.6 | AS1: 9.4.9; AS2–3: 9.4.19; AS4: 9.4.18; AS5: 9.4.35 and its preceding paragraph; AS6: 9.4.31. Apply the corrected inclusion of the identity in AS3. |
| 4.1.8 | Proposition 9.4.3 and Lemmas 9.4.6, 9.4.21. Part (2) retains a nonempty bounded subset. |
| 4.1.9 | Propositions 9.3.24–9.3.25, with the corrected restricted-building argument for 9.3.25. |
| 4.1.16 | The derived route through 9.6.5–9.6.6, corrected 4.4.5, 7.3.12 and 7.4.9, explained below; no separate paragraph for this axiom appears in the printed §9.5. |
| 4.1.17 | Each valued-field isomorphism and covering group isomorphism induce an equivariant isomorphism of reduced buildings. Proposition 7.9.5 gives this compatibility in the Chapter 7 construction, and §9.5 invokes it for the Gamma action. |
| 4.1.20 | Actual model descent in 9.2.5 and the integral-point identities in §9.5. Use 9.3.24 for the G(k)^0 intersection law; G(k)^1 has its own law. |
| 4.1.22 | Parts (1), (2), (7) descend geometrically; (7) uses perfect residue to descend the unipotent radical. Parts (3), (5) use facet correspondence and 9.4.31; (4) is 9.3.3; (6) is 9.4.23. |
| 4.1.27 | Fixed-locus and base-change constructions in §9.2, special tori from 9.3.4, and affine-root compatibility from 9.4.28. UR 4 gives the maximal-unramified base-change isomorphisms for both the full and neutral models and both fixer intersection identities. |

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
and Theorem 1.1.15. The fixed point is constructed from these metric inputs.

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

Writing A=pi_1(G)_I, the third quotient in 11.7.6 is recorded explicitly
as A^Gamma/(A_tor)^Gamma. This unpacks the torsion-free quotient of
A^Gamma, using torsion(A^Gamma)=(A_tor)^Gamma. It does not identify it
with (A/A_tor)^Gamma without a separate exactness argument. All of these
are source targets and dependency descriptions; no Kottwitz
construction, quotient bijection, Hecke distinctness or finite-support
theorem is proved by this note. The Library states the Kottwitz
homomorphism, selected by its characterizing property, and Lean
statements of these four targets (Library commit `0c3f30c2`); none of
them was proved at that commit.

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

The seventh update records a conditional implementation on supplied
models: the Section 13.2.6 row lists the reduction isomorphism, the
inflation, the kernel-invariant adjunction and compact induction with
Frobenius reciprocity. The kernel there is the radical preimage, not yet
compared with `P_{x,0+}`; finiteness, compactness and the intertwining
theorem remain open.

The tenth update records that `congruenceNeighborhoodBasis_proof` makes
the integral points of every supplied model over a local field compact
and open, and that `CompactInductionIntertwiningStatement` states the
intertwining theorem for compact induction from an open subgroup, with a
double-coset form for compact open subgroups; its proofs are open.
Finiteness of `Gred_x(f)` and the comparison with the actual `P_{x,0}`
remain open.

The twelfth update records the finiteness and topological parts of the
local-field consumer on supplied models. With a finite residue field,
the supplied quotient has finitely many residue-field points, which form
a finite group. Over a Henselian base the radical preimage has index
equal to their number, the supplied form of `[P_{x,0} : P_{x,0+}] =
|Gred_x(f)|`. Over a nonarchimedean local field the radical preimage
contains the level-one congruence subgroup and is a compact open
subgroup of `G(F)`. The tenth update's remark that finiteness of
`Gred_x(f)` is open no longer applies to supplied data; the comparison
with the actual `P_{x,0}` and `P_{x,0+}` remains open.

The fourteenth update records Lean statements of parts of the Chapter 8
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
seventh and tenth updates that the intertwining theorem is open no
longer apply; the comparison with the actual `P_{x,0}` and `P_{x,0+}`
remains open.

The seventeenth update records regression instances of the supplied-data
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

The twenty-first update records non-split and non-hyperspecial
regression instances. A norm-one torus `R¹_{E/F} G_m` with a finite free
integral form `B` whose norm-one kernel is smooth and whose special
fibre over `𝓀[F]` is a field `k'` has a torus special fibre, the
norm-one torus of `k'` over `𝓀[F]`, so the identity quotient is
reductive and the depth-zero index is the number of norm-one units of
`k'`. Both hypotheses are supplied; smoothness alone does not make the
special fibre a torus. Over every local field an unramified quadratic
instance exists, with index `q+1`. The published decomposition criterion
gives smoothness only for integral forms that split after a faithfully
flat base change; the trace criterion needs only an element of trace
one, which exists whenever the rank is a unit of the base, whether or
not the form is étale. It proves smoothness only: the field special
fibre, and with it the torus special fibre and the identity reductive
quotient, must still be supplied. For `GL_N`, the standard Iwahori
subgroup is the preimage of the Borel subgroup of the special fibre, as
in Theorem 8.4.19(3), and its quotient by the preimage of the unipotent
radical is the diagonal torus, the reductive quotient at a chamber by
Theorem 8.4.10(2); no Iwahori model data is constructed. Regression
instances with a multipliable root or a nontrivial component group
remain open.

The twenty-third update records progress on the Chapter 8 statements.
For the root datum of Theorem 8.4.10, the descended facet statement is
proved on supplied data. For Theorem 8.3.2 the `G(K)^1_Ω` model is
constructed for every supplied building datum, and the comparison of its
relative identity component with `G(K)^0_Ω`, the content of Theorem
8.3.13, is reduced to the torus case of Appendix B: the connected Néron
model of a torus has the Iwahori subgroup `T(K)^0` as its integral
points (Corollary B.8.7), which published theorems reduce in turn to
four focused torus statements. For Theorem 8.4.19 the kernel statement
is reduced to smoothness and connectedness of the kernel in a special
case, and the parabolic-image statement to that, the positive-radical
inclusion of Corollary 8.4.12 and a singleton form of radical
generation. The ramified quadratic norm-one torus `R¹_{E/F} G_m`, `E =
F(√ϖ)`, gives a regression for a disconnected special fibre: the
residue-field points of the special fibre are the `x + yα` with `α^2 =
0` and `x^2 = 1`, in two classes `x = ±1`; every point of `T(F)` is
integral, and those reducing into the class `x = 1` form a subgroup of
index `2`. This agrees with corrected Remark 2.5.15, but no Lean
declaration identifies the subgroup with KP's `T(F)_0`.

The twenty-seventh update completes the `GL_N` Iwahori regression at the
level of models. The unit group of the standard Iwahori order `Λ`, the
integral matrices whose strictly lower entries lie in the maximal ideal,
is a smooth integral model of `GL_N` whose integral points are the
Iwahori subgroup `I`. Its special fibre is the unit group of `𝓀 ⊗ Λ`;
reduction to the diagonal `𝓀^N` has a section, and its kernel `1 + J`,
with `J` spanned by the images of the scaled off-diagonal matrix units,
is unipotent by a weight argument. So the maximal reductive quotient is
the diagonal torus, as Theorem 8.4.10(2) gives at a chamber, and the
preimage of the radical is `I^+`, the preimage of the upper unipotent
group. Nothing identifies this model with KP's parahoric model at a
point of a chamber. The model statement of Theorem 8.3.13 now follows,
through published theorems, from connected generation (Lemma A.4.26)
alone.

The twenty-eighth update records the root-group case of the kernel and
the depth-zero theory of the Iwahori model. KP Lemma C.5.3 says that for
depths `s ≥ r` the kernel of the special-fibre map between the
root-group models at depth `s` and depth `r` is smooth, connected and
unipotent, and the proof of Proposition 8.4.15 applies it to each factor
of the kernel product. Its Lean form on supplied root models is proved
for every relative root none of whose multiples `n • a`, `n ≥ 2`, is a
root. For multipliable roots it is proved from valued unitary
coordinates `R_{E/K} U_{L/E} → U_b`, following KP Proposition C.5.1 and
Lemma C.4.4; the existence of those coordinates is unproved. Published
chart theorems assemble the factors into the ambient kernel from torus
and root model families, ordered charts and a range condition. Published
results construct such families with open charts, conditionally on the
unproved connected torus bound (KP Corollary B.8.7), and prove the range
condition from an ordered fixer factorization that is itself proved in
the open-cell order; no published declaration yet combines them into the
smooth connected kernel statement. On the actual Iwahori model and
quotient data of `GL_N`, the general depth-zero theory gives `I/I^+ ≅
(𝓀ˣ)^N` compatibly with the residue diagonal and `[I : I^+] = (q −
1)^N`, the values KP 13.2.6 predicts at a chamber, and shows that `I`
and `I^+` are compact open; the model is still not identified with KP's
parahoric model.

The thirtieth update records Theorem 8.4.19 for the simplest incident
pair of `GL_N`, the standard alcove `F'` and its hyperspecial vertex
`F`. The inclusion of the Iwahori order `Λ` into `M_N(𝒪)` induces a
model map from the Iwahori model to `GL_{N,𝒪}` that is the identity on
generic fibres. On special fibres its kernel is `1 + J_-`, where `J_-`
is spanned by the classes of the scaled strictly lower matrix units
`ϖE_ij` in `𝓀 ⊗ Λ`, so it is smooth, connected and unipotent; its image
is the upper triangular Borel subgroup; and the integral matrices that
reduce into that subgroup form `I`. Together with the inclusion of the
principal congruence subgroup in `I^+`, these give parts (1)–(3) of the
theorem, except the product description of the kernel, together with the
parabolicity of `℘_F(F')` and the inclusion of Corollary 8.4.12 at that
pair. The models are still not identified with KP's parahoric models.
The same update records that KP Lemma C.5.3 is now proved for every
relative root: valued unitary coordinates of the multipliable root
groups exist, so the reduction recorded by the twenty-eighth update
applies. On the chart route to the kernel statement, the construction of
families with open charts remains conditional on the unproved connected
torus bound, and no published declaration assembles the factors into the
kernel statement.

The thirty-second update records proofs, for all supplied data, of
`UnramifiedParahoricModelStatement` (Theorems 8.3.2 and 8.3.13), the
three statements of the Corollary 8.4.12 row and the kernel,
common-torus and parabolic-order statements of Theorem 8.4.19; its
parabolic-image statement follows from published proofs that no
published declaration composes. For Theorems 8.3.2 and 8.3.13, the model
of `G(K)^1_Ω` and its relative identity component with points `G(K)^0_Ω`
exist, since connected generation (KP Lemma A.4.26) and the torus inputs
are proved. For Corollary 8.4.12, the Axiom 4.1.22(7) inclusion holds,
and the radical preimage of a nonempty subset of one facet is generated
by the positive root groups `U_{a,Ω,0+}` and one subgroup, chosen before
the subset and not identified with the image of `T(K)^{mc}_{0+}`. For
Theorem 8.4.19, the connected torus bound is proved, so the integral
open cells exist for all supplied data, and the proof of
`unramifiedModelKernel` assembles the chart route into the kernel
statement; the facet tori are common and the parabolic order holds. The
building data and models are still supplied rather than built from the
actual building; the dagger model and the product description of the
kernel have no Lean statement, and `G(K)_{Ω,0+}` itself has no Lean
definition.

## Bundle E: filtrations, comparison alternatives and later instability

This bundle now has eleven rows: Proposition 13.2.5, Sections 13.3.1–4,
Definitions 13.4.1–13.4.2, Theorem 13.5.1, corrected Proposition 13.5.2,
and the later Propositions 13.6.7 and 13.7.4. The nine original rows
were source-only when the bundle was first recorded. Positive-depth
implementation remains behind the depth-zero release and its
inflation/compact-induction consumer. The seventh update records a
published statement of Proposition 13.2.5 on supplied data, the eighth
update adds its part (3), and the ninth adds parts (5) and (6) and a
double-root restatement of parts (1), (2) and (4). The sixteenth update
records that every part is proved on supplied data, parts (1), (2) and
(4) with the double-root premise, so that row is `conditional`.
Corrected Proposition 13.5.2 has the published statement
`AvailableMaximalProPStatement`; the eighteenth update records its proof
`availableMaximalProP` on available data, so that row is `conditional`.
The thirty-second update records that the Lie lattice of a supplied
smooth integral model is a lattice (Section 13.3.1) and that the
integral points of a supplied integral model preserve its Lie lattice
under the adjoint action (Section 13.3.4), so those two rows are
`conditional`. The thirty-fourth update records a partial published
statement of part (1) of Theorem 13.5.1 on supplied data, so that row is
`statement`. The thirty-fifth update records that `g_{x,0}/g_{x,0+} ≅
Lie(Gred_x)` holds for supplied integral-model and reductive-quotient
data, with `g_{x,0+}` identified with the Lie lattice of a supplied
model only under hypotheses (Section 13.3.2, `conditional`); that KP's
intrinsic span description of `g_{x,r}` is a published definition on
supplied lattices (Section 13.3.3, `definition`); and that the
filtration, its extension to real depths under a periodicity hypothesis
and the dual lattices are defined on those lattices (Section 13.3.1).
The thirty-sixth update records a partial published statement of part
(1) of Proposition 13.7.4 on supplied Lie lattices, so that row is
`statement`. The thirty-seventh update expands the scope of Sections
13.3.1, 13.3.3 and 13.3.4 on supplied data and adds the two
optimal-point definition rows. Proposition 13.6.7 remains source-only.
The two instability targets remain behind the separate positive-depth
acceptance test.

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

The eighth update records `MoyPrasadProductStatement` (first published
in Library commit `63d9b857523edf47443b7bf30844159e526d00b0`), which
states this route on supplied data. For r > 0, a positive system given
by a generic cocharacter and injective enumerations of the indivisible
roots of each sign, the ordered product of the negative blocks
`U_{a,x,r} U_{2a,x,r}`, the full factor `Z(F)_r` and the positive blocks
is a bijection onto `P_{x,r}`. Proposition 7.3.12(5) has the factor
`Z♯_{x,r}` and the target `G(k)♯_{x,r}` instead. The statement's
Markdown derives the full-filtration form from Proposition
7.3.12(3)–(5), the proof of Lemma 7.3.16 (`Z♯_{x,r} ⊆ Z(k)_r`), V 6,
Definition 7.3.3(3) and the open cell of Proposition 2.11.3(2). For
`G_m`, `Z♯_{x,r}` is trivial while `Z(k)_r`, which equals `P_{x,r}`, is
not. The proof obligation stays open until a proof of the statement is
published.

The ninth update records `MoyPrasadLeviStatement` (first published in
Library commit `6bff2655fd831aefb39f6688f904aa7410cb0f73`) for parts (5)
and (6). Its Markdown derives both parts from part (3) as in the proof
on PDF p.500, with the roots of the Levi innermost in the ordered
product and the open cell of Proposition 2.11.3(2). Definition 13.2.4(2)
prints the first inclusion as `aN^+a^{-1} ⊂ N`, which holds for every `a
∈ A_M(k)` since `A_M` normalizes `N`; the statement uses `aN^+a^{-1} ⊂
N^+`, the analogue of the printed second inclusion `a^{-1}N^-a ⊂ N^-`.
This is a derived reading, not an authors' erratum.

The sixteenth update (13 November 2026) records both proofs on supplied
data. `moyPrasadProduct` (Library commit `cfedefb6`) proves
`MoyPrasadProductStatement` by combining
`orderedMoyPrasadProduct_injective` and
`range_orderedMoyPrasadProduct_eq`. This discharges the part (3)
obligation in its indivisible-root block form; the printed all-root form
is not claimed. `moyPrasadLevi` (Library commit `cc5aa77f`) proves
`MoyPrasadLeviStatement` and takes the ordered covering from
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

The ninth update records `MoyPrasadDoubleRootStatement` (first published
in Library commit `297a8ef0ba780a488196cf62285af3ded2e2baa6`). Its
predicate `IsDoubleRootCommutatorFriendly` asks for `Z(F)_{2r}` when `u
∈ U_{2a}(F)` or `u' ∈ U_{-2a}(F)`; the statement restates the published
covariance and commutator statements with it as an extra premise, and
`CentralizerFiltrationDoubleRootExistenceStatement` asserts a filtration
satisfying it. The original statements are not withdrawn: no
counterexample is known, but their premises do not include the bound and
no derivation of them from the published filtration axioms is known. The
Markdown derives the bound for the actual Section 9.8 filtration. This
is a source-derived reading, not an authors' erratum. The published
`isMoyPrasadAt_unique_of_double_opposite_bound` (module
`MoyPrasadCovarianceReduction`, Library commit `297a8ef0`) proves the
conclusion of the original covariance statement from its premises and
the single mixed case `U_{a,x,0}` against `U_{-2a,x,r}`, so the gap in
parts (1) and (2) is exactly this case.

The eleventh update (13 November 2026) records that the gap is real for
supplied filtrations. An unformalized paper argument gives a
counterexample: ramified quasi-split SU(3) over `Q_2`, split by
`Q_2(√2)`, with the smallest centralizer filtration `Z'` satisfying the
four published filtration axioms (decreasing, separated, `Z'_0 =
Z(F)^0`), assuming the actual building data satisfy the apartment
axioms. The pair `u(0,√2) ∈ U_{2a,x,1/2}`, `u⁻(2,-2) ∈ U_{-a,x,1/2}` has
a commutator with `Z`-component `t(1-2√2) ∉ Z'_1`, so
`MoyPrasadCommutatorStatement` fails; conjugating `u(0,√2)` by `u⁻(√2,1)
∈ U_{-a,x,0}` gives `Z`-component `t(1+√2) ∉ Z'_{1/2}`, so
`MoyPrasadCovarianceStatement` and `MoyPrasadFiltrationStatement` fail.
`Z'` violates `IsDoubleRootCommutatorFriendly`, so the double-root
statements are not affected, and KP's own filtration of `T(k)` is not
refuted (for odd `p` the smallest filtration equals it). The original
statements remain published as recorded targets; they have no proofs,
and the double-root statements carry the covariance and commutator
content. The argument is the note
`notes/bruhat-tits/moy-prasad-supplied-filtration-counterexample.md`,
present in Library commit `4b619cdd`.

The sixteenth update records that `moyPrasadDoubleRootCovariance` and
`moyPrasadDoubleRootCommutator`, both first in Library commit
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
over K, and an intrinsic span using the centralizer lattice and
affine-root lattices with `psi(x)>=r`. Its explicit Chevalley–Steinberg
basis formula over o requires G quasi-split; the general model/lattice
and intrinsic span constructions have no such extra hypothesis. Section
13.3.4 obtains actual f-rational representations of Gred_x on the Lie
and dual strict graded pieces from model conjugation. Descent and
factorization through Gred_x remain construction and proof obligations.
For a supplied integral model its integral points preserve its own Lie
lattice, the depth-zero result at the level of points. On supplied Lie
lattices the rational points preserving the filtration act on its strict
graded pieces. The abstract quotient actions have separate stabilizer,
normality and triviality hypotheses (Section 13.3.4). In particular they
do not provide the algebraic reductive-quotient representation needed for
instability.

The formalizations recorded in these rows take the models as supplied
data. For Section 13.3.2, `g_{x,0+}` is defined intrinsically as the
inverse image of `Lie(R_u)` under reduction, and it equals the Lie
lattice of a supplied model under hypotheses standing for Section
13.2.6, Proposition 8.5.18 and `m g_{x,0} ⊂ g_{x,0+}`. For Sections
13.3.1 and 13.3.3, `g_{x,r}` is defined from supplied lattices `z_r` and
`u_psi` by the intrinsic span, and the periodicity used to extend it to
real `r` is a hypothesis.

At opposite depths r and −r, periodicity makes evaluation integral and
gives a residue pairing. Its surjectivity and right nondegeneracy use the
lattice property at −r; its left kernel is the deeper dual piece under
left continuity at −r. A sufficient criterion for the latter uses opposite
factor pairs, periodicity and left continuity of the supplied centralizer
family at positive depths. The pairing is invariant under the rational
filtration stabilizer; this is not algebraic equivariance of a constructed
model action. Under the three hypotheses together, the dual grade at r is
identified with the residue-field dual of the Lie grade at −r, both grades
are finite, and the identification intertwines the stabilizer actions.
Under periodicity and finite generation at depth zero, the jump depths of
finitely many apartment points form a closed discrete subset of ℝ.

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

The published `MoyPrasadIsomorphismStatement` (Theorem 13.5.1 row)
states the abstract quotient isomorphism in part (1) over the base
field. It assumes `MoyPrasadAlternative`, a supplied centralizer
filtration and Lie lattices, and the isomorphisms for the centralizer
and each nondivisible root block. It retains the filtration axioms and
double-root commutator premise. At the Library pin,
`minimalCongruentPoints` defines the torus point filtration at finite
nonnegative depths, and `minimalCongruentCongruence` proves its
congruence shift. Specializing the supplied-data statement requires
the corresponding component isomorphisms on the chosen filtrations.

### The ambient group in corrected Proposition 13.5.2

This proposition additionally assumes that k is a local field with
finite residue of characteristic p. The authors' correction changes the
ambient group in part (1) to `G(k)^0`. Each `P_{x,0+}` is an open pro-p
subgroup there, maximal exactly for chamber points. Every maximal open
pro-p subgroup of `G(k)^0` is the positive-depth subgroup of an Iwahori,
which is its normalizer in `G(k)^0`. Neither assertion extends here to
the full `G(k)`. The source proof uses actual compactness, finite
filtration quotients, fixed points, type preservation, reduction and the
rational parabolic correspondence. The published
`Langlands.BruhatTits.MaximalProP.AvailableMaximalProPStatement` states
the four conclusions over facets of `B(G)`, with `G(F)^0` as ambient
group throughout, for every available `KPBuildingAssignment`
(Proposition 13.5.2 row). The theorem `availableMaximalProP` (Library
commit `410c7947`) proves it. It proves the normalizer identity at one
apartment chamber from the Iwahori factorization and the split
Tits-system normalizer theorem, and transports it to every chamber by
conjugation in `G(F)^0`. The validity clause of
`bruhatTitsCompletionCertificate` supplies availability for its descended
assignment, so `availableMaximalProP` applies on that assignment.

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

The literal rationality and optimality predicates are now defined in
KPOptimalPoints. The empty-affine-root obstruction is proved for any
supplied valuation building. This does not construct the chosen family of
optimizers or prove Lemma 13.4.4. The chapter's positive-indecomposable
generator rule for rational affine functionals is kept separate from the
Chapter 1 wall-root convention.

Separately, the [split type A₂ paper
calculation](kp-optimal-depth-scope.md) shows that the union of Lie jump
depths over all Definition 13.4.2 points need not be discrete. This rules
out that reading of the discreteness sentence following the construction
of O. The calculation is not Lean evidence and does not affect the
existence assertion of Proposition 13.6.7.

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

The published `DegenerateCosetOfDeeperIntersectionStatement`
(Proposition 13.7.4 row) states part (1) for points `x` and `y` of one
apartment and the real-depth lattices of the Section 13.3.1 row, with
nilpotence and degeneracy given by the published Definition 13.6.5
predicates `IsCocharacterNilpotent` and `IsDegenerateLieCoset`. If `X`
lies in `g_{x,r}` and the translate `X + g_{x,r+}` meets `g_{y,s}` for
some `s > r`, the translate contains a nilpotent element. Under the
periodicity hypothesis `IsPeriodic`, `g_{x,r+}` lies in `g_{x,r}` and
the translate is KP's coset in `g_{x,r}/g_{x,r+}`. For arbitrary
supplied lattices that inclusion can fail, and the statement concerns
the translate in `Lie(G)`. Part (2) and Proposition 13.6.7 have no Lean
statement: the Library has no algebraic action of `Gred_x` on the graded
pieces and no optimal points.

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

This proves continuity also when r=0 without division by r. Equivariance
follows from uniqueness and the inverse isometry. The published
`nearestPointProjection` proof implements these repairs using the
squared deficit directly and a neighborhood-filter continuity argument.
They do not change the theorem statement and remain independent repairs,
separate from the authors' errata. The proof and publication evidence
are recorded below and in the Proposition 1.1.20 row.

## Verified Theorem 1.1.15 proofs

The theorem `Langlands.Geometry.Metric.KP.barycenter` proves the exact
published `BarycenterStatement`: existence, uniqueness and invariance of
the barycenter of a bounded closed nonempty geodesically convex set. The
theorem `Langlands.Geometry.Metric.KP.boundedSetStabilizerFixedPoint`
proves `BoundedSetStabilizerFixedPointStatement`: one point is fixed
simultaneously by every isometry preserving a given nonempty bounded
set. Both targets quantify over arbitrary carrier universes and complete
NPC geodesic metric spaces. Part (2) imposes no closedness or convexity
on the original set and does not require the fixed point to belong to
it.

The barycenter proof uses a squared midpoint estimate and a Cauchy minimizing
sequence, including radius zero and attained minima. The second proof
establishes covariance of the actual closed convex hull under isometries and
applies the first theorem to that hull. The paired proof explanations are
[KPBarycenterProof](../../Langlands/Geometry/Metric/KPBarycenterProof.md) and
[KPBoundedSetStabilizerProof](../../Langlands/Geometry/Metric/KPBoundedSetStabilizerProof.md).

Both proofs were checked by a Lake build against the exact target, with
the statement and its inputs unchanged, and first appeared in the
Library commit recorded in the row; their Lean/Markdown files, as first
checked, agree with that commit. Local declaration inspections report
only `propext`, `Classical.choice` and `Quot.sound`. No external Lean
code is adopted by these proofs.

This verifies both parts of the source theorem recorded in the row. The
separate bounded-action and nearest-point proofs are recorded next. Applying
these metric theorems to a general reductive-group building still requires
that building's construction, completeness and NPC proofs.

## Verified bounded-action and nearest-point proofs

The theorem `Langlands.Geometry.Metric.KP.boundedActionFixedPoint`
proves the exact published `BoundedActionFixedPointStatement` for
independent universes of the metric carrier and acting group.
Completeness and the primitive NPC condition yield geodesics through the
published `completeNPCGeodesic` theorem. The proof then applies the
bounded-set stabilizer theorem to the actual orbit and shows that every
group element acts by an isometry preserving that orbit setwise. The
result is one common fixed point of the original action. Its paired
explanation is
[KPBoundedActionFixedPointProof](../../Langlands/Geometry/Metric/KPBoundedActionFixedPointProof.md).

It was checked by a Lake build against the exact target, with the
statement and its inputs unchanged, and first appeared in Library commit
`7543113c99690e18b45f3b22d252e8cf77c3964e`; the pair, as first checked,
agrees with that commit. This focused proof establishes Corollary
1.1.19. The aggregate proof built on it is recorded separately below.

The theorem `Langlands.Geometry.Metric.KP.nearestPointProjection` proves
the exact published `NearestPointProjectionStatement` in arbitrary
carrier universe. A minimizing sequence for the real distance infimum
converges to a point in the closed convex subset. The squared midpoint
deficit proves minimality, uniqueness and division-free continuity, and
distance preservation gives equivariance of the same chosen projection
under every preserving ambient isometry equivalence. This includes
unbounded subsets, attained infima and zero minimum distance. Its paired
explanation is
[KPNearestPointProof](../../Langlands/Geometry/Metric/KPNearestPointProof.md).

It was checked by a Lake build against the exact target, with the
statement and its inputs unchanged, and first appeared in Library commit
`7a2e42fd31831029d34cafb155ffad911920df25`; the pair, as first checked,
agrees with that commit. This proves the qualitative Proposition 1.1.20,
including the independent proof repairs above, while the building and
Bundle A obligations remain open.

## Verified aggregate metric fixed-point interface

The theorem `Langlands.Geometry.Metric.KP.metricFixedPointFoundation`
proves the exact published `MetricFixedPointFoundationStatement.{uX,
uG}` by conjunction introduction from the six published component
proofs: geodesic uniqueness, closed-ball convexity, the closed convex
hull, barycenters, bounded-set stabilizer fixed points and
bounded-action fixed points. The first three retain their NPC and
geodesic premises; the next two additionally require completeness; the
last requires a nonempty complete NPC space and constructs its
geodesics. The aggregate assumes none of these statements as an input
and preserves the independent metric-carrier and group universes. Its
implementation is described in
[KPMetricFixedPointFoundationProof](../../Langlands/Geometry/Metric/KPMetricFixedPointFoundationProof.md).

It was checked by a Lake build against the exact target, with the
statement and its inputs unchanged, and first appeared in Library commit
`286dd3b743f0437d22db0e793222073b9424e3eb`; the pair, as first checked,
agrees with that commit. A local declaration inspection reports `uX` and
`uG` and only `propext`, `Classical.choice` and `Quot.sound`. No
external Lean implementation is adopted.

This is an internal aggregate of the existing metric statements, not a further
source theorem or a new structured row. It closes the aggregate proof obligation.
The actual reductive-group building and the proofs of its completeness and
nonpositive curvature remain required before applying this interface to it.

## Initial interfaces and the next mathematical gates

The module `Langlands.Geometry.Metric.KPDefinitions`, namespace
`Langlands.Geometry.Metric.KP`, first appeared in Library commit
`6fd0709bd33fa6c33b4d74b4b638cfc51428b8f1`. The module uses a primitive
midpoint inequality and separates geodesic existence, completeness,
convexity and barycenters. Its radius and joint diameter take values in
the extended nonnegative reals; finite real readings require explicit
boundedness and nonemptiness. This definition publication supplied the
interface used by the subsequent Theorem 1.1.15 proofs above.

The corrected convexity predicate excludes the empty set. The published
Theorem 1.1.15 proofs establish actual barycenter existence and uniqueness,
including radius-zero cases, and the common fixed point for bounded-set
stabilizers. The published Corollary 1.1.19 proof now supplies an actual
common fixed point for every bounded isometric group action under its metric
hypotheses. Proposition 1.1.20 supplies the projection for the same metric
foundation. The building application must still prove completeness and
nonpositive curvature of the constructed building.

The derived quotient prerequisite asks for the actual algebraic
quotient, its group action, apartment embedding criterion and exact
stabilizer formula from an explicit covariant subgroup family. It also
asks for comparison maps under a universally quantified subgroup
inclusion. This is a conditional construction prerequisite. A parahoric
family and the full quotient point stabilizer need not coincide. It must
retain the normalizer's point stabilizer, exhibit a proper-containment
example, and avoid inferring a building isomorphism from quotient
surjectivity alone.

Dynamic parabolics, centralizers, unipotent groups and general algebraic
open cells belong to the algebraic-group formalization in
`Langlands/GroupScheme/`. Its published
`Langlands.GroupScheme.Dynamic.Basic` interface is a reuse input, not by
itself a proof of every assertion of Propositions 2.11.1–3. General open
cells require the source's scheme-theoretic open immersion, beyond an
assumed product map or a split matrix instance. A verified reuse bridge
remains required for the complete source targets in the ledger.

The common field interface remains Mathlib's
`IsNonarchimedeanLocalField`.
`Langlands.LocalField.ResidueNormalization` and the existing canonical
`Langlands.PadicField` realization are reuse inputs. The field
prerequisite asks for an actual Laurent-series fixture over every finite
field, residue and normalization comparisons, negative monomial
calculations and a characteristic-two test; stating it supplies no field
theorem. Generic topologies and compact/open integral-point results
belong to the Conrad program (see `notes/conrad-adelic/`); the KP
program constructs its specific models and later proves the comparisons.

## Verified finite separable-unramified prerequisite

The published theorem
`Langlands.LocalGalois.Separable.separableUnramified` proves the exact
`Langlands.LocalGalois.Separable.SeparableUnramifiedStatement.{u}`. Its
implementation and source correspondence are described in
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
The auxiliary modules construct the closed-fiber residue map and spectral
residue-tower comparisons and prove the criteria used in this composition.

| Published module | First appeared at Library commit |
| --- | --- |
| Finite spectral arithmetic, `Langlands.Galois.Local.SeparableUnramifiedFiniteArithmetic` | `428fa7c08e2fd98ecc08fa4e170f793c3c868556` |
| Spectral residue comparisons and inertia criterion, `Langlands.Galois.Local.SeparableUnramifiedGaloisProof` | `3c03a45ac21fd6b32cc3c822e5a641caace16a2b` |
| Exact finite maximality and exhaustion proof, `Langlands.Galois.Local.SeparableUnramifiedProof` | `0bafb17fad89ec0e812a3746bcaf72be623fc7d3` |

The full Lean/Markdown pairs were read; as first checked, they agree
with the commits above, and the final pair also matches Library
`690e7bce992fb723bd66806fa2db3acd6dc07d78`. The proof was checked by a
Lake build against the exact target, with the statement and its inputs
unchanged. A declaration inspection succeeds with zero diagnostics,
universe parameter `u`, and only `propext`, `Classical.choice` and
`Quot.sound`.

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

The complementary theorem `separableUnramifiedArithmetic` proves residue
algebraic closure, value-group discreteness, the DVR structure and
Henselian arithmetic of the infinite fixed field. The finite theorem
applies without completeness or local compactness of that infinite
field. The descended building and its axioms enter through
`bruhatTitsCompletionCertificate`, as recorded in the Theorem 9.2.7 row.

## Verified chamber and Iwahori–Weyl statements

Two source rows record the published **statements** below; the fifth
update adds the proof of the first and of part (4) of the second. The
complete Lean/Markdown pairs were checked; each of the four primary
files, as first checked, matches Library commit
`25b91125ea94e88d741b206d633e82eb0d87c3e5`. The original passages are
Corollary 7.4.9 and its setup at book PDF pp. 286–288, Theorem 7.8.1 and
7.8.2 at pp. 303–304, and corrections PDF pp. 33, 35–36. The corrected
Chapter 7 premise AS5 remains explicit.

| Published statement pair | First appeared at Library commit |
| --- | --- |
| `Langlands.Geometry.Building.ChamberIwahoriStatement` | `25b91125ea94e88d741b206d633e82eb0d87c3e5` |
| `Langlands.Geometry.Building.IwahoriWeylStatement` | same commit |

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
row, at universe `u`, as well as the companion chamber-splitting,
Iwasawa and replaced-coset targets. All quantify over supplied actual
building data. The normalities needed to form the component group maps
are conclusions where required. The equivalences are prescribed on every
normalizer representative. Corrected part (2) still needs chamber
splitting and the Iwahori–Tits Bruhat decomposition: the equality `I ∩
N(F) = Z(F)^0` alone does not prove double-coset injectivity. The added
part (4) retains both quotient bijections and the explicit Chapter 5
Henselian and perfect-residue hypotheses. Its actual unipotent group is
`standardUnipotentPoints P.i ν ∅`. Its comparison with the single
dynamic unipotent group used by the chamber products was then open. The
Library has since proved it for every cocharacter, generic or not
(`standardUnipotent_empty_eq_dynamic`; see the fourth update). This
update changes only the Corollary 7.4.9 and Theorem 7.8.1 rows. The
Chapter 5 rows (5.3.3 and replaced 5.3.5 from this module, 5.2.1 and
5.3.4 from the `Langlands.BruhatTits` statements) are recorded by the
second update of the 8 November 2026 refresh.

The following focused targets are separate proof obligations. All
unqualified global targets below belong to
`Langlands.Geometry.Building`; the chamber targets belong to its
`ParahoricBuildingData` namespace.

| Exact target or targets |
| --- |
| `ChamberIwahoriDecompositionStatement` |
| `ChamberIwahoriCompactOpenStatement` (separate target) |
| `IwahoriWeylExactSequenceStatement`, `IwahoriWeylChamberSplittingStatement` |
| `IwahoriDoubleCosetStatement`, `ParahoricDoubleCosetStatement` |
| `IwasawaDecompositionStatement`, `UnipotentNormalizerCosetStatement` |
| `UnipotentIwahoriDoubleCosetStatement` |
| `Langlands.BruhatTits.Iwasawa.AvailableIwasawaStatement` |
| `Langlands.BruhatTits.Cartan.AvailableCartanStatement` |

A proof of `IwasawaDecompositionStatement` on supplied data has since
been published (Theorem 5.3.3 row). `UnipotentNormalizerCosetStatement`
is now proved by `unipotentNormalizerCoset`, present in Library commit
`17dd94ea3f677b20fb5ab95b285cbc3fd7cde03e`, from the two proved inputs
of its published reduction (Lemma 5.3.5 row). Proofs of three other
targets in the table were first published in Library commit
`e449cde988d4e97ab280b8d4d11262887ccc26e0`:
`ChamberIwahoriDecompositionStatement`,
`UnipotentIwahoriDoubleCosetStatement` and `AvailableIwasawaStatement`.
The Corollary 7.4.9, Theorem 7.8.1 and Theorem 5.3.4 rows record them.
The proof `availableCartan` of `AvailableCartanStatement` was first
published in Library commit `d39b5aee822fe2ad1aadf07861ebd9a4c2df62a8`;
the Theorem 5.2.1 row records it.

A separate compile checked both statement modules and their companion
modules without errors or warnings. The local-field assignment used
to apply the results on available data comes from
`bruhatTitsCompletionCertificate`. The Section 13.2.6 row gives the
depth-zero representation consumer on that assignment.

## Building and model regression statements

`GeneralLinearTreeStatement` states the tree property for the reduced
building of `GL₂` and its identification with lattice classes.
`DepthZero.GeneralLinearStatement` states the vertex and chamber model
comparisons, their reductive quotients and the vertex stabilizer comparison
for `GLₙ`. `GeneralLinearLengthZeroStatement` states the extended
Iwahori–Weyl component description for the chain rotation of `GLₙ`.
These comparisons connect the group-valid building data to the integral
lattice and Iwahori models.
[Tree](../../Langlands/Geometry/Building/GeneralLinearTreeStatement.md)
[Parahorics and quotients](../../Langlands/Geometry/Building/DepthZero/GeneralLinearStatement.md)
[Length zero](../../Langlands/Geometry/Building/GeneralLinearLengthZeroStatement.md)

`KPTorusRegressionStatement` distinguishes the reduced point from the
enlarged central directions, and specifies the parahoric and component
comparisons for split tori and unramified and ramified quadratic norm-one
tori. `SU3Regression.ComponentData` states the equality of the full,
zero and one subgroups and the triviality of the length-zero part for the
quasi-split special unitary group of a separable quadratic extension.
`SU3Regression.RootsAndBuilding` states its multipliable-root and affine-root
descriptions, tree incidence and depth-zero quotients in both ramification
cases.
[Tori](../../Langlands/Geometry/Building/KPTorusRegressionStatement.md)
[Unitary component data](../../Langlands/Geometry/Building/SU3Regression/ComponentData.md)
[Unitary roots and building](../../Langlands/Geometry/Building/SU3Regression/RootsAndBuilding.md)

These modules state the comparisons on building data. The completion
certificate supplies group-valid data in their field scope. The comparisons
are separate propositions, with the explicit integral-model proofs recorded
where they enter the Section 13.2.6 row.

## Trust and scope of the proofs

At Library commit `2f86a99eb5616254ac5b9c399603c9bbbea15f7a` the Lean
4.35.0 environment uses Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
Declaration inspection of `bruhatTitsCompletionCertificate` and
`depthZeroConsumer` reports `propext`, `Classical.choice` and `Quot.sound`.
The checked application of `availableMaximalProP` uses the certificate's
own assignment. The theorem-level inspections concern the named proofs.
An inspection of a Prop-valued definition covers the elaboration of its
statement.

The Theorem 8.3.2 row records the provenance of the `SubHopf` helper used
by `finiteIndexEnlargement`. It was adapted from Anthropic FLT commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` under the Apache License 2.0
and enters through the Library dependency. The metric and declaration
inspections in earlier sections use the environments recorded with those
checks.

The certificate and the facet consumer give the general local-field
construction and the depth-zero conclusions stated above. The
real-depth quotient comparisons of Theorem 13.5.1, tame descent and
embedding theorems, and explicit regression and representation comparisons
have their own hypotheses and proof targets.

## Historical proof inventory before the completion certificate

The 143 entries below record a Library snapshot before the
completion-certificate proof at commit `db940683e1d682d84831e8365720f1c79b5c9b0c`.
The inventory was compiled by searching theorem types and the uses of the
statement declarations. It found 107 exact proofs, 14 reductions to further
statements, and 22 entries without a proof. The updated source rows above
record the certificate and facet results at the later pin.

| Statement | Status at the earlier snapshot |
| --- | --- |
| `ActualApartmentSplittingStatement` | proved by `actualApartmentSplitting` (`Langlands/Geometry/Building/ActualApartmentSplittingProof.lean`) |
| `AffineIwahoriTitsBuildingStatement` | proved by `affineIwahoriTitsBuilding` (`Langlands/Geometry/Building/AffineIwahoriTitsBuildingProof.lean`) |
| `AffineIwahoriTitsStatement` | not proved; `affineIwahoriTitsStatement_of_inputStatements` (`Langlands/Geometry/Building/AffineIwahoriTitsInputStatements.lean`) derives it from further statements |
| `AvailableCartanStatement` | proved by `availableCartan` (`Langlands/BruhatTits/Cartan/AvailableCartanProof.lean`) |
| `AvailableIwasawaStatement` | proved by `availableIwasawa` (`Langlands/BruhatTits/Iwasawa/AvailableProof.lean`) |
| `AvailableMaximalProPStatement` | proved by `availableMaximalProP` (`Langlands/BruhatTits/MaximalProP/AvailableProof.lean`) |
| `AvailableRenardCartanStatement` | not proved |
| `AvailableSimultaneousStandardBasisStatement` | proved by `availableSimultaneousStandardBasis` (`Langlands/BruhatTits/SpecialCompact/AvailableBasisProof.lean`) |
| `BruhatTits.SpecialCompact.AvailableSpecialLeviCompactStatement` | proved by `availableSpecialLeviCompact` (`Langlands/BruhatTits/SpecialCompact/AvailableSpecialLeviCompactProof.lean`) |
| `BoundedOpenNormalizerStatement` | proved by `boundedOpenNormalizer` (`Langlands/BruhatTits/RationalPoints/BoundedOpenNormalizerProof.lean`) |
| `BruhatTitsAvailabilityReductionStatement` | proved by `bruhatTitsAvailabilityReduction` (`Langlands/Geometry/Building/BruhatTitsAvailabilityReductionProof.lean`) |
| `BruhatTitsAvailabilityStatement` | not proved |
| `BuildingComparisonAxiomStatement` | proved by `buildingComparisonAxiom` (`Langlands/Geometry/Building/BuildingComparisonAxiomProof.lean`) |
| `AlgebraicFundamentalGroup.CentralTorusFundamentalExactnessStatement` | proved by `centralTorusFundamentalExactness` (`Langlands/GroupScheme/AlgebraicFundamentalGroupCentralTorusProof.lean`) |
| `CentralTorusInertiaExactnessStatement` | proved by `centralTorusInertiaExactness` (`Langlands/Geometry/Building/Kottwitz/CentralTorusExactnessProof.lean`) |
| `CentralizerFiltrationDoubleRootExistenceStatement` | proved by `centralizerFiltrationDoubleRootExistence` (`Langlands/Geometry/Building/KPDoubleRootFiltrationExistence.lean`) |
| `CentralizerFiltrationExistenceStatement` | proved by `centralizerFiltrationExistence` (`Langlands/Geometry/Building/CentralizerFiltrationExistenceProof.lean`) |
| `ChamberIwahoriCompactOpenStatement` | proved by `chamberIwahoriCompactOpen` (`Langlands/Geometry/Building/ChamberIwahoriCompactOpenProof.lean`) |
| `ChamberIwahoriDecompositionStatement` | proved by `chamberIwahoriDecomposition` (`Langlands/Geometry/Building/ChamberIwahoriProof.lean`) |
| `ChamberStatement` | not proved; `chamberStatement_of_surjective_of_geometricInputs` (`Langlands/Geometry/Building/Kottwitz/RationalChamberQuotientReduction.lean`) derives it from further statements |
| `ChapterSevenBuildingAxiomsStatement` | not proved |
| `CharacterKernelStatement` | proved by `characterKernel` (`Langlands/Geometry/Building/Kottwitz/CharacterKernelProof.lean`) |
| `CocenterTargetTorsionStatement` | proved by `cocenterTargetTorsion_proof` (`Langlands/Geometry/Building/Kottwitz/CocenterTargetTorsionProof.lean`) |
| `CompactInductionDoubleCosetStatement` | proved by `compactInductionDoubleCoset` (`Langlands/Representation/Induction/OpenIntertwiningDoubleCosetProof.lean`) |
| `CompactInductionFiniteTypeKernelStatement` | proved by `compactInductionFiniteTypeKernel` (`Langlands/Representation/Induction/OpenIntertwiningFiniteTypeProof.lean`) |
| `CompactInductionIntertwiningStatement` | not proved |
| `CompactInductionKernelStatement` | proved by `compactInductionKernel` (`Langlands/Representation/Induction/OpenIntertwiningKernelProof.lean`) |
| `CongruenceNeighborhoodBasisStatement` | proved by `congruenceNeighborhoodBasis_proof` (`Langlands/GroupScheme/IntegralModel/CongruenceNeighborhoodBasisProof.lean`) |
| `ConnectedGenerationStatement` | proved by `connectedGeneration` (`Langlands/GroupScheme/IntegralModel/ConnectedGenerationProof.lean`) |
| `DegenerateCosetOfDeeperIntersectionStatement` | not proved |
| `GroupScheme.DerivedCentralSplitTorusProductStatement` | proved by `derivedCentralSplitTorusProduct` (`Langlands/GroupScheme/Derived/CentralSplitTorusProductProof.lean`) |
| `FacetParabolicComparisonStatement` | not proved |
| `FiniteIndexEnlargementStatement` | proved by `finiteIndexEnlargement` (`Langlands/GroupScheme/IntegralModel/FiniteIndexEnlargementProof.lean`) |
| `FiniteVertexFixerApproximationStatement` | proved by `finiteVertexFixerApproximation` (`Langlands/Geometry/Building/UnramifiedFiniteVertexFixerAssembly.lean`) |
| `FundamentalInertiaMapStatement` | proved by `fundamentalInertiaMapStatement` (`Langlands/Geometry/Building/Kottwitz/FundamentalInertiaMapProof.lean`) |
| `GroupAxiomsExistenceReductionStatement` | proved by `groupAxiomsExistenceReduction` (`Langlands/Geometry/Building/GroupAxiomsExistenceReduction.lean`) |
| `GroupAxiomsExistenceStatement` | not proved |
| `HenselianDiscreteQuasiSplitStatement` | proved by `henselianDiscreteQuasiSplit` (`Langlands/GroupScheme/Rational/HenselianDiscreteQuasiSplitProof.lean`) |
| `InducedCentralTorusInertiaInjectivityStatement` | proved by `inducedCentralTorusInertiaInjectivity` (`Langlands/Geometry/Building/Kottwitz/CentralTorusInertiaInjectivityProof.lean`) |
| `InducedTorusKottwitzRationalSurjectivityStatement` | proved by `inducedTorusKottwitzRationalSurjectivity` (`Langlands/Geometry/Building/Kottwitz/InducedTorusRationalSurjectivityProof.lean`) |
| `InducedTorusQuotientPointSurjectivityStatement` | proved by `inducedTorusQuotientPointSurjectivity` (`Langlands/GroupScheme/Torus/InducedQuotientPointSurjectivityProof.lean`) |
| `IntegralModelAxiomsStatement` | not proved |
| `IntegralOppositeFactorsStatement` | proved by `integralOppositeFactors` (`Langlands/BruhatTits/IntegralModels/IntegralOppositeFactorsProof.lean`) |
| `IsomorphismCompatibilityAxiomStatement` | proved by `isomorphismCompatibilityAxiom` (`Langlands/Geometry/Building/IsomorphismCompatibilityAxiomProof.lean`) |
| `IwahoriDecompositionAxiomStatement` | not proved; `iwahoriDecompositionAxiom_of_iwahoriWeylChamberSplitting` (`Langlands/Geometry/Building/IwahoriDecompositionAxiomReduction.lean`) derives it from further statements |
| `IwahoriDoubleCosetStatement` | not proved; `iwahoriDoubleCosetStatement_of_statements` (`Langlands/Geometry/Building/DoubleCosetStatementReduction.lean`) derives it from further statements |
| `IwahoriWeylChamberSplittingStatement` | not proved; `iwahoriWeylChamberSplittingStatement_of_exactSequence` (`Langlands/Geometry/Building/IwahoriWeylExactSequenceReduction.lean`) derives it from further statements |
| `IwahoriWeylExactSequenceStatement` | not proved; `iwahoriWeylExactSequenceStatement_of_prerequisites` (`Langlands/Geometry/Building/IwahoriWeylExactSequenceReduction.lean`) derives it from further statements |
| `IwasawaDecompositionStatement` | proved by `iwasawaDecomposition` (`Langlands/Geometry/Building/IwasawaDecompositionProof.lean`) |
| `IwasawaExistenceStatement` | not proved |
| `KPLocalDoubleRootCommutatorStatement` | proved by `kpLocalDoubleRootCommutator` (`Langlands/Geometry/Building/KPLocalDoubleRootCommutatorProof.lean`) |
| `Geometry.Building.LeviApartmentAxiomsInheritanceStatement` | proved by `leviApartmentAxiomsInheritance` (`Langlands/Geometry/Building/LeviApartmentAxiomsInheritanceProof.lean`) |
| `MaximalUnramified.LocalMoyPrasadDepthZeroStatement` | proved by `localMoyPrasadDepthZero` (`Langlands/Geometry/Building/KPLocalMoyPrasadDepthZeroProof.lean`) |
| `LocalMoyPrasadGroupPropertiesStatement` | proved by `localMoyPrasadGroupProperties` (`Langlands/Geometry/Building/KPLocalMoyPrasadGroupPropertiesProof.lean`) |
| `MaximalUnramified.LocalMoyPrasadPositiveProductStatement` | proved by `localMoyPrasadPositiveProduct` (`Langlands/Geometry/Building/KPLocalMoyPrasadPositiveProductProof.lean`) |
| `MaximalBoundedIntegralModelStatement` | proved by `maximalBoundedIntegralModel` (`Langlands/GroupScheme/IntegralModel/MaximalBoundedConstruction.lean`) |
| `MoyPrasadCommutatorStatement` | not proved |
| `MoyPrasadCovarianceStatement` | not proved |
| `MoyPrasadDoubleRootCommutatorStatement` | proved by `moyPrasadDoubleRootCommutator` (`Langlands/Geometry/Building/KPMoyPrasadDoubleRootCommutatorProof.lean`) |
| `MoyPrasadDoubleRootCovarianceStatement` | proved by `moyPrasadDoubleRootCovariance` (`Langlands/Geometry/Building/KPMoyPrasadDoubleRootCovarianceProof.lean`) |
| `MoyPrasadFiltrationStatement` | not proved |
| `MoyPrasadIsomorphismStatement` | not proved |
| `MoyPrasadLeviStatement` | proved by `moyPrasadLevi` (`Langlands/Geometry/Building/KPMoyPrasadLeviProof.lean`) |
| `MoyPrasadProductStatement` | proved by `moyPrasadProduct` (`Langlands/Geometry/Building/KPMoyPrasadProductProof.lean`) |
| `MultipliableRootGroupCoordinatesExistenceStatement` | proved by `multipliableRootGroupCoordinatesExistence` (`Langlands/Geometry/Building/MultipliableRootGroupCoordinatesExistenceProof.lean`) |
| `ParahoricDoubleCosetStatement` | not proved; `parahoricDoubleCosetStatement_of_statements` (`Langlands/Geometry/Building/DoubleCosetStatementReduction.lean`) derives it from further statements |
| `QuasiSplitAdjointSimpleRootTransitivityStatement` | proved by `quasiSplitAdjointSimpleRootTransitivity` (`Langlands/Geometry/Building/QuasiSplitAdjointSimpleRootTransitivityProof.lean`) |
| `QuasiSplitIntegerApartmentExistenceStatement` | proved by `quasiSplitIntegerApartmentExistence` (`Langlands/Geometry/Building/QuasiSplitIntegerApartmentExistenceProof.lean`) |
| `QuasiSplitValuedRankOneCoordinatesStatement` | proved by `quasiSplitValuedRankOneCoordinates` (`Langlands/Geometry/Building/QuasiSplitValuedRankOneCoordinatesProof.lean`) |
| `QuotientStatement` | not proved; `quotientStatement_of_chamberStatement` (`Langlands/Geometry/Building/Kottwitz/QuotientReduction.lean`) derives it from further statements |
| `ReductiveKottwitzDescentStatement` | proved by `reductiveKottwitzDescent_assembled` (`Langlands/Geometry/Building/Kottwitz/ZExtensionKernelProof.lean`) |
| `ReductiveKottwitzExistenceStatement` | proved by `reductiveKottwitzExistence_assembled` (`Langlands/Geometry/Building/Kottwitz/ZExtensionKernelProof.lean`) |
| `ReductiveKottwitzFunctorialityStatement` | proved by `reductiveKottwitzFunctoriality` (`Langlands/Geometry/Building/Kottwitz/ReductiveFunctorialityProof.lean`) |
| `ReductiveKottwitzRemainingInputsStatement` | proved by `reductiveKottwitzExistence_of_remaining_inputs` (`Langlands/Geometry/Building/Kottwitz/ReductiveMapRemainingInputs.lean`) |
| `RootGroupActionAxiomStatement` | not proved |
| `RootValuationBuildingConstructionStatement` | not proved |
| `SeparableUnramifiedArithmeticStatement` | proved by `separableUnramifiedArithmetic` (`Langlands/Galois/Local/SeparableUnramifiedArithmeticProof.lean`) |
| `SimplyConnectedDerivedKottwitzStatement` | proved by `simplyConnectedDerivedKottwitz_proof` (`Langlands/Geometry/Building/Kottwitz/SimplyConnectedDerivedKottwitzProof.lean`) |
| `SimplyConnectedFacetFixingStatement` | not proved; `simplyConnectedFacetFixing_of_rankOneCentralizerGeneration` (`Langlands/Geometry/Building/SimplyConnectedFacetFixingReduction.lean`) derives it from further statements |
| `SimplyConnectedKneserTitsCentralizerStatement` | not proved |
| `SimplyConnectedNormalizerAffineWeylStatement` | not proved; `simplyConnectedNormalizerAffineWeyl_of_affineIwahoriTits` (`Langlands/Geometry/Building/AffineIwahoriTitsNormalizerReduction.lean`) derives it from further statements (`simplyConnectedNormalizerAffineWeyl` in `Langlands/Geometry/Building/UnramifiedSimplyConnectedNormalizerAffineWeylProof.lean` proves `MaximalUnramified.SimplyConnectedNormalizerAffineWeylStatement`, the statement for the maximal unramified extension) |
| `SimplyConnectedRankOneCentralizerGenerationStatement` | not proved |
| `SimplyConnectedReflectionTranslationStatement` | not proved; `simplyConnectedReflectionTranslation_of_rankOneGeneration` (`Langlands/Geometry/Building/SimplyConnectedReflectionTranslationReduction.lean`) derives it from further statements |
| `SmoothIntersectionStatement` | proved by `smoothIntersection` (`Langlands/GroupScheme/IntegralModel/SmoothIntersectionConstruction.lean`) |
| `SpecialTorusBoundedModelStatement` | proved by `specialTorusBoundedModel` (`Langlands/Geometry/Building/SpecialTorusBoundedModelProof.lean`) |
| `SpecialTorusExistenceStatement` | proved by `specialTorusExistence` (`Langlands/Geometry/Building/SpecialTorusExistenceProof.lean`) |
| `SpecialTorusIntegralModelStatement` | proved by `specialTorusIntegralModel` (`Langlands/Geometry/Building/SpecialTorusIntegralModelProof.lean`) |
| `TorusCharacterKernelStatement` | proved by `torusCharacterKernel` (`Langlands/Geometry/Building/Kottwitz/TorusCharacterKernelProof.lean`) |
| `TorusKottwitzKernelStatement` | proved by `torusKottwitzKernel` (`Langlands/Geometry/Building/Kottwitz/TorusKernelProof.lean`) |
| `UnipotentIwahoriDoubleCosetStatement` | proved by `unipotentIwahoriDoubleCoset` (`Langlands/Geometry/Building/UnipotentIwahoriDoubleCosetProof.lean`) |
| `UnipotentNormalizerCosetStatement` | proved by `unipotentNormalizerCoset` (`Langlands/Geometry/Building/UnipotentNormalizerCosetProof.lean`) |
| `UnramifiedChamberExactSequenceStatement` | proved by `unramifiedChamberExactSequence` (`Langlands/Geometry/Building/Kottwitz/UnramifiedChamberExactSequenceProof.lean`) |
| `UnramifiedComparisonExistenceStatement` | proved by `unramifiedComparisonExistence` (`Langlands/Geometry/Building/KPUnramifiedComparisonExistenceProof.lean`) |
| `UnramifiedComparisonLeviFieldStatement` | proved by `unramifiedComparisonLeviField` (`Langlands/Geometry/Building/KPUnramifiedComparisonLeviFieldProof.lean`) |
| `UnramifiedComparisonOpenFieldStatement` | proved by `unramifiedComparisonOpenField` (`Langlands/Geometry/Building/KPUnramifiedComparisonOpenProof.lean`) |
| `UnramifiedComparisonRootFieldStatement` | proved by `unramifiedComparisonRootField` (`Langlands/Geometry/Building/KPUnramifiedComparisonRootFieldProof.lean`) |
| `UnramifiedComparisonZeroFieldStatement` | proved by `unramifiedComparisonZeroField` (`Langlands/Geometry/Building/KPUnramifiedComparisonZeroFieldProof.lean`) |
| `UnramifiedCompatibleModelKernelSmoothConnectedStatement` | not proved |
| `UnramifiedDoubledRootDepthModelStatement` | proved by `unramifiedDoubledRootDepthModel` (`Langlands/Geometry/Building/UnramifiedDoubledRootDepthModelProof.lean`) |
| `UnramifiedFacetParabolicImageStatement` | proved by `unramifiedFacetParabolicImage` (`Langlands/BruhatTits/IntegralModels/UnramifiedFacetParabolicImageProof.lean`) |
| `UnramifiedFacetPositiveRadicalStatement` | proved by `unramifiedFacetPositiveRadical` (`Langlands/BruhatTits/IntegralModels/UnramifiedFacetPositiveRadicalProof.lean`) |
| `UnramifiedFacetRootDatumStatement` | proved by `unramifiedFacetRootDatum` (`Langlands/BruhatTits/IntegralModels/UnramifiedFacetRootDatumProof.lean`) |
| `UnramifiedFixedDepthZeroOppositeStatement` | proved by `unramifiedFixedDepthZeroOpposite` (`Langlands/Geometry/Building/UnramifiedFixedDepthZeroOppositeProof.lean`) |
| `UnramifiedFixedLeviTransportStatement` | proved by `unramifiedFixedLeviTransport` (`Langlands/Geometry/Building/UnramifiedFixedLeviTransportProof.lean`) |
| `UnramifiedFixedOppositeStatement` | proved by `unramifiedFixedOpposite` (`Langlands/Geometry/Building/UnramifiedFixedOppositeProof.lean`) |
| `UnramifiedFixedPairSpecialApartmentStatement` | proved by `unramifiedFixedPairSpecialApartment` (`Langlands/Geometry/Building/UnramifiedFixedPairSpecialApartmentProof.lean`) |
| `UnramifiedFixedPointTransporterStatement` | proved by `unramifiedFixedPointTransporter` (`Langlands/Geometry/Building/UnramifiedFixedPointTransporterProof.lean`) |
| `UnramifiedFixedWallInvarianceStatement` | not proved |
| `UnramifiedGaloisFixedApartmentStatement` | proved by `unramifiedGaloisFixedApartment` (`Langlands/Geometry/Building/UnramifiedGaloisFixedApartmentProof.lean`) |
| `UnramifiedLeviSharpApartmentTransportStatement` | proved by `unramifiedLeviSharpApartmentTransport` (`Langlands/Geometry/Building/UnramifiedLeviSharpApartmentTransportProof.lean`) |
| `UnramifiedModelKernelStatement` | proved by `unramifiedModelKernel` (`Langlands/BruhatTits/IntegralModels/UnramifiedModelKernelProof.lean`) |
| `UnramifiedOrderedIntegralOpenCellReductionStatement` | proved by `unramifiedOrderedIntegralOpenCellReduction` (`Langlands/BruhatTits/IntegralModels/OrderedIntegralOpenCellReduction.lean`) |
| `UnramifiedOrderedIntegralOpenCellStatement` | proved by `unramifiedOrderedIntegralOpenCell` (`Langlands/BruhatTits/IntegralModels/OrderedIntegralOpenCellTheorem.lean`) |
| `UnramifiedParahoricModelStatement` | proved by `unramifiedParahoricModel` (`Langlands/BruhatTits/IntegralModels/UnramifiedParahoricModelProof.lean`) |
| `UnramifiedQuasiSplitReductionStatement` | proved by `unramifiedQuasiSplit_of_henselianDiscrete` (`Langlands/Geometry/Building/UnramifiedQuasiSplitReduction.lean`) |
| `UnramifiedRationalMoyPrasadStatement` | proved by `unramifiedRationalMoyPrasad` (`Langlands/Geometry/Building/KPUnramifiedRationalMoyPrasadProof.lean`) |
| `UnramifiedRootDepthKernelStatement` | proved by `unramifiedRootDepthKernel` (`Langlands/BruhatTits/IntegralModels/RootDepthKernel.lean`) |
| `UnramifiedSmoothModelDescentStatement` | proved by `unramifiedSmoothModelDescent` (`Langlands/GroupScheme/IntegralModel/UnramifiedSmoothDescentProof.lean`) |
| `UnramifiedTorusConnectedBoundStatement` | proved by `unramifiedTorusConnectedBound` (`Langlands/BruhatTits/IntegralModels/UnramifiedTorusConnectedBoundProof.lean`) |
| `UnramifiedTorusIwahoriConnectedImageStatement` | proved by `unramifiedTorusIwahoriConnectedImage` (`Langlands/BruhatTits/IntegralModels/UnramifiedTorusIwahoriConnectedImageProof.lean`) |
| `UnramifiedTorusUnitFixedApartmentStatement` | proved by `unramifiedTorusUnitFixedApartment` (`Langlands/Geometry/Building/UnramifiedTorusUnitFixedApartmentProof.lean`) |
| `UnramifiedTwistedChamberQuotientStatement` | proved by `unramifiedTwistedChamberQuotient` (`Langlands/Geometry/Building/UnramifiedTwistedChamberQuotientProof.lean`) |
| `UnramifiedTwistedChamberStatement` | proved by `unramifiedTwistedChamber` (`Langlands/Geometry/Building/UnramifiedTwistedChamberProof.lean`) |
| `UnramifiedTwistedChamberThroughFixedPointStatement` | proved by `unramifiedTwistedChamberThroughFixedPoint` (`Langlands/Geometry/Building/UnramifiedTwistedChamberThroughFixedPointProof.lean`) |
| `UnramifiedTwistedFixedTranslationStatement` | proved by `unramifiedTwistedFixedTranslation` (`Langlands/Geometry/Building/UnramifiedTwistedFixedTranslationProof.lean`) |
| `UnramifiedTwistedGeneratorChamberStatement` | not proved; `unramifiedTwistedGeneratorChamber_of_quotient` (`Langlands/Geometry/Building/UnramifiedTwistedChamberQuotientReduction.lean`) derives it from further statements |
| `UnramifiedTwistedReductiveQuotientDescentStatement` | proved by `unramifiedTwistedReductiveQuotientDescent` (`Langlands/BruhatTits/IntegralModels/UnramifiedTwistedReductiveQuotientDescent.lean`) |
| `UnramifiedTwistedResidueQuotientStatement` | proved by `unramifiedTwistedResidueQuotient` (`Langlands/Geometry/Building/UnramifiedTwistedResidueQuotientProof.lean`) |
| `UnramifiedUpstairsRadicalRootGenerationStatement` | proved by `unramifiedUpstairsRadicalRootGeneration` (`Langlands/BruhatTits/IntegralModels/UnramifiedUpstairsRadicalRootGenerationProof.lean`) |
| `UnramifiedValuationDescentStatement` | proved by `unramifiedValuationDescent` (`Langlands/Geometry/Building/UnramifiedValuationDescentProof.lean`) |
| `UnramifiedZeroDescentStatement` | not proved |
| `UnramifiedZeroKernelStatement` | proved by `unramifiedZeroKernel` (`Langlands/Geometry/Building/Kottwitz/UnramifiedZeroKernelProof.lean`) |
| `UnramifiedZeroPointsIndependenceStatement` | proved by `unramifiedZeroPointsIndependence` (`Langlands/Geometry/Building/UnramifiedZeroIndependenceProof.lean`) |
| `ValuationApartmentAxiomsExistenceStatement` | not proved |
| `ValuationBuildingApartmentAxiomsStatement` | not proved |
| `ValuationBuildingQuasiSplitAdjointTranslationStatement` | proved by `valuationBuildingQuasiSplitAdjointTranslation` (`Langlands/Geometry/Building/ValuationQuasiSplitAdjointTranslationProof.lean`) |
| `VertexOneStabilizerMaximalBoundedStatement` | proved by `vertexOneStabilizerMaximalBounded` (`Langlands/Geometry/Building/UnramifiedVertexMaximalBoundedProof.lean`) |
| `ZExtensionCommonDominationStatement` | proved by `zExtensionCommonDomination` (`Langlands/GroupScheme/ZExtensionCommonDominationProof.lean`) |
| `ZExtensionKottwitzKernelSurjectivityStatement` | proved by `zExtensionKottwitzKernelSurjectivity` (`Langlands/Geometry/Building/Kottwitz/ZExtensionKernelProof.lean`) |
| `ZExtensionMorphismDominationStatement` | proved by `zExtensionMorphismDomination` (`Langlands/GroupScheme/ZExtensionMorphismDominationProof.lean`) |
| `ZExtensionPointSurjectivityStatement` | proved by `zExtensionPointSurjectivity` (`Langlands/GroupScheme/Torus/ZExtensionPointSurjectivityProof.lean`) |
| `ZExtensionRationalKottwitzKernelStatement` | no theorem has it as its type; `zExtensionKottwitzKernelSurjectivityStatement_iff` (`Langlands/Geometry/Building/Kottwitz/ZExtensionKernelReduction.lean`) is an equivalence that involves it |
| `ZeroKernelStatement` | not proved; `zeroKernel_of_unramifiedZeroDescent` (`Langlands/Geometry/Building/Kottwitz/UnramifiedZeroKernelProof.lean`) derives it from further statements |
