# External Library audit: smooth representations and release status

Worker 184, original audit 2026-10-22; final correction-status check 2026-10-24.
Parent task: `651119f8-4579-446c-ac91-e18c3778f140`, revision 1.

All twelve assigned findings **held** at the original checked pilot Library
commit `dc8cdb2866562d5f929dc912f3563a75cc16ce79`. At the current check,
`e4296643398fb6f96e73eb81e8e5d19a0d2650be`, **all twelve no longer hold after
independently accepted and published documentation corrections**. Eight
correction candidates cover C1–C6, including the C5 definition, statement and
neighboring proof-document units. Their exact validation, independent-review,
publication and file-comparison evidence is recorded below. This audit found
no reason to change the corresponding Lean declarations or proof targets.
The final verdict-note update itself still requires independent acceptance and
publication before parent-task completion.

All correction statuses below describe the 2026-10-24 check at Library
`e4296643398fb6f96e73eb81e8e5d19a0d2650be`; they do not assert the status of
later Library revisions. Historical evidence limits and unrelated mathematical
proof obligations remain as explicitly described below.

## Evidence boundary

The allegations are in the registered source
`external-library-audits-2026-10-22`, folder SHA-256
`975133657fad9fc7d0806e2cf4aaefac907edd151ec4df6cdd5d92b18a95a93b`, retained at
`/home/taskhub/pilot/literature/External Library audits 2026-10-22/`.
`ISSUES-2.md` supplies I014, I033, I036 and I053–I060; `ISSUES-1.md` supplies
DOC-03. Their mirror snapshots correspond respectively to pilot commits
`f9c1742752d97c488fc1a835070bf50b534f4427` and
`c5a40b0f54880b1825ea05214c2b066f68bfc156`. Neither report supplies acceptance
evidence. The verdicts below retain the original audit findings and distinguish
the current status after correction. Exact files are identified in the hash
inventory and correction evidence, rather than treating the report's line
numbers as current by assumption.

The complete relevant declarations, hypotheses, quantifiers, universes and
imports were inspected, together with paired Markdown and the original-source
passages listed below. The 34 audited pairs were unchanged between the earlier
check at `208944fe891035d0c3be003664e2ad2d471951e3` and the original audit commit.
At the 2026-10-24 current check all 34 Lean files and 14 paired Markdown files
still have those hashes. The 20 changed Markdown files are exactly the corrected
files recorded with their current hashes under C1–C6 below: four C1/C2/C4/C6
pages, three C3 pages, eight C5 definition/statement pages, and five C5 proof
pages. The five newly corrected proof pages and their submitted Lean file match
their reviewed, published and current bytes. All 106 project modules in the
audited import closure retain unchanged Lean since the prior check at
`62ea36c5cce8fa88e0b551b153b0fdc3087190e0`; the only paired-Markdown changes
in that closure are the five C5 proof pages. All 2,408 workspace Lean files match
the current Library. There is no changed Lean module to recompile in this
continuation; the exact-candidate proof validation and fresh integrated build
for the new correction are recorded separately below.
A recovery development check, `b243e903-330c-40ef-8d5e-f68e184fbef5`, succeeded
with zero errors and warnings for `Compact.ProjectionProof`,
`Compact.SurjectivityProof`, `Smooth.Contragredient.CompactDualityProof` and the
four `Smooth.SmoothPart` proof modules Basic, FixedVectors, Functoriality and
Universal (all under `Langlands.Representation`). The Lean service reused their
build outputs. This is development compilation, **not** independent acceptance
or a fresh exact-target proof receipt. Historical acceptance claims below instead
come from the identified independent reviews, validations and publication records.

Paths in the tables are relative to the Library root. Unless explicitly labeled
current, line numbers refer to the original audit commit; they remain current
for the unchanged files. The short prefixes used in the verdict table expand as follows:

- `VR` = `Langlands/VirtualRepresentation/Supercuspidal/`.
- `GL` = `Langlands/Group/GL/`.
- `C` = `Langlands/Representation/Compact/`.
- `D` = `Langlands/Representation/Smooth/Contragredient/`.
- `SP` = `Langlands/Representation/Smooth/SmoothPart/`.
- `RT` = `Langlands/Representation/RestrictedTensor/`.
- `F` = `Langlands/Representation/Smooth/Factorization/`.
- `CS` = `Langlands/Representation/CuspidalSupport/`.

## Per-finding verdicts

| Finding | Verdict | Evidence, reason and retained scope | Correction |
| --- | --- | --- | --- |
| I014 | Held at audit; no longer holds after C1 | Original `VR/Dual.md:56–65` described the lattice map as its own square. `VR/Dual.lean:67–106` constructs `dualLatticeEquiv` by reindexing and proves `dualLatticeEquiv_symm`, `dualLatticeEquiv_apply_apply` and `dualLatticeEquiv_trans_self`: inverse equals itself, square equals identity. Current `VR/Dual.md:59–60` states precisely those two identities. C1's independent review, publication and matching file hashes are verified below. | C1 published; no further change needed for I014. Conditional supercuspidal closure is retained. |
| I033 | Held at audit; no longer holds after C2 | Original `GL/BlockUnipotentHaarStatement.md:46–53` called the triangular principle unproved. `Langlands/HarmonicAnalysis/TriangularTranslationProof.lean:83–85` proves `finiteTriangularTranslation`; `GL/BlockUnipotentHaarProof.lean:165–168` applies it to close the coordinate-Haar target. Current `GL/BlockUnipotentHaarStatement.md:51–72` describes both existing proofs and their application. C2's independent review, publication and matching hashes are verified below. | C2 published; no further change needed for I033. The local Prop-only scope and separate scaling results remain distinct. |
| I036 | Held at audit; no longer holds after C3 | Original `C/Definitions.md:66–68` used future tense for existing statements and proofs. `C/ProjectionStatement.lean:9–19`, `C/ProjectionProof.lean:47–80`, `C/SurjectivityStatement.lean:9–17` and `C/SurjectivityProof.lean:8–17` supply projection, identity on fixed vectors, naturality and fixed-vector surjectivity. Current `C/Definitions.md:65–86` accurately describes these implementations and the historical-receipt limit. | C3 published; construction-only local scope and one-compact-open hypotheses retained. |
| I053 | Held at audit; no longer holds after C3 | Original `D/CompactDualityStatement.md:52–54` called those two proofs pending. The proof declarations cited for I036 are complete. `D/CompactDualityProof.lean:1–2` imports its target and averaging definitions; its argument does not import or assume the two separate proof modules. Current `D/CompactDualityStatement.md:45–71` preserves this dependency distinction and names the existing proofs. | C3 published; historical independent acceptance of the three compact proof submissions is not inferred. |
| I054 | Held at audit; no longer holds after C3 | Original `D/FixedVectorsProof.md:62` called compact duality and reflexivity pending. `D/CompactDualityProof.lean:113–118` proves `smoothDualCompactFixedDuality`; `D/AdmissibleDualityProof.lean:116–123` proves `smoothAdmissibleDuality`. Current `D/FixedVectorsProof.md:60–92,103–111` describes these separate results, their actual assumptions and verified admissible-duality receipt. | C3 published; compact-open cofinality and the distinct smoothness/admissibility clauses retained. |
| I055 | Held at audit; no longer holds after C4 | Original `F/RestrictedTensorStatement.md:135–139` described separation as pending/unavailable. `RT/Separation.lean:293–301,330–336,384–392,422–429` constructs `finiteSeparation`, inverse `reassemble`, `localSeparation` and `productSeparation`. Current `F/RestrictedTensorStatement.md:135–150` describes these available algebraic constructions and preserves the separate representation-theoretic targets. C4's independent review, publication and matching hashes are verified below. | C4 published; no further change needed for I055. Algebraic separation does not prove the four targets or general factorization. |
| I056 | Held at audit; no longer holds after C5 | Original `SP/BasicStatement.md:3–6,41–44` called the target unaccepted and the proof development-only. `SP/BasicProof.lean:63–71`, theorem `Langlands.smoothPartBasic`, supplies the entire target. Current `SP/BasicStatement.md:41–60` identifies that proof and records the separate original statement/proof acceptances and publications. | C5 statement and proof-document units published; no further change needed. |
| I057 | Held at audit; no longer holds after C5 | Original `SP/Definitions.md:3–5` called the pair unaccepted development. `SP/Definitions.lean:20–102` constructs the smooth-vector submodule, restricted representation, inclusion, lift, map and smooth equivalence. Current `SP/Definitions.md:3–7,91–127` records verified historical approval/publication and distinguishes construction fields from separate laws. | C5 definition and proof-document units published; no further change needed. |
| I058 | Held at audit; no longer holds after C5 | Original `SP/FixedVectorsDefinitions.md:27–35` called this construction merely proposed and neighboring laws unaccepted drafts. `SP/FixedVectorsDefinitions.lean:16–23` constructs `smoothPartFixedVectorsEquiv`; `SP/FixedVectorsProof.lean:13–35` proves the whole target. Current `SP/FixedVectorsDefinitions.md:38–72` and `SP/FixedVectorsStatement.md:51–59` separate the three original acceptances and preserve the proof final-export limitation. | All three C5 units published; historical final-export limit retained. |
| I059 | Held at audit; no longer holds after C5 | Original `SP/FunctorialityStatement.md:3–6,35–37` labeled the target unaccepted and the proof development evidence. `SP/FunctorialityProof.lean:36–41`, `Langlands.smoothPartFunctoriality`, proves all four clauses. Current `SP/FunctorialityStatement.md:35–58` identifies that proof and records successful original validation, independent approval and publication separately from earlier unsuccessful checks. | C5 statement and proof-document units published; no further change needed. |
| I060 | Held at audit; no longer holds after C5 | Original `SP/UniversalStatement.md:3–8,36–37` described an unaccepted target awaiting a separate proof. `SP/UniversalProof.lean:28–33`, `Langlands.smoothPartUniversalProperty`, proves the whole target. Current `SP/UniversalStatement.md:38–58` identifies it and records separate original acceptances/publications. Current `SP/UniversalProof.md:79–91,102–112` makes the preparation account historical and links the corrected dependency status sections. | C5 statement and proof-document units published; no target or binder change was required. |
| ISSUES-1 DOC-03 | Held at audit; no longer holds after C6 | Original `CS/TotalConjugatingCountStatement.md:43–47` denied a Library `Finite (BlockShape n)` instance. `CS/FiniteBlockShapes.lean:10–34` constructs `BlockShape.toComposition`, proves its injectivity and supplies `finiteBlockShape` for every natural rank, including zero. Current `CS/TotalConjugatingCountStatement.md:44–62` names the helper, explains its absence from the statement's complete import closure and distinguishes finite-sum infrastructure from the factorial count. C6's independent review, publication and matching hashes are verified below. | C6 published; no further change needed for DOC-03. The exact factorial target and all imports remain unchanged. |

## Mathematical scope and original-source checks

### I014: inverse and square

The namespace `Langlands.VirtualRepresentation.Supercuspidal` has independent
field and representation-carrier universes. Its construction takes rank-wise
compact-open cofinality and preservation of supercuspidality under smooth
contragredient (`Dual.lean:17–22`). Neither is supplied by the generic lattice
construction. The canonical p-adic specialization supplies cofinality but still
takes the supercuspidal contragredient statement as an input (`177–185`). Its
own inverse and square identities are at `242–256`.

The basis equivalence is involutive; finite-support reindexing gives the two
inverse identities of the lattice equivalence. The square is therefore the
identity linear equivalence. Henniart's §§2.5–2.6 describe extending the
contragredient from the free integral basis, matching this construction's
provenance. The error is in the sentence identifying the square, not in the
conditional Lean construction. No claim of unconditional supercuspidal closure
or compatibility with the full correspondence follows from correcting it.

### I033: triangular translation and coordinate Haar measure

`Langlands.HarmonicAnalysis.FiniteTriangularTranslationStatement`
(`TriangularTranslationStatement.lean:20–30`) quantifies a finite index type and
dependent additive commutative coordinate groups in independent universes. It
requires measurable addition, sigma-finite translation-invariant coordinate
measures, a measurable correction, and dependence of each correction only on
coordinates of strictly smaller rank. It does not require ranks to be distinct.
`finiteTriangularTranslation` proves precisely this general proposition.

`glBlockUnipotentCoordinateHaarStatement` applies its `{0,uF}` specialization.
The correction to block `(i,j)` uses lower gaps; measurability and this dependence
are checked in the proof. The actual coordinate homeomorphism transports
invariance, compact finiteness and positivity to the block radical. The result
covers every supplied p-adic topological realization and block shape, including
empty coordinate types. The statement file still only defines a Prop. Coordinate
Haar measure does not itself establish the separate determinant-scaling or
arbitrary-Haar block-modulus identity. Both results here have internal provenance;
no external theorem is being substituted for the exact Lean target.

### I036, I053, I054: averaging, fixed vectors and duality

`Langlands.Compact.ProjectionAndNaturality` and `FixedVectorSurjectivity` quantify
complex representations on independent carrier universes, a topological group,
smoothness of the representations, and a specified open subgroup with compact
underlying set. The latter also requires a surjective intertwiner. The proofs
use finite orbit means: `Langlands.Compact.averageMap_isProj` and
`Langlands.Compact.projectionAndNaturality` are in `ProjectionProof`, and
averaging a preimage proves `Langlands.Compact.fixedVectorSurjectivity` in
`SurjectivityProof`. No cofinal family
of compact opens is needed for these results.

`Langlands.SmoothDualCompactFixedDualityStatement` asserts bijectivity of the
actual restriction map from fixed smooth functionals to the algebraic dual of
the fixed-vector space, for a smooth complex representation and one specified
compact open subgroup. Its proof implements the inverse using averaging. It
needs neither admissibility nor global compact-open cofinality. The four
elementary identities in `D/FixedVectorsProof` remain independent of that
isomorphism proof and use arbitrary commutative coefficients.

By contrast, `Langlands.SmoothAdmissibleDualityStatement`
(`D/AdmissibleDualityStatement.lean:15–23`) explicitly assumes that every open
subgroup contains a compact open subgroup. Under this assumption the canonical
smooth-bidual map is injective for every smooth complex representation. For an
admissible representation, the smooth contragredient is admissible and the
canonical bidual map is bijective. These are distinct clauses; admissibility is
not required merely for injectivity. No topology on the representation carrier
is introduced. Casselman supplies the source context in II.1.2, II.1.3, II.3.1
and **Lemma II.3.2** (not II.3.3). The complex specialization and direct finite-orbit
arguments account for the weaker group/coefficient assumptions than the chapter's
ambient locally profinite/countability and Noetherian rational-algebra setting.

The current source and full implementations of compact projection, surjectivity
and compact duality are verified. Their original pre-migration independent
acceptance records were not located in the pilot ledger. This note therefore
does not label those three historical proof submissions independently accepted.
Admissible duality has the pilot proof receipt recorded below. Removing false
claims that proofs are pending does not require inventing missing release history.

### I055: algebraic separation and representation-theoretic targets

`Langlands.RestrictedTensor.finiteSeparation` splits off any finite set `A` from
the actual algebraic restricted tensor product. The exceptional set `E` need not
be contained in `A`; the tail retains the exceptions outside `A`. Reference
vectors must be nonzero outside `E`. `reassemble` is the inverse linear
equivalence, `localSeparation` exposes one carrier, and `productSeparation` uses
the bundled nonzero reference vectors. No finite-dimensionality of the local
carriers is required. These constructions and their coherence/naturality laws
are present in `Separation`; the statement module need not import them to state
its goals.

`F/RestrictedTensorStatement.lean:23–107` separately defines
`RestrictedTensorAdmissibilityStatement`, `RestrictedTensorIrreducibilityStatement`,
`RestrictedTensorReferenceIndependenceStatement`,
`RestrictedTensorFactorUniquenessStatement` and their conjunction
`FlathRestrictedTensorStatement`. The almost-everywhere fixed-line hypothesis in
the admissibility target is stronger than nonzero reference vectors. Algebraic
separation alone proves none of these four whole targets, nor general Flath
decomposition. Flath §2 and Example 2 distinguish the direct-limit construction,
restricted-product action and representation-theoretic conclusions; his later
archimedean and Hilbert settings are also separate. C4 corrects availability
without enlarging the mathematical conclusion.

### I056–I060: smooth parts and delivery status

Casselman II.1 p.2 describes the subspace of vectors fixed by some open subgroup
and its stability under the group action. The implementation expands those
construction fields directly. It works over a commutative ring and modules in
independent universes, without module topologies, admissibility or finite
generation. Submodule closure only needs a group with a topology. Restricting the
action, lifting maps, and the fixed-vector equivalence use topological-group
compatibility. For fixed vectors the subgroup is open; compactness and original
smoothness of the ambient representation are unnecessary.

The four closing proof theorems cite their actual adjacent Prop-valued targets.
They omit the ambient `IsTopologicalGroup` instance at the theorem boundary and
introduce it where the target quantifies it internally. For Basic, the earlier
membership/closure clauses precede that binder. Universal uses the actual subtype
inclusion to obtain unique factorization from a smooth source, with source and
target carrier universes independent. FixedVectors proves the two value formulas
and naturality. Functoriality proves inclusion compatibility, identity,
composition and the smooth-equivalence value formula. These are internal laws
of the construction, not separately numbered theorems quoted from Casselman.

The ten original Test 2 records below resolve the release-status discrepancies
beyond what neighboring documentation or source presence could establish. They
do not turn acceptance of a definition or statement into acceptance of its
separate proof. The FixedVectors proof has the explicitly narrower archived-file
evidence described below.

### DOC-03: finite shapes and the factorial count

`Langlands.GeneralLinear.BlockShape.toComposition` sends the actual ordered
positive block sizes to Mathlib's `Composition n`; `toComposition_injective`
proves that the ordered sizes and length recover the shape. Transferring
finiteness along this injection supplies `finiteBlockShape`, with no positivity
restriction on `n` or field hypothesis. Each
`Langlands.CuspidalSupport.MinimalConjugatingPermutations` fiber already has a
finite instance (`LeviDefinitions.lean:199–203`). Importing `FiniteBlockShapes`
therefore supplies finiteness of their dependent sum.

The complete project import closure of `TotalConjugatingCountStatement` has
20 modules and excludes `FiniteBlockShapes`. C6 preserves that local scope. Its
`Langlands.CuspidalSupport.TotalConjugatingCountTheorem`
(`TotalConjugatingCountStatement.lean:15–19`) still asserts the substantive exact
count `Nat.card ((C : BlockShape n) × MinimalConjugatingPermutations B C) =
Nat.factorial B.length`, as well as finiteness, for all ranks and actual p-adic
fields. Finiteness alone does not prove that equality. BZ77 §2.8 gives the
factorial count; §2.13(c) and §2.14(2) justify the minimal-representative and
sum-over-target-Levis formulation. The existing finite-shape helper claims
neither that classification nor the count.

## Registered originals and reading record

The original files were read directly, not through the external audit's proposed
wording. There were no corresponding project `notes/errata/<source-id>.md`
files at the checked snapshot. The public literature index
`/home/taskhub/pilot/literature/_central-library-pointers.md` gives the retained
Central-Library paths for these exact registered source IDs.

| Source ID | Original, locators and reading extent | Content SHA-256 |
| --- | --- | --- |
| `henniart-2000-simple-proof` | G. Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur un corps p-adique*, Invent. Math. 139 (2000), 439–455. §§2.5–2.6, printed p.446 / PDF p.8: free integral lattices and linear extension of contragredient. | `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de` |
| `casselman-2019-smooth-representations` | B. Casselman, *Introduction to admissible representations of p-adic groups*, Chapter II, June 16, 2019. Read pp.1–4 and 6–7; p.1 ambient conventions, p.2 smooth vectors, II.1.2 pp.3–4 averaging, II.1.3 p.4 fixed-vector exactness, II.3.1 and Lemma II.3.2 p.6 duality/reflexivity. | `2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d` |
| `flath-1979-tensor-products` | D. Flath, *Decomposition of representations into tensor products*, Corvallis, Proc. Symp. Pure Math. 33, Part I (1979), 179–183. Read the complete article, PDF pp.175–179 of the retained Part I volume; §2 pp.180–181 and Example 2 p.181 are the principal construction locators. Hash is of the whole retained volume. | `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5` |
| `bernstein-zelevinsky-1977-induced-i` | I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977), 441–472. Read printed pp.447–449 / PDF pp.8–10, especially §§2.6–2.8, Lemma 2.11, §2.13(c), §2.14(2). | `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092` |

## Verified historical acceptance and publication

These records establish prior acceptance of specific contributions; reuse of
mathematics is by current Lean name and import, not by artifact ID. They are
distinct from the later audit-correction candidates.

### Pilot records

For each row, the authoritative
`/home/taskhub/pilot/artifacts/<candidate-id>/1/record.json` and `publication.json`
were checked. Each has an accepted machine validation, an independent **approve**
review with no unresolved qualifications, and publication. Both current paired
file hashes equal the corresponding accepted published pair. Proof validations
include Lake build, exact-target, unchanged-statement and frozen-input checks;
definition validations include build and declaration-kind checks. The acceptance
of separation and finite shapes is under the definition policy, not a claim of
proof acceptance for the distinct representation-theoretic/counting targets.

| Current declaration | Accepted candidate / policy | Validation ID | Independent review task | Pilot publication commit |
| --- | --- | --- | --- | --- |
| `Langlands.HarmonicAnalysis.finiteTriangularTranslation` | `59aa9379-c26e-42d0-94ee-9fabfac51b8f` / `lean.proof@1` | `5b6c72d0-7849-45da-9875-bad163849d64` | `960f0503-7fc4-4914-b3c1-2aae39d3e13f` (approve) | `0686b4fa6c8df22845bba2e2668a723a41d47c84` |
| `Langlands.glBlockUnipotentCoordinateHaarStatement` | `69cecf67-1846-4c21-ac40-1f145c1ecdc7` / `lean.proof@1` | `30e93d83-de15-4a9e-b477-99bb4030e4c9` | `69ce0a30-0af8-4f0c-90f9-5522077ffc06` (approve) | `916154eeb26478d9efb73f26a117f337c9a438a2` |
| `Langlands.smoothAdmissibleDuality` | `81c91e2f-1a4d-45f0-98f2-0710f820d150` / `lean.proof@1` | `8baffe36-13a6-490e-bf75-053794418a71` | `40cf4bc6-85b4-42c5-93eb-ee31e50a6077` (approve) | `196ceda926c7cfe1fdbe5ae57c08133d83bbf940` |
| `Langlands.RestrictedTensor.productSeparation` | `d4ca532b-e95f-4823-9ecc-4f19488e70bc` / `lean.definition@1` | `e34f7deb-5730-4332-a449-5c8b4a91fa40` | `95c6803f-2cd9-4e08-9c0b-1af57ea5be39` (approve) | `68e8013fc4fed0de284fd849695676aca2e0c32d` |
| `Langlands.GeneralLinear.BlockShape.toComposition` | `4d11defa-f95d-48d8-ad62-6118f1630508` / `lean.definition@1` | `b9c8e433-f6d2-405d-bab7-53d02a1ffaae` | `61819b57-2bd2-4af6-8187-6095f126221b` (approve) | `2e31df852eed5b4c1a45eca581f8480418360a34` |

### Original Test 2 records for smooth parts

The trusted operator supplied the missing pre-migration ledger as a read-only
export at `/home/taskhub/pilot/literature/Test 2 acceptance receipts of smooth-part contributions/`.
It is registered as `test2-smooth-part-acceptance-receipts-2026-10-22`, folder
fingerprint `4d77169bf746114b7df83c650215ba7794fb523f1deb51a6be1b16ebfb376c6d`.
The pilot inherited these Library files but did not import Test 2's ledger.
The commits in this table are **Test 2 commits**, not pilot commits.

Each candidate's `receipts.json` supplies the original machine-validation rows,
independent review rationale and publication rows; `archive/1/record.json`,
`manifest.json` and `publication.json` supply the retained record/bundle and
integration evidence. All ten have accepted original validations, independent
approve reviews with no qualifications, and recorded publication. Before C5's
documentation corrections, all ten Lean/Markdown pairs at pilot
Library `fb40559309dd366f4145aa31aad8c3db11b7cc07` matched their original
accepted bundle SHA-256 values. For nine pairs the archived `archive/1/final/`
files were also present and matched those pre-correction bytes. All ten Lean
files remain identical at the current check; all ten of their Markdown files now
carry the C5 corrections recorded below. The exception to the archived-final
comparison is detailed immediately after the table.

The entry names below are modules under
`Langlands.Representation.Smooth.SmoothPart`. Each row records the original
candidate's successful validation, independently from acceptance of its neighboring
construction, statement or proof.

| Entry / kind | Original candidate | Independent approve review / date | Accepted original validation | Test 2 publication commit |
| --- | --- | --- | --- | --- |
| `Definitions` / `lean.definition` | `9fb5627f-6e8c-48a5-a92f-a4ddcf319b2d` | Reviewer 15, `1f969dc8-79b0-4e70-adf8-502752d70c6a`, 2026-10-13 | `049abffe-7b50-461f-b601-9df3ab4c8d67` | `cd8210540c75a7d0a9e2431e4bc9a2535ceaf919` |
| `FixedVectorsDefinitions` / `lean.definition` | `8bf36df6-8b13-4713-89e0-7d2ba5aa6824` | Reviewer 42, `51c5f743-c16d-4e28-919b-c64311bd5224`, 2026-10-14 | `6b264218-ebf7-4919-a0ce-da88df8d5734` | `a158df54c354b831c3b158cd0a299f3f78acb9da` |
| `BasicStatement` / `lean.statement` | `7101568f-3e71-4b9d-b1c5-f35546e0e8dd` | Reviewer 27, `a2c4fec7-eaaa-4396-889d-edf61fcd5156`, 2026-10-14 | `514d9ae0-7ad9-4dc6-a8bf-6909e90592fc` | `6c1028baa3f29e21f18dd147d07f4b7873a88b8c` |
| `BasicProof` / `lean.proof` | `b247128b-8881-47d1-ac8a-9d5b098e4548` | Reviewer 61, `b0087dbecfa84d449d6fecda76ccad74`, 2026-10-15 | `fb8124bc-935a-46bd-8708-2424ef72ad69` | `d0f5322f745425b08ae8e72c1031206f45cb049e` |
| `UniversalStatement` / `lean.statement` | `16500d55-deee-48eb-b34b-91e7fe62065f` | Reviewer 26, `ed612220-3b7d-4722-aac7-8b1e058f92fd`, 2026-10-14 | `8ae8f8a0-e2c1-4d05-9a54-7ec9461ad5c6` | `a28679cf25a4ce001af4e724a51fd7db72864cd3` |
| `UniversalProof` / `lean.proof` | `ab36e2ca-7530-48d6-9852-34b6a9d70ac0` | Reviewer 72, `281c1091d3e846919dd1aeb3a56db99f`, 2026-10-15 | `738b0000-73b3-4750-9eea-c1b6ccd72176` | `9db46907db3181b0c1dfd287b8ab2f1f02054cab` |
| `FixedVectorsStatement` / `lean.statement` | `d42c7a18-e1b0-4fb0-bd39-7d311c5b5d72` | Reviewer 71, `cc6d34baff1c435c917b8003e911577e`, 2026-10-15 | `29444ff2-4149-4659-9a1f-26a1f8649afb` | `9db46907db3181b0c1dfd287b8ab2f1f02054cab` |
| `FixedVectorsProof` / `lean.proof` | `845f3f41-937b-4cd6-93ac-408338821da3` | Reviewer 167, `ec2fa0110e8a4bde879fb9123be60895`, 2026-10-18 | `997582d4-ff38-42e2-a2da-611cc12605a4` | `e4e22245747ec04edd4445d4557b746f8f53de29` |
| `FunctorialityStatement` / `lean.statement` | `80ed7208-2a32-4a3f-b295-66c8a37f919a` | Reviewer 29, `0bbecfbd-08f8-4f0e-a83e-dd6a6d423711`, 2026-10-14 | `f3e0277e-2659-4769-a705-bf384c2e654a` | `672a1bfbca2444507019dc6764810d0c0bcb81e5` |
| `FunctorialityProof` / `lean.proof` | `9417e847-122a-4e31-8fc0-2206b502b4fa` | Reviewer 73, `be1294303e9b47058b1ae4894da9a552`, 2026-10-15 | `5d8f864d-330e-43c0-b26e-519dbaa668ff` | `d0f5322f745425b08ae8e72c1031206f45cb049e` |

The original Basic, Universal, FixedVectors and Functoriality proof validations
record `proof_accepted=true` and exact-target/build evidence. Definition and
statement validation does not constitute proof acceptance. FunctorialityStatement's
initial validation `fa1c3c0a-b1ae-48ed-89a0-db9d69bf78c7` was rejected before the
successful validation in the table. FunctorialityProof's first validation
`068d657a-0ad3-43cc-8d72-256152fea878` was unavailable before its successful retry.
These earlier outcomes were retained, not treated as the final outcome.

**FixedVectorsProof evidence limit.** Candidate
`845f3f41-937b-4cd6-93ac-408338821da3` has no `archive/1/final/` directory in this
export. Its unchanged current Lean hash
`62ce8bc649cf6947c364e7fd368aeaceb96343ed8b30e9a1a794e0ad7f6e988f`
and pre-correction Markdown hash
`6609d0147f6b4f96212902886307714314cd4ce2ddd18d78b12aefa8a350a8d9`
match the exact original accepted bundle. The current Markdown instead has
the C5 proof-document correction hash recorded below; it is not asserted to
match that original bundle. Original validation
`997582d4-ff38-42e2-a2da-611cc12605a4` has `proof_accepted=true`, Lake build and
exact-target evidence, and Reviewer 167 independently approved it. Its publication
row is present at the Test 2 commit in the table. However, the exported final
integration validation is a shared batch build with `proof_accepted=false`,
not a fresh exact-target proof acceptance; it supplies no final semantic-check
or source-binding record. Thus this note verifies original proof acceptance,
recorded publication, unchanged current Lean, and pre-correction Markdown
equality to the original accepted hashes. It
does not claim an archived-final-byte comparison or fresh exact-target acceptance
of that final integration batch. This limitation does not justify describing the
original construction/target as unaccepted, nor the implemented laws as nonexistent.

## Correction ledger

Status checked on 2026-10-24 against authoritative TaskHub fetch and publication
records. All eight correction candidates under C1–C6 are independently accepted
and published. Exact candidate bindings, complete independent approval reports,
final integrated validations and reviewed/published/current file comparisons
have been verified. No necessary correction candidate remains pending. C5's
executor retains its task-completion declaration, distinct from the verified
publication of all required corrections. Parent completion also requires
acceptance and publication of this final ledger update.

Each correction preserved Lean bytes and used the mathematical artifact workflow
for paired Markdown. The neighboring SmoothPart proof-document unit was
published as a focused proof task, preserving the exact published target. This
audit note uses the separate public-note workflow. Neither a note's validation
nor its publication supplies mathematical proof acceptance.

| Unit | Finding coverage | Correction task / revision | Candidate, review, validation and publication |
| --- | --- | --- | --- |
| C1 | I014 | `c3bb11ea-663b-419e-bd8c-5ca027ca5092` / 1 | Candidate `536e6fe6-890f-4cce-a477-e11fecad81a6`, `lean.definition@1`; validation `bdc3dea1-070a-4917-8eae-5aad72225c0d` accepted; Reviewer 1474 approved review task `587f9903-036f-4cde-b84f-7b7d66080503`, no qualifications; published at `a4f4742431c7298bf38f4d4e6bc03a6cd7a33a18`. |
| C2 | I033 | `5f109d54-307b-44b4-966e-f57a30351919` / 1 | Candidate `ae344c62-c5d1-4e53-ba14-6c41989de5ad`, `lean.statement@1`; validation `678e20d6-11ab-4e01-a1f4-66d2c678634c` accepted; Reviewer 1487 approved review task `ef89df93-2ea2-4712-974e-9c777f5a09cd`, no qualifications; published at `451f42a052568843a4d727659c3d0a6c66d38ca6`. |
| C3 | I036, I053, I054 | `8454a266-f4aa-441b-8c6e-366da6de6819` / 1 | Candidate `aa209996-51b4-409b-89fc-f762a4229d07`, `lean.statement@1`; validation `3428fcdc-0575-449a-95c5-38423a307e1a` accepted; Reviewer 1621 approved review task `6d9b4447-244e-468b-8e9d-bfd84a5d5dd5`, no qualifications; published at `4750a03e101b9ad45fc1a4d90a6a3d02d69c73e9`. |
| C4 | I055 | `55caa000-0cfc-4d80-be3f-6ba06d005315` / 1 | Candidate `a6cd0a84-f1fb-4f19-8752-05ad59077227`, `lean.statement@1`; validation `2e8f557d-0392-426e-828f-011dd6dbf0f2` accepted; Reviewer 1541 approved review task `a567610c-2256-4843-a437-a546010dcf2d`, no qualifications; published at `4ab35fd7cc442c437d97a7e9a247b902533aa199`. |
| C5 | I056, I057, I058, I059, I060 | `d3c12473-e617-41d9-bf73-729d7c71f1ea` / 2 | Definition candidate `c0047c69-da72-4c96-8eb6-9d7ae4069f5e`, `lean.definition@1`, accepted validation `a5206020-a292-4d3c-a54b-97940b7c1785`, Reviewer 1623 approval `83fdb6e2-887d-45b5-abb3-75d495ae6432`; statement candidate `078ba475-a6a9-4a33-8f4a-0fae37df22ff`, `lean.statement@1`, accepted validation `08c8c041-93e3-49d1-a9c7-b653ccd85499`, Reviewer 1629 approval `74e5aac7-ab60-4cae-9fcc-3aa885b10ef6`. Both published at `4750a03e101b9ad45fc1a4d90a6a3d02d69c73e9`, with no qualifications. Proof-document follow-up task `c559eb4c-3815-402d-bb34-46e14b686334` / 1: candidate `995398b4-f6f2-45dd-8a7f-d181404cc8c9`, `lean.proof@1`, accepted validation `c0dadffa-5f30-4ef5-8451-709ffde73efd`, Reviewer 2090 approval in `bc9c4b76-bc3a-4344-9e23-e24edd262f42`; published at `e4296643398fb6f96e73eb81e8e5d19a0d2650be`, no qualifications. All necessary C5 corrections are published. |
| C6 | ISSUES-1 DOC-03 | `89b3bb14-8afe-4e87-9c07-b14d0fe8c481` / 1 | Candidate `0b475cba-c9c0-4e82-b0c4-8326efa2de98`, `lean.statement@1`; validation `0662be3c-7bf8-4d13-a903-7fbb312021e9` accepted; Reviewer 1549 approved review task `fc700860-f4b7-4f83-9ed9-f50af6b99ddd`, no qualifications; published at `4ab35fd7cc442c437d97a7e9a247b902533aa199`. |

### C1: verified published correction

The exact candidate body hash is
`7634437513d32d5a68d4b66b8dde68aebacd5871df0bcec78f288161b11106e3`.
Independent approval receipt `0b291033bb034acb8d5abbeccafbd084` binds that candidate
and the review task above. Integration `2631191def1241618c5c39037bd9f76d` published
it at the stated commit with integrated snapshot
`7a6f66a15e6f534f4cdcdb9c8c3bd15fdc968ab684d3f587118f476cc6185c9e`.
The accepted fresh integrated Lake build has report SHA-256
`2ec17e0dd71fa727811633a4cca710e544036981da997ed716055a1592399e5c`;
its scope is source compilation, with `proof_accepted=false`. Independent
semantic approval comes from Reviewer 1474's exact-candidate report, not from
that batch build.

Both the publication commit and current checked Library match the reviewed pair:
`VR/Dual.lean` SHA-256
`5f92c2cbd3e2bfe655ccd3871b4e5fba2ef626d8429fd1ce32059a33331e44f4`
and `VR/Dual.md` SHA-256
`02ef511de373ea89512c1a4a725cb7dd2020f7dc97ca47cf72219941670d0eed`.
Direct comparison with the original audited pair confirms unchanged Lean and
only the corrected inverse/square sentence plus line wrapping. The generic
cofinality and supercuspidal-closure inputs, canonical closure input and
Henniart provenance remain unchanged.

### C2: verified published correction

The exact candidate body hash is
`b54c994c7539b28d126d7a3d6d62af5c4621db8f9805b2661354832bfe45c7e0`.
Its accepted machine validation includes Lake build and declaration-kind checks,
with `proof_accepted=false`; this is a statement documentation correction.
Reviewer 1487's full approval report, receipt
`39a42fb5ad1847748532c651dbd2cc53`, binds that hash and verifies the unchanged
Lean, the complete triangular theorem in independent universes, its `{0,uF}`
coordinate-Haar application, the measurable correction and lower-gap conditions,
and the separate scaling scope. Integration `071f190731564960a9e56d931bb6ffe1`
published the correction at `451f42a052568843a4d727659c3d0a6c66d38ca6`, with
integrated snapshot
`26e45bf490f598da6afe0c8c1dadddac3bc3f71d8b453034da9a96bab4f73258`.
The accepted fresh integrated Lake build has report SHA-256
`ea9c0753ebe3d8382c21582d8e2efb7ae912dc1f1ff955e4ebe65a576547fc5a`.
Its scope is source compilation, with `proof_accepted=false`; semantic approval
comes from the independent report.

The reviewed pair, its publication commit and the current checked Library have
identical hashes. The unchanged Lean hash is
`8b1dfe7dcaf22760546ef1c12255541643068b033a499d433c85043c3d8b27bf`;
the corrected Markdown hash is
`b6c99f2cf13b1caacca98f9de949bbba83faffcf7b13ae3c2f1bec0c62d76f0c`.
Current `GL/BlockUnipotentHaarStatement.md:6–12` distinguishes the local
Prop declaration from its separately published proof. Lines `51–72` describe
the complete triangular theorem, measurable correction, strict lower-gap
dependence and `{0,uF}` application; lines `74–76` retain the separate
determinant-scaling and block-modulus scope. I033 is therefore corrected.

### C4: verified published correction

Candidate `a6cd0a84-f1fb-4f19-8752-05ad59077227` has body SHA-256
`f0d9db00916382e837423c527337cd201584eef2b67fc0175df85cd40d492940`.
Its record preserves the audited Lean hash
`e3d72b95a267b6f0291efde9c11776fa6107fb4ff9091c58d58b8efad8ff1223`
and has corrected Markdown hash
`cea307af8be1439f64e9a3785c1b67569cc4ef598143f814e69e4637d408a128`.
The frozen pair was compared with the original audited pair: the sole change is
the availability paragraph, and the Lean hash is unchanged. Machine validation
`2e8f557d-0392-426e-828f-011dd6dbf0f2` passed Lake-build and declaration-kind
checks with no qualifications and `proof_accepted=false`. Its report SHA-256 is
`ff864b3ef69f81a0112af04b1f9dc382792a045fbf7109d165027d0bd24972d9`.
Reviewer 1541's full approving report binds this exact candidate hash and
verifies the four existing algebraic equivalences, their independent universes,
reference-vector conditions, actual restricted-product action and original
Flath pp.179–183. The review has no unresolved qualifications. The correction
retains all four distinct representation-theoretic targets and the separate
general-factorization scope. Approval receipt
`4d662b6cee0241d4a25defd901f5afe1` records that verdict.

Integration `4d314400a68d46c186a52e7d29e16597` published C4 at
`4ab35fd7cc442c437d97a7e9a247b902533aa199`, with integrated snapshot
`7d94b6a5406a06be154e889ef3d0870f864e6604255d424ec4f1c2afad0392f1`.
Its accepted fresh integrated Lake build has report SHA-256
`af997ec5514a8815548e06417a7a6f2d0cf9ae45f2c5363e4e6f854a988c5c97`.
The final validation has source-compilation scope and `proof_accepted=false`;
semantic acceptance comes from the independent report. Both reviewed file hashes
above match the publication commit and the current checked Library exactly.
Current `F/RestrictedTensorStatement.md:135–144` describes the constructions and
their hypotheses; lines `146–153` retain their limited scope. I055 is corrected.

### C6: verified published correction

Candidate `0b475cba-c9c0-4e82-b0c4-8326efa2de98` has body SHA-256
`f97f4c1df0ae7091a493006b4e6d20845acf8aa727e71d19b0a2a9634767d8f9`.
Its frozen Lean hash
`2abc2da82d63e7d3d0990232003e3c1647149a1463a28ffa7621da700e8d1118`
matches the audited and current `CS/TotalConjugatingCountStatement.lean`.
The corrected Markdown hash is
`0448a3105681043302fafee9291bbffba6b48c28c6e520e15c1733760f14030d`.
Direct comparison shows only the correction attribution and the availability
paragraph changed. Machine validation `0662be3c-7bf8-4d13-a903-7fbb312021e9`
passed Lake-build and declaration-kind checks with no qualifications and
`proof_accepted=false`; report SHA-256
`ee004796060329e3c64f3b4cb0bfa4d8c23bb0f9e4b9727ff31f62c8285946bb`.

Reviewer 1549's full approving report binds the exact candidate hash and has no
unresolved qualifications. It verifies the helper's all-rank finiteness,
including zero, its absence from the statement's complete import closure,
finite dependent-sum infrastructure, unchanged factorial target and original
BZ77 pp.447–449. The correction does not infer the factorial equality from
finite instances or deny the separate downstream counting proof. Approval receipt
`255e797306e146b1b81380814e94c66b` records that verdict.

Integration `ccc112b45d144b579974abfaee4d5377` published C6 at
`4ab35fd7cc442c437d97a7e9a247b902533aa199` in the same integrated snapshot
and accepted fresh Lake build recorded for C4. That batch build has
`proof_accepted=false` and supplies no fresh exact-target proof acceptance.
The reviewed pair, publication commit and current checked Library have identical
hashes. Current `CS/TotalConjugatingCountStatement.md:44–53` names the finite
fibers and all-rank finite-shape construction; lines `55–62` distinguish import
scope, finiteness and the exact factorial equality. DOC-03 is corrected.

### C3: verified published correction

Candidate `aa209996-51b4-409b-89fc-f762a4229d07` has body SHA-256
`5542e8a8c93eca9e7e877af8b1fae993580da734e21b414da6a1d10ca70d4a4d`.
Its accepted statement validation is listed above. Independent approval receipt
`cb29096901fc4ea281165d871376dbe5` binds that exact candidate hash. Reviewer
1621's complete report verifies the three corrected pages against the actual
proofs, full import closures and Casselman II.1.2, II.1.3, II.3.1 and II.3.2.
The approval has no qualifications. Integration
`6c4773686a534e5096e19ec906adcf57` published it at
`4750a03e101b9ad45fc1a4d90a6a3d02d69c73e9`.

Current `C/Definitions.md:65–86` replaces future tense with the implemented
projection and surjectivity results. `D/CompactDualityStatement.md:45–71`
identifies the complete compact-duality proof and preserves its independence
from the separate projection/surjectivity proof modules. Current
`D/FixedVectorsProof.md:60–92,103–111` separates elementary fixed-functional
laws from compact duality and admissible reflexivity, retaining compact-open
cofinality and the separate smoothness/admissibility requirements. Missing
historical compact-proof receipts remain explicitly outside these claims.

### C5: verified definition, statement and proof-document publications

The definition candidate `c0047c69-da72-4c96-8eb6-9d7ae4069f5e` has body hash
`a728be58e4a0791913b7a7851014baa7430915b966e4d82d6d317bd15f2e529f`.
Reviewer 1623's approval receipt `45f50e2389da4627a13a03069d1e7269`
binds that hash. Integration `bdfac3c09d1f49dab660f55ec2249d40` published its
three Markdown corrections beside unchanged Lean. The statement candidate
`078ba475-a6a9-4a33-8f4a-0fae37df22ff` has body hash
`b0732fe6297c2a519bfc828975c93dae1c23365a60cd16676b9a270eaa84bec9`.
Reviewer 1629's approval receipt `0b50440999af41f4a0dbd7c87d5b0fb4`
binds that hash. Integration `2bbae5fdead94769ae761e18cd0a0bb2` published its
five statement Markdown corrections. Both publications are at
`4750a03e101b9ad45fc1a4d90a6a3d02d69c73e9`; the definition publication
precedes the statement publication in the authoritative records.

The complete independent reports verify the unchanged constructions and targets,
Casselman's original conventions, and the Test 2 validation/review/publication
records. Both approvals have no qualifications. The corrected pages distinguish
construction fields, propositions and complete adjacent proofs, retain the
internal topological-group binders and independent universes, and preserve the
FixedVectorsProof final-export limit. `SP/HomDefinitions.md:47–56` and
`SP/HomStatement.md:50–57` accurately limit the ten-contribution export: it
does not establish acceptance or non-acceptance of the Hom pairs.

The subsequent proof-document unit is now independently accepted and published.
Current `SP/BasicProof.md:3–8,45–69`, `SP/FixedVectorsProof.md:3–11,79–91`,
`SP/FunctorialityProof.md:3–8,72–97` and
`SP/UniversalProof.md:3–8,69–91,102–112` explicitly distinguish original Test 2
preparation, validation, independent approval and publication from the later
pilot documentation correction. Universal no longer claims that its current
dependency Markdown retains draft labels. `SP/HomProof.md:8–13,38–62,79–87`
retains the ten-contribution export's coverage limit and asserts no independently
verified historical Hom acceptance or non-acceptance. Its Windows source locator
is labeled historical, with a readable current path at lines 64–77.
Functoriality's Casselman title is corrected at lines 77–82.

The exact candidate is `995398b4-f6f2-45dd-8a7f-d181404cc8c9`, body SHA-256
`91067e3b2388429b4c93da1d74d4fd25fcdcd878cd14bdc62f09aa0f912eebc3`, submitted
by Worker 374 with the original and reused-draft coauthors retained. Its primary
theorem is `Langlands.smoothPartUniversalProperty`, with the exact unchanged
`statement_declaration` `Langlands.SmoothPartUniversalProperty`. Accepted fresh
candidate validation `c0dadffa-5f30-4ef5-8451-709ffde73efd` binds its snapshot
`8dbb286a691e80b46a8e9fba11c0545f4d5d05028e5e89a0e0a6c8fc997e01ab` and
records `proof_accepted=true` with Lake-build, exact-target, unchanged-statement
and frozen-input checks. Its report SHA-256 is
`04b42aa494e3c46870a51b47ed250f99e8f27bedf38c6bad21225df8f93af871`.
Reviewer 2090's complete independent approval report, receipt
`45ad386c59b0420284ec55780e8a0eb2`, binds this candidate and verifies the five
explanations, original Casselman pp.1–2 and original Test 2 evidence. It has no
qualifications. This exact-target receipt concerns the Universal primary theorem;
it does not create missing historical Hom or FixedVectors final-export evidence.

Integration `7d0d94927504403e8b50d17428507678` published this correction at
`e4296643398fb6f96e73eb81e8e5d19a0d2650be`, integrated snapshot
`40dde754183034e47dd2200bf09d021822064741fe5a4f43e6dfecc6070f1812`.
The accepted fresh integrated batch validation has report SHA-256
`060ff2637339330b339ad5d7958e5dc44ba6b0a4c4964dfd5ab3ce45038df17a`,
`acceptance_scope=source-compilation-only` and `proof_accepted=false`.
It is a compilation receipt, distinct from the candidate's exact-target proof
validation and independent semantic approval. The six submitted files match
reviewed, published and current bytes exactly. Relative to the candidate's base
`e6045276bfca31676e0ceb0c8ed92e2709c53f61`, exactly the five proof Markdown
files changed in SmoothPart; all Lean and every other pair in that folder are
unchanged. The Universal target and the complete project import closure of its
statement, including the smooth-part and foundational definitions, are also
unchanged in both Lean and Markdown.

| File | Reviewed = published = current SHA-256 |
| --- | --- |
| `SP/BasicProof.md` | `aeb2a008caea74aa07c09f1fce5741adf518a63239e239545f2f0c5ba7ad0ed8` |
| `SP/FixedVectorsProof.md` | `3fa810121862bb82e77e53314b28f141e5b0cb7691cebe723a98d0584db1e0a0` |
| `SP/FunctorialityProof.md` | `f29b7db66221e5ef7e0db1e169378d4b3b51b7e5754d53c2b371e1ee4e17a56d` |
| `SP/HomProof.md` | `fc43b84cb9b238a2b711f12fbb7e8abfb97ea9ccd155e345b8db452763e1291f` |
| `SP/UniversalProof.lean` | `e8f0bf938c8b069f480b0ca6d41b6b65b8dca24033a960c5bf254388a1d4eea9` |
| `SP/UniversalProof.md` | `00c9919fc60ee4e0990251fd7f916b49998d05b02ee3b0ea06898bb969add1be` |

The corrected FixedVectors proof page preserves the original proof acceptance,
recorded publication, absence of archived final sources/binding and the final
exported batch's `proof_accepted=false`. No missing historical receipt is
invented. I056–I060 and their necessary neighboring status inconsistencies are
therefore corrected without changing any Lean target, binder or import.

### C3/C5 integrated validation and exact files

All three corrections share integrated snapshot
`9e08ed46eb39cf2aabd90e3d50a627417f6907663f5bbf01a3ce76c5529e1071`
and an accepted fresh integrated Lake build, report SHA-256
`87ce5d12470e47d78c5f4d4f7ce890f4916cc7abe25d4db647cbc598db350b41`.
The final validator reports `source-compilation-only` and
`proof_accepted=false`. Independent semantic approval comes from the three
exact-candidate reports, not that batch build. These are documentation
corrections submitted under definition/statement policies, not new proof
acceptances.

The following SHA-256 values match the reviewed files, publication commit and
current checked Library. Every paired Lean hash also equals the original audit
inventory. Additional Markdown files are listed as well as the primary pairs;
only the listed Markdown changed.

| Unit | File | Reviewed = published = current SHA-256 |
| --- | --- | --- |
| C3 | `C/Definitions.md` | `fa692bd5cba2ec7b62279d74b85164fbc2c96e16ec8d97afc3589dd0a959e01a` |
| C3 | `D/CompactDualityStatement.lean` | `aecf6195a2703a560242c597cce8c8de908a3be30ef3a12992956cffc7b3550d` |
| C3 | `D/CompactDualityStatement.md` | `27b6ba05c0923755f12cb6ed6508cc9fd0f4c1112bf6cdcd1a715a06f70c2abb` |
| C3 | `D/FixedVectorsProof.md` | `eb1ef5e384011db5ea8cada19ededfc9ee49b27d77516db25d3514f4783eba6a` |
| C5 definition | `SP/Definitions.lean` | `1362c38a196d6657c4d9dd2388e00c77059fc772bdd7f4369e0cbbee19ca4a47` |
| C5 definition | `SP/Definitions.md` | `b8775524d5fdc90acf4c52611d96c401e588f6eff68f682843ce999cf414ac60` |
| C5 definition | `SP/FixedVectorsDefinitions.md` | `5c1be2bfeb8dffa7bd2da042e1511b3d53eee52ef2320b244165dca32e3714a5` |
| C5 definition | `SP/HomDefinitions.md` | `d5461ee13a0efae027f8ebb4ec2b0263f3a5d6088c8ac76242b6888e466704ba` |
| C5 statement | `SP/BasicStatement.lean` | `d98185a4a0c18d4597f28a435391488f294aac6b8ca1280803930cde5b3964b2` |
| C5 statement | `SP/BasicStatement.md` | `af69366e079a8fe19ad08051b5185e497acf2a97a85f316ad84a62db01edc470` |
| C5 statement | `SP/FixedVectorsStatement.md` | `9eb37597e9af65bac1765cbbf1311d706ba91114899b9efc124835116fe32694` |
| C5 statement | `SP/FunctorialityStatement.md` | `21149561bf2d7fa00b0d069cd0d76b204f6b4955d6d1202b47b37d5a978b19e5` |
| C5 statement | `SP/HomStatement.md` | `210b256fcecde544d0410d9293cc5fcad5072bbcd44868ccf93ce303d159a2b5` |
| C5 statement | `SP/UniversalStatement.md` | `d67356027c3d46b6d32248a44e4088e3d0aa1c8f5a0966856851532393d84e09` |

### Verdict-note publication history

The original verdict note was independently accepted as
`de9e243f-c6c2-4225-8e48-22a084d4cbe0` and published at
`51dec7ffb8514b3e9cad965decf3f967fa045da4`.
The subsequent C1-status update `70a10e4d-e337-4362-9aa9-d6605dd51d50`
was independently approved by Reviewer 1520, receipt
`c0f733cd582149a98e24b2f0695bb390`, review task
`dd822e3b-6bf1-411f-8284-f4f9ac2dd677`, with no qualifications.
Metadata validation `ddec7a78-ad33-4c16-8303-51d012e39c1c` was accepted.
Integration `c09621bbc161407e9c9b93b910b41f8a` published it at
`bf3c3860965e0b6c10d816a5d41e68a8003ef281` after accepted fresh
public-documentation validation. Neither validation claims Lean compilation
or proof acceptance. That reviewed note, its publication and its later copy at
Library `9945aad13b444857950d4381970e4475b0f9673b` share SHA-256
`bc58efc296197e139ab18162a33c7cd3a52b50cc675ede3338dee8e2de244be7`;
the audit README entry also agrees, although later publications updated sibling
entries. That update was pinned to the earlier check at
`225a00380f8ef7b97eb15bda1157dee4ab8b2a03`.

The C2-status update `c2eea7f3-ffdb-453b-91ee-06d6b4eb9eb8` was independently
approved by Reviewer 1535 in review task
`90e118c2-1cdf-4cfc-a269-be07df359bea`, receipt
`7551441025a94aa180abd01962983c74`, with no qualifications.
Metadata validation `c5be8898-9d6a-421c-8bf7-91186ec764ab` was accepted.
Integration `cc80c6b8954a446783868086c195f4a4` published it at
`6e8b1662b2777952bbde62145eb5269a8b2efbef` after accepted fresh
public-documentation validation, with integrated snapshot
`daa1493c2e755951912cc719e4b668e0138d0ace7be9822b8393131b18cac35d`.
The reviewed note and its publication at that commit
have identical SHA-256
`5ebde6525a664c45fa5ece4903cc8feca84917fc7c48d8f524f6a42dccf1663c`.
The reviewed README hash is
`0cf969ad4d7c661e5be3d4f5acc0c64d4984ad1211ba9fb274f77e7a2b3a6336`;
the README hash at that publication is
`311a9a8b3ee5007729be733b667d1e4237f74b3bf90d6ebf8533c81de5d889b1`.
Their audit entries are identical; integration added the sibling Whittaker audit
entry. These public-note validations make no Lean compilation or proof-acceptance
claim. That note was pinned to the earlier check at
`9945aad13b444857950d4381970e4475b0f9673b`.

The C4/C6-approval update `99d61d29-25e6-473c-9436-4334a8bc3755` was
independently approved by Reviewer 1565 in review task
`e5528deb-8f82-4571-a556-22d209511da1`, receipt
`26e8ecbb14d746fb887e2d83ed4ec890`, without qualifications.
Metadata validation `a2f004cb-e0f0-4e92-938f-6745ad8f699e` was accepted.
Integration `6f77bcd02f074322850b455a35b97901` published it at
`0bfd14e8bc613b7c9562aa7ee70086679af1e1f9` after accepted fresh
public-documentation validation, with integrated snapshot
`b0ec7317a4c272cbfecc73248b3dac0a0efe6a7a0a78ce31d9f0d0bd3844ada8`.
The validation makes no Lean compilation or proof-acceptance claim.
Its reviewed note hash is
`183a6807d0e6a97500d971c4f6936c6e95e3da8a078c683b4121357a87b128f4`;
the publication and the pre-update note at Library
`fb40559309dd366f4145aa31aad8c3db11b7cc07` share
`ee6969bb6bcef83e406428b48028e06f72dcfcce60a1552b68b6dc36dec860b4`.
The only note difference is an explicit qualifier pinning its correction statuses
to `6e8b1662b2777952bbde62145eb5269a8b2efbef`. The reviewed README hash is
`e895448a3d6d0ee6ccb91960cb7be9f5f971d048d725d54f889bdc7958cd64fd`;
the published README and its copy at that earlier checked Library have hash
`da3829b5668a2fa4f48238779fda429cf20f37f165055a838aeba0182c5a77a5`.
Its diff adds “at the checked snapshot” to this audit's entry and preserves the
newer geometry sibling entry. These integration edits clarify the dated scope;
the reviewed and published files are not asserted to be byte-identical.

The C4/C6-publication update `35d22671-6020-4e9f-9090-df8e1aa825a9` was
independently approved by Reviewer 1619 in review task
`31bc3a51-e1db-40ed-8873-41a66b01b908`, receipt
`9e7b902432814ce4a1ad4a30aba6dbe1`, without qualifications. Metadata validation
`d23b2426-0099-476e-9004-d0938e7ac8ea` was accepted. Integration
`c64a90eb0d6847b4b3b0f8b5cf44c201` published it at
`9677445f51f08760576e38e9c78f584be84da0b4`, with integrated snapshot
`77dd1c1a3e2a15672de3bfaa7198bc3488dafe34354d9a5470dc56b8bb581a8c`
and accepted fresh public-documentation validation. Neither validation claims
Lean compilation or proof acceptance. The reviewed note, publication and
pre-update note at the earlier check
`4750a03e101b9ad45fc1a4d90a6a3d02d69c73e9` share SHA-256
`f2ea23f85c07cf49211e128cbf12179f55e8cf00a11f1bd68361f2a0308e9697`.
The reviewed README hash is
`4ba52103bf46500e8f5bab82d7034df901289978b01e8c3ce7e0ed70ab3f1310`;
the published README hash at that earlier check is
`dff6d8a355fd58dd43234c2b797d9cf3c5589080d9664d75c9dc8467e63e2b1c`.
This audit's entry is identical. Integration updated the geometry and factors
sibling entries and added the local-CFT sibling entry. That note's statuses
were explicitly pinned to `fb40559309dd366f4145aa31aad8c3db11b7cc07`.

The C3/C5-definition-and-statement update
`cc1a2607-7ad2-4cb3-bccf-ebd57d88a27e` was independently approved by Reviewer
1651 in review task `6ce92e59-eb9b-4e1d-a4ab-53a3daaa26da`, receipt
`5d02bc0502fe43fba2f784d83bd7f36b`, without qualifications. Metadata validation
`b6ad0ee0-3b8a-4c44-ad9a-d3b5925f19a1` was accepted. Integration
`f43c9ded87ba4c48ae1256768cacbdec` published it at
`acc39e30113233fe5beb6a6316d99215aec1ef8b`, integrated snapshot
`dbf66603db9a01a64ec1518bc7958f293acf317a020cf1d0d3c9ef68c63052c6`, after
accepted fresh public-documentation validation. Neither validation claims Lean
compilation or proof acceptance. Its reviewed and published note and the
pre-update note at the current check share SHA-256
`7d96b77123fed9849e77d14957ec1d113e113e7c1faf01df5a89be7ffa39c457`.
The reviewed README hash is
`e4ca1bd77d0ef9c243771ec0f17c4c4090594a81979b20bd9684cceadca0dea8`;
the publication's README hash is
`63c2272c2a1753f813d2ce048e00dd9522b740f11517fb97643406132cb7bb19`.
Integration only added the global-adeles-shimura sibling entry. Later Library
updates changed other sibling entries; this audit's entry remains unchanged
before the current edit. That note's statuses were explicitly pinned to
`4750a03e101b9ad45fc1a4d90a6a3d02d69c73e9`.

This final update records the C5 proof-document publication and preceding
ledger publication, retains all twelve historical/current verdicts and every
evidence limit, and verifies all eight necessary correction publications.
Independent acceptance and publication of this final ledger remain required
before parent completion. Unrelated open mathematical goals and the explicitly
unavailable historical evidence do not become accepted results by this audit.

## Checked file hashes

SHA-256 values below identify the exact audited Lean/Markdown pairs at pilot
commit `dc8cdb2866562d5f929dc912f3563a75cc16ce79`. The module path omits only
its `.lean` / `.md` extension. The inventory records evidence; it does not itself
establish acceptance. All Lean files remain unchanged by this note.

| Module path | Lean SHA-256 | Markdown SHA-256 |
| --- | --- | --- |
| `Langlands/Group/GL/BlockUnipotentHaarProof` | `ade3b6483f62acbbe13dff46feb3a2c4556684f7cb2aff243854a200b8070c73` | `e259545e632933a823ff659aa7f43ad65b9ce77a462661dbfb4d2a177dbe7e53` |
| `Langlands/Group/GL/BlockUnipotentHaarStatement` | `8b1dfe7dcaf22760546ef1c12255541643068b033a499d433c85043c3d8b27bf` | `1d114d44b8079084682f229ca96e53d2541cbdf3845e74e5119cd92b315a5b6c` |
| `Langlands/HarmonicAnalysis/TriangularTranslationProof` | `f73aefb221d55ba7ea911c211cfb35036a62470d979c797955055f9c1e9fb555` | `12bae01aea8c9e53c72408b3fc15f5232fbb7f278e22dd6e416c6e4b9985000a` |
| `Langlands/HarmonicAnalysis/TriangularTranslationStatement` | `abf107b9edbd855ea869b75b8585920523405acdb3c4321412220e93e07c02ee` | `c0295777c8c56408003e7f9f78a3eae490f471e7b2a7db844389cdb458dbec94` |
| `Langlands/Representation/Compact/Definitions` | `afb77f4a622710d058d58b781ebabc38eb3cf5ccb008fb1c12dbb4817db05289` | `aba516fbd56c2718a97650819d48d93acbb309b6442966c40bfedaecbae17916` |
| `Langlands/Representation/Compact/ProjectionProof` | `689b92fac7e04b7ee2cb3dd4702653725a597997331ca62c6461ba7ef12fcc41` | `a2217b34bacd418614535068dcc858ae3d44ad3a0638be726fc8838499f8d5b2` |
| `Langlands/Representation/Compact/ProjectionStatement` | `f0e69eeed6dcc35d12fdb78f554f85e5913355bfc4d2057bf658b5343eb2e45f` | `ab65518fa3a8fefc07ff69610b4332dae41c3a8e34406fb70c94e2dad863e94d` |
| `Langlands/Representation/Compact/SurjectivityProof` | `d1a89efb911951f85a1a691f4f5da3e76101f949eafae0d28b4e193e2fc5a20b` | `5c2ab76bcc362821fcb7363e69e752a0534f043779fe0a415ffbee792fad90f4` |
| `Langlands/Representation/Compact/SurjectivityStatement` | `ad704b0a5522cf5c27f265d3777de04994e251cdcffdbd9faea69fc40ba54778` | `e1fc904da47b1c1b35a7104a1f27d3e8614a5768d346bf6b22cef31545d608ce` |
| `Langlands/Representation/CuspidalSupport/FiniteBlockShapes` | `95a048178cdec1f8b1bf1b79cf7238322d23622022a26b610cbefb31e4b40ff5` | `141fce08a749aa5fc8e88d763c14562520084655a860f6dfa4a7d63c3ead4d3c` |
| `Langlands/Representation/CuspidalSupport/LeviDefinitions` | `313ab39ddedd66f91c734a1e8b9fdae6a8e4eebfb111e464421c28cbef9aae38` | `ecd6d283a17bd6e81bca58d1f7f61628fb5c501be5f1da955f435e324d7a12a2` |
| `Langlands/Representation/CuspidalSupport/TotalConjugatingCountStatement` | `2abc2da82d63e7d3d0990232003e3c1647149a1463a28ffa7621da700e8d1118` | `94796dded406826614d44d943a38af1d2330593903eb747ca75a461ceae78a40` |
| `Langlands/Representation/RestrictedTensor/Separation` | `cfe18e1577796cf61c1c58df88ee6a641862643862b53ae4319dfc5499556f48` | `9a0368e9f9558af2894e48fee4c445d2ee1a7389dc80448ec31f6d5f0ae9a9a2` |
| `Langlands/Representation/Smooth/Contragredient/AdmissibleDualityProof` | `5635b4f840d709a22782b6db40c49ac3ea8e3ca332f7b0973be862a5fda0b439` | `91d07b8385aee910961e6fb2dd4bd00eb0b134334ba3cbb8b531644b4d94cf58` |
| `Langlands/Representation/Smooth/Contragredient/AdmissibleDualityStatement` | `a3b9788828170bc1ef481d64332c945c3827876bcf3d12f7c9af7278b1378e09` | `bfb5809f5bfd36bd7b873b7b41932d0777f9f54e70369011b88800d9b15dfc26` |
| `Langlands/Representation/Smooth/Contragredient/CompactDualityProof` | `5b07a1aaf036dffa1609f488485992513e17ee9aec49c0e002584a7226220594` | `a198bbdda5652427b692f37ddb7326c67e1dd5c95f1b57a8ea531b4dabc334ec` |
| `Langlands/Representation/Smooth/Contragredient/CompactDualityStatement` | `aecf6195a2703a560242c597cce8c8de908a3be30ef3a12992956cffc7b3550d` | `613b594bff5e9079e0dee319d57fe8321165c06127ab5dab8e012e43081cc291` |
| `Langlands/Representation/Smooth/Contragredient/FixedVectorsProof` | `f475f265f111a5b478bbd257d57bab3721590a17e2a0593a063cfecc51c6c228` | `7d0a0117e8a59a1075ec43ac5f1850a99e785e62747cedd2d46a76bf5583e853` |
| `Langlands/Representation/Smooth/Contragredient/FixedVectorsStatement` | `b2084f9d4a83c71da4d5ade7e884edb4255ea350a747c2ed065a332dad278195` | `7f0facc6b58ec1267a7f9cf27398d8bfced185f91389a29f64ac81c79bde08ed` |
| `Langlands/Representation/Smooth/Factorization/RestrictedTensorStatement` | `e3d72b95a267b6f0291efde9c11776fa6107fb4ff9091c58d58b8efad8ff1223` | `4cee5acda4887bfd7b37c20b653af635ee28716605e0ee47be35336338d7795c` |
| `Langlands/Representation/Smooth/SmoothPart/BasicProof` | `68683b474202a221a179d5c989b8a5774a40ec80e28093b04821c403a25a28fc` | `ea0388747d7fae108c6750e55c168e59c6e7e2ec501b168c42595e425eff0a24` |
| `Langlands/Representation/Smooth/SmoothPart/BasicStatement` | `d98185a4a0c18d4597f28a435391488f294aac6b8ca1280803930cde5b3964b2` | `8c9c8131b33808f20f73048b7ef49e6f7775142614ef3c493a5d315015d80a6d` |
| `Langlands/Representation/Smooth/SmoothPart/Definitions` | `1362c38a196d6657c4d9dd2388e00c77059fc772bdd7f4369e0cbbee19ca4a47` | `f7c4bb00e2155c608859a8ea33d4297e9091bc1cfea55161119556d0e943741f` |
| `Langlands/Representation/Smooth/SmoothPart/FixedVectorsDefinitions` | `aa6aa3fc09cb94adeb9145f68906b8a9829952ba99bf256659b984a2bf792751` | `0136523bc644ba53ad612b8e68e9639b99ec5dae3d4a984a0db1dd4ba725921d` |
| `Langlands/Representation/Smooth/SmoothPart/FixedVectorsProof` | `62ce8bc649cf6947c364e7fd368aeaceb96343ed8b30e9a1a794e0ad7f6e988f` | `6609d0147f6b4f96212902886307714314cd4ce2ddd18d78b12aefa8a350a8d9` |
| `Langlands/Representation/Smooth/SmoothPart/FixedVectorsStatement` | `a452b0319d1b37a2bb6eb499dd4f6bcfb54ec04c6ea263cbd7104d5f3a01a345` | `691885e2eecf6a7652e96dfd89c681505243f83a877c41b79f0f7ce2fff5deee` |
| `Langlands/Representation/Smooth/SmoothPart/FunctorialityProof` | `68b70bb03a5f38eb1049430724032e2009b2af2ea6aa93b260f8eba8d71cd2ce` | `f3054a57ca4a641a8b75f7fb970002235d331b27a72da21b0b55962275c223d8` |
| `Langlands/Representation/Smooth/SmoothPart/FunctorialityStatement` | `d40715e20a723de77b915d314c531a5e90d54272b7d0f03df5a7420c4b150651` | `06d723793ba450cac16003b2917f8801dea1e5e046c81b75614d48fd650e075a` |
| `Langlands/Representation/Smooth/SmoothPart/HomDefinitions` | `089ae8481d71a254c643483f656eae1d71b8b0de2a33313f4692f5cafb1ee2b6` | `53777096511731ee5e20702052c3ea90390543c4891090c3a83d20bfd2a4a1cf` |
| `Langlands/Representation/Smooth/SmoothPart/HomProof` | `bd534e2e8bec43a0a5b1e68ad4f1fa51e1c7277261fd5f6536a89e040eb8d4bb` | `29f491f6fc5d8caf8270b5c2887e0be2a41e369bba3ae64200300d11d13a0ae5` |
| `Langlands/Representation/Smooth/SmoothPart/HomStatement` | `f21bed58d498ea6e0e5116b2ece50bf37082de4ce9271fe9971057a9931b78aa` | `f27387cdbd8536c0b301c0685e9241d82e3b10a32b2e035524754de4f49d8618` |
| `Langlands/Representation/Smooth/SmoothPart/UniversalProof` | `e8f0bf938c8b069f480b0ca6d41b6b65b8dca24033a960c5bf254388a1d4eea9` | `f8b2e6a4633eb2a44daf79b68cae3c6f1fcdf7f99d040a6f2ac56e5d80ff2b48` |
| `Langlands/Representation/Smooth/SmoothPart/UniversalStatement` | `ec4b14b1ec0e55840cdc1a1c2fc1aa5c31b65ee0de1ac9b70222242708cded3d` | `a96cc50171e131c2a0540ed4fc7b99706f84b67b77610be996ad1ee868890d7d` |
| `Langlands/VirtualRepresentation/Supercuspidal/Dual` | `5f92c2cbd3e2bfe655ccd3871b4e5fba2ef626d8429fd1ce32059a33331e44f4` | `315a4b0c512c5153f64552e68be1a87bf47897402ca20a07626f53409de0a691` |
