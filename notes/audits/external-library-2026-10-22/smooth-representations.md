# External Library audit: smooth representations and release status

Worker 184, original audit 2026-10-22; correction-status update 2026-10-23.
Parent task: `651119f8-4579-446c-ac91-e18c3778f140`, revision 1.

All twelve assigned findings **held** at the original checked pilot Library
commit `dc8cdb2866562d5f929dc912f3563a75cc16ce79`. At the current check,
`225a00380f8ef7b97eb15bda1157dee4ab8b2a03`, **I014 no longer holds after its
independently accepted and published correction**; the other eleven still hold.
I033 has independent approval but awaits publication. The other four correction
units remain pending. This audit found no reason to change the corresponding
Lean declarations or proof targets. Publication of this verdict note does not
complete the parent task: every required correction must also pass independent
review and be published, and its evidence must be added to the ledger.

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
At the 2026-10-23 current check all 34 Lean files and 33 paired Markdown files
still have those hashes. The sole changed file is `VR/Dual.md`, whose reviewed
correction and current hash are recorded under C1 below.
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
| I033 | Holds | `GL/BlockUnipotentHaarStatement.md:46–53` still calls the triangular principle unproved. `Langlands/HarmonicAnalysis/TriangularTranslationProof.lean:83–85` proves `finiteTriangularTranslation`; `GL/BlockUnipotentHaarProof.lean:165–168` applies it to close the coordinate-Haar target. Their independent acceptance and publication are verified below. | C2: distinguish the statement module's local scope from the existing proofs. |
| I036 | Holds | `C/Definitions.md:66–68` uses future tense for existing statements and proofs. `C/ProjectionStatement.lean:9–19`, `C/ProjectionProof.lean:47–80`, `C/SurjectivityStatement.lean:9–17` and `C/SurjectivityProof.lean:8–17` supply projection, identity on fixed vectors, naturality and fixed-vector surjectivity. | C3: use present implementation status while retaining construction-only local scope. |
| I053 | Holds | `D/CompactDualityStatement.md:52–54` calls those two proofs pending. The proof declarations cited for I036 are complete. `D/CompactDualityProof.lean:1–2` imports its target and averaging definitions; its argument does not import or assume the two separate proof modules. Independence of dependencies is true; nonexistence of their proofs is false. | C3: preserve the dependency distinction and remove obsolete pending wording. |
| I054 | Holds | `D/FixedVectorsProof.md:62` calls compact duality and reflexivity pending. `D/CompactDualityProof.lean:113–118` proves `smoothDualCompactFixedDuality`; `D/AdmissibleDualityProof.lean:116–123` proves `smoothAdmissibleDuality`. The latter's cofinality and admissibility conditions cannot be omitted. | C3: name the existing separate results and their assumptions; retain the elementary proof's independence from them. |
| I055 | Holds | `F/RestrictedTensorStatement.md:135–139` describes separation as pending/unavailable. `RT/Separation.lean:293–301,330–336,384–392,422–429` constructs `finiteSeparation`, inverse `reassemble`, `localSeparation` and `productSeparation`. Its acceptance is verified below. | C4: distinguish available algebraic separation from representation-theoretic goals. |
| I056 | Holds | `SP/BasicStatement.md:3–6,41–44` calls the target unaccepted and the proof development-only. `SP/BasicProof.lean:63–71`, theorem `Langlands.smoothPartBasic`, supplies the entire target. Original independent statement and proof acceptances and publications are verified below, beyond the neighboring Markdown's claims. | C5: reconcile dated target and proof status. |
| I057 | Holds | `SP/Definitions.md:3–5` calls the pair unaccepted development. `SP/Definitions.lean:20–102` constructs the smooth-vector submodule, restricted representation, inclusion, lift, map and smooth equivalence. Original definition approval/publication is verified below. | C5: remove obsolete undated status, while retaining the distinction between compilation and acceptance. |
| I058 | Holds | `SP/FixedVectorsDefinitions.md:27–35` calls this construction merely proposed and the neighboring laws unaccepted drafts. `SP/FixedVectorsDefinitions.lean:16–23` constructs `smoothPartFixedVectorsEquiv`; `SP/FixedVectorsProof.lean:13–35` proves the value, inverse-value and naturality laws and whole target. Definition, target and original proof approval/publication are verified below, with the proof archive limitation explicitly retained. | C5: distinguish construction, statement, implemented laws and original proof acceptance accurately. |
| I059 | Holds | `SP/FunctorialityStatement.md:3–6,35–37` labels the target unaccepted and the proof development evidence. `SP/FunctorialityProof.lean:36–41`, `Langlands.smoothPartFunctoriality`, proves all four clauses. Original statement/proof validation, independent approval and publication are verified below. | C5: reconcile statement and proof status. |
| I060 | Holds | `SP/UniversalStatement.md:3–8,36–37` describes an unaccepted target awaiting a separate proof. `SP/UniversalProof.lean:28–33`, `Langlands.smoothPartUniversalProperty`, proves the whole target, including its internal topological-group binder and cross-universe unique factorization. Original statement and proof acceptances/publications are verified below. | C5: retain Prop-definition local scope and cite the existing proof. |
| ISSUES-1 DOC-03 | Holds | `CS/TotalConjugatingCountStatement.md:43–47` denies a Library `Finite (BlockShape n)` instance. `CS/FiniteBlockShapes.lean:10–34` constructs `BlockShape.toComposition`, proves its injectivity and supplies `finiteBlockShape` for every natural rank, including zero. The statement module's entire project import closure excludes this helper. Local import absence is true; Library absence is false. | C6: distinguish global availability, local imports, finiteness and the exact factorial count. |

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
archimedean and Hilbert settings are also separate. C4 must correct availability
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
20 modules and excludes `FiniteBlockShapes`. That local scope must remain
unchanged by this documentation correction. Its
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
mathematics is by current Lean name and import, not by artifact ID. They are not
the pending audit-correction candidates.

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
approve reviews with no qualifications, and recorded publication. All ten
current Lean/Markdown pairs match their original accepted bundle SHA-256 values.
For nine pairs the archived `archive/1/final/` files are also present and match
the current bytes. The exception is detailed immediately after the table.

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
export. Its current Lean hash
`62ce8bc649cf6947c364e7fd368aeaceb96343ed8b30e9a1a794e0ad7f6e988f`
and Markdown hash
`6609d0147f6b4f96212902886307714314cd4ce2ddd18d78b12aefa8a350a8d9`
match the exact original accepted bundle. Original validation
`997582d4-ff38-42e2-a2da-611cc12605a4` has `proof_accepted=true`, Lake build and
exact-target evidence, and Reviewer 167 independently approved it. Its publication
row is present at the Test 2 commit in the table. However, the exported final
integration validation is a shared batch build with `proof_accepted=false`,
not a fresh exact-target proof acceptance; it supplies no final semantic-check
or source-binding record. Thus this note verifies original proof acceptance,
recorded publication and current equality to the original accepted hashes. It
does not claim an archived-final-byte comparison or fresh exact-target acceptance
of that final integration batch. This limitation does not justify describing the
original construction/target as unaccepted, nor the implemented laws as nonexistent.

## Correction ledger

Status checked on 2026-10-23 against authoritative TaskHub fetch and task records.
C1 is accepted and published. C2 has successful machine validation and independent
approval, but fetch still reports `accepted=false`, `public=false` and
`status=staged`; its publication remains pending. C3–C6 were freshly inspected:
each is ready, unassigned, with no candidate. Each task requires unchanged Lean
bytes and the mathematical artifact workflow for paired Markdown, followed by
independent review and publication.
C5 permits the necessary neighboring SmoothPart documentation to be reconciled
within the same status issue. This audit note uses the separate public-note
workflow. The ledger must be updated when actual correction evidence arrives.

| Unit | Finding coverage | Correction task / revision | Candidate, review, validation and publication |
| --- | --- | --- | --- |
| C1 | I014 | `c3bb11ea-663b-419e-bd8c-5ca027ca5092` / 1 | Candidate `536e6fe6-890f-4cce-a477-e11fecad81a6`, `lean.definition@1`; validation `bdc3dea1-070a-4917-8eae-5aad72225c0d` accepted; Reviewer 1474 approved review task `587f9903-036f-4cde-b84f-7b7d66080503`, no qualifications; published at `a4f4742431c7298bf38f4d4e6bc03a6cd7a33a18`. |
| C2 | I033 | `5f109d54-307b-44b4-966e-f57a30351919` / 1 | Candidate `ae344c62-c5d1-4e53-ba14-6c41989de5ad`, `lean.statement@1`; validation `678e20d6-11ab-4e01-a1f4-66d2c678634c` accepted; Reviewer 1487 approved review task `ef89df93-2ea2-4712-974e-9c777f5a09cd`, no qualifications; publication pending. |
| C3 | I036, I053, I054 | `8454a266-f4aa-441b-8c6e-366da6de6819` / 1 | All pending |
| C4 | I055 | `55caa000-0cfc-4d80-be3f-6ba06d005315` / 1 | All pending |
| C5 | I056, I057, I058, I059, I060 | `d3c12473-e617-41d9-bf73-729d7c71f1ea` / 2 | All pending |
| C6 | ISSUES-1 DOC-03 | `89b3bb14-8afe-4e87-9c07-b14d0fe8c481` / 1 | All pending |

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

### C2: approval awaiting publication

The exact candidate body hash is
`b54c994c7539b28d126d7a3d6d62af5c4621db8f9805b2661354832bfe45c7e0`.
Its accepted machine validation includes Lake build and declaration-kind checks,
with `proof_accepted=false`; this is a statement documentation correction.
Reviewer 1487's full approval report binds that hash and verifies the unchanged
Lean, the complete triangular theorem in independent universes, its `{0,uF}`
coordinate-Haar application, the measurable correction and lower-gap conditions,
and the separate scaling scope. The candidate's paired Lean hash is
`8b1dfe7dcaf22760546ef1c12255541643068b033a499d433c85043c3d8b27bf`;
its proposed Markdown hash is
`b6c99f2cf13b1caacca98f9de949bbba83faffcf7b13ae3c2f1bec0c62d76f0c`.
The current Library still has the old Markdown hash recorded below. Approval
therefore does not yet discharge this correction's publication requirement.

The original verdict note was independently accepted as
`de9e243f-c6c2-4225-8e48-22a084d4cbe0` and published at
`51dec7ffb8514b3e9cad965decf3f967fa045da4`; this update adds the correction evidence
without changing the original twelve findings or the historical evidence limits.
No required correction is waived by publication of this verdict ledger. Completion
requires the independently accepted and published updated ledger and every
still-needed correction. Unrelated open mathematical goals remain outside this
audit's completion conditions.

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
