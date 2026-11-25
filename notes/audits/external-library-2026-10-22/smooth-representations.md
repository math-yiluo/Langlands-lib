# External Library audit: smooth representations and release status

All twelve findings of this area **held** at the original checked Library
commit `dc8cdb2866562d5f929dc912f3563a75cc16ce79` (audit of 2026-10-22). At the current check (2026-10-24),
`e4296643398fb6f96e73eb81e8e5d19a0d2650be`, **all twelve no longer hold after
documentation corrections, which are in the Library**. Eight corrections
cover C1–C6, including the C5 corrections of the definition, statement and neighboring
proof documents. The commits where they entered the Library and the
file comparisons are recorded below. This audit found no reason to change the
corresponding Lean declarations or proof targets.

All correction statuses below describe the check at Library
`e4296643398fb6f96e73eb81e8e5d19a0d2650be`; they do not assert the status of
later Library revisions. Historical evidence limits and unrelated mathematical
proof obligations remain as explicitly described below.

## Evidence boundary

The allegations are in the registered source
`external-library-audits-2026-10-22`, folder SHA-256
`975133657fad9fc7d0806e2cf4aaefac907edd151ec4df6cdd5d92b18a95a93b`, retained at
`literature/External Library audits 2026-10-22/`.
`ISSUES-2.md` supplies I014, I033, I036 and I053–I060; `ISSUES-1.md` supplies
DOC-03. Their mirror snapshots correspond respectively to Library commits
`f9c1742752d97c488fc1a835070bf50b534f4427` and
`c5a40b0f54880b1825ea05214c2b066f68bfc156`. Neither report is evidence. The verdicts below retain the original audit findings and distinguish
the current status after correction. Exact files are identified in the hash
inventory and correction evidence, rather than treating the report's line
numbers as current by assumption.

The complete relevant declarations, hypotheses, quantifiers, universes and
imports were inspected, together with paired Markdown and the original-source
passages listed below. The 34 audited pairs were unchanged between the earlier
check at `208944fe891035d0c3be003664e2ad2d471951e3` and the original audit commit.
At the current check (2026-10-24) all 34 Lean files and 14 paired Markdown files
still have those hashes. The 20 changed Markdown files are exactly the corrected
files recorded with their current hashes under C1–C6 below: four C1/C2/C4/C6
pages, three C3 pages, eight C5 definition/statement pages, and five C5 proof
pages. The five newly corrected proof pages and their submitted Lean file match
their corrected versions in the Library. All 106 project modules in the
audited import closure retain unchanged Lean since the prior check at
`62ea36c5cce8fa88e0b551b153b0fdc3087190e0`; the only paired-Markdown changes
in that closure are the five C5 proof pages. There is no changed Lean module
to recompile.
A recovery development check succeeded
with zero errors and warnings for `Compact.ProjectionProof`,
`Compact.SurjectivityProof`, `Smooth.Contragredient.CompactDualityProof` and the
four `Smooth.SmoothPart` proof modules Basic, FixedVectors, Functoriality and
Universal (all under `Langlands.Representation`). The Lean service reused their
build outputs. This is development compilation, **not** a proof check against
exact targets. The historical claims below rest on the records of the results'
entry into the Library.

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
| I014 | Held at audit; no longer holds after C1 | Original `VR/Dual.md:56–65` described the lattice map as its own square. `VR/Dual.lean:67–106` constructs `dualLatticeEquiv` by reindexing and proves `dualLatticeEquiv_symm`, `dualLatticeEquiv_apply_apply` and `dualLatticeEquiv_trans_self`: inverse equals itself, square equals identity. Current `VR/Dual.md:59–60` states precisely those two identities. C1's entry into the Library and matching hashes are verified below. | C1 published; no further change needed for I014. Conditional supercuspidal closure is retained. |
| I033 | Held at audit; no longer holds after C2 | Original `GL/BlockUnipotentHaarStatement.md:46–53` called the triangular principle unproved. `Langlands/HarmonicAnalysis/TriangularTranslationProof.lean:83–85` proves `finiteTriangularTranslation`; `GL/BlockUnipotentHaarProof.lean:165–168` applies it to close the coordinate-Haar target. Current `GL/BlockUnipotentHaarStatement.md:51–72` describes both existing proofs and their application. C2's entry into the Library and matching hashes are verified below. | C2 published; no further change needed for I033. The local Prop-only scope and separate scaling results remain distinct. |
| I036 | Held at audit; no longer holds after C3 | Original `C/Definitions.md:66–68` used future tense for existing statements and proofs. `C/ProjectionStatement.lean:9–19`, `C/ProjectionProof.lean:47–80`, `C/SurjectivityStatement.lean:9–17` and `C/SurjectivityProof.lean:8–17` supply projection, identity on fixed vectors, naturality and fixed-vector surjectivity. Current `C/Definitions.md:65–86` accurately describes these implementations and the limits of their historical records. | C3 published; construction-only local scope and one-compact-open hypotheses retained. |
| I053 | Held at audit; no longer holds after C3 | Original `D/CompactDualityStatement.md:52–54` called those two proofs pending. The proof declarations cited for I036 are complete. `D/CompactDualityProof.lean:1–2` imports its target and averaging definitions; its argument does not import or assume the two separate proof modules. Current `D/CompactDualityStatement.md:45–71` preserves this dependency distinction and names the existing proofs. | C3 published; historical independent acceptance of the three compact proof submissions is not inferred. |
| I054 | Held at audit; no longer holds after C3 | Original `D/FixedVectorsProof.md:62` called compact duality and reflexivity pending. `D/CompactDualityProof.lean:113–118` proves `smoothDualCompactFixedDuality`; `D/AdmissibleDualityProof.lean:116–123` proves `smoothAdmissibleDuality`. Current `D/FixedVectorsProof.md:60–92,103–111` describes these separate results, their actual assumptions and the verified proof of admissible duality. | C3 published; compact-open cofinality and the distinct smoothness/admissibility clauses retained. |
| I055 | Held at audit; no longer holds after C4 | Original `F/RestrictedTensorStatement.md:135–139` described separation as pending/unavailable. `RT/Separation.lean:293–301,330–336,384–392,422–429` constructs `finiteSeparation`, inverse `reassemble`, `localSeparation` and `productSeparation`. Current `F/RestrictedTensorStatement.md:135–150` describes these available algebraic constructions and preserves the separate representation-theoretic targets. C4's entry into the Library and matching hashes are verified below. | C4 published; no further change needed for I055. Algebraic separation does not prove the four targets or general factorization. |
| I056 | Held at audit; no longer holds after C5 | Original `SP/BasicStatement.md:3–6,41–44` called the target unaccepted and the proof development-only. `SP/BasicProof.lean:63–71`, theorem `Langlands.smoothPartBasic`, supplies the entire target. Current `SP/BasicStatement.md:41–60` identifies that proof and records the separate original statement/proof acceptances and publications. | C5 statement and proof-document corrections published; no further change needed. |
| I057 | Held at audit; no longer holds after C5 | Original `SP/Definitions.md:3–5` called the pair unaccepted development. `SP/Definitions.lean:20–102` constructs the smooth-vector submodule, restricted representation, inclusion, lift, map and smooth equivalence. Current `SP/Definitions.md:3–7,91–127` records verified historical approval/publication and distinguishes construction fields from separate laws. | C5 definition and proof-document corrections published; no further change needed. |
| I058 | Held at audit; no longer holds after C5 | Original `SP/FixedVectorsDefinitions.md:27–35` called this construction merely proposed and neighboring laws unaccepted drafts. `SP/FixedVectorsDefinitions.lean:16–23` constructs `smoothPartFixedVectorsEquiv`; `SP/FixedVectorsProof.lean:13–35` proves the whole target. Current `SP/FixedVectorsDefinitions.md:38–72` and `SP/FixedVectorsStatement.md:51–59` separate the three original acceptances and preserve the proof final-export limitation. | All three C5 corrections published; historical final-export limit retained. |
| I059 | Held at audit; no longer holds after C5 | Original `SP/FunctorialityStatement.md:3–6,35–37` labeled the target unaccepted and the proof development evidence. `SP/FunctorialityProof.lean:36–41`, `Langlands.smoothPartFunctoriality`, proves all four clauses. Current `SP/FunctorialityStatement.md:35–58` identifies that proof and records successful original validation, independent approval and publication separately from earlier unsuccessful checks. | C5 statement and proof-document corrections published; no further change needed. |
| I060 | Held at audit; no longer holds after C5 | Original `SP/UniversalStatement.md:3–8,36–37` described an unaccepted target awaiting a separate proof. `SP/UniversalProof.lean:28–33`, `Langlands.smoothPartUniversalProperty`, proves the whole target. Current `SP/UniversalStatement.md:38–58` identifies it and records separate original acceptances/publications. Current `SP/UniversalProof.md:79–91,102–112` makes the preparation account historical and links the corrected dependency status sections. | C5 statement and proof-document corrections published; no target or binder change was required. |
| ISSUES-1 DOC-03 | Held at audit; no longer holds after C6 | Original `CS/TotalConjugatingCountStatement.md:43–47` denied a Library `Finite (BlockShape n)` instance. `CS/FiniteBlockShapes.lean:10–34` constructs `BlockShape.toComposition`, proves its injectivity and supplies `finiteBlockShape` for every natural rank, including zero. Current `CS/TotalConjugatingCountStatement.md:44–62` names the helper, explains its absence from the statement's complete import closure and distinguishes finite-sum infrastructure from the factorial count. C6's entry into the Library and matching hashes are verified below. | C6 published; no further change needed for DOC-03. The exact factorial target and all imports remain unchanged. |

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
For admissible duality, the check of its proof is recorded below. Removing false
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
files at the checked snapshot. The literature index
`literature/_central-library-pointers.md` gives the retained Central-Library
paths for these exact registered source IDs.

| Source ID | Original, locators and reading extent | Content SHA-256 |
| --- | --- | --- |
| `henniart-2000-simple-proof` | G. Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur un corps p-adique*, Invent. Math. 139 (2000), 439–455. §§2.5–2.6, printed p.446 / PDF p.8: free integral lattices and linear extension of contragredient. | `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de` |
| `casselman-2019-smooth-representations` | B. Casselman, *Introduction to admissible representations of p-adic groups*, Chapter II, June 16, 2019. Read pp.1–4 and 6–7; p.1 ambient conventions, p.2 smooth vectors, II.1.2 pp.3–4 averaging, II.1.3 p.4 fixed-vector exactness, II.3.1 and Lemma II.3.2 p.6 duality/reflexivity. | `2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d` |
| `flath-1979-tensor-products` | D. Flath, *Decomposition of representations into tensor products*, Corvallis, Proc. Symp. Pure Math. 33, Part I (1979), 179–183. Read the complete article, PDF pp.175–179 of the retained Part I volume; §2 pp.180–181 and Example 2 p.181 are the principal construction locators. Hash is of the whole retained volume. | `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5` |
| `bernstein-zelevinsky-1977-induced-i` | I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977), 441–472. Read printed pp.447–449 / PDF pp.8–10, especially §§2.6–2.8, Lemma 2.11, §2.13(c), §2.14(2). | `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092` |

## Results already in the Library

These are earlier results in the Library; reuse of mathematics is by current
Lean name and import. They are distinct from the later audit corrections.

### First appearance in this Library

For each row, both current paired file hashes equal the version that first
entered the Library, at the commit given. Proofs were checked with a Lake
build, against their exact targets, with statements and inputs unchanged;
definitions with build and declaration-kind checks. Separation and finite
shapes are definitions here, not proofs of the distinct
representation-theoretic/counting targets.

| Current declaration | Publication commit |
| --- | --- |
| `Langlands.HarmonicAnalysis.finiteTriangularTranslation` | `0686b4fa6c8df22845bba2e2668a723a41d47c84` |
| `Langlands.glBlockUnipotentCoordinateHaarStatement` | `916154eeb26478d9efb73f26a117f337c9a438a2` |
| `Langlands.smoothAdmissibleDuality` | `196ceda926c7cfe1fdbe5ae57c08133d83bbf940` |
| `Langlands.RestrictedTensor.productSeparation` | `68e8013fc4fed0de284fd849695676aca2e0c32d` |
| `Langlands.GeneralLinear.BlockShape.toComposition` | `2e31df852eed5b4c1a45eca581f8480418360a34` |

### Smooth parts: records of an earlier line of the Library

The smooth-part modules were first published in an earlier line of the
Library (called Test 2 in its records) and carried into this Library without
their records. A read-only export of those records is registered as
`test2-smooth-part-acceptance-receipts-2026-10-22`, folder fingerprint
`4d77169bf746114b7df83c650215ba7794fb523f1deb51a6be1b16ebfb376c6d`
(literature folder `Test 2 acceptance receipts of smooth-part contributions/`).
The commits in this table are commits of that earlier line.

All ten modules passed their checks there. Before C5's documentation
corrections, all ten Lean/Markdown pairs at Library
`fb40559309dd366f4145aa31aad8c3db11b7cc07` matched the hashes recorded there,
and for nine pairs the final files kept in the export matched those bytes.
All ten Lean files remain identical at the current check; all ten of their
Markdown files now carry the C5 corrections recorded below. The exception to
the final-file comparison is detailed immediately after the table.

The entry names below are modules under
`Langlands.Representation.Smooth.SmoothPart`.

| Module and its kind | Publication commit in the earlier line |
| --- | --- |
| `Definitions`: definitions | `cd8210540c75a7d0a9e2431e4bc9a2535ceaf919` |
| `FixedVectorsDefinitions`: definitions | `a158df54c354b831c3b158cd0a299f3f78acb9da` |
| `BasicStatement`: statement | `6c1028baa3f29e21f18dd147d07f4b7873a88b8c` |
| `BasicProof`: proof | `d0f5322f745425b08ae8e72c1031206f45cb049e` |
| `UniversalStatement`: statement | `a28679cf25a4ce001af4e724a51fd7db72864cd3` |
| `UniversalProof`: proof | `9db46907db3181b0c1dfd287b8ab2f1f02054cab` |
| `FixedVectorsStatement`: statement | `9db46907db3181b0c1dfd287b8ab2f1f02054cab` |
| `FixedVectorsProof`: proof | `e4e22245747ec04edd4445d4557b746f8f53de29` |
| `FunctorialityStatement`: statement | `672a1bfbca2444507019dc6764810d0c0bcb81e5` |
| `FunctorialityProof`: proof | `d0f5322f745425b08ae8e72c1031206f45cb049e` |

The Basic, Universal, FixedVectors and Functoriality proofs were checked
there against their exact targets with Lake builds; definitions and
statements are not proofs. Two modules passed only on a second check.

**FixedVectorsProof evidence limit.** The export keeps no final files for
FixedVectorsProof. Its unchanged current Lean hash
`62ce8bc649cf6947c364e7fd368aeaceb96343ed8b30e9a1a794e0ad7f6e988f`
and pre-correction Markdown hash
`6609d0147f6b4f96212902886307714314cd4ce2ddd18d78b12aefa8a350a8d9`
match the bundle originally checked. The current Markdown instead has the C5
proof-document correction hash recorded below; it is not asserted to match
that original bundle. Its original check against the exact target passed, and
it was published at the commit in the table; but the exported final check of
the integrated batch was a compilation only, with no record binding the final
source. Thus this note verifies the original proof check, the publication,
the unchanged current Lean and the equality of the pre-correction Markdown
with the original hashes; it does not claim a final-file comparison or a
fresh check against the exact target. This limitation does not justify
describing the original construction/target as unchecked, nor the
implemented laws as nonexistent.

## Corrections

All eight corrections under C1–C6 are in the Library. Each preserved the Lean
bytes and changed paired Markdown; the SmoothPart proof-document correction
was checked against the exact proof target. A note in the Library is not a
proof.

| Correction | Finding coverage | First in the Library at commit |
| --- | --- | --- |
| C1 | I014 | `a4f4742431c7298bf38f4d4e6bc03a6cd7a33a18` |
| C2 | I033 | `451f42a052568843a4d727659c3d0a6c66d38ca6` |
| C3 | I036, I053, I054 | `4750a03e101b9ad45fc1a4d90a6a3d02d69c73e9` |
| C4 | I055 | `4ab35fd7cc442c437d97a7e9a247b902533aa199` |
| C5 | I056, I057, I058, I059, I060 | definition and statement corrections `4750a03e101b9ad45fc1a4d90a6a3d02d69c73e9`; proof-document correction `e4296643398fb6f96e73eb81e8e5d19a0d2650be` |
| C6 | ISSUES-1 DOC-03 | `4ab35fd7cc442c437d97a7e9a247b902533aa199` |

### C1: correction

The correction was checked against the exact unchanged Lean, built with Lake
when it entered the Library, and first appeared at the commit stated.

Both the commit where it entered the Library and the checked Library have the corrected pair:
`VR/Dual.lean` SHA-256
`5f92c2cbd3e2bfe655ccd3871b4e5fba2ef626d8429fd1ce32059a33331e44f4`
and `VR/Dual.md` SHA-256
`02ef511de373ea89512c1a4a725cb7dd2020f7dc97ca47cf72219941670d0eed`.
Direct comparison with the original audited pair confirms unchanged Lean and
only the corrected inverse/square sentence plus line wrapping. The generic
cofinality and supercuspidal-closure inputs, canonical closure input and
Henniart provenance remain unchanged.

### C2: correction

The correction was checked against the unchanged Lean, the complete
triangular theorem in independent universes, its `{0,uF}` coordinate-Haar
application, the measurable correction and lower-gap conditions, and the
separate scaling scope. It first appeared in the Library at
`451f42a052568843a4d727659c3d0a6c66d38ca6`, where it was built with Lake.

The corrected pair, the commit where it entered the Library and the checked
Library have identical hashes. The unchanged Lean hash is
`8b1dfe7dcaf22760546ef1c12255541643068b033a499d433c85043c3d8b27bf`;
the corrected Markdown hash is
`b6c99f2cf13b1caacca98f9de949bbba83faffcf7b13ae3c2f1bec0c62d76f0c`.
Current `GL/BlockUnipotentHaarStatement.md:6–12` distinguishes the local
Prop declaration from its separately published proof. Lines `51–72` describe
the complete triangular theorem, measurable correction, strict lower-gap
dependence and `{0,uF}` application; lines `74–76` retain the separate
determinant-scaling and block-modulus scope. I033 is therefore corrected.

### C4: correction

The correction keeps the audited Lean hash
`e3d72b95a267b6f0291efde9c11776fa6107fb4ff9091c58d58b8efad8ff1223`
and has corrected Markdown hash
`cea307af8be1439f64e9a3785c1b67569cc4ef598143f814e69e4637d408a128`; compared
with the original audited pair, the sole change is the availability
paragraph. It was checked against the four existing algebraic equivalences,
their independent universes, reference-vector conditions, actual
restricted-product action and original Flath pp.179–183. The correction
retains all four distinct representation-theoretic targets and the separate
general-factorization scope. It first appeared in the Library at
`4ab35fd7cc442c437d97a7e9a247b902533aa199`, where it was built with Lake, and
both file hashes match that commit and the checked Library.
Current `F/RestrictedTensorStatement.md:135–144` describes the constructions and
their hypotheses; lines `146–153` retain their limited scope. I055 is corrected.

### C6: correction

The Lean hash
`2abc2da82d63e7d3d0990232003e3c1647149a1463a28ffa7621da700e8d1118`
of `CS/TotalConjugatingCountStatement.lean` is unchanged. The corrected
Markdown hash is
`0448a3105681043302fafee9291bbffba6b48c28c6e520e15c1733760f14030d`. Direct
comparison shows only the correction attribution and the availability
paragraph changed. The correction was checked against the helper's all-rank
finiteness, including zero, its absence from the statement's complete import
closure, finite dependent-sum infrastructure, the unchanged factorial target
and original BZ77 pp.447–449. It does not infer the factorial equality from
finite instances or deny the separate downstream counting proof. It first
appeared in the Library at `4ab35fd7cc442c437d97a7e9a247b902533aa199`, built
with Lake together with C4. The corrected pair, that commit and the checked
Library have identical hashes. Current `CS/TotalConjugatingCountStatement.md:44–53` names the finite
fibers and all-rank finite-shape construction; lines `55–62` distinguish import
scope, finiteness and the exact factorial equality. DOC-03 is corrected.

### C3: correction

The correction was checked against the actual proofs, their full import
closures and Casselman II.1.2, II.1.3, II.3.1 and II.3.2, and first appeared in
the Library at `4750a03e101b9ad45fc1a4d90a6a3d02d69c73e9`.

Current `C/Definitions.md:65–86` replaces future tense with the implemented
projection and surjectivity results. `D/CompactDualityStatement.md:45–71`
identifies the complete compact-duality proof and preserves its independence
from the separate projection/surjectivity proof modules. Current
`D/FixedVectorsProof.md:60–92,103–111` separates elementary fixed-functional
laws from compact duality and admissible reflexivity, retaining compact-open
cofinality and the separate smoothness/admissibility requirements. Missing
historical records of the compact proofs remain explicitly outside these claims.

### C5: definition, statement and proof-document corrections

The definition correction changes three Markdown files beside unchanged Lean;
the statement correction changes five statement Markdown files. Both first
appeared in the Library at `4750a03e101b9ad45fc1a4d90a6a3d02d69c73e9`. They
were checked against the unchanged constructions and targets, Casselman's
original conventions and the records of the earlier line. The corrected
pages distinguish construction fields, propositions and complete adjacent
proofs, retain the internal topological-group binders and independent
universes, and preserve the FixedVectorsProof final-export limit.
`SP/HomDefinitions.md:47–56` and `SP/HomStatement.md:50–57` accurately limit
the ten-module export: it does not establish that the Hom pairs were or were
not checked.

The subsequent proof-document correction is in the Library.
Current `SP/BasicProof.md:3–8,45–69`, `SP/FixedVectorsProof.md:3–11,79–91`,
`SP/FunctorialityProof.md:3–8,72–97` and
`SP/UniversalProof.md:3–8,69–91,102–112` explicitly distinguish the original
preparation, checks and publication in the earlier line from the later
documentation correction. Universal no longer claims that its current
dependency Markdown retains draft labels. `SP/HomProof.md:8–13,38–62,79–87`
retains the ten-module export's coverage limit and asserts no verified
historical check of the Hom pairs either way. Its Windows source locator
is labeled historical, with a readable current path at lines 64–77.
Functoriality's Casselman title is corrected at lines 77–82.

Its primary theorem is `Langlands.smoothPartUniversalProperty`, with the
exact unchanged statement `Langlands.SmoothPartUniversalProperty`. It was
checked with a Lake build, against that exact target, with statement and
inputs unchanged, and against the five explanations, original Casselman
pp.1–2 and the records of the earlier line. This check concerns the
Universal primary theorem; it does not create missing historical Hom or
FixedVectors final-export evidence. The correction first appeared in the
Library at `e4296643398fb6f96e73eb81e8e5d19a0d2650be`. The six changed files
match the Library exactly. Relative to its base
`e6045276bfca31676e0ceb0c8ed92e2709c53f61`, exactly the five proof Markdown
files changed in SmoothPart; all Lean and every other pair in that folder are
unchanged. The Universal target and the complete project import closure of
its statement, including the smooth-part and foundational definitions, are
also unchanged in both Lean and Markdown.

| File | SHA-256 (corrected = in the Library) |
| --- | --- |
| `SP/BasicProof.md` | `aeb2a008caea74aa07c09f1fce5741adf518a63239e239545f2f0c5ba7ad0ed8` |
| `SP/FixedVectorsProof.md` | `3fa810121862bb82e77e53314b28f141e5b0cb7691cebe723a98d0584db1e0a0` |
| `SP/FunctorialityProof.md` | `f29b7db66221e5ef7e0db1e169378d4b3b51b7e5754d53c2b371e1ee4e17a56d` |
| `SP/HomProof.md` | `fc43b84cb9b238a2b711f12fbb7e8abfb97ea9ccd155e345b8db452763e1291f` |
| `SP/UniversalProof.lean` | `e8f0bf938c8b069f480b0ca6d41b6b65b8dca24033a960c5bf254388a1d4eea9` |
| `SP/UniversalProof.md` | `00c9919fc60ee4e0990251fd7f916b49998d05b02ee3b0ea06898bb969add1be` |

The corrected FixedVectors proof page preserves the record of the original
proof check and publication, and the absence of archived final sources and of
a final proof check of the exported batch. No missing historical record is
invented. I056–I060 and their necessary neighboring status inconsistencies are
therefore corrected without changing any Lean target, binder or import.

### C3/C5 exact files

C3 and the C5 definition and statement corrections were built with Lake
together when they entered the Library; they are documentation corrections,
not new proofs.

The following SHA-256 values match the corrected files, the commit where they
entered the Library and the checked Library. Every paired Lean hash also equals the original audit
inventory. Additional Markdown files are listed as well as the primary pairs;
only the listed Markdown changed.

| Correction | File | SHA-256 (corrected = in the Library) |
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

### Versions of this note

Earlier versions of this note entered the Library at
`51dec7ffb8514b3e9cad965decf3f967fa045da4` (the original verdicts) and, as
successive updates recording the corrections then in the Library, at
`bf3c3860965e0b6c10d816a5d41e68a8003ef281`,
`6e8b1662b2777952bbde62145eb5269a8b2efbef`,
`0bfd14e8bc613b7c9562aa7ee70086679af1e1f9`,
`9677445f51f08760576e38e9c78f584be84da0b4` and
`acc39e30113233fe5beb6a6316d99215aec1ef8b`. This version records the C5
proof-document correction and retains all twelve historical/current verdicts
and every evidence limit. Unrelated open mathematical goals and the
explicitly unavailable historical evidence do not become results by this
audit.

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
