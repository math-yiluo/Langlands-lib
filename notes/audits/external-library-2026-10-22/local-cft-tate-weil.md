# External Library audit: local class-field theory, Tate cohomology and Weil parameters

## Scope and checked versions

This note addresses I006, I009, I018–I021 and I062–I065 of
`External Library audits 2026-10-22/ISSUES-2.md`. The external report is a set of
allegations; the verdicts below come from the published Lean and Markdown and
the cited originals. Its registered source ID is
`external-library-audits-2026-10-22`, folder SHA256
`975133657fad9fc7d0806e2cf4aaefac907edd151ec4df6cdd5d92b18a95a93b`.

The report's mirror commit `0972f45da7d1b581f2e9d8dcb690f960ccdb65ad`
corresponds to Library `f9c1742752d97c488fc1a835070bf50b534f4427`.
The Tate findings were first checked at
`f1b212cc117b9c34dced95c0ac88e6328827334d`, then rechecked at
`aee7fdb7f6d4283cce4db9035fd9478c923d4926`. Both affected Lean/Markdown
pairs were unchanged across those three versions. Thus these findings had
not been repaired by an intervening publication at the second check.
Line references in the Tate analysis below refer to that second checked
version, except where explicitly identified as the correction.
The Tate correction was subsequently published at
`2173e15e1a7e4f96682e6274d63c4f98ccce2c73`; both integrated pairs and
the supporting hashes below were checked at that commit. The two findings
therefore describe verified defects now repaired, rather than defects still
present in that publication.

The final reconciliation checked current Library
`fb40559309dd366f4145aa31aad8c3db11b7cc07`. All ten findings held when
independently verified, and all ten are now repaired by eight documentation
corrections, which are in the Library. The ledger records the
historical verdict and the present corrected state separately. Earlier
per-section commits and hashes identify the exact pre-correction inputs;
the final publication table gives the current corrected hashes. Every other
listed input hash was rechecked at the final commit and is unchanged.
Unless a historical version is explicitly named, locations in the new
I064/I065 sections refer to this final commit.

## Per-ID ledger

| ID | Verdict at verification | Reason and correction decision |
| --- | --- | --- |
| I006 | Holds; corrected | The downward augmentation requires finite ambient `G`; the coordinate map and upward exact sequence do not. Corrected the hypothesis description in `SubgroupShifts.md`; Lean unchanged. |
| I009 | Holds; corrected | The surjectivity theorem specializes both maps to identities. Corrected `CochainComparison.md` and described the general invariant map before the quotient; Lean unchanged. |
| I018 | Holds; corrected | The two existential invariant-family targets already exist; the later transfer-compatible strengthening also exists. The correction corrects the status prose and preserves the open realization boundary. |
| I019 | Holds; corrected | Actual positive-degree corestriction, its fundamental-class predicate and the existential targets are published. The same correction corrects the obsolete construction status; Lean unchanged. |
| I020 | Holds; corrected | Structural laws, conditional compact lifting and actual unramified unit-norm surjectivity are separately proved and published. The correction corrects their status, preserving every hypothesis. |
| I021 | Holds; corrected | Coherent-family relations, actual-degree system targets, the absolute filtration and its reciprocity targets already exist. The correction documents them while retaining the unproved reciprocity boundary. |
| I062 | Holds; corrected | The genuine dual and continuous-character twist equivalences and actual local lattice specialization already exist. The correction corrects the companion status with unchanged Lean. |
| I063 | Holds; corrected | `algebraicProperties` already proves the complete generic target, including degree surjectivity conditional on surjectivity of `φ`. Its earlier checks and unchanged current files are verified below. |
| I064 | Holds; corrected | The actual local Weil assembly and its complete 22-clause theorem are published. The correction links them while preserving the generic-module boundary. |
| I065 | Holds; corrected | The complete relation target family is published. The correction records it, distinguishes existing certified parameter operations, and retains the open complete-family proof goal. |

## I006: subgroup shifts

The affected description is
[SubgroupShifts.md](../../../Langlands/Cohomology/Tate/SubgroupShifts.md),
original lines 5–18. In
[SubgroupShifts.lean](../../../Langlands/Cohomology/Tate/SubgroupShifts.lean),
lines 14–47 define `Langlands.Tate.restrictedCoinducedCoordinates` and
`restrictedCoinducedIso` for an arbitrary subgroup, with no finiteness or
normality assumption. Lines 49–81 have these exact finiteness scopes:

| Declaration in `Langlands.Tate` | Required finiteness |
| --- | --- |
| `restrictedCoinduced_tate_isZero` | `[Fintype H]` |
| `restrictedShiftUpSequence_shortExact` | None |
| `restrictedShiftDownSequence_shortExact` | `[Fintype G]` |
| `restrictedShiftUpIso` | `[Fintype H]` |
| `restrictedShiftDownIso` | `[Fintype G]` and `[Fintype H]` |

These are the complete unapplied declaration types, including parameters
retained or omitted by Lean, not assumptions inferred from section headers.
They preserve the arbitrary common universe `u`, commutative scalar ring
`R`, and arbitrary `A : Rep.{u} R G`. The Tate shifts range over all integer
degrees. The ambient requirement comes from
[ShiftDefinitions.lean](../../../Langlands/Cohomology/Tate/ShiftDefinitions.lean),
lines 82–90: `coinducedProjectionLinear A f` sums
`A.ρ g⁻¹ (f.1 g)` over all `g : G`.

The report identifies a real omission in the short description of the two
sequences. It does not identify a false Lean theorem, or assert that ordinary
finite-group Tate theory has been extended to infinite `H`. The correction explicitly separates all these scopes
in `SubgroupShifts.md`, lines 5–31, with unchanged Lean.

## I009: the canonical cochain comparison

The affected description is
[CochainComparison.md](../../../Langlands/Cohomology/Tate/CochainComparison.md),
original lines 11–18. In
[CochainComparison.lean](../../../Langlands/Cohomology/Tate/CochainComparison.lean),
lines 60–75 define the general comparison for `f : H →* G` and
`φ : Rep.res f A ⟶ B` and identify its positive-degree map with ordinary
cohomology pullback, after the comparison isomorphisms.
Lines 154–219 identify its degree-zero map as
`cochainInvariantMap f φ` followed by `zeroClass B`.
In particular, the general map is not merely a quotient map on the original
invariants. These formulas require finite `H`, not finite `G`.

The theorem `Langlands.Tate.cochainsToTate_surjective`, lines 239–250,
instead uses `f := MonoidHom.id G` and `φ := 𝟙 A`, with finite `G`,
arbitrary `A`, and every `n : ℕ`. The positive-degree case is an
isomorphism by `cochainsToTate_homology_id` and `cochainsToTateIso`,
lines 221–237. The zero case uses the surjective class map from invariants
to invariants modulo norms. The general coefficient action need not be trivial.
All statements preserve the arbitrary common universe `u` and commutative
coefficient ring.

Thus the omission of the identity specialization is real; the Lean theorem
already has the correct scope. For example, a zero coefficient morphism gives
a zero induced map, which cannot be surjective when its target is nonzero.
No arbitrary-map surjectivity theorem follows from the canonical comparison.
The same correction makes the specialization and the general
degree-zero factorization explicit in `CochainComparison.md`, lines 12–34.

## Tate original-source comparison

The original is Serre, *Local Fields*, Greenberg translation, GTM 67,
Springer (1979), source ID `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The retained original is `Serre--Local Fields--1979.pdf` in Central-Library.
No source erratum was present in the current Library or project notes at
verification.

Chapter VII §1, printed p. 110 / PDF p. 116, describes induced surjections,
coinduced embeddings and their identification for finite groups; its exercise
extends the setup to a commutative scalar ring. Chapter VIII §1, printed
pp. 127–129 / PDF pp. 133–135, defines the degree-zero norm quotient,
identifies positive Tate degrees with ordinary cohomology, and gives the two
scalar-split dimension shifts. Chapter VIII §2, printed pp. 129–130 /
PDF pp. 135–136, gives restriction/corestriction and compatibility with
connecting maps.

These passages agree with the finite-group conventions of the implementations.
The explicit arbitrary-ambient-group coset coordinates and auxiliary zero-splice
construction are internal realizations, not statements attributed verbatim to
Serre. The exact scopes in the two corrections follow from the Lean definitions
and complete declaration types.

## Tate checks and correction

Development and recovery checks completed with zero errors or warnings.
They printed the complete unapplied declarations with universe parameters.
They are supporting development evidence, not proofs.

The correction was checked against the full types, the original Serre
pages, the Markdown and the unchanged Lean, and first appeared in the
Library at `2173e15e1a7e4f96682e6274d63c4f98ccce2c73`, where it was built with
Lake. The Markdown hashes in the Library match the corrected hashes below;
the two Lean files and the supporting inputs remain byte-identical.

## Tate input fingerprints

These SHA256 hashes identify the checked inputs at Library
`aee7fdb7f6d4283cce4db9035fd9478c923d4926`.
Paths are relative to `Langlands/Cohomology/Tate/`.

| Path | SHA256 |
| --- | --- |
| `SubgroupShifts.lean` | `4add52b4ea3a38bfaea83443bcc2eabb088b2f80a6c2960156a849273a55b275` |
| `SubgroupShifts.md` | `4cddd2f565d56bdffad8f3ca0ce75e5078d14120defb99d0a4d5568a7ae67239` |
| `CochainComparison.lean` | `e9bb52f7e6d162c9fbb3cd7bd34c8df2a37577a9103687b695f55d354e4695db` |
| `CochainComparison.md` | `94ae58541114299560ac636e4f747004559631419a1e6c57b42ea69bef443279` |
| `ShiftDefinitions.lean` | `52912bd320237433a4f59bd4dda6053efbb298a6d53a579d036dc8cd9da6ee7f` |
| `ShiftDefinitions.md` | `b4c457a0d6091399c70700572ea26f5f60d9fc147510964cd2f43a3e34664aa3` |
| `ZeroDefinitions.lean` | `d0b650881aef493ceaf637562c6f3a3d63e680f74ef6d566c8d4e9a7dca656e0` |
| `ZeroProof.lean` | `3d45b34adccc16b386c898356cdcc3ee1092c38079b3ebf56b9c81f067fc74f2` |

The corrected Markdown hashes, as submitted and in the Library, are
`656eac9f41b5a10b3d87bbc4ebfe6f71d372727190f574d55f7f5dbaa4cd401c`
for `SubgroupShifts.md` and
`113e2470d4acd06a455dc59d8e30c8278cdb7acc4f7496a260a36c314342602d`
for `CochainComparison.md`. Both Lean hashes remain as listed above.

## I018–I019: class-formation targets and positive transfer

These findings were checked against Library
`350369b5ca2d36132eb7e57d869fc0454f3a3707`. Both primary pairs and all five
companion pairs listed below are byte-identical at the report snapshot
`f9c1742752d97c488fc1a835070bf50b534f4427`, correction base
`b263cfa454b11d485198ae46d8290f32435e48c6`, and this checked snapshot.
Thus no intervening change had repaired either finding at verification.

I018 concerns [ClassFormation.md](../../../Langlands/ClassFieldTheory/Local/ClassFormation.md),
original lines 141–148. The complete declarations in
[ClassFormationStatement.lean](../../../Langlands/ClassFieldTheory/Local/ClassFormationStatement.lean),
lines 20–49, already define `LocalRelativeClassFormationStatement` and
`LocalCompatibleClassFormationStatement`. Each universally quantifies the
prime and existentially quantifies **one** raw `InvariantFamily.{u,u}`.
The required properties belong to that same witness. The compatible target
adds continuous absolute properties, the genuine ordinary-to-absolute
comparison diagram, all-integer Tate cup bijectivity and positive Tate
inflation. These are Prop definitions, not local existence proofs.
[ClassFormationTransferStatement.lean](../../../Langlands/ClassFieldTheory/Local/ClassFormationTransferStatement.lean),
lines 19–33, also defines the strengthening
`LocalTransferCompatibleClassFormationStatement`, adding the all-integer
restriction/corestriction cup compatibility. None includes absolute continuous
corestriction as a clause. A current-Library search found these three named
targets as definitions and explanatory references, with no theorem discharging
them. The correction preserves that proof boundary.

I019 concerns [FundamentalClasses.md](../../../Langlands/ClassFieldTheory/Local/FundamentalClasses.md),
original lines 73–90. In
[Corestriction.lean](../../../Langlands/ClassFieldTheory/Local/Corestriction.lean),
lines 20–55, `relativeGaloisSubgroupEquiv` identifies the actual restriction-of-scalars
image of `Gal(M/L)` inside `Gal(M/K)`. `relativeCorestriction` transports the
constructed Tate transfer through the positive ordinary/Tate comparisons,
with identity coefficients on the top field's units. Its raw construction
has independent field universes and requires finite dimensionality of `M/K`
and a positive degree `[NeZero n]`; it does not assume an arbitrary transfer
map. [ClassFormation.lean](../../../Langlands/ClassFieldTheory/Local/ClassFormation.lean),
lines 23–32, already defines `FundamentalClassCorestriction`, with formula
`Cor(u[M/L]) = [L:K] u[M/K]`. The target predicates retain the additional
finite Galois and tower hypotheses they explicitly quantify.

The downstream comparison is also constructed:
[FiniteComparison.lean](../../../Langlands/ClassFieldTheory/Local/FiniteComparison.lean),
lines 16–50, gives `continuousToRelativeEquiv`, `closureInflation`, and its
compatibility with continuous representatives.
[FiniteInvariantCompatibility.lean](../../../Langlands/ClassFieldTheory/Local/FiniteInvariantCompatibility.lean),
lines 16–40, defines `OrdinaryClosureCompatibility` and proves
`closureCompatibility_iff`. These constructions do not establish existence
of an invariant family satisfying the diagram. The correction links them
without adding them as imports or hypotheses of `FundamentalClasses.lean`.

The source formulas were checked in the retained Serre original identified
above: XI §3, printed pp. 168–169 / PDF pp. 174–175, gives positive invariant
`1/[L:K]`, exact order/generation, the four functorial laws, cup bijectivity
and the degree multiplier for inflation. XIII §3, Propositions 6–7 and
Corollary 2, printed pp. 193–194 / PDF pp. 198–199, gives the absolute invariant
and its finite-stage image. XIII §4, Theorem 1, printed pp. 195–196 / PDF
pp. 200–201, is the local realization conclusion, rather than an assumption
already supplied by the raw invariant family. The positive fundamental-class
normalization is unchanged. Serre XIII §4 Proposition 13, printed p. 197 / PDF
p. 202, uses arithmetic reciprocity; Henniart (2000), §1.1, printed p. 439 /
PDF p. 1, sends geometric Frobenius to a uniformizer. The latter retained
original is source `henniart-2000-simple-proof`, SHA256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
The reciprocal convention changes by inversion separately from the positive
fundamental class. No relevant errata file was found in the checked Library.

### Companions in the Library

The companions below are in the Library; the table gives the commit where
each first appeared, and their paired hashes match the current files. They
establish their stated definition/statement scope, not proofs of local
realization.

| Companion | Publication commit |
| --- | --- |
| `ClassFormationStatement` | `056b7c747e32f712be4ac7fd004fd0af4845c968` |
| `ClassFormationTransferStatement` | `15d892539cb2f99d22c0903905b053d7c86de92a` |
| `Corestriction` | `15f4ec1bc9d27d00acfb08e2d8667e7b44317ee7` |
| `FiniteComparison` | `f01c1864161b6d1cdc1d04b1f8d577dfd4e8400f` |
| `FiniteInvariantCompatibility` | `18fac9a1ce0cc1ae5ed2c754ff093194569c18e3` |

### Correction status and fingerprints

The documentation-only correction covers only I018–I019; it was checked
against the originals, the companions and the unchanged Lean, and first
appeared in the Library at `886e27567a757917705b7adef45a2c2621bf4bf7`, where it
was built with Lake. Both corrected pairs match the checked Library
`77b88e13c66c007890e05a700979f65279070987` byte for byte. The corrected prose
appears at `ClassFormation.md:141–160` and `FundamentalClasses.md:73–104`.

SHA256 inputs at checked Library `350369b5ca2d36132eb7e57d869fc0454f3a3707`,
with paths relative to `Langlands/ClassFieldTheory/Local/`:

| Path | SHA256 |
| --- | --- |
| `ClassFormation.lean` | `c933d3fa297afcd89f91c3833bc9488d216cb07278ecd1c75d4709baca4a1d19` |
| `ClassFormation.md` | `74c223f21979754a7c5e5ef7453719adb329fda3b43511c1c280851d1e1b327a` |
| `FundamentalClasses.lean` | `db1a49324657977336547bc4b2b8d66b814bbc6ffb8b2d55eed99b8743135261` |
| `FundamentalClasses.md` | `ba5f7ada0ff1358d0d6799e2db2820c6e0c3b290b63b08069f5c7980a4c57b48` |
| `ClassFormationStatement.lean` | `359d2804f9fa372e86b13deb8af20755f192f8049eba3b2dcef122deaf67f983` |
| `ClassFormationStatement.md` | `d6fe6663753755fca64360f148ec1936f9df91359c78deb5acf4845c12e94033` |
| `ClassFormationTransferStatement.lean` | `5250731a3ebb3473d622ccc133bdf70b217abc3adb8a46c3eb8b06e2b23459f8` |
| `ClassFormationTransferStatement.md` | `e4eddee57cea20a73ca286d3e66dc34a12adc1653a91bd1db802df817fd3e7b1` |
| `Corestriction.lean` | `4b71bc026884184652b70a3f38ef0ad837f865a3490017c47c725a8dba528dfc` |
| `Corestriction.md` | `9c519fb174b05b19fe4414d21c939fa816308b3839e6b40d616c20d0337430d9` |
| `FiniteComparison.lean` | `38ac0887df02e4543ebfb107a5fef25dfb88a5829c0b7dea16d0a2b875336f9d` |
| `FiniteComparison.md` | `901743107a6e0a5db56a511349ca95bf2f7d88764aba152ae311c183ae01d935` |
| `FiniteInvariantCompatibility.lean` | `87d7aade4975b8e1bd9f73a896be93f03f80e09b70c464925c9d2f738191fe1c` |
| `FiniteInvariantCompatibility.md` | `def97b2126e6f16e4cb2f1f2b0d9996c384f3508b0ad5fecc9051ad96d2c621a` |

Corrected Markdown hashes are
`540ae013a15ee4fbfcf0a53a847cae8f70fa426aeee5de4a0bfe5fa422334a72`
for `ClassFormation.md` and
`d452d2fc2107e558a881ed24e7face6e1833f77ef74c9b71e7a639714e452bc1`
for `FundamentalClasses.md`; all Lean bytes are unchanged.


## I020: proved topology and the separate arithmetic norm theorem

This finding holds at Library `886e27567a757917705b7adef45a2c2621bf4bf7`.
The seven Lean/Markdown pairs in the hash table below are unchanged from
both the report snapshot and `350369b5ca2d36132eb7e57d869fc0454f3a3707`.
The obsolete text is in
[UnitFiltrationTopologyStatement.md](../../../Langlands/ClassFieldTheory/Local/UnitFiltrationTopologyStatement.md),
lines 48–54, 86–97 and 107–115. Its module-local statement-only description
is correct, but its future-work claims about separate proofs are not.

The complete target in
[UnitFiltrationTopologyStatement.lean](../../../Langlands/ClassFieldTheory/Local/UnitFiltrationTopologyStatement.lean),
lines 18–48, preserves arbitrary supplied topological data and two independent
carrier universes. `UnitFiltrationStructuralLaws.{u}` asserts compactness and
closedness at each natural level, antitonicity, separation and the zeroth-level
equality. `UnitFiltrationCompactLifting.{u,v}` concerns an arbitrary continuous
homomorphism between field-unit groups; the fields need no extension relation.
It explicitly assumes preservation at every level and one-level approximation
with error `y * (f x)⁻¹`. Its conclusion is equality of the subgroup images at
every level, including zero. `UnitFiltrationTopologyTheorems` conjoins the
structural laws in **both** universes and that conditional lifting criterion.

The corresponding proofs already exist:

- [UnitFiltrationStructuralProof.lean](../../../Langlands/ClassFieldTheory/Local/UnitFiltrationStructuralProof.lean):123–126
  proves `unitFiltrationStructuralLaws`. The actual reduction-kernel filtration
  is used throughout; compactness comes from closed integer-unit kernels and
  their continuous images, while separation uses Krull intersection and the
  injective integer-unit inclusion.
- [UnitFiltrationTopologyProof.lean](../../../Langlands/ClassFieldTheory/Local/UnitFiltrationTopologyProof.lean):10–67
  proves the structural-premise helper, discharges those premises in
  `unitFiltrationCompactLifting`, and assembles `unitFiltrationTopologyTheorems`.
  Successive finite corrections produce nested nonempty closed approximate
  fibers in a compact source level; their intersection and target separation
  give an exact preimage. Preservation and one-level approximation remain
  premises for the arbitrary map.
- [UnitNormProof.lean](../../../Langlands/ClassFieldTheory/Local/UnitNormProof.lean):156–178
  proves `unramifiedUnitNorms : UnramifiedUnitNorms.{u,v}`. The full definition
  in [UnitNormStatement.lean](../../../Langlands/ClassFieldTheory/Local/UnitNormStatement.lean):22–29
  quantifies a compatible finite p-adic extension, arbitrary supplied data,
  and equality of absolute ramification indices. It proves surjectivity of
  the **actual determinant norm** on every filtration level, including zero,
  without a Galois assumption or added preservation/approximation premises.
  Those premises are established using the integer norm and then transported
  to the actual continuous field norm `localNorm` before compact lifting.

`Units.lean:68–98` defines the exact maximal-ideal quotient, reduction kernel
and image used above; `Norms.lean:22–25,108–131` identifies the determinant norm
and its continuity for the supplied topologies. The full paired explanations
and implementations were read. This evidence does not assert a proof of the
five-conjunct `UnitNormTheorems` bundle (`UnitNormStatement.lean:88–93`) or
local reciprocity, and the correction makes neither claim.

Serre's retained original, with the fingerprint given above, was read directly:
II §1, printed pp.26–28/PDF pp.34–36 (valuation topology and compact integer ring);
IV §2, printed p.66/PDF p.73 (`U^0=U`, positive congruence levels and decreasing
closed neighborhoods); V §1 Lemma 2, printed p.81/PDF p.88 (complete separated
filtered-group lifting); V §2 Propositions 1–3, corollary, finite-residue remark
and non-Galois exercise, printed pp.81–82/PDF pp.88–89. Positive-level norm
surjectivity follows via residue trace; finite-residue norm surjectivity supplies
level zero. The compact-intersection and Krull-intersection implementations
are disclosed as derived routes, not Serre's verbatim proof. No Serre erratum
was present in the checked Library.

### Companions and correction

The three proofs below are in the Library; each was checked with a Lake
build, against its exact target, with its statement and inputs unchanged.
All six proof-pair hashes equal the current files.

| Proof | Publication |
| --- | --- |
| Structural | `bfd2c6b428660be7889841323ce92565132580bb` |
| Topology | `9173b91d7bd642075001f7d8d56e9e6d26cae822` |
| Unramified unit norm | `08ce07bfdc79298778cd3e9ee6d5318c23c3b75b` |

The original topology statement first appeared at
`f8488ce760fd0ec518e405f24e33da3f8aaf7ef2`. Its current Lean differs only by
canonicalizing the `Units` import; its Markdown has the corresponding two
module-name changes. These complete differences were inspected.

The correction preserves all Lean bytes. It was checked against the original
Serre passages and all three companions, and first appeared in the Library at
`4ccd65d85917da26d0a67b9c48a37859533fffa9`. The corrected Markdown SHA256 is
`06a7403c4d0254ee50545083e3203bc1bf6a73a9860fe88437259804ccca0fb3`.

Input SHA256 hashes at the checked commit, relative to
`Langlands/ClassFieldTheory/Local/`:

| Path | SHA256 |
| --- | --- |
| `UnitFiltrationTopologyStatement.lean` | `e000edf1bc65561816352fee8ec4c1bf172a3367317974c7c0de5763c692bd9c` |
| `UnitFiltrationTopologyStatement.md` | `512dacc456031b0412dbea97f6b4a1dd2472610ea6ecb9f482b5814e070e025d` |
| `UnitFiltrationStructuralProof.lean` | `a2c845142de412955ee3e6764f7a1d2a546f762ff6fb7c0a749f5aa938f09a93` |
| `UnitFiltrationStructuralProof.md` | `81d707c28f55f66483784be460b41a0a72f71c92d51416b8e89f7f4dc9924963` |
| `UnitFiltrationTopologyProof.lean` | `86c4dc6cc395462da1ced59d4722f8e3319797ee99c371fadfed9dd6c501182d` |
| `UnitFiltrationTopologyProof.md` | `fc3159179a100a83aa862253fa3bf6eff4fa237257bfbb2dcae111e9f7a735a1` |
| `UnitNormProof.lean` | `6af9860e1160e42ecf8a7b21fb0232bfc9b9e35aa8cf130dd43ece003c9faee5` |
| `UnitNormProof.md` | `afbab4d8a4f152cf56d3f9e9accb028fa7d8b645c9ca33c288b2336cf4409312` |
| `UnitNormStatement.lean` | `730c63141804e05a75bcd38a2e384aef0e0c46e2cf4727aab6ddc9658faeb26a` |
| `UnitNormStatement.md` | `d1e9b81187d88ac5712d6493e06653611b33b5c6f0e2046b70b2bb31c188d9b3` |
| `Units.lean` | `4c0a4ea98a2acee28712326b598dff39bcb1300de0d77cd94aa8f90b8a6499a9` |
| `Units.md` | `b68e2c249a44251f0d59505c59086e9642a095b48bdce9ed800d944dbb487c58` |
| `Norms.lean` | `696b8c578a372037c4729160b4be63fac3365e96360abf5b50b8b546fe994d87` |
| `Norms.md` | `36ebee619ae3ad6ab5bed3286549564dd9ab3bf3cd1c852006bfdbad5141dab9` |

## I021: existing coherent-system and absolute-filtration modules

The finding holds at Library `886e27567a757917705b7adef45a2c2621bf4bf7`.
The checked pairs below are unchanged from the report snapshot and
`350369b5ca2d36132eb7e57d869fc0454f3a3707`. The stale claim is
[WeilReciprocityStatement.md](../../../Langlands/ClassFieldTheory/Local/WeilReciprocityStatement.md):95–98,
which calls the separate definitions outstanding. This is a documentation
defect; the single-field Weil aggregate itself still correctly contains
exactly six proposition targets in
[WeilReciprocityStatement.lean](../../../Langlands/ClassFieldTheory/Local/WeilReciprocityStatement.lean):96–102:
existence/uniqueness, completion, inertia image, unramified characters,
unramified twists, and norm-character transport.

The existing separate content is precise:

- [ReciprocitySystem.lean](../../../Langlands/ClassFieldTheory/Local/ReciprocitySystem.lean):22–23
  indexes all finite intermediate fields of one actual algebraic closure,
  including nonnormal fields. Lines 206–276 define candidate families and the
  five-part `CoherentFamilyRelation`: actual norm, transfer and conjugation
  squares, density, and completion comparison. `CoherentFamilyExistence` is
  a Prop definition, not a constructed family. Lines 283–301 add the distinct
  geometric normalization and define normalized existence and uniqueness.
  The maps, transfers and conjugations are constructed from actual fields;
  the raw degree map remains an explicit parameter.
- [ReciprocitySystemStatement.lean](../../../Langlands/ClassFieldTheory/Local/ReciprocitySystemStatement.lean):21–36
  uses the constructed `Weil.Local.localResidueDegree F` and canonical data
  on every extension field. `CommonClosureReciprocityTheorems` states normalized
  existence and uniqueness for every prime, arbitrary carrier universe and
  arbitrary supplied **base** topology. It does not assume a reciprocity family
  or silently quantify arbitrary extension-field realizations in place of the
  specified canonical ones.
- [Herbrand/Absolute.lean](../../../Langlands/LocalFactor/Ramification/Herbrand/Absolute.lean):33–45
  constructs continuous finite restrictions and
  `Langlands.Ramification.Padic.absoluteUpperRamificationGroup`, the intersection
  of upper-group preimages over all finite Galois subextensions. Lines 121–124
  define `localAbelianUpperRamificationGroup` as its actual image under the
  closed-commutator quotient projection. It is not an independently supplied
  family of finite abelian images. The general finite-field packaging helper
  retains independent ambient and base universes; the absolute closure
  specialization uses Mathlib's same-universe carrier.
- [AbsoluteReciprocityStatement.lean](../../../Langlands/ClassFieldTheory/Local/AbsoluteReciprocityStatement.lean):22–87
  defines the five separate targets for inertia, natural and real higher-unit
  images, conductor levels and the last upper break. Each quantifies a supplied
  continuous map satisfying `GeometricProfiniteReciprocityRelation`; none
  constructs that map. The real indices are nonnegative and use natural
  ceiling; the character criteria retain arbitrary continuous complex
  quasicharacters, including infinite-image and nonunitary ones.

Complete implementations and paired Markdown were read. Current-Library
searches for all three reciprocity aggregates and every component found their
Prop definitions and conjunctions, with no theorem proving them. The existing
elementary absolute-filtration lemmas do not establish those reciprocity goals.
The correction therefore replaces the false missing-definition claim while
retaining the outstanding reciprocity proofs. None of these separate targets
is an added conjunct or assumed input of the six-part Weil aggregate.

`ReciprocityRelations.lean:30–83` supplies conditional character transport
through the topological Weil abelianization and a given candidate inverse;
no inverse into the nonabelian Weil group is chosen.
`ProfiniteReciprocityStatement.lean:21–35` specifies geometric residue
normalization of the actual finite norm-residue system.
`Weil/Local/Assembly.lean:23–48,83–107` constructs the actual residue degree,
Weil group, degree surjectivity and norm character. These semantic inputs were
read directly; their existence does not by itself prove reciprocity.

### Original-source correspondence

Tate, *Number theoretic background*, Corvallis Part II (1979), source
`tate-1979-number-theoretic-background`, SHA256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`, was read
in the retained original. Section 1.1, printed pp.3–4/PDF pp.12–13, gives
families over all finite subextensions, conjugation, transfer and norm
compatibility. Section 1.4.1, printed p.6/PDF p.15, specifies the local
integer-Frobenius subgroup with inertia open and sends uniformizers to
**geometric** Frobenius. Section 1.4.6, printed p.7/PDF p.16, identifies the
norm with normalized absolute value; §4.1.3, printed p.20/PDF p.29, writes
it as `q^(-degree)`. Thus degree positive one has value `q^(-1)`. The project's
candidate direction is the inverse of Tate's maps into Weil abelianizations.

Serre IV §3, Proposition 14 and Remark 1, printed pp.74–75/PDF pp.81–82,
was read for finite quotient compatibility and the inverse-limit definition
of the infinite upper filtration. The actual subgroup intersection is its
internal realization. Serre XI §§3–5, printed pp.169–175/PDF pp.175–181,
and XIV §6, printed pp.218–219/PDF pp.223–224, were also read directly for
finite norm-residue maps, the norm/transfer/conjugation diagrams, completion,
open finite-index norm groups, the trivial universal norm kernel, and units
versus inertia. Inverting Serre's arithmetic reciprocity preserves kernels,
compatibility diagrams and subgroup images. These sources support the declared
interfaces and conventions; they do not supply Lean proofs. No relevant Tate
or Serre erratum was present in the checked Library.

### Modules and correction

The five modules below are in the Library; the table gives the commit where
each first appeared. They are definitions or statements and do not certify
reciprocity proofs.

| Module | Publication |
| --- | --- |
| Weil statement | `bfd2c6b428660be7889841323ce92565132580bb` |
| System definitions | `0fbab0ee36b0ab602b6d43bc3d60ada813fcedbf` |
| Actual system targets | `8728166c7a3a18d2d8347cd6c907cc2226768605` |
| Absolute filtration | `6700bb7581ced62a8982c39bcea021acff83aad7` |
| Absolute reciprocity targets | `ef274d37c255e4b25a990dd377d10e2da436807d` |

Archived pairs equal the current files except for the canonicalized Galois
import in `Herbrand.Absolute`, its matching Markdown description, and the
module-directory description in `ReciprocitySystem.md`. These full differences
were inspected; no mathematical statement changed.

The correction keeps the Lean unchanged. It first appeared in the Library at
`4ccd65d85917da26d0a67b9c48a37859533fffa9`. Its corrected Markdown SHA256 is
`30f10173b6c45f3b08e52359ab1005c469d023bf10eeae3fa9383e5d34ef3748`.
The old statement pair's entry into the Library is distinct from this
correction.

Current input SHA256 hashes at the checked commit:

| Path | SHA256 |
| --- | --- |
| `Langlands/ClassFieldTheory/Local/WeilReciprocityStatement.lean` | `b8e6143debd6db966242ce15560f28f1d386bf6c3e322b5753a2ff9b8e9a57c5` |
| `Langlands/ClassFieldTheory/Local/WeilReciprocityStatement.md` | `75e37ddd9d20779f803677b9ac38b2602b297cec00936e76f61d826f33cf1fdc` |
| `Langlands/ClassFieldTheory/Local/ReciprocitySystem.lean` | `ef84a7adf56eac2b7d07d30096aaea771a526cf98649431c3e7a14ad9b314fca` |
| `Langlands/ClassFieldTheory/Local/ReciprocitySystem.md` | `c727e0a7d8b8389077b655504c976129943dce470f41f89e0b93e509f984122d` |
| `Langlands/ClassFieldTheory/Local/ReciprocitySystemStatement.lean` | `0796b3ae3397f283b065f086db8de969427d0de4df1c2f2112c5e2d2c0d4fccc` |
| `Langlands/ClassFieldTheory/Local/ReciprocitySystemStatement.md` | `9d029277395a71060ef74b4d5364ebdbe1406f7d894c563d203399b52db2615e` |
| `Langlands/ClassFieldTheory/Local/AbsoluteReciprocityStatement.lean` | `9c772f2c308ab05d0364926599ab008160f4695316bcf9ffd49e4294e2700147` |
| `Langlands/ClassFieldTheory/Local/AbsoluteReciprocityStatement.md` | `851b86441c1a0cbc476aceacb2626ca5410a932f0e3b25e7d9fcc18af97a6123` |
| `Langlands/ClassFieldTheory/Local/ReciprocityRelations.lean` | `fcd99ef64f5ce350be95d49fbc884bc1641c7cde1f861dfbe7c030b47591526a` |
| `Langlands/ClassFieldTheory/Local/ReciprocityRelations.md` | `3f79e264a6e890997273c53151bd86b6d893156df4ab64d0f78c3b162312b72c` |
| `Langlands/ClassFieldTheory/Local/ProfiniteReciprocityStatement.lean` | `fb9b0865614133c3f860b6f42c8bf9de3319af758d7629549a3c22eaf05f6a84` |
| `Langlands/ClassFieldTheory/Local/ProfiniteReciprocityStatement.md` | `e051e3b819b527494a1722f367b0a98d353d072154a4804e8e6d286883ab3c7d` |
| `Langlands/LocalFactor/Ramification/Herbrand/Absolute.lean` | `9e2915881c1324db6bf6935303db618ea3628cf80afde2f4d5810795502622ab` |
| `Langlands/LocalFactor/Ramification/Herbrand/Absolute.md` | `f97ae08756e0c4a87a921d346bd7e5984ba6804834950ee6051dddbdd79ac2cf` |
| `Langlands/Weil/Local/Assembly.lean` | `576d8ad3c15763bdf047c2289beea60530c5d95a70963395444fd1efbd49cad8` |
| `Langlands/Weil/Local/Assembly.md` | `6fb1c6a6e8e5a6ba9748ed021c5050bbca06589072e1ef3d26af0d850beb8b83` |

## I063: the generic Weil algebraic proof

This finding holds at checked Library
`350369b5ca2d36132eb7e57d869fc0454f3a3707`. The complete
[Algebraic.lean](../../../Langlands/Weil/Algebraic.lean), lines 12–24,
defines `Langlands.Weil.AlgebraicProperties : Prop`: injectivity of the
canonical integer map, followed by seven clauses quantified over every
`Γ : Type u`, `[Group Γ]`, `[TopologicalSpace Γ]` and continuous
`φ : Γ →ₜ* ProfiniteIntegers`. No compatibility between the topology and
group operations is assumed. The last clause is explicitly conditional:
`Function.Surjective φ → Function.Surjective (degree φ)`.

[AlgebraicProof.lean](../../../Langlands/Weil/AlgebraicProof.lean), lines
13–30, already proves `degree_residuallyFinite` using reduction modulo
`|n| + 1` and proves `frobenius_injective` using Mathlib's criterion for the
actual profinite-completion map. Lines 36–97 prove the commuting square,
projection injectivity and image, inertia inclusion and its image as the
degree kernel, and conditional degree surjectivity by explicit coordinates.
Lines 100–105 assemble the entire unchanged target in
`Langlands.Weil.algebraicProperties : AlgebraicProperties.{u}`. The proof
retains the arbitrary universe and all original hypotheses.

Thus [Algebraic.md](../../../Langlands/Weil/Algebraic.md), lines 3–4 and
27–32, has obsolete future-proof wording. Its claim that the statement
module itself only defines a proposition remains accurate. The correction
links the companion proof and keeps that module distinction and the
conditional-surjectivity boundary. It first appeared in the Library at
`a4f4742431c7298bf38f4d4e6bc03a6cd7a33a18`. The corrected Markdown SHA256 is
`0a93572cc4956df7085c6024121f40f5446178acf07cab6b653207c00b511154`. Lean is
unchanged.

The complete supporting [Pullback.lean](../../../Langlands/Weil/Pullback.lean),
lines 18–75, defines `Degree := Multiplicative ℤ`, the actual profinite
completion, its canonical map, the equalizer subgroup of `Γ × Degree`,
continuous coordinates and inertia inclusion. Multiplicative degree `1`
means integer degree zero. The generic result does not identify a local
field's Weil group or establish reciprocity; those are separate conclusions.

The original source was read directly: Henniart, *Représentations du groupe
de Weil d'un corps local* (1980), §1.1, printed p.155/PDF p.2, and §2.1 plus
the opening of §2.2, printed p.158/PDF p.5. It gives the local-field
integer-Frobenius preimage and inertia description and the integer quotient.
The generic construction and theorem are derived content, not an assertion
that Henniart states the arbitrary-input theorem. Source
`henniart-1980-weil-representations`, retained file
`Henniart--Representations du groupe de Weil dun corps local--1980.pdf`,
SHA256 `451a8bd31a58be9bf5ce49588503c2d229b1a73bf3e65ae0c7b2f491c1c4e017`.
No relevant errata file was found in the checked notes.

### Checks in an earlier line of the Library and current-file continuity

These three modules were first published in an earlier line of the Library
(called Test 2 in its records) and imported into this Library without their
records. A read-only export of those records is registered as
`provided-646d3159d992a5cae36711e43fde410b44eb8ff157d3dee3abb1c23a3177ae85`
(literature folder `Test 2 acceptance receipts of the Weil pullback algebraic proof/`,
folder SHA256 `f1bd0a306f83a23f74243d5bdb9dcda6da121e89e037a3295c0b31e1a9954027`).
Their source bindings, checks and final source files were read there. The
commits below are commits of that earlier line:

| Content | Publication in the earlier line |
| --- | --- |
| Generic proof | `5bc58c2525e0499012801c80f17b6a9c04d57263` |
| Algebraic target | `9db46907db3181b0c1dfd287b8ab2f1f02054cab` |
| Pullback definition | `32f1fbf4cd19ab3f273133995b573b41c814aaff` |

The proof's binding targets the exact statement above, fingerprint
`cf576391460530659e34a842c1b05c7da15ec77124156dff986d83fa3385ace4`.
It passed Lake-build, exact-target, statement-definition and frozen-input
checks; its target matches,
and the only recorded axioms are `propext`, `Classical.choice`, `Quot.sound`.
The final theorem retains universe `u`. The statement and definition
validations establish their corresponding scopes and do not separately
claim a proof.

All six final files match both the external report snapshot
`f9c1742752d97c488fc1a835070bf50b534f4427` and the checked Library
`350369b5ca2d36132eb7e57d869fc0454f3a3707` byte for byte. This ties the
earlier checks to the files carried into this Library; neither compilation
alone nor downstream use supplies that conclusion. Paths below are relative to `Langlands/Weil/`:

| Path | SHA256 |
| --- | --- |
| `Algebraic.lean` | `a7c4651e692c5368802732fc344a99bdca22140ba35238684ad46fe2cb9a5da7` |
| `Algebraic.md` | `11ae46bcff12b6547bf8a90176994aa47be5d078618314c34fbcf09b7f91bd16` |
| `AlgebraicProof.lean` | `c9619175e9b1ec1b3e22ab4f42a132c3a7b92fb9770766e51da3b5d388d2389c` |
| `AlgebraicProof.md` | `6e55facba45a7e38be7b9564c8682f6b7e21ee0c2fbbf426d150261bad2e20c3` |
| `Pullback.lean` | `1dd3491a90d6849c98bd49a0abd9fa684313ef2b040c9ab11bc49d3967cd6380` |
| `Pullback.md` | `f312612d762200dffabd64f3589383423c9b8ad933c891f607724193b298eed5` |

## I062: actual dual and twist lattice operations

This finding holds at Library `77b88e13c66c007890e05a700979f65279070987`.
The primary pair and all companions below are unchanged from the report
snapshot. [Generic.md](../../../Langlands/VirtualRepresentation/Weil/Generic.md):69–73
incorrectly leaves both the actual local specialization and the operations
in the future. The scope of `Generic` itself is accurately described: it
constructs types and integral lattices on genuine continuous irreducible
classes, with independent group and carrier universes.

[Dual.lean](../../../Langlands/VirtualRepresentation/Weil/Dual.lean):20–140
constructs `Langlands.VirtualRepresentation.Weil.dualBasisEquiv` and
`dualLatticeEquiv`, by rank-wise genuine contragredient classes and finite
integral reindexing. It proves the involution, representative, coefficient,
degree, pairing and effective-cone laws. Its full hypotheses include
`[Group G] [TopologicalSpace G] [IsTopologicalGroup G]`, with independent
`uG` and `uV`. [Twist.lean](../../../Langlands/VirtualRepresentation/Weil/Twist.lean):20–134
constructs `twistBasisEquiv` and `twistLatticeEquiv` and the parallel laws
for `χ : G →ₜ* ℂˣ`; no `IsTopologicalGroup G` hypothesis is needed there.
The inverse is the twist by `χ⁻¹`. The imported `DualClasses` and
`TwistClasses` definitions were also read: these are operations on genuine
representation classes, not arbitrary supplied permutations.

[Local.lean](../../../Langlands/VirtualRepresentation/Weil/Local.lean):14–20
already specializes the basis and lattice to `localWeilGroup F` for every
prime `p` and `F : PadicField.{uF} p`, keeping `uV` independent. Its rank
family and Galois-type predicate reuse `LocalContinuousIrreducibleWeilClasses`
and `IsLocalGaloisType` from `Weil.Local.Parameters`. Reading the complete
pairs confirms that the generic-module boundary does not imply a missing
Library construction. The correction does not assert unitary preservation,
character orthogonality, a global spanning result or a correspondence.

The retained Henniart 2000 original, source `henniart-2000-simple-proof`,
SHA256 `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`,
was read directly at §§1.1–1.2 (printed pp.439–440/PDF pp.1–2), §§2.4–2.7
(pp.445–447/PDF pp.7–9) and §3.1 (p.448/PDF p.10). These give the genuine
continuous irreducible Weil classes, contragredience and character twists,
free integral lattice, degree and coefficient pairing, and the finite Galois
support used in the source. The arbitrary-group interface and finite-support
implementation are derived. No relevant errata file was present.

The companions below are definitions in the Library; the table gives the
commit where each first appeared. They do not claim a new proof target.

| Companion | Publication |
| --- | --- |
| Dual | `1058c134c0d2fb45ec96d08ea2956983aaac1d80` |
| Twist | `4fbc1953d45ea9aa3fa4b80478542c845102a4e5` |
| Local | `0aa8ebf100fddc512af4406817bcd1730dd75f75` |

Dual and Twist archived pairs equal the current pairs. Local's published
pair equals the current pair; its integration canonicalized the submitted
rank-family and Galois-type aliases to the existing `Parameters` declarations.
The complete differences and actual alias definitions were checked.

The correction (an earlier version did not enter the Library) first appeared
in the Library at `a4f4742431c7298bf38f4d4e6bc03a6cd7a33a18`. The corrected
Markdown hash is
`c510235fb9204ad7e8443c6ed821736e43166f0ff4ebe615a1bab6e52e15c4b2`;
Lean is unchanged.

Input hashes at the checked commit:

| Path | SHA256 |
| --- | --- |
| `Langlands/VirtualRepresentation/Weil/Generic.lean` | `12bb1f27ca71184ca7b089d6b8720fbae30378b6405647164d48ac3b47f6fc50` |
| `Langlands/VirtualRepresentation/Weil/Generic.md` | `45e75869403d34a93003f96f414458b70d58f7e12cca7fec6519a62e58877e88` |
| `Langlands/VirtualRepresentation/Weil/Dual.lean` | `323ec8c791062e702b843b8ab8569de964df0c1ef357a161325f994ded7fa7bc` |
| `Langlands/VirtualRepresentation/Weil/Dual.md` | `08eb97e2c378e71f4d626ec52bc5e722cbf36c09ed16fdcaf1d7ecdffc47368a` |
| `Langlands/VirtualRepresentation/Weil/Twist.lean` | `10cace6b1825b43a5b0886f14d2a60b289b7389187d8bcb2ae137ed0b8298122` |
| `Langlands/VirtualRepresentation/Weil/Twist.md` | `14e36c84cd58340915593d0e837b038742681a06a17622901e1290442cbb1bcd` |
| `Langlands/VirtualRepresentation/Weil/Local.lean` | `841da167450a9bef6c017b3e5e38161075520c5088b1366346be16167adb23e6` |
| `Langlands/VirtualRepresentation/Weil/Local.md` | `d964e29b234528fdb236af8fb1b52664ce6d29abfadf8e0ec5fe37ab194fb648` |
| `Langlands/Weil/Local/Parameters.lean` | `411478f2fd50ec77e62978dbc2352f5d3511bdb4d9d8cfc99e040c73fca8b551` |


## I064: the actual local Weil assembly

This finding holds for the obsolete missing-specialization checklist in
`Pullback.md:96–131` at the report Library
`f9c1742752d97c488fc1a835070bf50b534f4427`; the same checklist persisted
until this audit's correction. The generic
[Pullback.lean](../../../Langlands/Weil/Pullback.lean):18–75 remains a
construction for arbitrary `[Group Γ] [TopologicalSpace Γ]` and continuous
`φ : Γ →ₜ* ProfiniteIntegers`. Its own absence of field-specific objects
is a correct module boundary, not evidence that the Library lacks them.

[Local/Assembly.lean](../../../Langlands/Weil/Local/Assembly.lean):20–107
constructs the actual specialization for every prime `p` and
`F : PadicField.{u} p`. `localResidueMap` bundles the actual absolute
residue action; `localResidueDegree` composes it with the finite-field
comparison, and `localWeilGroup F` is exactly its generic pullback.
The residue field and its cardinality come from `F.canonicalTopologicalData`.
The kernel equality is proved, degree surjectivity follows from the actual
residue action and comparison, and the geometric lift is chosen from this
proved surjectivity. No surjectivity certificate, residue equivalence,
reciprocity map or Frobenius lift is assumed as input.

[Local/AssemblyStatement.lean](../../../Langlands/Weil/Local/AssemblyStatement.lean):11–50
defines the 22-clause `LocalAssemblyProperties` and the universally quantified
`LocalAssemblyStatement : Prop`. The complete pairs were compared with
[Local/AssemblyProof.lean](../../../Langlands/Weil/Local/AssemblyProof.lean):17–195.
The theorem `Langlands.Weil.Local.localAssembly` at lines 193–195 proves
that exact complete target, retaining the arbitrary field universe.
Its properties include the residue-action formula, injective dense
projection, surjective degree, inertia comparison, openness, compactness,
normality, nonarchimedean and locally compact Hausdorff totally disconnected
topology, and the normalized characters.

The projection-density proof at lines 37–50 uses the proved **open-map**
property of the residue degree and density of the integer image. Continuity
and surjectivity alone are not its argument. Lines 52–124 identify inertia
with the preimage of actual absolute inertia and give an open embedding and
a topological group equivalence preserving that original topology.
Lines 153–179 show that the chosen lift acts by geometric Frobenius, has
integer degree `+1`, and satisfies
`localNormCharacter(w) = q ^ (-localDegreeInt(w))`, hence value `q⁻¹` on
the lift. Here `q` is the actual residue cardinality. Unramified character
`z` has value `z` on that lift and value one on inertia. The generic degree's
multiplicative identity still denotes integer zero.

The supporting `Topology`/`TopologyProof` pairs, actual residue-action and
finite-field comparison declarations, and residue-character definitions
were read. Henniart 1980 §1.1 and §2.1/opening §2.2 (printed pp.155,158;
PDF pp.2,5; fingerprint recorded under I063) give the integer-Frobenius
preimage and the prescribed inertia topology. Henniart 2000 §1.1
(printed p.439/PDF p.1; fingerprint under I062) fixes the geometric
reciprocity convention. Tate, source `tate-1979-number-theoretic-background`,
*Number theoretic background*, Corvallis Part II, (1.4.1), (1.4.6), (4.1.3)
(printed pp.6,7,20/PDF pp.15,16,29), confirms geometric Frobenius and
`q^(-degree)`. The retained `Part II.pdf` SHA256 is
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
These originals were read directly; no relevant errata note was found.
The explicit pullback assembly and topology arguments are derived
implementations of these descriptions, not verbatim source theorems.

### Assembly acceptance and later publication continuity

The three companions are in the Library; the table gives the commit where
each first appeared:

| Companion | Publication |
| --- | --- |
| Assembly | `0fbab0ee36b0ab602b6d43bc3d60ada813fcedbf` |
| AssemblyStatement | `22b4f024e0d4218752e970d09329d1799f6d81d1` |
| AssemblyProof | `f01c1864161b6d1cdc1d04b1f8d577dfd4e8400f` |

The proof was checked with a Lake build, against its exact target, with its
statement and inputs unchanged.
Assembly and AssemblyStatement published pairs equal the current files.
AssemblyProof subsequently underwent two inspected refactors: import
relocation at `8728166c7a3a18d2d8347cd6c907cc2226768605` and extraction of
shared nonarchimedean subgroup helpers at
`056b7c747e32f712be4ac7fd004fd0af4845c968`. The complete differences and
extracted helper proof were checked; the target and field quantification
are unchanged. The latter publication's proof pair exactly matches the
final checked Library.

Both refactors were built with Lake when they entered the Library; these
are compilation checks, not new checks against the exact target.

The correction leaves Lean unchanged and replaces the obsolete checklist
with direct companion links and precise properties in current
`Pullback.md:98–136`. It first appeared in the Library at
`4ccd65d85917da26d0a67b9c48a37859533fffa9`.
This correction does not claim reciprocity or the entire parameter framework.

## I065: the published parameter-relation target family

This finding holds for the obsolete future-submission sentence in
`ParameterRelations.md:91–93` at the report Library
`f9c1742752d97c488fc1a835070bf50b534f4427`; it persisted until the correction.
[ParameterRelations.lean](../../../Langlands/WeilDeligne/ParameterRelations.lean):18–39
already defines `forget`, `IsDualOf` and `IsTwistOf` in
`Langlands.WeilDeligneRepresentation.ParameterRelations`.
The relations assert equality after forgetting to actual pair-isomorphism
classes: `forget E = dualClass (forget D)` and
`forget E = twistClass χ (forget D)`. They neither select an output nor
assert one exists. Dual uses inverse-element dual action and negative
transpose monodromy; twist scales the action and leaves monodromy unchanged.

[Parameters.lean](../../../Langlands/WeilDeligne/Parameters.lean):20–73
supplies the actual quotients and fixed-rank Frobenius-semisimple class types.
Open inertia kernel and semisimplicity of every nonzero-degree action are
separate predicates; Frobenius semisimplicity does not force monodromy to
vanish (`Basic.lean:220–225`). Both group universe `uG` and carrier universe
`uV` remain independent, with complex coefficients and arbitrary `n : ℕ`.
Rank zero is an internal extension of the sources' positive ranks.

The complete
[ParameterRelationStatements.lean](../../../Langlands/WeilDeligne/ParameterRelationStatements.lean):18–146
and its paired Markdown were checked. In namespace
`Langlands.WeilDeligneRepresentation.ParameterRelationLaws`,
`AlgebraicFamily` combines twelve Prop targets: forgetful injectivity,
representative characterization, class-rank preservation, rank normalization,
dual and twist uniqueness, dual preservation/existence/unique existence,
inverse laws, twist composition and dual-twist compatibility. It requires
only the separately specified group and topology. `TwistPreservation`,
`TwistExistence`, `TwistUniqueExistence`, and their complete conjunction
`Statement` explicitly retain `[IsTopologicalGroup G]`. The three twist
totality clauses quantify algebraic `χ : G →* ℂˣ` and require
`IsOpen ((χ.comp I.subtype).ker : Set I)`. Continuity with the ordinary
complex topology is not substituted for this condition. The relation laws
on existing outputs do not silently imply totality for arbitrary characters.

A final search throughout the current Library for `ParameterRelationLaws`,
`ParameterRelationStatements`, `ForgetInjective`, `DualUniqueExistence`
and `TwistUniqueExistence` found no theorem proving the complete target.
This is a checked status statement, not an inference from the report's date.
It does not mean that all individual operation facts lack proofs:
[ParameterOperations.lean](../../../Langlands/WeilDeligne/ParameterOperations.lean):35–43,99–107
already constructs `parameterDual`, `parameterTwist`, `parameterDualClass`
and `parameterTwistClass`, with actual preservation certificates and quotient
descent. Their general open-inertia parameter objects/classes have no
Frobenius-semisimple fixed-rank restriction. The required topological group
structure and character's open inertia kernel are explicit. The supporting
`Weil/Representation/InertiaOperations.lean` proofs were read. Those certified
constructions do not by themselves prove the complete relation family.
Thus the finding about stale target availability holds; the report's phrase
about propositions awaiting proof is not adopted as a blanket assertion
that every component fact is unproved.

The original sources were read directly: Henniart 2002, source
`henniart-2002-characterization`, *Une caractérisation de la correspondance
de Langlands locale pour GL(n)*, §§1.1–1.2 and §2.1 (printed pp.588–589,593;
PDF pp.2–3,7), retained SHA256
`40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`;
and Tate 1979 §§4.1.2–4.1.5 (printed pp.20–21/PDF pp.29–30; source and
fingerprint under I064). They support the finite-dimensional complex
pairs, morphisms, semisimplicity, duals and tensor operations. Character
twist is tensoring with a one-dimensional zero-monodromy character.
The arbitrary-group quotient predicates and separate preservation targets
are internal derived formulations. No relevant errata note was found.

### Parameter-family acceptance and correction

The three modules below, of definitions and statements, are in the Library; the
table gives the commit where each first appeared. This establishes the
definitions and targets, not a proof of the complete `Statement`.

| Content | Publication |
| --- | --- |
| Relation definitions | `4fbc1953d45ea9aa3fa4b80478542c845102a4e5` |
| Relation targets | `1058c134c0d2fb45ec96d08ea2956983aaac1d80` |
| Parameter operations | `0fbab0ee36b0ab602b6d43bc3d60ada813fcedbf` |

The published target and operation pairs remain byte-identical at the final
checked commit. Only the relation definition's Markdown changes in the
present correction. The correction retains the complete Lean bytes. It
first appeared in the Library at `4ccd65d85917da26d0a67b9c48a37859533fffa9`. Current `ParameterRelations.md:29–39`
and `96–106` state the target, hypotheses and precise proof-status boundary.

## I064/I065 fingerprints at the final checked commit

The following hashes were computed directly at
`fb40559309dd366f4145aa31aad8c3db11b7cc07`. Supporting hashes already listed
under I063 remain unchanged except for the corrected `Pullback.md` and
`Algebraic.md`, whose final hashes appear in the final correction table.

| Path | SHA256 |
| --- | --- |
| `Langlands/Weil/Local/Assembly.lean` | `576d8ad3c15763bdf047c2289beea60530c5d95a70963395444fd1efbd49cad8` |
| `Langlands/Weil/Local/Assembly.md` | `6fb1c6a6e8e5a6ba9748ed021c5050bbca06589072e1ef3d26af0d850beb8b83` |
| `Langlands/Weil/Local/AssemblyStatement.lean` | `257bab85d6935726336a9451ed7a458d08b43b5a90140be68afefcb6252c6a70` |
| `Langlands/Weil/Local/AssemblyStatement.md` | `9e3b835470aa59015a12dba2b50db820c74c31d555cfc2362247805f57ecddf7` |
| `Langlands/Weil/Local/AssemblyProof.lean` | `a8e8087cb95c9de574ef67997d1134fca381d2d0843db106996d3eaad36b6f8d` |
| `Langlands/Weil/Local/AssemblyProof.md` | `1b23a1c8a5dd80f57cd8a01d108793059eb7cb71d8cf1472622a03b41447dacb` |
| `Langlands/WeilDeligne/ParameterRelations.lean` | `29d82698b08437c8230780ae06d36818cc62708cf164be30aa9ea6bb77a00c66` |
| `Langlands/WeilDeligne/ParameterRelations.md` | `3012083002f45d4dfee70f6909fbf2a19f19703229d923b557c27af57e17a773` |
| `Langlands/WeilDeligne/ParameterRelationStatements.lean` | `d64c91bcadfaf0a3250250cb1bc1ddfe177ca2a2c91d370eec404d4f2ea87a0e` |
| `Langlands/WeilDeligne/ParameterRelationStatements.md` | `3347b44a6ac06b7546e776a29c09b5b1555710e177357378df5c15c106dade1f` |
| `Langlands/WeilDeligne/ParameterOperations.lean` | `69e66e699930c8e2262bd57356fd84a75db516d63770e37b263a43f496d60027` |
| `Langlands/WeilDeligne/ParameterOperations.md` | `4d0bdb46bfebea0d5017f759f6f499a72c8c5df5acffa2cfd23d5959aa167e9b` |
| `Langlands/WeilDeligne/Parameters.lean` | `73663a8250d1bdc055a419d6574169de0278ee17e26cc457841be3ff6b38898c` |
| `Langlands/WeilDeligne/Parameters.md` | `372bc4b5bdcc3581e8d1c77291f200a453ca65a8d46f7d9c8d1e793e9a90d196` |
| `Langlands/Topology/Nonarchimedean/Subgroup.lean` | `a45ededd3f67a6645df268d1bf9da0cbcac964137c448ef89966630cd4b4c026` |
| `Langlands/Topology/Nonarchimedean/Subgroup.md` | `01724029b2c592535f55fea2ec4a857a7d15d15156063567d1216e1e4b265675` |

## Final correction publications and current-file reconciliation

All eight corrections are in the Library and were built with Lake when they
entered it. The table gives the commit where each first appeared. These documentation corrections leave every
affected Lean file unchanged. Integrated compilation alone is not asserted
to check meaning or an exact proof target.

| Findings | Publication commit |
| --- | --- |
| I006/I009 | `2173e15e1a7e4f96682e6274d63c4f98ccce2c73` |
| I018/I019 | `886e27567a757917705b7adef45a2c2621bf4bf7` |
| I020 | `4ccd65d85917da26d0a67b9c48a37859533fffa9` |
| I021 | `4ccd65d85917da26d0a67b9c48a37859533fffa9` |
| I062 | `a4f4742431c7298bf38f4d4e6bc03a6cd7a33a18` |
| I063 | `a4f4742431c7298bf38f4d4e6bc03a6cd7a33a18` |
| I064 | `4ccd65d85917da26d0a67b9c48a37859533fffa9` |
| I065 | `4ccd65d85917da26d0a67b9c48a37859533fffa9` |

Each of the ten corrected Markdown files, and its unchanged Lean partner,
was compared directly among the corrected version, the commit where it
entered the Library and the final checked Library. All three hashes agree. The corrected Markdown
hashes are:

| Path | Current SHA256 |
| --- | --- |
| `Langlands/Cohomology/Tate/SubgroupShifts.md` | `656eac9f41b5a10b3d87bbc4ebfe6f71d372727190f574d55f7f5dbaa4cd401c` |
| `Langlands/Cohomology/Tate/CochainComparison.md` | `113e2470d4acd06a455dc59d8e30c8278cdb7acc4f7496a260a36c314342602d` |
| `Langlands/ClassFieldTheory/Local/ClassFormation.md` | `540ae013a15ee4fbfcf0a53a847cae8f70fa426aeee5de4a0bfe5fa422334a72` |
| `Langlands/ClassFieldTheory/Local/FundamentalClasses.md` | `d452d2fc2107e558a881ed24e7face6e1833f77ef74c9b71e7a639714e452bc1` |
| `Langlands/ClassFieldTheory/Local/UnitFiltrationTopologyStatement.md` | `06a7403c4d0254ee50545083e3203bc1bf6a73a9860fe88437259804ccca0fb3` |
| `Langlands/ClassFieldTheory/Local/WeilReciprocityStatement.md` | `30f10173b6c45f3b08e52359ab1005c469d023bf10eeae3fa9383e5d34ef3748` |
| `Langlands/VirtualRepresentation/Weil/Generic.md` | `c510235fb9204ad7e8443c6ed821736e43166f0ff4ebe615a1bab6e52e15c4b2` |
| `Langlands/Weil/Algebraic.md` | `0a93572cc4956df7085c6024121f40f5446178acf07cab6b653207c00b511154` |
| `Langlands/Weil/Pullback.md` | `c0e3920055cbff41b823da174209cb8531e528672b3ed271a90270209b9f101c` |
| `Langlands/WeilDeligne/ParameterRelations.md` | `3012083002f45d4dfee70f6909fbf2a19f19703229d923b557c27af57e17a773` |

The 67 input-table entries recorded before I064/I065 were reconciled with
the final current tree. Only the nine corrected Markdown entries in those
tables changed; all other listed hashes remain exact. The tenth corrected
pair, `ParameterRelations`, is fingerprinted above. The latest Tate
declaration inspection also completed
with zero errors or warnings; it is development evidence.

The corrected current prose is located at `SubgroupShifts.md:5–31`,
`CochainComparison.md:12–34`, `ClassFormation.md:141–160`,
`FundamentalClasses.md:73–104`, `UnitFiltrationTopologyStatement.md:49–61,93–114`,
`WeilReciprocityStatement.md:97–126,183–186`, `Generic.md:69–85`,
`Algebraic.md:29–36,69–77`, `Pullback.md:98–136`, and
`ParameterRelations.md:29–39,96–106`, in the directories identified above.
The unchanged Lean locations in the analysis remain current.

No assigned correction remains unpublished at this checked commit. The
accurately disclosed open realization, reciprocity and complete parameter-law
proof goals are outside the correction obligation. This note records the ten
findings and their repairs; it does not certify the entire local Langlands
correspondence.
