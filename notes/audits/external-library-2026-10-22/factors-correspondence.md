# External Library audit: local factors and correspondence

Author: Worker 46. Audit task `7d7f925d-f349-4657-b964-a38871b7c372`, revision 2.
Checked on 2026-10-23 against Library
`fb40559309dd366f4145aa31aad8c3db11b7cc07`.

All nine assigned findings have verdicts below. The verified documentation
defects have been repaired by seven independently accepted and published
correction candidates. The current documents distinguish conditional
constructions, available statements and proved results from the remaining
existence and correspondence goals. No Lean change was required by these
findings; all seven corrections preserve Lean bytes.

All assigned primary Lean and paired Markdown were read, together with the
relevant definitions and consumers. Original-source readings and authoritative
review, validation and publication evidence are recorded below. Verification
began at `b26cde6370d6c0976d0002a7f4c955db801efd02`; the 68-file audit set
was rechecked at the current snapshot, and the additional `LanglandsLFactor`
pair was read and checked against its accepted publication. Historical and
current fingerprints are retained separately below. This audit does not certify
the full correspondence or require proofs of accurately disclosed unrelated
goals. Independent publication of this verdict note is separate from acceptance
of the mathematical correction candidates.

The external reports are leads, not acceptance evidence. Their registered source
is `external-library-audits-2026-10-22`, folder fingerprint
`975133657fad9fc7d0806e2cf4aaefac907edd151ec4df6cdd5d92b18a95a93b`.
ISSUES-1 describes Library `c5a40b0f54880b1825ea05214c2b066f68bfc156`;
ISSUES-2 describes `f9c1742752d97c488fc1a835070bf50b534f4427`.
Line locations refer to the checked current snapshot unless explicitly labelled
historical; they are not copied from the report snapshots.

## Verdicts

| Finding | Verdict at the checked snapshot | Correction / no-change decision |
| --- | --- | --- |
| I001 | Does not hold in the current Library. The historical uniqueness-without-existence error held and is repaired. | Published correction retains actual existence and uniqueness for the same reciprocity family, normalization when applying `Exists`, and the outer base-reciprocity witness. No further correction. |
| I011 | Does not hold in the current Library. The historical valuation-convention error held and is repaired. | Published prose uses the actual multiplicative-valuation subgroup, including the identity at every level. No further correction. |
| I034 | Does not hold in the current Library. The historical finding of stale epsilon-zero availability prose was confirmed and repaired. | Published correction describes the conditional value and unproved Swan goals. Shared correction with DOC-05; no further correction. |
| I035 | Does not hold in the current Library. The historical pending-assembly description held and is repaired. | Published correction identifies actual local Weil assembly and common-closure specialization while retaining base-field normalization. No further correction. |
| I050 | Does not hold in the current Library. The historical finding of stale dual-function proof status was confirmed and repaired. | Published correction distinguishes the proved transformation from the separate contragredient identification. Shared candidate with this file's DOC-08 correction; no further correction. |
| ISSUES-1 DOC-05 | Does not hold in the current Library. The historical stale claim held; repaired by the same candidate as I034. | Conditional epsilon-zero construction and stated Swan formulas are now distinguished from unconditional existence and proofs. No further correction. |
| ISSUES-1 DOC-08 | Does not hold in the current Library as an allegation of missing library interfaces. The four historical stale availability passages were confirmed and repaired. | Three published correction candidates cover the four documents. Their narrower generic or L-only scope and unproved goals remain unchanged. No further correction. |
| ISSUES-1 GOAL-01 | Holds as an accurately disclosed open-proof observation. Correspondence and assembly goals remain proposition definitions. | No corrective mathematical change. Their proof obligations remain separate work. |
| ISSUES-1 GOAL-02 | Holds in part. Missing-adapter, missing-unified-specification and no-consumer claims do not hold. Universal factor existence and full correspondence proofs remain open. | Published interfaces and certified class transport supply counterevidence to the absence claims. No duplicate specification task or target weakening; remaining obligations are mapped below. |

## I001: the same fixed reciprocity family

At the historical baseline,
`Correspondence/SupercuspidalFactorCompatibility.md:135–142` claimed that
`NonabelianSystem.Unique` alone makes the existential and universal forms agree.
The corrected current paragraph (142–169) supplies the missing existence and
normalization conditions and retains the fixed-family and base-reciprocity
requirements. The actual definition at
`SupercuspidalFactorCompatibility.lean:88–95` retains
an existential reciprocity family `eC`, assignment, system witness and
`IsBaseReciprocity F e eC`. It does not make the invalid replacement.

`LocalFactor/NonabelianSystem.lean:58–71` distinguishes:

- `IsSystem F eC ε`, which includes `NormalizedReciprocity F eC`;
- `Exists F eC`, an implication from that normalization to an actual system;
- `Unique F eC`, equality of any two assignments satisfying `IsSystem`.

For one fixed `eC`, existence **and** uniqueness justify the equivalence between
existential compatibility and compatibility for every system. To obtain
existence from `Exists`, normalization must also be supplied. The outer
existential choice of `eC` with its prescribed base reciprocity remains:
uniqueness for one family does not compare assignments for different families.
An empty abstract predicate illustrates the logical error; it does not establish
that an actual arithmetic family has no system. Nor is truth or vacuity determined
by whether an existence proof has yet been formalized.

Tate 1979 (3.4.1), printed pp.14–15 / retained Part II PDF pp.23–24,
asserts both existence and uniqueness. Henniart 2000 §§1.1–1.3,
pp.439–441, supplies the correspondence, normalization and pair-factor context.
The published correction is documentation only.

## I011: principal units at the identity

The historical Objects paragraph of `LocalFactor/EpsilonOneStatement.md`
described `U^m` using `ord(u-1) ≥ m` immediately after introducing the
integer-valued `T.ord`. The current paragraph (16–24) instead gives both
multiplicative-valuation conditions and explains why the identity is included.
`LocalField/Normalization/Definitions.lean:104–106` explicitly uses
zero as its value at zero; `Normalization/Proof.lean:65` proves `ord_zero`.
Thus the historical displayed description excluded `u = 1` for positive `m`.

The actual subgroup in `HarmonicAnalysis/Conductor.lean:175–218` requires
`T.discreteValuation u = 1` and
`T.discreteValuation (u-1) ≤ WithZero.exp (-m)`. Its subgroup identity field
includes `1`, and `mem_principalUnits_zero` identifies level zero with the
integral units. A correct additive-order description must retain the integral-unit
condition and say `u = 1` or `T.ord (u-1) ≥ m`.
Tate (3.2.6), p.13 / PDF p.22, and (3.6.10)–(3.6.11), p.18 / PDF p.27,
were checked. This finding changes neither the conductor definition nor the
epsilon-one formula.

## I034 and DOC-05: epsilon zero already has a conditional value

At the historical baseline, `LocalFactor/ConductorExponentStatement.md:166–169`
said that epsilon zero was undefined and the Swan formulas unstated. The current
paragraph (166–185) identifies the conditional construction and all three
unproved Swan goals with their hypotheses. In the published
`LocalFactor/EpsilonZeroStatement.lean`, `EpsilonZero.value` (49–55) multiplies
the supplied system's spectrally twisted epsilon by `invariantDeterminant`.
`invariantDeterminant_eq_of_frobenius` and `value_eq_of_frobenius` (58–81) prove
independence of the geometric lift. At spectral parameter zero this has
Deligne's (5.1) orientation: epsilon zero equals epsilon times the determinant
of minus Frobenius on inertia invariants.

`SpectralSwanStatement`, `UnramifiedCharacterSwanStatement` and
`UnramifiedTensorSwanStatement` (132–190) are explicit `Prop` goals. They retain
the supplied system, genuine continuous representation, finite-inertia
presentation, surjective restriction, geometric lift, and rational Swan/integer
exponent witnesses. They are not proofs of the Swan formulas or of unconditional
system existence. Deligne 1973 (5.1)–(5.5.3), printed pp.548–549 / PDF pp.48–49,
was checked from the original text and page images. One published correction
resolves both finding IDs.

## I035: abstract twists and actual arithmetic assembly

The historical `LocalFactor/SpectralTwist.md:91–97` correctly described a
general continuous degree on a topological group and positive `q`, but
incorrectly left actual local Weil assembly pending. The corrected current
paragraphs (91–115) identify both arithmetic companions and retain the
abstract module's scope. `Weil/Local/Assembly.lean:30–106` constructs the
arithmetic residue map, `localResidueDegree`, `localWeilGroup`, `localDegree`,
and a geometric degree-one lift; degree surjectivity is proved.
`LocalFactor/CommonClosureSpectral.lean:26–56` supplies `baseDegree`,
`baseCardinality`, `character` and `virtualTwist` for actual common-closure
subgroups. The base degree is restricted from the base-field Weil group; its
normalization must not silently become the intermediate field's degree.

These companions instantiate the abstract construction. They do not turn every
arbitrary `d,q` into arithmetic data or prove unrelated local-factor laws.
Tate (1.4.1), p.6 / PDF p.15, and §2 opening and (2.2), pp.9–10 / PDF pp.18–19,
were checked for the Weil-group and degree conventions.

## I050 and DOC-08: transformations and nongeneric factors

The historical
`Representation/RankinSelberg/PairEpsilonNormalizationStatement.md:134` wrongly
said that neither dual-function transformation nor contragredient identification
had been proved. The current paragraph (146–157) names the transformation
results and explicitly keeps the contragredient-identification obligation
separate. `Representation/Whittaker/DualTransform` constructs the
transformed functional and proves its coefficient formula and nonvanishing.
`RankinSelberg/LocalFactor.lean:679–694`,
`dualFunction_mem_whittakerSet`, proves the resulting Whittaker-set membership
for `inverseTransposePullback` and `ψ.scale (-1)`. This does not identify that
representation with its smooth contragredient. JPSS 1983, p.386 / PDF p.21,
formula (4), states the function transformation separately from that
identification; the original scan was read visually. BH99 §3.3, p.540 / PDF p.7,
was also checked.

The four corrected DOC-08 locations are:

| Document under `Langlands/` | Current corrected lines | Preserved module scope |
| --- | --- | --- |
| `Representation/RankinSelberg/PairEpsilonNormalizationStatement.md` | 159–181, 192–201 | Its normalization and exponent goals use the generic integral relation. The exponent goal itself asserts no factor existence and can be vacuous without the required Whittaker functionals. |
| `Correspondence/FullLFactorCompatibility.md` | 129–154 | This module defines the full L condition only; it now identifies the separate full epsilon/specification interfaces. |
| `Correspondence/AssemblyLFactorStatement.md` | 124–142 | Its inheritance and characterization goals are L-only and unproved; separate epsilon inheritance and conditional assembly goals are identified. |
| `Global/Factors/GLPoleRegionStatement.md` | 181–202 | This pole-region statement retains its generic JPSS factors and hypotheses while identifying the separate nongeneric L relation and conditional constructors. |

`RankinSelberg/LanglandsFactors.lean:152–210` already defines
`IsLanglandsPairEpsilonFactor` with actual square-integrable Langlands quotient
data for **both** representations and a block-product certificate for every
presentation. It proves uniqueness and constructs `langlandsPairEpsilonFactor`
from actual data, block-factor existence and presentation independence.
`LanglandsFactorDescent.lean:122–162` derives independence conditionally from
classification and constructs the factor from explicit classification,
exhaustion and block-existence inputs. Those inputs are not proved by the
constructor.

`LanglandsQuotientLFactorStatement.lean:78–114` likewise requires actual tempered
Langlands quotient data for both representations before its universal
standard-module condition; it proves uniqueness. The universal
`LanglandsPairLFactorExistenceStatement` (171–186) and
`GenericLanglandsQuotientLFactorStatement` (146–165) remain unproved
propositions. `LanglandsLFactor.lean:197–255` constructs a certified polynomial
from supplied regular classification and standard-module analytic existence,
using supplied actual quotient data or explicit exhaustion to obtain those data. Its classification constructors use the
enlarged block universes `max uF uV` and `max uF uW`.
`langlandsPairLFactor` (121–139) constructs the rational unit `1/P(X)` from a
certified polynomial. These constructions do not prove their input hypotheses.
Missing presentations cannot make either relation true through an empty universal
quantifier. None of these facts enlarges a generic theorem into a nongeneric one.

The product and classification conventions were checked against BH99 p.538 /
PDF p.5 and Henniart 2002 §2.8, p.596 / PDF p.10. JPSS §9.4, p.458 / PDF p.93,
was read visually for the nongeneric L construction. For the pole-region scope,
Henniart 1986 §§2.5–2.6(a), p.152; Proposition 4.5(ii), p.160; and §4.8,
pp.162–163 (PDF pp.9,17,19–20), were read. The published corrections distinguish
these available interfaces from universal existence and generic-comparison proofs.

## GOAL-01 and GOAL-02: available specifications and open proofs

`Correspondence/SupercuspidalSpecification.lean:25–52` contains the substantive
predicate and its existence, uniqueness, exists-unique and all-fields goals.
`AssemblyRelation.lean:97–125` and `AssemblyLFactorStatement.lean:38–56` contain
assembly goals. They are `Prop` definitions, not proofs; their documentation
says so. Current declaration/use searches and the publication/work map below
supply no proof of these goals. GOAL-01 is an accurate status observation,
not a mistranslation requiring a corrective candidate.

GOAL-02's specific missing-interface claims are superseded by the published
`FullFactorCompatibility`, `FullSpecification` and `AssemblyTheorems` bundle:

- `IsAutomorphicPairEpsilonFactor` (`FullFactorCompatibility.lean:37–47`) is a
  predicate on actual automorphic classes. It existentially supplies actual
  representatives and equivalent smooth representations in the enlarged carrier
  universe, then requires `IsLanglandsPairEpsilonFactor`.
- `IsPairEpsilonCompatibleAt` (52–63) requires existence of a self-dual measure
  and, for **every** such measure, a common `e : ℂˣ × ℤ` witnessing the
  automorphic and arithmetic relations. The arithmetic side retains the actual
  transported representation and geometric Frobenius requirements.
- `FullEpsilonCompatibility` (83–88) existentially retains a normalized
  local-constant system with the **same** prescribed base reciprocity.
  `FullFactorCompatibility` combines this with full L compatibility.
- `IsFullCorrespondence` (`FullSpecification.lean:30–35`) combines rankwise
  bijectivity, duality, geometric reciprocity, rank one, determinant, twist and
  full pair factors for all allowed characters. `FullCorrespondenceStatement`
  (54–56) is an all-fields exists-unique proposition with no correspondence input.
- `AssemblyTheorems.lean:27–40` states epsilon inheritance and conditional
  assembly. Despite its filename, these are unproved propositions.

The exact current Lean and Markdown for these three modules equal the accepted
bundle's archived bytes. Direct imports of `LanglandsFactors` now occur in
`FullFactorCompatibility`, `LanglandsFactorDescent` and `LanglandsGammaFactor`.
The last constructs a rational gamma unit conditionally from epsilon, L and
actual-dual L certificates. Its acceptance does not identify it with the
correspondence gamma predicate: the auxiliary-character and representative
comparison remains separate.

The published `Correspondence/AutomorphicPairFactors` supplies the
representative-independence bridge as well. Its
`IsLanglandsPairEpsilonFactor.congr_equiv` and
`IsLanglandsPairLPolynomial.congr_equiv` (Lean lines 92–136) transport actual
quotient witnesses forward and universally quantified datum certificates
backward, preserving the same block universes. The class iff lemmas (153–191)
compare the existential class predicates with the relations on supplied
equivalent representatives. The two class `unique` theorems (195–214) then
transport one certificate to the other's representatives and apply the
published representation-level uniqueness result.

These results fix the additive character and Haar measure. The class adapters
use block universe `uA` on both sides and carriers in `max uF uA`, with actual
equivariant linear equivalences to the class representatives. The L constructor
(231–254) forms the rational unit `1/P(X)` from a certified polynomial; the
epsilon constructor (256–276) still requires quotient-data existence for both
representations, block-factor existence and datum independence. It does not
silently use the classification constructor at a different block universe.
The complete pair and independent review were read; the integrated files match
the submitted hashes. Henniart 2002 §1.2, p.589, and §2.8, p.596, and JPSS §9.4,
p.458, supply the normalization and class/product interpretation already checked
from the originals.

Thus representative independence and uniqueness for these certified class
relations are now proved, in addition to the earlier predicates and
specification. The absent-adapter, absent-unified-goal and no-consumer subclaims
do not hold. Existence of a factor for every class pair, character/measure
independence, block-universe lowering and the full correspondence proofs are
not established by this construction.

The remaining obligations map to the existing work below. This is the ownership
map recorded at the initial audit, including its historical DAG revision; it is
not a claim about the current queue state or accepted proof evidence. The current
Library declaration/use search still finds the named correspondence, assembly,
universal L-existence and generic-comparison targets as `Prop` definitions,
with no theorem proving them.

| Obligation | Existing work or planning location |
| --- | --- |
| Square-integrable classification consumed by epsilon descent | Exact-target proof task `1cb45da2-7007-4351-a694-594fb148b8d1`, revision 1. |
| Square-integrable exhaustion consumed by epsilon descent | Exact-target proof task `cd8ab97c-0b78-4bce-97c4-d307a28159a4`, revision 1. |
| Actual representation-side factors, analytic existence and intrinsic construction bridges | Definition/construction host `6f0365a3-7419-4804-b209-3fc348b878de`; associated JPSS statement branch `80b8ac90-940b-487d-acdf-1f228d63f8d6`. Conditional constructor acceptance does not close this host. |
| Correspondence predicates and assembly statement interfaces | Statement task `1fecded2-fe72-47d9-8d3f-035897e9bc29`; the accepted bundle below fills the reported specification gap. |
| Full factor compatibility, assembly, characterization and final LLC proofs | Shared proof DAG revision 340: `proof.full-factor-compatibilities`, `proof.conditional-classification-assembly`, `proof.full-llc-characterization`, `proof.local-langlands-all-ranks`. These are planned proof obligations, not implemented theorems. |

No new statement or proof task is justified merely by an accurately disclosed
open goal. The published class-transport bridge belongs to the existing factor
host; its acceptance does not discharge that host's remaining existence work.

## Original-source record

The retained originals were read at the locations above, and all seven source
fingerprints were rechecked on 2026-10-23. Existing source/errata navigation was
checked; sources were reused, not substituted by report quotations.
PDF page numbers are one-based. Full source fingerprints are:

| Registered source | SHA-256 |
| --- | --- |
| `tate-1979-number-theoretic-background` | `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6` |
| `henniart-2000-simple-proof` | `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de` |
| `deligne-1973-local-constants` | `b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844` |
| `bushnell-henniart-1999-epsilon-pairs` | `ef13701607152419ec6d0a6e5d4c07803405bc134eef71a2780b1ffddbe6566f` |
| `henniart-2002-characterization` | `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306` |
| `henniart-1986-cyclic` | `096fba993b7368b1af9f7cc1f0c053e5436ba447f291c2acd402f058eb44b0ba` |
| `jpss-1983-rankin-selberg` | `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245` |

For GOAL-02, Henniart 2002 §§1.1–1.8, pp.588–592 / PDF pp.2–6, and §2.8
were checked directly. The verdict concerns the availability and scope of the
current predicates, not a new independent acceptance of every LLC statement.

## Accepted companion evidence

The following authoritative artifact archives and `publication.json` receipts
were checked, including independent approvals and accepted validation. All listed
reviews have empty qualifications. Definition/statement acceptance is not proof
acceptance of their unproved goals. These records establish the particular
published companions used above, not completion of their broad host tasks.

| Companion | Candidate | Independent review task | Publication commit |
| --- | --- | --- | --- |
| Epsilon-zero definition and statement family | `02bb9cbf-0e28-432f-9be8-2dad72f3eb8f` | `d5591dba-1ef1-4e9b-9a77-b9ae2f755637` (approve) | `e3c2fa98be720f63c6981efbbdf15cd223329e76` |
| Actual local Weil assembly | `3b435643-8dc4-46a5-833c-78f20652b225` | `e999a445-baa0-4b07-bfbd-f80cde88f530` (approve) | `0fbab0ee36b0ab602b6d43bc3d60ada813fcedbf` |
| Common-closure spectral specialization | `8e20959a-d7a5-4932-a36b-1d60f61451bd` | `507bac7b-2197-4e3f-9a4d-fb47833dadef` (approve) | `7db0c477a21f8471b1e5cff5f20d8ecb3dd2285b` |
| Local-factor module containing the dual-function membership theorem | `b5a9a5a8-7d2f-4d84-9acb-9678053ceff9` | `10d48baa-2272-4dac-9763-fcc9b25cabfc` (approve) | `7db0c477a21f8471b1e5cff5f20d8ecb3dd2285b` |
| Nongeneric epsilon relation and constructor | `b8752e4e-5383-4013-9095-36e5a351ceaf` | `1404006d-9764-4b16-a140-de9bf0d8dbfc` (approve) | `2e31df852eed5b4c1a45eca581f8480418360a34` |
| Nongeneric L relation and statement family | `bb2f6617-d42a-409a-a4b7-ee6968df5dd6` | `4167e4f5-596c-41c4-8a9d-e55c62ac069d` (approve) | `01a58491bc71539f1ecd3d5f0eec6ab8eae20fed` |
| Full compatibility/specification/assembly bundle | `93e999f3-90cd-4126-94fb-a4f181baaa27` | `b65bce71-9b18-4ffa-a31e-338c481c7435` (approve) | `a93d5169d27e08500e30b75e254252103329adc1` |
| Epsilon descent conditional on classification | `1adb6aa6-c23b-4b42-962a-b89cb4a26bb5` | `c68c11b2-3b8a-4ea5-aafb-cd706e34173f` (approve) | `ed386d3458bf6efda6bdcd8bafd745280be7efb6` |
| Conditional nongeneric gamma unit | `79e2d944-1b25-4560-86d0-0ca08a35d740` | `2f1fb87c-ae81-4a2a-8796-0469bf7e973c` (approve) | `f1b212cc117b9c34dced95c0ac88e6328827334d` |
| Certified automorphic-class pair factors and representative independence | `9f85b200-5b60-43e9-b3d8-91652d027ea4` | `dbcb00a4-c1b2-440b-afd4-d06210120cf1` (approve, Reviewer 1266) | `9ff0d4f8edaf10dd32d87468c3045da6ec3ee5c6` |
| Conditional nongeneric L-polynomial and rational unit | `f2887fab-657b-4267-86e8-0fd328decbf3` | `695d1290-78da-4e50-9ab7-13f83b98de74` (approve, Reviewer 1091) | `cddb0412f1a617f8f0476ab118a15618a386cf2d` |

The gamma candidate's archived submission differs from the integrated module:
the duplicate reciprocal-residue scale and its coercion lemma were moved to
`LocalFactor/ResidueReflection`. The current gamma and reflection pairs equal
the files published at `f1b212cc117b9c34dced95c0ac88e6328827334d`. Its Library
manifest snapshot, publication snapshot and accepted fresh integrated Lake-build
validation all name
`0fc6ba034bfd0ce7a64c05098764866083ff214217448ceda8251ff3329d8499`.
The independent review explicitly identified the duplicate scale; the shared
module preserves its value. This is an integration adjustment, not byte identity
with the original submitted pair. The full-compatibility/specification/assembly,
epsilon-descent and nongeneric-L pairs do equal their archived submissions.

The class-adapter candidate has accepted machine validation
`6e2b61f0-d0cf-45e5-bad4-6ae1fc2dd642` under `lean.definition@1` and unqualified
independent approval. Its publication integration
`148983378bb2432f91bb11e3c3da274c` records a successful fresh integrated Lake
build of snapshot
`d9065036c82d8e163875e4f95ce3ae42466ca33d4787557bbda0e8d35856d1a1`.
The integrated review differs from the original approval only by integration
identifiers. This acceptance concerns the certified construction, not universal
factor existence or completion of the broad host.

## Correction ledger

All seven candidates below are accepted and public. Their complete independent
reviews were read; all are unqualified approvals. Exact-candidate machine
validations and fresh integrated Lake builds were accepted. For each correction,
the frozen snapshot was compared with its repository base: only the intended
paired Markdown changed, with no Lean changes. For sparse archives the unchanged
files were resolved from the recorded base. Archive hashes and the target pairs
were checked against the publication commit, the checked current Library and the
workspace. The integrated review reports differ from the original approvals
only in integration metadata. Worker 46 verifies these receipts and does not
self-review the correction candidates on which Worker 46 is a coauthor.

| Finding coverage | Correction task (revision) | Accepted/public candidate | Independent reviewer / review task | Accepted machine validation | Publication commit |
| --- | --- | --- | --- | --- | --- |
| I001 | `7ab65f0d-3be2-45d7-a4ab-d9ad2c31cbcb` (1) | `983c0d99-8b95-486f-b1e0-c73a2d2bbc07` | Reviewer 1344, approve: `92068d9c-ed33-488e-91fd-4cf26874b62f` | `50f6dd1f-9c9e-4182-8f6c-91df97b09c6e` | `b263cfa454b11d485198ae46d8290f32435e48c6` |
| I011 | `3030c695-849f-43d7-babe-4a0e41084e5f` (1) | `4c95c30b-a4f9-47cf-9d07-2162651619ba` | Reviewer 1415, approve: `911ed731-56d0-4246-998a-2d26855cfd71` | `b988be0f-a0dd-4001-a6b0-6bd503e640eb` | `886e27567a757917705b7adef45a2c2621bf4bf7` |
| I034 and DOC-05 | `9bca79c2-e874-4f9c-8755-bbe9d8a7f76c` (1) | `b3d7132d-038d-48a7-b5d2-7ddf40c1bc8d` | Reviewer 1423, approve: `412dc076-97b3-4d5f-81d8-d164b8733304` | `b41b22e9-a966-4265-ba14-40902328ac57` | `886e27567a757917705b7adef45a2c2621bf4bf7` |
| I035 | `ca457911-4ae7-4810-bf81-70b1905008fa` (1) | `def45475-3949-48a4-96bd-e011345066dc` | Reviewer 1412, approve: `ec41d6aa-1e00-4e20-896d-459acb08e66c` | `88d0c005-6ee4-4c52-add0-f49b1b1a90c8` | `886e27567a757917705b7adef45a2c2621bf4bf7` |
| I050 and DOC-08: epsilon normalization | `cfd3fa07-a9f1-4ad0-b4e1-ab40bd2645b5` (1) | `b3be91c3-dd4e-4ac1-af23-5adcb891a55a` | Reviewer 1546, approve: `8f04739c-728b-4391-a9b3-e0fc7b665a67` | `a88ee1f5-42b1-4bbc-92c7-55e405cad399` | `4ab35fd7cc442c437d97a7e9a247b902533aa199` |
| DOC-08: FullL and AssemblyL | `ee850127-e062-4b61-81d1-9d472cee0126` (1) | `fbe00d99-2457-4134-b0ff-2d171a591c33` | Reviewer 1547, approve: `21afff0c-e022-4f01-955b-0923a319536d` | `95e56d26-7680-4c10-adbf-76a5d6f91d7f` | `4ab35fd7cc442c437d97a7e9a247b902533aa199` |
| DOC-08: GLPoleRegion | `e70861e2-26e4-4421-8ca3-1aa394092a9c` (3) | `cc06ce2d-a9d5-48ee-a333-2ebab2aac633` | Reviewer 1543, approve: `2c4cbdb8-9ab2-4270-aee1-04b5c028a0e7` | `13c5ffb3-453d-4924-81ef-c8704366c96a` | `4ab35fd7cc442c437d97a7e9a247b902533aa199` |

I001 published at `b263cfa454b11d485198ae46d8290f32435e48c6`.
I011, I034/DOC-05 and I035 share accepted integration snapshot
`4afbced190956c6e3bb82471470a91acddabf971fcdcc4cbd3c0054901959929` at
`886e27567a757917705b7adef45a2c2621bf4bf7`. The final three corrections share
snapshot `7d94b6a5406a06be154e889ef3d0870f864e6604255d424ec4f1c2afad0392f1`
at `4ab35fd7cc442c437d97a7e9a247b902533aa199`; the accepted fresh integrated
build report has SHA-256
`af997ec5514a8815548e06417a7a6f2d0cf9ae45f2c5363e4e6f854a988c5c97`.
These are build receipts, not proofs of the Prop-valued goals.

Pole-task revision 3 corrected only the declaration name to the existing
`Langlands.Global.GLPairPoleRegionStatement`. The mathematical target and Lean
bytes did not change. Its accepted statement validation is listed above.

The conditional L-constructor companion has accepted machine validation
`2cbe0552-ff24-46c7-8cd9-a2d54641958d` under `lean.definition@1` and a successful
fresh integrated build of snapshot
`6ac054fdbe21c5964c2e86871e416bb056b7459e7fe667a2f35acdc80ddd449d`.
Its frozen, published and current pair hashes agree. Its independent approval
preserves the explicit classification, exhaustion and analytic-existence inputs.

The two preliminary audit notes are also independently accepted and published:
`b065d09c-70a3-43f8-a800-1a50055ffad8`, review
`a395b363-6293-4bc2-8ccf-c785250db498`, at
`dc8cdb2866562d5f929dc912f3563a75cc16ce79`; and
`a72e6a5c-f94e-45be-9987-fa2bb02b84df`, review
`bbcf0af7-9395-4ed0-9c68-9a1ad6584383`, at
`637a0f1ab722507f1e8565d6bd8d1a9f3b00ed53`.
Their pending correction ledgers are historical and are superseded by this final
verdict update. Neither preliminary publication alone completed this audit.

GOAL-01 requires no correction. GOAL-02's superseded absence claims require no
new interface candidate; the accepted companions above supply the counterevidence.
All required corrective publications are now verified. The remaining mathematical
proof and construction obligations stay in their existing work map.

## File fingerprints at the checked snapshot

Paths are relative to `Langlands/`. Each row records the complete current SHA-256
of both files at `fb40559309dd366f4145aa31aad8c3db11b7cc07`. All 34 Lean files
in the prior 68-file audit set are unchanged. The last row adds the conditional
L-constructor pair, also checked against its accepted archive and publication.

| Module path without extension | Lean SHA-256 | Markdown SHA-256 |
| --- | --- | --- |
| `Correspondence/SupercuspidalFactorCompatibility` | `28f432e159f2756cb643fee46bc4066a828c9de2dcb2ed93641d7d56192818a5` | `63e608f7ece4670d1f4414dc382f333d724111c0ddfaa0e347676c117078775b` |
| `LocalFactor/NonabelianSystem` | `2c1af8c3021a5815ceee9c40af3abeefedf637601beec85d1711b4e7ee3f9cc8` | `c3c7e08bb74c6151296da8ca0eb14f7a21358522fe9151ba66c920489b46f1cf` |
| `LocalFactor/CommonClosure` | `b9031e072d4a5eea194baa9c0030d6d97223929cee5c5a9eb8e438c2bf697726` | `356e06adad8ad0864812b5bba61e61bbf7a7d5283597a24c0f995c3fef8e5227` |
| `ClassFieldTheory/Local/ReciprocitySystem` | `ef84a7adf56eac2b7d07d30096aaea771a526cf98649431c3e7a14ad9b314fca` | `c727e0a7d8b8389077b655504c976129943dce470f41f89e0b93e509f984122d` |
| `LocalFactor/EpsilonOneStatement` | `db0e4a6c386245e30b336bea2618efe81b9f763ee7d7a65173b48d57dada8602` | `e1de85953df377f6cffc1ebfd5320a39ff09ec7326d899ec68c86904eea95cd9` |
| `HarmonicAnalysis/Conductor` | `1780ea3172b1c84654e647efa3208d12c669a8c51a0942a1b80f4a66f84b4a53` | `ef4097816de90b81e1be2bc9b1dad6de7896a8b9fb658e122afd8876fa7faeac` |
| `LocalField/Normalization/Definitions` | `b997a64a0f59ce13d45e2b5349de9ad87466a5e2d3e16ab3f1a4ef97a048214b` | `dac7d3aeb5229c505e5271f66d7decf6c7c4404853e9f15a363b4f9401902436` |
| `LocalField/Normalization/Proof` | `4efa0826ddc069b2963ab4933716979e5bc7c5c866498047aabfbfc417071ded` | `1c3bf219eca92cd04af13c152757d83b4d92dd9787c334acec773bb51a4ad161` |
| `LocalFactor/ConductorExponentStatement` | `6f243269beccf794d5e929b6f843ea37dfe49c73f5613dc91b96293a92be6ebd` | `7bf454c4accd9cfa7d5f20b9cbc81a3b6935783d5bb6bf94b95e8f9a69ba0656` |
| `LocalFactor/EpsilonZeroStatement` | `11a5825aa1a8c79b9d0de5ccd42ded2aa67a02dbc39ba6bb4847bdcbe69a07af` | `9b9839d8e4b4e436237bceadb5924350504d13641f28d255fdcc355c0cc4de6c` |
| `LocalFactor/SpectralTwist` | `8a8b4859cf28e862c8dbdc8ea1962565f6efffe62c1bbfc427270d4d5d5d9013` | `f67a31e7ed589874a1214601dae3df5830851a10d0d5323f1c7b2c80958dc18f` |
| `Weil/Local/Assembly` | `576d8ad3c15763bdf047c2289beea60530c5d95a70963395444fd1efbd49cad8` | `6fb1c6a6e8e5a6ba9748ed021c5050bbca06589072e1ef3d26af0d850beb8b83` |
| `LocalFactor/CommonClosureSpectral` | `a769293d9df46b1e3413f2d1984461c3a16c87296da9d07af7c128e7075c06e7` | `b20ddd980003219141abe494375f99f53f95222399eba65c9458683e72308396` |
| `Representation/RankinSelberg/PairEpsilonNormalizationStatement` | `e0ee82edcef466cd49ef05d29b49d24a88214b8e26f45bd471509b96d3e4414b` | `01d13d13cd4981e18a2f256e573f70401e894d7ccee3f9e20c907e39c83478f7` |
| `Representation/Whittaker/DualTransform` | `a82f7ab37f3c534eca18afec42d3692158546b18da8df2f3927cc27721d510b7` | `4e6c51db110a4d4843bf25084975c8c3806896c8a45f4c7a36ef72dc49f38fce` |
| `Representation/RankinSelberg/LocalFactor` | `af7cf52dcf557bfffba6dcd468e1f4b2c82dd5632d8c0075b265a5fe2a587083` | `4ee2f81dd1816154d15cd3a345b460f61e29ea984341a4952fe2a3b569d2eeb2` |
| `Representation/RankinSelberg/LanglandsFactors` | `1a3252c080fdfd68872233a1274c5a207cd0cba60556e14e16c238f55d8fae99` | `d61bcf57ed676819004db8b7d183ab10078891467b20f5004facf7a17f033dc3` |
| `Representation/RankinSelberg/LanglandsFactorDescent` | `b8aacee1e85de05c440a124bc2a30ad4f3e087f836071cde6da462815a536a99` | `6f8f2ab41bca051d647f92213dd0a2bbf7b5325e6ef0ee4f572b9273bd9c3edf` |
| `Representation/RankinSelberg/LanglandsQuotientLFactorStatement` | `5096be373e6cb9c13b64c5e0ef0276de08af0efd54d67630fc7695edbaf8e404` | `6b16f7a72b7ffb6be2eaed3cd2db28f6dca7fc008a01792e64663d1542cd9c6f` |
| `Representation/RankinSelberg/LanglandsGammaFactor` | `14d2b65d08a411dc17af70a9f77d65c02049d4c26a91c1aef93737545ef1afaa` | `1c274c1c70421a42929eafa71a1ae2408562f47d80d604376f63efa9733448af` |
| `LocalFactor/ResidueReflection` | `4b2dac7f7b40cf463c64c14ad034320b6aa954ac60e5276edd18ca9002154545` | `7a601ff1ecdbd81b8080427656024bfa164c9a5632f2bbea65173b759d52bd54` |
| `Correspondence/SupercuspidalSpecification` | `b40cc87cb82b47750afc3d726affa9ad59fd3973359b46ace5a150818bcb2423` | `5ceea3448e699c3ee889f1945a6213865cad14d35c30568262ecc800ebb70656` |
| `Correspondence/AssemblyRelation` | `e263ca93e58bf1db78ad789eb4d52068da3c5690540def78137b02f5cc0a833e` | `0521dd18a2820a1bd78e3dcd67764c5c110986d77ac5fa767af428a734d3e363` |
| `Correspondence/AssemblyLFactorStatement` | `ff36c9f9cb367851ea4bfe8c90e36f82f1870c5b859ab26c8f69f073c2bbfe99` | `f100f9e187805ab45324590bf38087930dfa3c70a6b54a8a3b8ec9ec84a68752` |
| `Correspondence/Domains` | `34903bc088631a1337cb5e33c5cd73e097ee83bafab2a653419c97af8b3fe2f1` | `92d944647716a92e01c3cbb997d6bba256ef3f29a5b29fa8c99f4bbb0a24dfdb` |
| `Correspondence/OperationCompatibility` | `6d2b6cb9b1eed98b540da3960fd269f7cc0f74e7d222dabbe303dfb2982f0e15` | `f7cfcd49e6d0eb32629fd5d409cacb78cd796a7b88551a3e0da7b809be25ea72` |
| `Correspondence/UnramifiedNormalization` | `0e9c50c34985391524280dea47eb24e19d46660e3999262a89e6007827fa89bd` | `135569540a9dc32aaaf78682e2496a3c3e0615c4a06307f89e67b98dc5b6d04b` |
| `Correspondence/ArithmeticFactors` | `5ae9d179ff86c24824a038ab1d87a3af614c565e03a2b1c78b239b32501250fa` | `27b25df19e25a313153795a9f19a71693f4c0e99c922a49a091b68ffece0bfe7` |
| `Correspondence/FullLFactorCompatibility` | `a4dafdb6fd296bafa394e60c92156b97dd44d8d71891a9b07bb48d91d7a48ce4` | `e155404caf84e7ad7f64eb6cb004ade665d09e3ecf94787998a9d161d4e79b05` |
| `Correspondence/FullFactorCompatibility` | `99251af7fcc2c2174d15df3d7724fa066e57c8623e70a747779a0e76dea631fc` | `4485a7cc212e2335ae4acd2368abc0c8e7e0237300fe63c70fb57d456e3f7b84` |
| `Correspondence/FullSpecification` | `c47b7d95881fdd1fe1aa1da030eab43614f5da5996a864735ecd5c4fa1ee10eb` | `15263e32729bc10e61a13169212f287672cb88498e493a8485c50854ce77a8cb` |
| `Correspondence/AssemblyTheorems` | `2691d0f6bfb71e205f71ef0f62a34d3ea8e6f7417f1214232972f94c0ad94bec` | `7957e9535e23cf0007e2c9ff13110c7d4c2475f81e1a80e8f5d3478bf8417c1e` |
| `Global/Factors/GLPoleRegionStatement` | `3b1f8b980a4dca255c3116ca6ed7cd7ecdc5f6c24a6b927fe34530b01bbaf297` | `7a429f77c796d8f3f9379d009154a2a8c52b5c41666675295c7a8041e722c72f` |
| `Correspondence/AutomorphicPairFactors` | `c471f183e5de79ce9f4fbbc0bd1d9045593f1f9b932f30d31299bb637ede1c4f` | `258298e90a25b9e6185fd3885f28b72851dddb8dc55f48db37da30ec00976385` |
| `Representation/RankinSelberg/LanglandsLFactor` | `ce1e0b194bb49abc700f6a6c085cb24cac7a349a268835e2cb953a2d18aa18c4` | `0500699b543e746a2a8e857911511b227eaa26aec6b23451ea2c11fdc4a1aa4f` |

## Historical fingerprints and intervening documentation changes

The initial 33 pairs were fingerprinted at
`aee7fdb7f6d4283cce4db9035fd9478c923d4926` and rechecked byte-identical at
`9ff0d4f8edaf10dd32d87468c3045da6ec3ee5c6`; the class-adapter pair was added
at the latter snapshot. Their historical Lean hashes and all unlisted Markdown
hashes equal the current table. The nine changed historical Markdown hashes are
preserved here; their replacements are in the current table.

| Markdown path | Historical SHA-256 |
| --- | --- |
| `Correspondence/SupercuspidalFactorCompatibility.md` | `18e7272760c9c3ba64d3f728efe65a8c48b85bf0fa8c21982d196df4fca05453` |
| `LocalFactor/EpsilonOneStatement.md` | `eb67602b4b442e746d37e06401fdf58b80bc0ea00ad9a2c7aae7ce28b10ee1b6` |
| `LocalFactor/ConductorExponentStatement.md` | `ca34e7d40625dd83724894001b0a0b7c42247fc5b321ce05b24d5ade0b12935d` |
| `LocalFactor/SpectralTwist.md` | `02322d8586bfdd0eb79b55e3dfdbcf6486a5bf15eee12ee7b8ff8cfc76ec21a8` |
| `Representation/RankinSelberg/PairEpsilonNormalizationStatement.md` | `b6b618b93e45ea2b1c80ae1adb379f98267df33a6e30114cb7ceebd02fb024a0` |
| `Representation/RankinSelberg/LocalFactor.md` | `92e0b22fc59e1cb22480bbd944e8e85f4aff47b4b115b84c52012e1c011696c9` |
| `Correspondence/AssemblyLFactorStatement.md` | `9c4171e4ac5cb69093c7f0c45fe7cfcd2716bd71ded47023745d6aa9a99ba999` |
| `Correspondence/FullLFactorCompatibility.md` | `1e0a191ead60d12cb735cbcc3e3abc83449b28f407d0e23423a616f472bbb57d` |
| `Global/Factors/GLPoleRegionStatement.md` | `b75dd24111bf2097435bcc2d75865b8e5ea2cb97c3550a4177fef65683dffb4b` |

Eight of these changes are the assigned documents repaired by the seven
correction candidates. The ninth, `RankinSelberg/LocalFactor.md`, is the sibling
quotient-Haar status update. Its Lean hash is unchanged, including
`dualFunction_mem_whittakerSet`. The availability claim was checked against
complete `UnipotentQuotient` and `QuotientHaarExistence` pairs and the exact
`QuotientHaarExistenceStatement`. The definition companion
`eb738941-1de1-4153-bc1d-5bc7a0833dbd` was independently approved in review
`57d6426e-673e-469f-b46f-71da94069e4d`, validated by
`0ddd80de-5108-4207-910b-98a519121b77`, and published at
`3afe6f3ba5efc4d00cccb18dba321ef341bbaf68`.
The proof `7242bb53-8416-495f-ae65-a8b1ca741775` was independently approved in
review `126b1e95-48f6-4539-ac3a-751fe7adc8b7`, accepted with Lake-build and
exact-target validation `75a2e2f2-254e-4bdf-ac84-1f32121d27a6`, and published at
`4897b8b0eeea4fd4761194eb8fe4c2103d02aae4`. These companions establish the stated
fixed-normalization quotient-measure availability; they do not prove the
remaining Rankin–Selberg analytic assertions. This audit uses that evidence only
to account for the intervening prose change.
