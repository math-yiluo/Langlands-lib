# NYLL public port: declaration partition and dependency routing

Worker 25, 25 October 2026. This note routes the verified NYLL import union into
small definition, statement and proof work. It does not publish the external
mathematics. The first three focused tasks have been published; the remaining
source units have explicit conservative prerequisites and unresolved semantic
work. Their proposed names are reservations in this plan, not Library declarations.

The [complete inventory](nyll-public-port/index.md) covers **422 modules and
7,340 source declaration commands**, including unchanged dependencies. Each
source command has a stable unit ID, exact pinned source path and start line,
source spelling, proposed adapted name, phase and incoming scheduling
dependencies. The [routing record](nyll-public-port/routing.md) identifies actual
child tasks, downstream owners and missing bridges. The
[generation and verification record](nyll-public-port/verification.md) explains
the inventory's reproducible checks and its lexical limits.

## 1. Scope, sources and evidence

The source is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
Every appendix source path is relative to that root and links to its readable
file. The source registrations are:

| Registration | Content fingerprint |
| --- | --- |
| `external-lean-reuse-snapshots-2026-10-21` | `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01` |
| `nyll-classfieldtheory-fbd320cd-supplement` | `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330` |

The [source audit](nyll-finite-local-reciprocity-audit.md) and
[bounded feasibility report](nyll-port-feasibility.md) supply the earlier
source/signature comparisons and build evidence. The latter was accepted as note
`ec85353d-df58-4fd6-a2e3-c9bc13221c39` and published at Library
`85f8418871da64b24ce5842668f010b12822eed1`. That accepted report did not accept
the 422-module union. Its immutable
[evidence index](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/INDEX.md)
contains the six manifests, patch10 and terminal check records. This partition
reuses them; it does not repeat that build or claim a smaller checked closure.

The approved environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`,
Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Upstream used Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. All future checks use the
project Lean service. No external repository is installed by this note.

The host comparison uses the Library checkout
`da90f21ba20b6d762325ec051bd63406a7c3a3cf` and actual declarations named
below. Source files were checked against all 422 manifest hashes. No matching
NYLL erratum was found in the project errata lookup during this planning work.
The original-source reading behind specific route decisions is recorded in
the verification page; most source units still need semantic reading.

## 2. Architecture and retained mathematical boundary

External support uses `Langlands.NYLL`. Host adapters and targets use
`Langlands.LocalClassField.NYLL`, under
`Langlands/ClassFieldTheory/Local/NYLL/`. This is the architecture authorized
by parent task `b853faaf-14e1-4055-8ab6-16526483e9ba` revision 1 and coordinated
by Worker 0. Worker 21 confirmed that the existing finite construction and its
cohomological ownership boundary remain unchanged.

One named family, adapted from
`LocalClassFieldTheory.abelianLocalArtinMap`, must supply quotient evaluation,
restriction, norm/transfer, unramified and ramified normalization, inertia and
universe transport. It is not permissible to assemble unrelated existential
maps. Preserve the actual range of `Units.map (Algebra.norm F)`, the quotient
topology and actual Galois groups. The host finite reciprocity Props keep every
prime, independent field universes and arbitrary supplied `TF` and `TE`;
the source's `Type` results are intermediate.

Class formation, the simultaneous invariant family, relative fundamental
classes, genuine cup/transfer, ordinary-cochain/Tate comparison and absolute
corestriction remain with their existing owners. NYLL's internal class-field
axiom and internal class-formation proof do not discharge those host targets.
Equality with `geometricReciprocityOfCup` would need a separate comparison.
This plan has no Weil, common-closure or coherent Weil-system conclusion.

Norm and scalar inclusion have opposite directions. To obtain the host transfer
formula, specialize the source norm square to a tower and then use the norm of
an included scalar, which is the degree power. Geometric normalization concerns
the inverse automorphism: the required valuation comparison is
`valuationMap (Additive.ofMul a) = - TF.ord a`. Thus a host element of order one
requires the source valuation-one formula at its inverse. These are obligations,
not consequences of compiling the source.

## 3. Exhaustive partition and dependency rules

The inventory order is the original dependency order of the first manifest,
followed by previously unseen modules of each subsequent manifest:

| Phase | Original root module, after `Nyll.` | Root ID | Own closure | New modules | New commands |
| --- | --- | --- | ---: | ---: | ---: |
| 1 | `ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.NormResidue` | M258 | 258 | 258 | 5,384 |
| 2 | `ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GeneralTowerNaturality` | M262 | 262 | 4 | 32 |
| 3 | `ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedNormalization` | M269 | 265 | 7 | 117 |
| 4 | `ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.NormRestriction` | M288 | 280 | 19 | 155 |
| 5 | `ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.FiniteAbelian` | M420 | 402 | 132 | 1,640 |
| 6 | `ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ShrinkTransport` | M422 | 33 | 2 | 12 |

“Own closure” is not a cumulative count: for example, the 280-module
NormRestriction closure is not all 288 modules listed by the end of phase 4.
The six-root union is exactly 422. Rewalking the recorded original imports
reproduces each manifest's module set, so every selected root is reachable in
the schedule, including its unchanged dependencies.

An ID such as `M128.001` denotes one **source declaration command**, not a
whole module. It is normally a singleton public work boundary. Only the
explicit Q1 and Q2 bundles below group several tightly related commands.
Structure fields, generated projections, recursors and generated instance names
travel with the owning declaration; the lexical count does not count these
generated constants separately. Local instances and private declarations are
included, since their mathematical work cannot be discarded by renaming.

Each module header lists its exact original imports. For scheduling, the first
source unit depends on completion of every imported NYLL module; each later
source unit also depends on completion of the preceding source unit. Completion
of a module is completion of its last unit and that chain. External imports
are listed by actual module name. These are deliberately conservative,
acyclic **scheduling edges**, not kernel dependencies or proposed minimal
imports. In particular, an early definition should not be delayed by an
irrelevant earlier theorem once a focused successful check establishes a
smaller dependency set. No such reduction is asserted by the inventory.

For the three published children, their explicit original Mathlib-only imports
and selected declaration boundaries supersede the conservative full-module
schedule. This identifies a task's proposed inputs; the child still must
compile its adapted unit. It is not a new successful reduced-closure claim.

### Names and separate phases

For a nonprivate, nonlocal named source declaration `q`, the prospective
definition or proof name is `Langlands.NYLL.q`. Preserve the distinction between
source namespaces `ClassFieldTheory` and `LocalClassFieldTheory`. A source
theorem/lemma receives a separate Prop-valued `def` or `abbrev`
`Langlands.NYLL.qStatement`; its later proof has the adapted source name.
Q3 instead reserves the explicit name `Langlands.NYLL.LocalFieldTheory.ValuedTopologyStatement`.
These target names do not yet specify the full types: each future statement
must retain all source universe/section parameters and hypotheses, inspected
from the source and then checked by the Lean service.

For private/local/anonymous source commands, the appendix reserves
`Langlands.NYLL.PortInternal.Mxxx.dyyy`. A theorem's target adds `Statement`.
This is a fresh implementation name, not a claim about the original mangled
private kernel name. Review whether it should remain private within a small
unit or become a separately reviewed helper. No anonymous instance is assigned
an invented original Lean name.

The suggested support module stem replaces the initial `Nyll/` in the source
path with `Langlands/NYLL/`. Under it, a singleton may use
`Uyyy/Definitions.lean`, `Uyyy/Statements.lean` and `Uyyy/Proofs.lean`.
The three child contracts specify shorter concrete paths. These are alternative
layouts for the same small units, not a direction to create three empty files
per command. Every actual Lean file needs its own complete same-stem Markdown.

| Row code | Required route before completion |
| --- | --- |
| `S→P` | Independently publish the exact Prop target, then create a `lean.proof@1` task against that Library target and publish its proof. |
| `D` | Inspect and publish the small data definition with its constructor laws and source map; do not add unrelated result families. |
| `R` | Reuse a verified existing definition/instance by Lean name and document the source correspondence; do not duplicate it. |
| `Prop?` | A source `def`/`abbrev` lexically appears to return `Prop`; inspect the full type and classify it as a predicate definition or a statement target. The question mark is not semantic certification. |
| `bundle?`, `instance?`, `data?` | Read the entire declaration and its context. Separate a substantive existence, equivalence or equation theorem before constructing data if needed. Reuse canonical instances or install them locally/scoped; no conflicting global instance. |

A `def` containing `by` is not automatically a trivial definition. For example,
the three `TateCohomology.iso*` declarations in M003 construct homological
isomorphisms. Each needs a reviewed construction route and may need antecedent
existence/equation targets before its data definition. Likewise an individual
long theorem may need further helper targets; its singleton row is a precise
place to split, not a guarantee that its proof is already suitably small.

`U.END` means that the chosen route has been resolved with accepted published
mathematics or verified reuse. It is only a planning marker. Neither the
inventory nor a checked build resolves it.

### Blockers and next routing responsibility

Every row inherits its module's license, patch, imports and family below.
Unless its explicit route says otherwise, no equivalent Library/Mathlib result
has yet been established. “None established” means reuse is unresolved, not
that Mathlib lacks a result.

| Code | Exact remaining work | Next responsible coordinator |
| --- | --- | --- |
| Q1–Q3 | Existing focused task, identified below; wait for its actual candidate, acceptance and publication. | Child executor; Worker 25 tracks support, Worker 0 tracks downstream routing. |
| B0 | Read full theorem context/body; search semantic replacements; validate the Prop target's dependencies; split long proof obligations as needed. | Worker 25 publishes the next focused support unit, consulting the family contact. No proof task until target publication. |
| B1 | The source command has not been semantically classified as data, predicate, instance or a construction requiring prior proof. Resolve this before publishing its contract. | Worker 25; specialist contact by family. |
| B2 | Source boundary and intended data meaning inspected, but no focused task/candidate yet. Search active work, then publish the data unit before dependent targets. | Worker 25; valuation/unramified consumers Worker 109, principal-unit consumer Worker 106. |
| B3 | Exact support/host signature difference identified. Decide a qualified alias or Mathlib reuse, retaining the source's generality, and check it. | Worker 25 with Worker 63; norm consumers Worker 66. |

The unclassified rows are the explicit set of mathematics **not yet semantically
routed**. Their exact paths and declaration IDs are in the appendices; the
status is per row, not hidden behind the nine patched files. Most of the port
remains in this set. The route can be advanced one bounded unit at a time
without requiring a new repository-wide feasibility study.

| Family | Module count | Scope and first unresolved semantic issue | Coordination boundary |
| --- | ---: | --- | --- |
| G | 1 | Separable-closure embeddings and continuous automorphism conjugation, M001. Source embeddings include number-field specializations; retain only checked necessary units. | Worker 25; Worker 63 consumes finite realization. |
| C | 42 | Cyclic cohomology, profinite integers and local class-formation bridges. M002 universe transport, M003 homological isomorphisms, M007 topological generation, M113 low-degree data and M144 normal-basis lattice all need separate semantic routes. | Worker 25 coordinates with Worker 45 for Tate comparisons and Workers 42/49 for class formation. These contacts do not transfer ownership of their host targets. |
| A | 76 | Abstract degree, norm, Frobenius and reciprocity construction. M010's 140 and M065's 35 commands are individual units; M072's internal cohomology data/axiom must be distinguished from host class formation. | Worker 25; consult existing construction owners before replacement claims. |
| V | 21 | Chosen discrete valuations, completion, extension, integral closure and finite extension uniqueness. Q2 handles only M103's initial data; it does not prove the later DVR/integral-closure laws. | Worker 25; Worker 109 consumes relative integer structure. |
| H | 47 | Hensel factorization and unique extension; absolute-value and exponential-valuation infrastructure. M170–M183 include iteration and limits, M190 completeness, M196 uniqueness. Mathematical replacement by Mathlib is unresolved. | Worker 25 must split at the recorded declarations before publishing; no whole Hensel-module candidate. |
| F | 60 | Norms, principal units, finite residue fields, valuations and local topology. M123's 199 commands and M132's 103 commands require their recorded individual data/target/proof phases. | Worker 25; Workers 63, 66, 109 and 106 consume the respective host bridges. |
| R | 57 | Finite/absolute ramification, Herbrand quotient/tower formulas and actual residue kernels. M232 has 167 commands; M327 and M328 connect the chosen valuation to actual local ramification. | Worker 25; Worker 106 consumes zero-depth inertia, Worker 70 ramified normalization. |
| N | 71 | Finite local reciprocity realization, topological Artin map, towers and normalization; later filtered/existence modules. M254→M257→M258 is the named-map interface. | Worker 25 routes support; host consumers are listed in the routing record. |
| L | 45 | Lubin–Tate series, primitive torsion, finite automorphisms, ramification and standard norm subgroups. No replacement route has yet removed these dependencies. | Worker 25 routes individual units; Worker 106 consumes the resulting filtered theorem. |
| U | 2 | Smallness and shrink transport. The source smallness proof precedes transported local-field data and topology; host coherent model assembly is separate. | Worker 25 handles M421–M422 support; Worker 82 owns host universe transport. |

## 4. First published children and concrete reuse decisions

These are published **tasks**, not accepted mathematical results.

| Unit | Exact source scope | Child task | Intended result and inputs |
| --- | --- | --- | --- |
| Q1 | M005.001–002, `Nyll/GaloisCohomology/GroupTheory/QuotientTower.lean`, lines 30–60 | `240769f1-98bd-4ae3-aa5f-9c73aa599500` | `Langlands.NYLL.Subgroup.quotientSubgroupOfEquiv` and `.quotientTowerEquiv`; only source import `Mathlib.GroupTheory.Index`. These are equivalences of types of cosets; no normality or group-isomorphism assertion. |
| Q2 | M103.002–010, `Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Basic.lean`, lines 37–87 | `d0e1c313-787b-4a52-8f88-bc3418b30614` | `Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF` and its valuation-subring/maximal-ideal/residue-field/residue-map aliases, preserving independent field/value-group universes. Canonical instance aliases are reused, not duplicated. Excludes line 28 and all theorems from line 90. |
| Q3 | M111.001, `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuedTopology.lean`, lines 27–33 | `a92dbd56-a3cd-49cc-95d2-fe800c0c82cc` | `Langlands.NYLL.LocalFieldTheory.ValuedTopologyStatement`, from `Field F`, ordered value group, `MulArchimedean`, supplied `Valued F Γ` and nontrivial valuation to `IsValuativeTopology F` after `ValuativeRel.ofValuation`. Only source import `Mathlib.Topology.Algebra.Valued.ValuativeRel`. No proof child yet. |

Task and current Library/Mathlib exact-name searches found no duplicates of
these three selected units before publication. The child contracts still
require semantic reuse searches and focused compilation. The initial candidates
are bounded by source declarations, not by the 258-module baseline.

| Source units / host use | Actual reusable names | Qualification or missing comparison |
| --- | --- | --- |
| Q1 quotient constructions | `Subgroup.subgroupOfEquivOfLe`, `Subgroup.quotientEquivProdOfLE`, `Subgroup.subgroupOf_mono`, `Quotient.map'`, `Equiv.prodCongr` | These are the construction tools read in the original. Preserve quotient relations without inventing normality. |
| Q2 residue data | `Valuation.valuationSubring`, `IsLocalRing.maximalIdeal`, `IsLocalRing.ResidueField`, `IsLocalRing.residue` | Use their canonical ring/local-ring/domain/field structures. No separate global copies of the source's four bookkeeping instances. |
| Q3 valuative topology | `IsValuativeTopology.of_zero`, `ValuativeRel.ValueGroupWithZero.orderMonoidIso`, `ValuativeRel.valuation_lt_symm_orderMonoidIso`, `ValuativeRel.restrict_lt_orderMonoidIso` | Tools for the source neighborhood comparison. The existing construction of `Valued` from valuative topology is the converse direction, not this theorem. |
| M092.002, M093.001–002; finite-extension host quotient | `Units.map`, `Algebra.norm`; `Langlands.LocalClassField.normUnits`, `.normSubgroup`, `.NormQuotient` | Source `normUnits` has no finite-dimensional premise, whereas the host definition has one. Reuse at finite-extension applications; preserve general support with a qualified alias/Mathlib expression where needed. No global signature identification. |
| Host quotient/evaluation and towers | `Langlands.LocalClassField.finiteNormQuotientMap`, `.finiteNormResidueEquiv`, `.normQuotientTowerProjection`, `.normQuotientTowerNorm` | First two are conditional constructions, not reciprocity proofs. Their closure-indexed extension is not automatically a standalone `E.Carrier`. Worker 63's child constructs directly on the latter and must prove the named-map evaluation. |
| M138 integer/residue maps, host supplied data | `Langlands.PadicField.TopologicalData.relativeIntegerMap`, `.relativeResidueMap`, `.relativeIntegerAlgebra`, `.relativeResidueAlgebra`, `.relativeIntegerFieldAlgebra`, `.relativeIntegerFieldTower`, `.relativeIntegerTower`, `.relativeResidueTower` | Existing `RelativeIntegers` already constructs maps and tower/comparison laws for arbitrary supplied data. Reuse it; the NYLL `HasExtension`, integral-closure and finite-module bridges remain separate obligations. |
| M128/M134 valuation sign; M271 normalized valuation | `IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt`; `Langlands.PadicField.TopologicalData.discreteValuation`, `.ord` | The host `ord` is negative `WithZero.log`. Source `v` and `valuationMap` must be compared under the exact supplied instances; the source exponent and host order cannot be equated with the same sign. |
| Canonical transport portion of host assembly | `Langlands.LocalClassField.extensionIntermediatePadicEquiv`, `.extensionIntermediateUnitsEquiv`, `.extensionIntermediateResidueEquiv`, `.extensionIntermediate_ord`, `.extensionIntermediate_discreteValuation`; `Langlands.PadicField.CanonicalTransport.residueEquiv`, `.ord_map`, `.discreteValuation_map` | Existing image-field and canonical-data transport. It stays in the base universe and is not a Type 0 model or a theorem for arbitrary supplied data without further comparison. |
| Geometric residue normalization | `Langlands.LocalClassField.ResidueNormalization.geometricFrobeniusClass`, `.HasGeometricResidueAction`, `.hasGeometricResidueAction_iff_inverse_power` | Preserve the inverse action and actual residue cardinality. This interface does not construct the source Artin map. |
| Structural inertia-fixed-field comparison | `Langlands.PadicField.InertiaFixedFieldUnramifiedExhaustion` | Its statement uses canonical absolute ramification-index equality for finite intermediate fields. It is not definitionally the NYLL `IsUnramifiedValuedExtension` class; the ramified bridge owners must establish the relative comparison. |
| M003 Tate comparison and M114 cohomology bridge | Actual Mathlib homology is used by source `TateCohomology.isoZeroBoundary`, `.isoFiniteCyclicZero`, `.isoFiniteCyclicNegOne` | No host replacement is established here. Compare with Worker 45's work before publishing duplicate comparisons; retain genuine cohomology, not an assumed reciprocity package. |

No reuse entry removes a source module from the verified closure without a
focused successful build of the alternative. The rest of the inventory inherits
“replacement unresolved” and the family-specific next action.

## 5. Root-facing units and exact later blockers

The following are selected interfaces within the exhaustive singleton schedule.
The full source paths, all helper names and import prerequisites are in the
appendices. Prefix every source name here with `Langlands.NYLL` when porting;
the source names remain visible to avoid hiding namespace distinctions.

| Support boundary | Definition phase | Separate target/proof phase | Remaining prerequisite and consumer |
| --- | --- | --- | --- |
| M007 topological generation | `ClassFormation.TopologicallyGenerates`, `closedSubgroupGenerated`, `closedSubgroupGeneratedMap` | `topologicallyGenerates_iff_dense`, then generated-density and image/quotient laws, each at its own row | Semantic reuse and exact imports; Worker 25 with Worker 45. |
| M128/M134 normalized unit valuation | M128.001 `LocalFieldTheory.IsNonarchimedeanLocalField.v`; M134.001–002 `valuationUnitsMulHom`, `valuationMap` | `v` laws and `valuationMap` comparison precede the host `-TF.ord` bridge | B2: no task or candidate yet. Worker 25 routes data, Worker 109 consumes sign comparison. Do not bring in all 44 M134 commands as one unit. |
| M131 principal units | `LocalFieldTheory.principalUnits` at line 24 | `mem_principalUnits_iff`, `principalUnits_zero` at line 73, then order laws and later quotient units | B2 data; M131.004 states `principalUnits K 0 = ⊤` for actual integer-ring units. Worker 106 needs it for inertia. |
| M161 actual unramified extension | `LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension` at lines 36–44, a Prop-valued class encoding actual ideal ramification index one | Separate residue-degree, residue-action and Frobenius comparison targets | B2 class/predicate design; preserve `Valuation.HasExtension` and `Module.Finite 𝒪[K] 𝒪[L]`. Worker 109 coordinates the supplied-data bridge; Worker 70 uses the ramified subextension. |
| M254→M257→M258 named Artin map | `localArtinMonoidHom`, continuous `localArtinMap`, `abelianLocalArtinMonoidHom`, `topologicalAbelianizationEquivSelf`, `abelianLocalArtinMap` | `abelianLocalArtinMap_toMonoidHom`, `_surjective`, `_ker`; source M258.006–008 | All preceding abstract/class-formation/local-field support, plus topological openness/discreteness in M257. Worker 63's host quotient child waits on these exact names/properties. |
| M259–M262 restriction increment | Only the recorded intermediate-field and private tower data, each separately | M262.010–014 concrete restriction, algebraic-map restriction and `autCongr`; M262.015 `ClassFieldTheory.finiteAbelianLocalArtinMap_restrict_tower` | Named map and inherited support; Worker 29 adapts to the host tower and actual Galois restriction. |
| M263–M269 unramified increment | M264 arithmetic Frobenius and M268 unramified comparison maps, with their prior equivalences proved as required | M269.020–023: `abelianLocalArtinMonoidHom_eq_frobenius_zpow`; `ClassFieldTheory.finiteAbelianLocalArtinMap_eq_frobenius_zpow`, `_uniformizer`, `_inverseUniformizer_residue_pow` | Actual unramified class, supplied integer structure, `valuationMap` sign and residue comparison. Worker 109 consumes these. |
| M270–M288 norm increment | Normalized valuation/fixed-field data and embedded norm-quotient comparisons, all separate | M288.001–004: `AmbientEmbeddedFixedFieldPresentation.quotientRestriction`, `.fixedFieldNormResidueTransport`, `ambientEmbeddedNormResidueElement_norm_restriction`, `abelianLocalArtinMonoidHom_norm_restriction` | Four-field/source-scalar identification and host tower specialization. Worker 66 derives norm/transfer; the source theorem at line 686 is not one short wrapper proof. |
| M327/M328 actual zero-depth inertia | `RamificationTheory.LocalField.localLowerRamificationGroup`, `.localUpperRamificationGroup` and actual residue-action homomorphism | M328.001–002 `localLowerRamificationGroup_zero_eq_residue_ker`, `localUpperRamificationGroup_zero_eq_residue_ker` | Unique valuation extension, actual integer-ring identification, `IsIntegralClosure` and `Module.Finite`; Worker 106 consumes actual kernel equality. |
| M289–M420 filtered increment | Filtration data, M292 `artinPrincipalUnitGroup`, standard extension and Lubin–Tate data at their individual boundaries | M420.001 `LocalClassFieldTheory.finiteAbelian_filteredLocalReciprocity` and its earlier restriction/descent targets | Standard Lubin–Tate dominating extension, fixed-field descent and `AlgEquiv.autCongr`. Worker 106 specializes at zero and combines M131/M328. Other M420 conductor/tame corollaries remain separate rows. |
| M421–M422 smallness/transport | After M421 smallness: `shrinkLocalFieldValuation`, `shrinkLocalFieldValuativeRel` | `nonarchimedeanLocalField_small`; shrink compactness/nontriviality/topological-add-group/valuative-topology/local-field targets; finally `hasExtension_comap_ringEquivs`, `hasExtension_of_isEquiv` | Worker 25 routes external support; Worker 82 supplies coherent host Type 0 models and all transport compatibilities. Generic final two transport targets have no syntactic NYLL constants, but their focused import reduction has not been checked. |

For the unramified root at M269.021–023 the explicit source scope is
`K L : Type`, fields and local-field certificates, `ValuativeRel` on both,
`TopologicalSpace K`, `UniformSpace L`, `IsUniformAddGroup L`,
`Algebra K L`, `FiniteDimensional K L`, `IsAbelianGalois K L`,
`Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)`
and the actual unramified valued-extension class. The class itself uses the
finite integer-module structure; the source has installed it through its
preceding local theory. The host bridge must establish the matching supplied
structures. Neither this table nor a class instance may hide that obligation.

For the inertia route, requesting only `t = 0` does not remove the 132-module
increment of the verified general filtered theorem. A shorter proof is a
possible future optimization, requiring its own mathematical argument and
successful focused check. The existing proof passes through standard
Lubin–Tate domination, composita and fixed-field transport.

For universe transport, preserve the coherent algebra square, norms, residue
maps, topologies and conjugation of actual Galois groups. The source
`hasExtension_comap_ringEquivs` retains four independent field universes and
two ordered value groups. `hasExtension_of_isEquiv` even works with
`CommRing F`, `Ring G` and ordered commutative monoids with zero, so a field-only
restatement would lose source generality. Smallness alone is not host assembly.

## 6. Compatibility and attribution inherited by every unit

All 422 original files retain the same upstream author/license header:
copyright 2026 Naganori Yamaguchi; Apache-2.0; authors Naganori Yamaguchi
(assisted by OpenAI Codex). Retain the original header and applicable `LICENSE`,
`NOTICE` and third-party attributions in each actual public subset; record
namespace/import and proof modifications explicitly. The source license and
notice hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The feasibility inventory found no intersection of these selected files with
the root NOTICE's 926 named Lean paths or the five third-party source tables'
908 named paths. This scoped finding does not authorize dropping NOTICE or
ignoring attribution in newly imported material.

The final cumulative
[patch10](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/patches/patch-10.diff.md)
has payload SHA-256
`385b2353d0b3a0942433de5adfa4ab948687e70a5f33790284973b584e52421b`.
The following module-level flags are inherited by each row in that module;
they mean “inspect this diff when extracting the row,” not “every declaration
was edited.”

| Flag | Module | Required compatibility consideration |
| --- | --- | --- |
| P1 | M023 `KummerDelta` | Replace missing `AddMonoidHom.ofClass` by `AddMonoidHomClass.toAddMonoidHom wp.hom`; preserve the chosen module structure. |
| P2 | M191 `HenselianFinite` | Replace missing `IsConcreteLE.le_iff` by the explicit ideal-containment `change` used in patch10. |
| P3 | M247 `ValuedAdicComplete` | Explicit `(MonoidWithZeroHom.ofClass val).ValueGroup₀` and local `let` witness for `MulArchimedean`. |
| P4 | M271 `NormalizedIntegerValuation` | Explicit hom and monotonicity for `Valuation.map`; explicit preimage calculation for surjectivity. Preserve evaluation formula. |
| P5 | M327 ramification `LocalField/Core` | Older `MonoidHom.coe_coe` replaces `MonoidHom.coe_ofClass`. |
| P6 | M379 `CyclicValueGroup` | Explicit `MonoidWithZeroHom.ofClass v` in value-group type and embedding. |
| P7 | M385 `CompleteRangeRestriction` | Remove unavailable `Valuation.ofClass_eq_toMonoidWithZeroHom` rewrite. |
| P8 | M386 `UniformizerIntegerValuation` | Explicit `MonoidWithZeroHom.ofClass F.valuation` in membership expressions. |
| P9 | M387 `RangeRestrictedTopology` | Explicit underlying valuation hom in the value-group embedding. |

All other module headers say “none in patch10.” This is a compatibility
inventory, not semantic approval of unchanged code. The original-to-adapted
map must identify any fresh edits made when isolating or namespacing a unit.
Reused patch10 changes include Worker 25 as an actual coauthor; further
contributors and reused-draft authors must also be recorded.

## 7. Publication sequence and completion boundary

Worker 25 has notified Worker 0 and the downstream owners of the first child
IDs and the intended support names. The stable routing record gives exact
task IDs for the host-side work and explicitly labels peer-reported routes.
Before creating another unit, search current tasks and Library declarations
again, because this planning snapshot does not reserve ownership forever.

For each unresolved source unit: inspect and decide semantic reuse; publish
its missing definition phase; publish the exact Prop target; only after that
target is accepted into the Library publish its proof task. A statement check
must inspect the declaration and confirm `statement_returns_prop = true`.
Proofs require independent semantic review plus the Lake/kernel/exact-target
checks and frozen dependency policy. A successful check, this note and a peer's
progress message are not substitutes for acceptance and publication.

The parent planning task completes when this accurate partition and routing
note, its appendices and README entry are independently accepted and
published. It does not wait for every mathematical child, and it does not
certify any child by completing. No candidate from this task installs the
422-module union.
