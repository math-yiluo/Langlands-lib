# Anthropic local flatness: exact 00MK feasibility and tower limits

Worker 362, 25 October 2026. This is a bounded source and Library-interface
audit, with private Lean development checks. It publishes no mathematical
port. Independent acceptance of this note does not accept the external proofs.

**Verdict: adapt the primary proof for the existing 00MK task; defer the
secondary tower proof.** The primary adaptation compiles against the pinned
project environment and specializes to the complete, unchanged
`Langlands.Algebra.LocalFlatnessCriterionStatement.{u,v,w}`. The tower
experiments fail in a Tor naturality dependency. Even a repaired tower build
would leave the general-module, universe and conclusion gaps described below.

The evidence appendix contains the [source closure, exact original root
types, name mapping, scripts, patches, and declaration/axiom output](anthropic-local-flatness-evidence/reproduction.md).
The four terminal Lean reports are retained in full:
[primary](anthropic-local-flatness-evidence/primary-report.md),
[initial tower failure](anthropic-local-flatness-evidence/tower-initial-report.md),
[failed compatibility edit](anthropic-local-flatness-evidence/tower-edit-report.md),
and [primary recheck](anthropic-local-flatness-evidence/primary-recheck-report.md).
These appendices are audit evidence, not Lean modules.

## Source, scope and attribution

The selected original is registered as
`anthropic-flt-complete-lean-source-6e837e75`, content SHA256
`a2baece9c13f309f914ac09f2d8342a17d363c8ad27e587b84337ff943ed2e1a`,
at `literature/Anthropic - Fermat's Last Theorem - complete Lean source at
6e837e75355538c7f80bab5b956861e86c4eacc2/`.
The [upstream revision](https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2)
uses Lean 4.33.1 and Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`.
The project checks use environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`,
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
The Library comparison base is
`05e9d802f08c814de1be8cfe174ad0e47a37c791`.

The textual import traversal terminates at external Lean/Mathlib imports and
counts each selected source module once per root:

| Root suffix after `Theorems.Thm_` | Modules | Lines |
| --- | ---: | ---: |
| `Module_flat_of_comap_maximalIdeal_rTensor_injective` | 3 | 851 |
| `IsLocalRing_flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map` | 5 | 1490 |
| The preceding root with `_univ` | 5 | 1498 |

The primary closure contains its theorem wrapper, its `P2M/Sol/S_...`
implementation and `P2M/Util.lean`. Each tower closure adds the corresponding
local Tor criterion wrapper and implementation. There are no `Definitions/`
modules in these closures. Their union has eleven files and 3585 lines; only
the utility is shared across the three roots. These are source-import counts,
not declaration-minimal dependency counts. Every selected proof and utility
was read. The `_univ` Tor proof normalizes to the Type-0 proof after replacing
universes; the tower variant additionally supplies explicit `.{u}` at five
uses of proposition abbreviations.

The source's `LICENSE` is Apache-2.0; `NOTICE` names Copyright 2026 Anthropic,
PBC and the third-party works. All eleven selected paths were checked against
the complete `ATTRIBUTION.md` table; none has a per-file third-party row.
This establishes absence of a listed row, not exclusive authorship:
`NOTICE` covers Mathlib generally, and `ATTRIBUTION.md` §5 explicitly limits
the attribution search, including short passages. The experimental directory
retains complete copies of `LICENSE`, `NOTICE`, and `ATTRIBUTION.md`;
adapted files add Anthropic copyright, source revision, adaptation author and
change notices. Any later extraction must preserve those notices and recheck
attribution for additional files it selects.

No source-specific errata file was found in the project or baseline Library
`notes/errata/`. The bounded current issue search read all eleven returned
issue/PR bodies and their available issue comments, registered as
`anthropic-flt-issues-2026-10-25`, SHA256
`80c46a2d0db976277b7c771e4f0d58fe79809c5365a5ac272d5af513eda5cd78`.
Issues [8](https://github.com/anthropics/fermats-last-theorem/issues/8) and
[10](https://github.com/anthropics/fermats-last-theorem/issues/10) describe
full-repository build failures; later comments report successful builds after
raising `vm.max_map_count`. PR
[11](https://github.com/anthropics/fermats-last-theorem/pull/11) describes stale
artifact selection when reusing a comparator work directory across checkouts;
its stated scope is a verification-wrapper defect. No local-flatness
correction was found in this bounded set. This audit neither reproduces those
full builds nor uses their reports as evidence for the selected proofs.

## Primary result and the exact Library specialization

The original theorem is
`Module.flat_of_comap_maximalIdeal_rTensor_injective`; its implementation is
`P2MW.S_Module_flat_of_comap_maximalIdeal_rTensor_injective.solution`.
The private namespace is `FlatnessAudit.Primary`, with nested helper
namespace `LocalFlatnessCriterionAtPrime`.

The full unapplied declaration inspection confirms three independent
universes for `R`, `S`, and `M`. Its hypotheses are commutative Noetherian
rings `R,S`, an algebra `R → S`, a local ring `S`, compatible `R/S` actions
on the additive commutative group `M`, finiteness of `M` over `S`, an ideal
`p : Ideal R`, the equality
`(IsLocalRing.maximalIdeal S).comap (algebraMap R S) = p`, and injectivity of
`p.subtype.rTensor M`. The conclusion is `Module.Flat R M`.
It does not require `R` local, a local-map instance, finiteness over `R`,
or a nonzero module. For the Library specialization, the existing local
hypotheses supply the needed equality.

The unchanged Library target is the Prop-valued definition
`Langlands.Algebra.LocalFlatnessCriterionStatement.{u,v,w}` in
`Langlands/Algebra/LocalFlatnessCriterionStatement.lean`.
Its companion Markdown identifies Stacks 00MK and explains its tensor-kernel
form. The private bridge is:

```lean
theorem FlatnessAudit.exact00MK :
    Langlands.Algebra.LocalFlatnessCriterionStatement.{u,v,w} := by
  intro R S M _ _ _ _ _ _ _ _ _ _ _ _ _ h
  exact FlatnessAudit.Primary.solution (S := S)
    (IsLocalRing.maximalIdeal R)
    (IsLocalRing.maximalIdeal_comap (algebraMap R S)) h
```

Here `IsLocalRing.maximalIdeal_comap` has exactly the required orientation,
for the actual `algebraMap R S`, using its `IsLocalHom` instance.
`p.subtype.rTensor M` is the same `LinearMap.rTensor M p.subtype` as the
target: its domain is `p ⊗[R] M`, its codomain is `R ⊗[R] M`, and it tensors
the inclusion with the identity of `M`. There is no added kernel comparison,
finiteness, nontriviality, or universe restriction in this bridge.
The original proof internally switches between left and right tensor
injectivity using `LinearMap.lTensor_inj_iff_rTensor_inj`.

The adaptation removes `P2M.Util`, renames the enclosing namespace, and
replaces each `p2m_reactivate` command by `open scoped` with the same renamed
scopes. It directly uses the solution instead of importing the theorem's
`p2m_exact_reverting` wrapper. It does not import the utility's global
attribute-reset machinery. The mathematical proof text otherwise remains
unchanged. Finite heartbeat limits remain in place.

The implemented route is:

1. Use a free cover and tensor right exactness to transfer injectivity.
   Define `TorVanish R M N` as the tensor-injectivity property for every
   short exact presentation of `N`, without importing categorical Tor.
2. Establish this property for modules killed by the chosen ideal and
   preserve it under extensions, hence under powers of the ideal.
3. Bound each ideal-tensor kernel by arbitrarily deep powers using an
   intersection/sum exact sequence and Artin–Rees.
4. Prove `M ⊗[R] a` finite over `S`, transport the power bounds to `S`,
   and apply Krull intersection there. This is precisely where finiteness
   over `S` suffices.
5. For the comapped maximal ideal, localize at its prime complement.
   Elements of the complement act invertibly on `M`; semisimplicity of the
   localized residue-field modules supplies the required splitting.

Check `9dac7498-4a33-44de-949d-e1bb2187cde6` succeeded with zero errors
and twelve style/deprecation warnings. It prints the full unapplied solution,
the exact bridge type, and both axiom lists. Each list is exactly
`[propext, Classical.choice, Quot.sound]`.
The fresh standalone recheck
`b5d6dfb1-a9b1-4f41-bfdf-65b810315a3a` also succeeded, with declaration
inspection reporting level parameters `["u","v","w"]` and the same axioms.
Its build output has no warnings; this does not establish that the source is
warning-free, since the earlier build emitted them.

Both reports explicitly say `proof_accepted: false`.
Inspection has `target_matches: false` because no proof-submission target was
requested; `statement_returns_prop: false` classifies a theorem rather than
a Prop-valued statement definition. Neither field is an exact-proof receipt.
The bridge's checked declared type establishes development feasibility
against the existing target. Independent proof review, formal exact-target
validation and publication remain necessary.

## Secondary tower result: scope and failed feasibility

The original tower root is
`IsLocalRing.flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map`,
and the second root appends `_univ`. The former has `R S S' : Type`;
the latter has all three in the same `Type u`. Both assume commutative local
rings, compatible algebras `R → S → S'`, both local homomorphisms,
and Noetherian `S,S'`. They do not assume Noetherian `R`.
With the explicitly constructed quotient algebra structure, they assert

```text
Flat R S' →
Flat (S / map(m_R)) (S' / map(m_R)) →
Flat S S'.
```

The module is `S'` itself, not a separate finite `S'`-module. Its finiteness
over itself is automatic. The solution's `localCriterion00MK_stub` is a
proved application of the imported local Tor criterion despite its name;
it is not an unproved axiom or hypothesis. The full selected closure was
read to make this distinction.

The private adaptations use `FlatnessAudit.TorZero`, `TorUniv`,
`TowerZero`, and `TowerUniv`. Initial edits remove the unused utility import,
rename namespaces, and redirect the tower's Tor-criterion import and call.
Check `f43f80d0-14e4-4b9b-8942-5975399f64d5` failed with two errors and
42 warnings. Both errors occur in the Tor dependency at
`MK00Port.ar_tor0_map_fromLeftDerivedZero_naturality`,
on the first explicit `hbr` cancellation in a composition chain.
The attempted deletion of that step also failed:
`9b300eab-7016-4613-9f4f-5f365725f4c4`, two errors and 42 warnings,
now at the subsequent `hι` composition. The same attempted edit was applied
to the corresponding tower naturality proof, but those modules were blocked
by the dependency failure. The records and both versions of every patch are
retained. The hypothesis that the step had become redundant was not verified.

There is no successful tower-root declaration inspection or axiom report,
and no tower helper is claimed to compile independently. The report's
`built_modules` field lists requested modules even on failure; it is not
evidence that each listed module built. A separate resumption recheck was
cancelled before starting after a transport timeout; its terminal service
state is retained in the reproduction appendix and supplies no Lean evidence.

The Library comparison is at the declaration level:

| Existing target | Additional obligations beyond the tower source |
| --- | --- |
| `NoetherianFiberwiseFlatnessStatement` (00MP) | A separate finite, nontrivial `S'`-module `M`, four independent universes, the tensor-product fibre action, and both `Flat R S` and `Flat S M`. The target also assumes Noetherian `R`. |
| `EssFinitePresentationFiberwiseFlatnessStatement` (00R7) | A separate finitely presented nontrivial module, independent universes, essentially finitely presented `R`-algebras in place of the source's Noetherian assumptions, and both flatness conclusions. |
| `LocalFiberwiseFlatnessStatement` (05UV) | The preceding module/universe/fibre work, the exact essentially-finite-type hypothesis on `S`, and the extra `EssFinitePresentation R S` conclusion. |
| `IdealLocalFlatnessCriterionStatement` (00ML) | An arbitrary proper ideal `I`, injectivity for `I`, and quotient flatness; the primary theorem treats the particular comapped maximal ideal and does not directly discharge this target. |

For tower reuse, an explicit scalar-compatible equivalence must identify
the source quotient rings with `S ⊗[R] ResidueField R` and its module base
change. A general finite-module argument, transport between independent
universes, and descent yielding `Flat R S` are further proof obligations.
None was attempted or established here. There is no scheme-flatness port:
replacing the project's locally-finite-type assumption by locally finite
presentation would strengthen its hypotheses.

## Reusable interfaces and a dependency-ordered implementation plan

Searches in the baseline Library and pinned Mathlib found no declaration
with the selected root names. This is a bounded source search, not a proof
that no equivalent theorem exists. Relevant existing APIs were read:

| Existing interface | Use and boundary |
| --- | --- |
| `IsLocalRing.maximalIdeal_comap`, `map_maximalIdeal_le` in `RingTheory/LocalRing/RingHom/Basic` | Exact local-map equality and its ideal-map consequence; the former is used in the checked bridge. |
| `Module.Flat.iff_lTensor_injective'`, `iff_rTensor_injective'` in `RingTheory/Flat/Tensor` | Reduce flatness to ideal inclusions; preserve the existing tensor formulation. |
| `TensorProduct.lTensor_exact`, `rTensor_exact` in `LinearAlgebra/TensorProduct/RightExactness` | Tensor right exactness, with exactness and surjectivity premises. |
| `Ideal.exists_pow_inf_eq_pow_smul`, `iInf_pow_smul_eq_bot_of_le_jacobson` in `RingTheory/Filtration` | Artin–Rees and Krull intersection, used by the primary tail over the appropriate coefficient ring. |
| `TensorProduct.AlgebraTensorModule.cancelBaseChange` in `LinearAlgebra/TensorProduct/Tower` | Scalar-compatible base-change cancellation used in the primary splitting and source tower helper. |
| `TensorProduct.quotTensorEquivQuotSMul` and `Algebra.TensorProduct.quotientTensorEquiv` | Existing module/ring quotient equivalences; still require the exact fibre and action identifications for the target. |
| `Ideal.mem_map_iff_of_surjective`, `map_eq_submodule_map` | Existing ideal-image tools underlying the tower's restriction-of-scalars helper. |
| `Module.Finite.base_change`, `Module.Finite.tensorProduct` in `RingTheory/TensorProduct/Finite` | Useful standard finiteness cases; their displayed statements alone do not give the source's mixed `S`/`R` coefficient assertion without an equivalence/transport argument. |
| `Langlands.Algebra.quotientBaseChangeComparison` | Published Library proof for canonical quotient maps when extended ideals agree. It is not the missing general fibrewise-flatness theorem. |

For an authorized future implementation, the primary proof supports these
focused units, in dependency order. Each new definition and Prop target
must be reviewed/published before its exact proof task; small helper lemmas
may be grouped with the unit that uses them.

1. **Free-cover tensor transport and the internal predicate.**
   `FreeCover`, its evaluation map, `lTensor_injective_of_cover`,
   `lTensor_injective_of_comap_cover`, `lTensor_mapRange_injective`, and
   `TorVanish`. The predicate is a presentation property, not a claimed
   identification with categorical Tor.
2. **Torsion and extensions.**
   `torVanish_of_torsion`, `torVanish_of_extension`,
   `torVanish_of_subsingleton`, and `torVanish_of_torsion_pow`.
3. **The separatedness tail.**
   `ker_le_range_of_torVanish`, `range_lTensor_inclusion_le_smul`,
   `finite_lTensor_ideal`, and `flat_of_torVanish_pow`.
4. **Localization and final assembly.**
   `isLocalizedModule_id_of_units`, `isTorsionBySet_baseChange`,
   `lTensor_injective_of_torsion`, then
   `flat_of_comap_maximalIdeal_lTensor_injective`, the right-tensor
   solution and the checked 00MK specialization.

All these primary names are below
`FlatnessAudit.Primary.LocalFlatnessCriterionAtPrime` except the final
`FlatnessAudit.Primary.solution`; the source namespace mapping is in the
appendix. This partition is a recommendation, not newly created tasks.
Review may choose a smaller local-ring specialization if it removes
unneeded general localization infrastructure without changing 00MK.

For the deferred tower, plausible focused extraction leads are
`LocalCritPort.kwFF11_idealTowerTensorFactor_proved`
(a surjective tensor comparison with a commutative inclusion square),
`kwFF13_idealMap_restrictScalars_eq_submoduleMap`, and
`kwFF13_restrictScalars_subtype_rTensor_inj_of_flat`.
The Tor dependency also contains
`MK00Port.ar_rTensor_injective_of_tor1_isZero`,
`ar_finite_tensorProduct_left`, and `ar_mem_smul_pow_extend`.
These are source-reviewed leads only. Repair or avoid the categorical
naturality dependency, give each selected helper its own complete
declaration/axiom check, and generalize its universes/module where needed.
The primary route is preferable for this tensor-form 00MK target because
its feasibility is established without this categorical Tor dependency.

## Ownership and remaining acceptance

The existing 00MK statement task is
`9e754bcc-9ee0-4dc5-95c7-66f127c778a8`; its unchanged target was published
at `84f5d5a32df09643d499627f7ca72504805d3365`.
The exact-proof task is
`11a11b7f-7747-4bd1-b219-2e8febc50673` (ready, without an executor at
the audit's status check). This audit creates no rival implementation task.

Worker 336 coordinates parent
`3456d315-11f6-4139-a252-2bd081630700`; Worker 9 owns scheme assembly
`bd62242a-a240-4c31-a976-42e83d95485b`.
Preserved tasks include 00R7
`8644bad3-d88e-4471-aa5e-c9c93babe680`, 046Y
`de630fa7-ed99-4739-a333-8db01375d3dd`, approximation
`232f59bb-1e1e-4636-bc62-45f0e72ae43c`, 00ML
`e2c919ab-5dc7-461a-bc41-8c89cd609e37`, and 00MP
`3acee84e-e8aa-45da-81f1-bc803f9db121`.

The next mathematical work belongs to those owners: choose the focused
primary units, retain attribution, publish their required interfaces, and
obtain independent semantic review, successful Lake and exact-target
validation, and publication for a theorem of the unchanged 00MK target.
The tower limitations remain explicit obligations. Audit acceptance and
publication discharge only this note's documentary task.
