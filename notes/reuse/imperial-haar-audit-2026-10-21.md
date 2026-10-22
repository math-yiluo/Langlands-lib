# Imperial FLT Haar determinant scaling: reuse audit

Worker 90, 21–22 October 2026. Audit task
`0187489b-6545-4d68-ab0c-4b535596ce9c`, revision 2.

**Verdict: adapt the isolated determinant argument if the existing owners need
it; reuse the Library's scalar theorem.** Imperial's determinant theorem has the
right mathematical generality, including dimension zero. Its p-adic scalar
theorem concerns only `ℚ_[p]`, whereas our target concerns arbitrary finite
extensions and the residue-normalized absolute value. The Library already
supplies that stronger scalar result. A private compatibility adaptation of both
Imperial modules builds in our approved environment, and inspection of each
selected declaration reports exactly `propext`, `Classical.choice`, and
`Quot.sound`. The exact original upstream environment was not built or inspected.

This note is source analysis and a port plan. Its review does not admit an
external theorem, the private adaptation, or a proof of the rectangular target.
It introduces no public Lean code and changes no mathematical target.

## 1. Sources, pins, and audit boundary

The registered source is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Its collection is at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/`.
The Imperial subdirectory is `ImperialCollegeLondon--FLT/`, with `source/`,
`head.json`, `tree.json`, and `metadata.json`. The collection's
`SURVEY-SNAPSHOT.md` and `SNAPSHOT-INDEX.json` describe the source selection: it
is a reading collection, not a certified complete checkout.
See also the [external reuse survey](external-lean-survey-2026-10-21.md).

| Item | Exact version |
| --- | --- |
| ImperialCollegeLondon/FLT | `923d45174c500aa1d994ba973bac38ea39eacbf7` |
| Upstream Lean | `leanprover/lean4:v4.35.0-rc4` |
| Upstream Mathlib | `1f414401f69059aa7eead47b53ee40bd38455eeb` |
| Approved target environment | `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` |
| Target Lean | `leanprover/lean4:v4.34.0`, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` |
| Target Mathlib | `5ed2965256430c3649e86755f9576b54eca72435` |
| Library initially compared | `01a58491bc71539f1ecd3d5f0eec6ab8eae20fed` |
| Library rechecked after context restoration | `0686b4fa6c8df22845bba2e2668a723a41d47c84` |

The two selected files are
[FiniteDimensional.lean](https://github.com/ImperialCollegeLondon/FLT/blob/923d45174c500aa1d994ba973bac38ea39eacbf7/FLT/HaarMeasure/HaarChar/FiniteDimensional.lean)
and
[Padic.lean](https://github.com/ImperialCollegeLondon/FLT/blob/923d45174c500aa1d994ba973bac38ea39eacbf7/FLT/HaarMeasure/HaarChar/Padic.lean).
All source readings in this audit used the registered local snapshot.

Recursive traversal of explicit imports, including private imports, found 26
local FLT files for `FiniteDimensional` and 20 for `Padic`, with a union of 29.
Every referenced FLT file was present. All 29 original files' Git blob hashes
matched the entries in the pinned recursive tree. Appendix A records closure
membership and file attribution; Appendix B records the Mathlib import boundary.
The boundary has 65 distinct Mathlib modules for the determinant closure and 50
for the scalar closure. These are file-import closures, not minimal
declaration-dependency closures.

Missing evidence is precise: the original pinned Mathlib transitive source
closure and an approved original Lean/Mathlib execution environment were not
available as part of this audit. No upstream toolchain or Mathlib was downloaded
or rebuilt. Consequently, there is no claim here that the original upstream
build passes or that its exact transitive axiom set has been measured. The
positive kernel dependency evidence below belongs to the explicitly described
adaptation against our Mathlib.

## 2. Complete selected types and meaning

The following are the complete binder lists printed by Lean in the adapted
environment, with generated instance names suppressed, universes renamed, and
standard notation restored. No hypothesis is omitted. The selected determinant
file itself was byte-identical to the pinned original.

```lean
MeasureTheory.addEquivAddHaarChar_eq_ringHaarChar_det.{u, v} :
  ∀ {F : Type u}
    [MeasurableSpace F] [TopologicalSpace F] [BorelSpace F]
    [LocallyCompactSpace F] [Field F] [IsTopologicalRing F]
    {V : Type v}
    [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
    [BorelSpace V] [Module F V] [FiniteDimensional F V]
    [IsModuleTopology F V] [IsTopologicalAddGroup V]
    [LocallyCompactSpace V] [SecondCountableTopology F]
    (ρ : V ≃L[F] V),
    MeasureTheory.addEquivAddHaarChar ρ.toContinuousAddEquiv =
      MeasureTheory.ringHaarChar ρ.toLinearEquiv.det

MeasureTheory.ringHaarChar_padic :
  ∀ {p : ℕ} [Fact p.Prime] (x : ℚ_[p]ˣ),
    MeasureTheory.ringHaarChar x = ‖(x : ℚ_[p])‖₊
```

The field and vector space have independent universes in the first theorem.
The second has no universe parameters: it is about the concrete Mathlib
`Padic p : Type`, not an arbitrary isomorphic copy or finite extension.
There is no positive-dimension or nonempty-basis assumption. The first theorem
has no explicit `T2Space`, normed-field, or topological-division hypothesis.
`LocallyCompactSpace V` remains explicit; the source notes that typeclass
inference cannot find the scalar field automatically. General commutative rings
occur in intermediate results only with an explicit diagonal/transvection
decomposition hypothesis; the selected final theorem assumes a field.

In current Mathlib, for a locally compact Borel topological additive group `G`,
`addEquivAddHaarChar φ : ℝ≥0` is
`addHaarScalarFactor addHaar (addHaar.map φ)`. It is the positive factor `c`
satisfying `c • μ.map φ = μ` for every **regular** additive Haar measure `μ`.
The complete measure-facing interface is:

```lean
MeasureTheory.addEquivAddHaarChar_smul_map.{u} :
  ∀ {G : Type u}
    [AddGroup G] [TopologicalSpace G] [MeasurableSpace G]
    [BorelSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G]
    (μ : MeasureTheory.Measure G)
    [MeasureTheory.Measure.IsAddHaarMeasure μ]
    [MeasureTheory.Measure.Regular μ]
    (φ : G ≃ₜ+ G),
    MeasureTheory.addEquivAddHaarChar φ • μ.map φ = μ
```

Thus the character measures **image scaling**: `μ (φ '' S) = c * μ S`.
The pushforward formula required by our target is
`μ.map φ = c⁻¹ • μ`. Positivity permits inversion; values are coerced from
`ℝ≥0` to `ℝ≥0∞` when evaluating measures. Confusing these directions would
invert the desired answer.

Imperial defines
`ringHaarChar : Rˣ →ₜ* ℝ≥0` under
`[Ring R] [TopologicalSpace R] [IsTopologicalRing R]
[LocallyCompactSpace R] [MeasurableSpace R] [BorelSpace R]`.
Its value at `u` is definitionally
`addEquivAddHaarChar (ContinuousAddEquiv.mulLeft u)`.
It packages this function as a continuous monoid homomorphism; continuity is
proved using a nonnegative compactly supported function with positive integral.
`ringHaarChar_mul_volume μ u` states
`μ (u • S) = ringHaarChar u * μ S` for arbitrary sets and any regular additive
Haar measure. It does not restrict the result to a chosen normalized volume.

The determinant proof first treats diagonal matrices using the product formula
for Haar characters. A transvection preserves product Haar measure by integrating
one coordinate and using translation invariance; uniqueness of Haar measure
transfers this to `addHaar`. Diagonal/transvection induction gives the matrix
case. A continuous finite basis equivalence conjugates an arbitrary
finite-dimensional space to a finite function space.

The p-adic proof computes the index of `x ℤ_p` inside `ℤ_p` for a nonzero
p-adic integer, and uses the volume-one unit ball to identify the character.
It extends the identity to all units of `ℚ_p` by fractions and subgroup
generation. Although the source comment says “density”, its
`PadicInt.closure_nonZeroDivisors_padicInt` uses **algebraic**
`Subgroup.closure`, with a fraction representation from
`IsFractionRing.div_surjective`. This step is not topological density of the
nonzero integers in `ℚ_pˣ`.

## 3. Correspondence with the Library target

The target is
`Langlands.HarmonicAnalysis.PadicAdditiveHaarScalingStatement` in
[PadicHaarScalingStatement.lean](../../Langlands/HarmonicAnalysis/PadicHaarScalingStatement.lean).
It is the conjunction of scalar and rectangular statements. It quantifies over
every prime `p`, `F : PadicField.{uF} p`, supplied `T : F.TopologicalData`,
arbitrary Borel measurable structures, and arbitrary additive Haar measures.
The rectangular part also quantifies over every `r s : ℕ`, including zero.

| Concern | Imperial result | Project use and remaining obligation |
| --- | --- | --- |
| Field | General field for determinant; only `ℚ_[p]` for scalar computation | `PadicField.{uF} p` is a finite-dimensional field algebra over `Padic p`; retain arbitrary `uF` |
| Topology | Locally compact topological field/ring and finite-dimensional module topology | Use exactly `T.topology`, its local-field data, and the induced finite product topology |
| Continuity | Input is a continuous linear equivalence | Construct the rectangular action and its inverse using continuous finite matrix operations |
| Borel structure | Borel spaces on both field and vector space | Preserve the arbitrary target Borel structure and reconcile it with the product Borel structure |
| Countability | Explicit second countability of the field | Derive from `T.secondCountableTopology`; add no new target premise |
| Haar measure | Character is measure independent; measure formula needs regularity | Derive regularity for each supplied Haar measure |
| Normalization | `ringHaarChar_padic = ‖·‖₊` only on `ℚ_p` | Use residue normalization on `F`, supplied by the existing scalar proof |
| Scaling direction | Image factor is the character | Pushforward uses its inverse |
| Empty dimensions | No positive-dimension hypothesis | Rectangular action is the identity on a singleton; factor is one |

The published
[PadicScalarHaarScalingProof.lean](../../Langlands/HarmonicAnalysis/PadicScalarHaarScalingProof.lean)
already contains
`Langlands.HarmonicAnalysis.padicScalarHaarScalingStatement` and the application
theorem `padicScalarHaarScaling`. These prove the exact scalar target for every
such `F`, `T`, Borel structure, Haar measure, and unit. This was checked in both
Library commits listed above. The rectangular theorem is not supplied by that
file. The scalar proof's
`Langlands.PadicField.TopologicalData.distribHaarChar_eq_normalizedAbsUnits`
is **private**, so its source is useful evidence but its name is not a public
interface for a later port.

### Topology, regularity, and arbitrary measurable structures

Public theorems for `T` include `fieldT2`, `secondCountableTopology`,
`sigmaCompactSpace`, `pseudoMetrizableSpace`, `isCompact_integers`,
`isOpen_integers`, and `haarMeasure_regular`. Install the supplied topology,
valuative relation, and local-field instance consistently. These results
justify the regularity required by the general Haar API without weakening the
target to a chosen Haar measure.

For matrices, finite products inherit local compactness, sigma compactness, and
pseudometrizability. Current Mathlib's
`Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure` then gives
regularity of any additive Haar measure. The needed
`IsModuleTopology F (Matrix (Fin r) (Fin s) F)` is over **F**, not merely the
`ℚ_p`-module topology supplied in `T`. Mathlib's
`IsTopologicalSemiring.toIsModuleTopology` and `IsModuleTopology.instPi` provide
the relevant route. A future port must check these instance choices explicitly.

The rectangular target supplies a measurable space on the matrix type, not
separately on `F`. Internally one may choose `borel F`; second countability
gives the finite product Borel instance. The target's `BorelSpace` identifies its
supplied measurable space with that Borel structure. This reconciliation is a
proof obligation, not a reason to add a product-measurable-space premise.

### Residue normalization and the field-character bridge

For nonzero `x`, `T.normalizedAbs x = q ^ (-T.ord x)`, where
`q = T.residueCardinality` is the actual residue-field cardinality; its value at
zero is zero. `T.normalizedAbsUnits : F.Carrierˣ →* ℝ≥0ˣ` restricts this
absolute value to units.
`T.determinantNorm n` is its composition with `GeneralLinear.determinant`.

The Library's `T.normalizedAbs_eq_canonicalNorm_pow_degree` gives
`|x|res = canonicalNorm(x) ^ [F : ℚ_p]`. Replacing this by the spectral norm
would be wrong when the degree `d` exceeds one: at `p`, the residue-normalized
value is `p^(-d)`, whereas the extending spectral norm is `p^(-1)`.
Imperial's scalar theorem on `ℚ_p` alone does not close this gap.

The existing Library scalar proof closes the mathematical gap by the compact
integer ring, maximal-ideal index `q`, a uniformizer, and valuation powers.
If a future port retains Imperial's literal `ringHaarChar`, it still needs a
public equality
`ringHaarChar a = (T.normalizedAbsUnits a : ℝ≥0)`.
One route identifies it with current Mathlib's `distribHaarChar`; another
deduces it from the published scalar pushforward theorem and Haar character
scaling, cancelling the finite positive measure of a compact open set.
Publishing a suitable bridge, or adapting the determinant proof to the existing
character API, is smaller than porting the `ℚ_p` computation and then
generalizing it again. The private helper must not be imported by a guessed
generated name.

An alternative mathematical route applies the determinant theorem over `ℚ_p`
to scalar multiplication on `F`, identifies its determinant with
`Algebra.norm`, and proves `|Norm(x)|p = |x|res`. Those norm/determinant and
normalization bridges would be additional obligations; this audit has not
implemented that route.

### Rectangular determinant and the zero cases

For `A ∈ GL_r(F)` and `B ∈ GL_s(F)`, define
`ρ(X) = A X B⁻¹`. Its inverse is `X ↦ A⁻¹ X B`, so it is an `F`-linear
equivalence; continuity follows from finite matrix operations.
Using coordinates indexed by the row-column pair, its matrix is
`A ⊗ (B⁻¹)ᵀ`, because its coefficient at `((i,j),(k,l))` is
`A i k * (B⁻¹) l j`. Consequently,

```text
det_F(ρ) = (det A)^s * (det B)^(-r) = (det A)^s / (det B)^r,
image factor = |det A|res^s / |det B|res^r,
pushforward factor = (|det A|res^s / |det B|res^r)^(-1).
```

The determinant is best stated in `Fˣ`, matching `LinearEquiv.det` and
`normalizedAbsUnits`. Column-first coordinates reverse the Kronecker order and
give the same determinant. Current Mathlib's `Matrix.det_kronecker` assumes
finite decidable index types and a commutative ring, with no nonempty-index
assumption. `Matrix.det_transpose` and `LinearMap.det_toLin'` are also
available. For a finite-product decomposition, `LinearMap.det_pi` gives the
determinant of coordinatewise linear endomorphisms of a finite product of a
finite free module as the product of their determinants. These are candidate
ingredients, not a claim that the rectangular coordinate calculation has been
formalized.

If `r = 0` or `s = 0`, the matrix space is a singleton and the action is its
identity. The determinant on the empty square index is one; the other
determinant has exponent zero. Hence the displayed ratio and its inverse are
one, and `μ.map id = μ`. No `0 < r`, `0 < s`, or `Nonempty (Fin r/s)`
hypothesis may be added.

## 4. What was checked

The audit distinguished four kinds of evidence.

1. **Textual closure checks.** A local scanner removed nested block comments
   and line comments, traversed explicit imports, and searched the 29 files for
   `sorry`, `admit`, `axiom`, `knownin1980s`, `native_decide`,
   `implemented_by`, `extern`, `unsafe`, `run_cmd`, and `initialize`.
   There were no hits. The scanner is not a Lean parser; this result alone
   establishes neither compilation nor transitive axiom independence.
2. **Original upstream evidence.** `FLT/Assumptions/KnownIn1980s.lean`
   declares the arbitrary-proposition axiom `knownin1980s`. Neither that module
   nor `FLT.Proof` occurs in either local import closure. The broader
   repository's documentation and CI presentation were not treated as kernel
   certificates. No original-environment declaration inspection was obtained.
3. **Adapted compilation and transitive inspection.** The full union of 29
   local files was copied only into `.private/drafts/imperial-haar-audit/`.
   Three files needed the compatibility edits in Appendix C. Both selected
   declarations then passed separate `lean_check` Lake builds and declaration
   inspections in the approved target environment. Each inspection's complete
   axiom list was `["propext", "Classical.choice", "Quot.sound"]`.
   This positively excludes `knownin1980s`, `sorryAx`, and any other axiom from
   the transitive dependencies of these **adapted declarations**.
4. **Admission status.** These are development checks:
   `proof_accepted` is false. No published statement target was supplied, so
   `target_matches` is false. No independent mathematical acceptance of this
   adaptation is claimed. A later port needs its own published Prop-valued
   statement, exact-target validation, semantic review, and integration.

The diagnostic sequence is retained to make failed and superseded checks clear:

| Diagnostic record | Actual result |
| --- | --- |
| `3a4ed2d0-6f82-4f0d-8203-e7c9d659b3db` | Verbatim closure failed with four errors: missing module import, missing coercion lemma names, and a faithfulness/coercion rewrite mismatch |
| `f3237b2c-5667-4a8c-a9bd-d6a923eb46ce` | First adaptation built the determinant module; scalar module still failed on `PadicInt.norm_coe` |
| `6ac58d43-b915-4c19-abe6-bad8b61308b5` | Both modules built, but determinant inspection was empty because the final scalar module did not import it; overall check was unsuccessful |
| `441c4885-35e5-4ebb-bf72-0f9468034c20` | Determinant build and exact named-declaration inspection: `ok: true`, zero errors/warnings, the three axioms above |
| `974cf7f1-a016-4cc5-b34e-1840619114c0` | Scalar build and exact named-declaration inspection: `ok: true`, zero errors/warnings, the same three axioms |
| `1064714d-3785-4d35-bae3-1b08332aaeef` | Diagnostic module printed complete types, including all hypotheses and universes |
| `575030fe-b6e3-4f67-b63c-5e6d4a6f450a` | After context restoration, both adapted modules and the type-printing module rebuilt successfully with zero errors/warnings; no new axiom inspection was requested |
| `47d38d57-fd76-4652-ac0a-ea0c67763cff` | After review, both adapted modules and the extended type-printing module rebuilt successfully with zero errors/warnings, verifying `LinearMap.det_pi`, `Matrix.det_transpose`, and `LinearMap.det_toLin'`; no new axiom inspection was requested |

The two successful declaration inspections have source-root fingerprint
`4a36bca408dcd16663a18446e772a3432831886f16d95608a1a199687af612d8`.
Their type fingerprints are, respectively,
`d5c6b5b5327b15dcfb54c2de4260312e408b45526759b45a85e445e1be22ea03`
and
`92b43f3a4f1d8c0f37aca8a54dec643616e1cfcd7b3079347f4aeed49136e162`.
The restoration build, with the additional diagnostic module and refreshed
workspace, has source-root fingerprint
`af895e126611a39a25273301611d505c2304ecd23618ae682e406b3f24176fee`;
it is not represented as the earlier identical source-root snapshot.
The post-review build adds the determinant API checks and has source-root
fingerprint
`9a408b3b99e033f29acf71af26e355b12a75ac1553695d12882ef37e40b530f1`.

The immutable diagnostic JSON files are retained in Worker 90's workspace
`.private/notes/records/<diagnostic-id>.json`. The audit working directory
`.private/notes/imperial-haar-audit/` also contains `scan.json`,
`blob-check.json`, `complete-types.txt`, and `compatibility.patch`. These are
review lookup locations, not Library API or accepted mathematical artifacts.
The public appendices below preserve the essential source inventory and complete
adaptation patch independently of those private working files.

## 5. Overlap, version changes, and extraction cost

Our current Mathlib already has `MeasureTheory.addEquivAddHaarChar` and its
regular-Haar measure formulas in
`Mathlib/MeasureTheory/Measure/Haar/MulEquivHaarChar.lean`, and
`MeasureTheory.distribHaarChar` in
`Mathlib/MeasureTheory/Measure/Haar/DistribChar.lean`.
The latter handles distributive group actions, including scalar multiplication
by units. Reusing these avoids copying the continuous `ringHaarChar` wrapper
unless continuity of that wrapper is separately needed.

The determinant, matrix Kronecker determinant, matrix transvection
decomposition, regularity, and finite product module-topology APIs are also
already present. Imperial's
`FLT.Mathlib.LinearAlgebra.Matrix.Transvection` adds a
determinant-unit induction interface adapted from Mathlib; compare that small
interface before copying it. Some continuous matrix/basis conversion helpers
in `FLT.Mathlib.Topology.Algebra.Module.Equiv` may need adaptation.

The successful compatibility patch is confined to:

| File | Required changes against our pinned Mathlib |
| --- | --- |
| `FLT/Mathlib/Topology/Algebra/Module/Quotient.lean` | Replace import `Mathlib.Topology.Algebra.Module.Equiv.Basic` by `Mathlib.Topology.Algebra.Module.Equiv` |
| `FLT/Mathlib/NumberTheory/Padics/PadicIntegers.lean` | Supply `PadicInt.coe_inj` using `Subtype.coe_inj`; use `AddMonoidHom.coe_coe`; replace the faithfulness rewrite with `(FaithfulSMul.algebraMap_injective R A).eq_iff` |
| `FLT/HaarMeasure/HaarChar/Padic.lean` | Use `MonoidHom.coe_coe`; replace `PadicInt.norm_coe` by `PadicInt.padic_norm_e_of_padicInt` |

Every edited file received a prominent modification notice. The determinant
entry file needed no edit. This demonstrates a feasible compatibility
adaptation; it is not a proposal to integrate all 29 files.

The file-level closure carries unrelated material. `Ring`/`AddEquiv` bring in
restricted-product infrastructure. The determinant entry file has later
simple-ring applications, and its auxiliary determinant file imports
algebraic-closure, central/simple-ring, and related material. Those imports are
part of the checked full-file build but are unnecessary to the diagonal,
transvection, and basis-conjugation argument. A future port should extract
only declarations actually needed by its proof and use current Mathlib
equivalents. An umbrella `FLT` import would defeat this scope.

## 6. Licenses and attribution

The pinned Imperial root contains `LICENSE` with the Apache License 2.0.
Every one of the 29 source headers states that license, with the copyright and
author information recorded in Appendix A. Searching the complete pinned
recursive tree for license/notice/attribution paths found `LICENSE` and no
`NOTICE` or `ATTRIBUTION` file. No notice from another fork or repository is
being assigned to this source.

For a later distributed extraction, retain the Apache license and relevant
copyright/attribution notices and identify modified files, following the
pinned license's redistribution terms. Preserve the provenance of copied
Mathlib material as well: Imperial's transvection helper explicitly says it was
copied/adapted from Mathlib's
`Mathlib/LinearAlgebra/Matrix/Transvection.lean`, whose header credits
Sébastien Gouëzel, copyright 2021. The current Haar-character source credits
Kevin Buzzard (2025) in `MulEquivHaarChar.lean`; `DistribChar.lean` credits
Andrew Yang, Yaël Dillies, and Javier López-Contreras (2024).
The audit note itself does not distribute a standalone Lean port.

## 7. Smallest next units

Search the current Library by declaration name before starting any of these:
other workers may have completed them after the commits audited here.
Existing harmonic-analysis tasks
`e534647a-77a5-4c12-91d7-8a00fe104fc4` and
`615ca923-6212-4825-94f8-3dbabc39095d`, and modulus task
`04f6388c-bbfb-439c-99f1-96ae81cd761c`, retain their objectives.
This audit creates no duplicate implementation task.

1. **Definitions, only if absent:** package the continuous linear equivalence
   `X ↦ A X B⁻¹` with its explicit inverse. Prefer current character APIs; add
   a field-character wrapper only if a consumer actually requires it.
2. **Statements before new proofs:** publish a general finite-dimensional
   determinant-scaling proposition, a rectangular determinant proposition in
   units, and, only if needed, a public normalized field-character bridge.
   Preserve universes, topology/Borel hypotheses, and empty dimensions.
   Existing `PadicRectangularHaarScalingStatement` needs no replacement.
3. **Focused proofs:** adapt the diagonal/transvection/basis argument using
   current Mathlib; separately prove the rectangular determinant with
   `det_kronecker` or a finite-product decomposition. Derive a public
   normalization bridge from the existing scalar theorem if the chosen
   interface requires one.
4. **Specialization:** derive countability and regularity, identify the
   rectangular determinant, apply the residue-normalized scalar character,
   and invert the factor for pushforward. Prove the existing rectangular
   target and conjoin it with `padicScalarHaarScalingStatement` to obtain the
   existing additive target. Block/product-Haar and modulus computations
   remain their consumers' separate work.

Each mathematical unit requires separate task authority, the normal Lean
checks, independent semantic review, and publication. The recommended route
rests on the actual compatibility checks and available Library scalar proof.
Its unresolved obligations are the minimal determinant extraction, public
character connection if retained, coordinate determinant proof, and exact
specialization; original-upstream axiom evidence remains unavailable.


## Appendix A. Exact local closure and source attribution

`D` means the determinant file closure; `P` means the scalar file closure.
Every path is relative to the pinned Imperial `source/` directory. All listed
files are Apache 2.0. Copyright entries below retain the year and holder; each
original header also says “All rights reserved.” The authors column is separate
from the copyright holder.

| Closure | File | Copyright | Authors |
| --- | --- | --- | --- |
| D, P | `FLT/Deformations/ContinuousRepresentation/IsTopologicalModule.lean` | 2025 Javier López-Contreras | Javier López-Contreras |
| D, P | `FLT/HaarMeasure/HaarChar/AddEquiv.lean` | 2025 Kevin Buzzard | Kevin Buzzard, James Sundstrom, Ruben Van de Velde, Anatole Dedecker, Bryan Wang Peng Jun, David Renshaw |
| D | `FLT/HaarMeasure/HaarChar/FiniteDimensional.lean` | 2025 Kevin Buzzard | Kevin Buzzard, Norbert Voelker |
| P | `FLT/HaarMeasure/HaarChar/Padic.lean` | 2024 Yaël Dillies, Javier López-Contreras | Yaël Dillies, Javier López-Contreras |
| D, P | `FLT/HaarMeasure/HaarChar/Ring.lean` | 2025 Kevin Buzzard | Kevin Buzzard |
| P | `FLT/HaarMeasure/MeasurableSpacePadics.lean` | 2024 Yaël Dillies, David Loeffler | Yaël Dillies, David Loeffler |
| D | `FLT/Hacks/RightActionInstances.lean` | 2025 Kevin Buzzard | Kevin Buzzard, Pietro Monticone |
| D | `FLT/Mathlib/Algebra/Algebra/Bilinear.lean` | 2025 Kevin Buzzard | Kevin Buzzard, Salvatore Mercuri, Ruben Van de Velde |
| D | `FLT/Mathlib/Algebra/Algebra/Hom.lean` | 2025 Kevin Buzzard | Kevin Buzzard, Salvatore Mercuri |
| D, P | `FLT/Mathlib/Algebra/Algebra/Tower.lean` | 2025 Salvatore Mercuri | Salvatore Mercuri, Kevin Buzzard |
| D | `FLT/Mathlib/LinearAlgebra/Determinant.lean` | 2025 Kevin Buzzard | Kevin Buzzard, Yunzhou Xie |
| D | `FLT/Mathlib/LinearAlgebra/Matrix/Transvection.lean` | 2026 Kevin Buzzard | Kevin Buzzard |
| D | `FLT/Mathlib/LinearAlgebra/Pi.lean` | 2025 Salvatore Mercuri | Salvatore Mercuri, Kevin Buzzard |
| D, P | `FLT/Mathlib/MeasureTheory/Constructions/BorelSpace/RestrictedProduct.lean` | 2025 Kevin Buzzard | Kevin Buzzard |
| D, P | `FLT/Mathlib/MeasureTheory/Group/Action.lean` | 2024 Yaël Dillies | Yaël Dillies, Kevin Buzzard, Ruben Van de Velde, David Ledvinka |
| D, P | `FLT/Mathlib/MeasureTheory/Group/Measure.lean` | 2025 David Ledvinka | David Ledvinka |
| D, P | `FLT/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean` | 2025 David Ledvinka | David Ledvinka |
| P | `FLT/Mathlib/NumberTheory/Padics/PadicIntegers.lean` | 2024 Yaël Dillies | Yaël Dillies, Kevin Buzzard, Pietro Monticone, Ruben Van de Velde |
| D, P | `FLT/Mathlib/Order/Filter/Cofinite.lean` | 2025 Kevin Buzzard | Kevin Buzzard |
| D | `FLT/Mathlib/RingTheory/SimpleRing/TensorProduct.lean` | 2025 Jujian Zhang | Jujian Zhang, Yunzhou Xie |
| D, P | `FLT/Mathlib/Topology/Algebra/ContinuousMonoidHom.lean` | 2025 Salvatore Mercuri | Salvatore Mercuri, Kevin Buzzard |
| D, P | `FLT/Mathlib/Topology/Algebra/Group/Units.lean` | 2025 Kevin Buzzard | Kevin Buzzard, Ruben Van de Velde |
| D | `FLT/Mathlib/Topology/Algebra/Module/Equiv.lean` | 2024 Kevin Buzzard | Kevin Buzzard, Salvatore Mercuri, Pietro Monticone |
| D, P | `FLT/Mathlib/Topology/Algebra/Module/ModuleTopology.lean` | 2024 Kevin Buzzard | Kevin Buzzard, Pietro Monticone, Salvatore Mercuri, Matthew Jasper, Ruben Van de Velde, William Coram |
| D, P | `FLT/Mathlib/Topology/Algebra/Module/Quotient.lean` | 2025 Salvatore Mercuri | Salvatore Mercuri, Kevin Buzzard, Pietro Monticone |
| D, P | `FLT/Mathlib/Topology/Algebra/RestrictedProduct/Basic.lean` | 2025 Matthew Jasper | Matthew Jasper, Kevin Buzzard, Ruben Van de Velde |
| D, P | `FLT/Mathlib/Topology/Algebra/RestrictedProduct/Equiv.lean` | 2025 Kevin Buzzard | Kevin Buzzard, Salvatore Mercuri |
| D, P | `FLT/Mathlib/Topology/Algebra/RestrictedProduct/TopologicalSpace.lean` | 2025 Matthew Jasper | Matthew Jasper, Kevin Buzzard, Bhavik Mehta, Ruben Van de Velde, Bryan Wang Peng Jun, Pietro Monticone |
| D, P | `FLT/Mathlib/Topology/Bases.lean` | 2025 Kevin Buzzard | Kevin Buzzard |

The SHA-256 values of the original source bytes are recorded here in addition
to the Git tree verification. They do not describe the modified copies.

```text
76373ff5838596d8e9d6bea52261f4950814ed8fe7ebac81f52b198333518e15  FLT/Deformations/ContinuousRepresentation/IsTopologicalModule.lean
d96e644f47ddf6991c9eed09cec126e455d02449cf5642853e465e0cb23df6c0  FLT/HaarMeasure/HaarChar/AddEquiv.lean
9609f5f9ce8e8ca9fe4808ecc8b76d066028e16fa1520aa1fc52e5826b75c632  FLT/HaarMeasure/HaarChar/FiniteDimensional.lean
7423e83321910101caa9f0e6d10e1b9aa95f6020efe3f8c46e2265ee21ac5e63  FLT/HaarMeasure/HaarChar/Padic.lean
f7e70a15f800bafd303f2a28da1ada584eaf3d72a586b96e4e757d8c27c3d740  FLT/HaarMeasure/HaarChar/Ring.lean
29de8cf9b3cd0ffaba31ad1bdc400661c3dd61a258685686b0e974de0710a109  FLT/HaarMeasure/MeasurableSpacePadics.lean
415821986ecf2e127a3b9b81d3f330641538cdd715e8b51118b4af069c651dc6  FLT/Hacks/RightActionInstances.lean
dff310571f7230f9e00aff592346f24a8a8214d95740939516e1b28eb9e7e0c1  FLT/Mathlib/Algebra/Algebra/Bilinear.lean
d67cf7f4f5abae7a1d30ec7650137c4c32eb20346f45ced255de830161efa1e0  FLT/Mathlib/Algebra/Algebra/Hom.lean
d014b1e04e6219f7e0a53302c20007a928d00c45d45fabaf07eea97bda156389  FLT/Mathlib/Algebra/Algebra/Tower.lean
7daeee1c0020b18cc921a17b062d4a25e8696730f509f11d36afa770a42b0a42  FLT/Mathlib/LinearAlgebra/Determinant.lean
60d6d713026a86ccdd9403948102431e36002c12b9b16d65d490d8fb680b95f1  FLT/Mathlib/LinearAlgebra/Matrix/Transvection.lean
0105d12a889e8b8a2b03ded4c559d55d46269aaa13ba93af12adc9834df94866  FLT/Mathlib/LinearAlgebra/Pi.lean
8eb2e92b6c5237a64445cf68bed4be620f465b806c93b1e35b81413b52b114e9  FLT/Mathlib/MeasureTheory/Constructions/BorelSpace/RestrictedProduct.lean
b04fdfbd44d18353cba92dbf3d87dd43d95d7cc0f0bf3331f1bc5e3e13970b1d  FLT/Mathlib/MeasureTheory/Group/Action.lean
cf598f607d0b3059afd2388eb6eb1fefe1a02fe1fe190bad1c0f4b0e658f9f78  FLT/Mathlib/MeasureTheory/Group/Measure.lean
aca33268c4b7e8c12e457518d8b50aaa79e93c760831e01e0649f3308bb0756e  FLT/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean
4243005870e8f1d444a2d49617bb3b6ce661fb9f8abf719269003b7dfc459e71  FLT/Mathlib/NumberTheory/Padics/PadicIntegers.lean
d476b430484c6a89aaab48839a06b355f3f5712df880c499100af3bc1efc7017  FLT/Mathlib/Order/Filter/Cofinite.lean
1052f6e29667ed59bbae81a3a948b7f743eb66bddd590fbdc8c3d7276c1304a4  FLT/Mathlib/RingTheory/SimpleRing/TensorProduct.lean
20677139a9f2162db2c3b8b04b1a65e8cc6ea5f1f9b56139892df79785684198  FLT/Mathlib/Topology/Algebra/ContinuousMonoidHom.lean
ad910df7ecdfb186458ea1991cb734ff96ad49fa164d07c61b54a51702667ce7  FLT/Mathlib/Topology/Algebra/Group/Units.lean
daaafadd4336cc59b9bfc189e3702f63be8e87cb6e1e49ba618583c7f5efcd19  FLT/Mathlib/Topology/Algebra/Module/Equiv.lean
8aade8d311874ef18e0a43c411c3c0e596abf070a11168cef1db63183024439c  FLT/Mathlib/Topology/Algebra/Module/ModuleTopology.lean
9f77fa01adc77baaf32c4468e6fb20188b3ffd569038ff70b6614add82666b2a  FLT/Mathlib/Topology/Algebra/Module/Quotient.lean
7b3b53b41297aaa957453701b1feab7b27ca9e616411bbc0b5cf150a267e26f3  FLT/Mathlib/Topology/Algebra/RestrictedProduct/Basic.lean
9ab27aedd30e2062291cb7d6028a59821147fe7d5fd7d6107aee6662c1a91900  FLT/Mathlib/Topology/Algebra/RestrictedProduct/Equiv.lean
d5fe125c11ed3f5fb06f16722e43e7fd2d34ba1f9a90c93d9bd120e3b03a43d8  FLT/Mathlib/Topology/Algebra/RestrictedProduct/TopologicalSpace.lean
856cabfa256753254de706d62504b3e7b934ba9ae484ca019d08b9cea2902d01  FLT/Mathlib/Topology/Bases.lean
```

## Appendix B. Exact Mathlib import boundary

These lists stop at Mathlib imports; they are not Mathlib's transitive closure.
The upstream missing input and target import rename are described in sections
1 and 5. Shared entries appear in both lists so each closure is reproducible.

### Determinant boundary (65 modules)

```text
Mathlib.Algebra.Algebra.Prod
Mathlib.Algebra.Central.Basic
Mathlib.Algebra.Central.Defs
Mathlib.Algebra.Group.Pi.Units
Mathlib.Algebra.Group.Pointwise.Set.Basic
Mathlib.Algebra.Group.Submonoid.Units
Mathlib.Algebra.Lie.OfAssociative
Mathlib.Algebra.Module.Equiv.Defs
Mathlib.Algebra.Module.LinearMap.Defs
Mathlib.Algebra.Module.Pi
Mathlib.Algebra.Module.Submodule.Defs
Mathlib.Algebra.Ring.Subring.Basic
Mathlib.CategoryTheory.Category.Basic
Mathlib.CategoryTheory.Category.Init
Mathlib.CategoryTheory.Types.Basic
Mathlib.Data.Nat.Totient
Mathlib.Data.Sym.Sym2.Init
Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
Mathlib.GroupTheory.Index
Mathlib.LinearAlgebra.Basis.VectorSpace
Mathlib.LinearAlgebra.Charpoly.BaseChange
Mathlib.LinearAlgebra.DFinsupp
Mathlib.LinearAlgebra.Determinant
Mathlib.LinearAlgebra.Dimension.Free
Mathlib.LinearAlgebra.FreeModule.PID
Mathlib.LinearAlgebra.Matrix.Defs
Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
Mathlib.LinearAlgebra.Matrix.Transvection
Mathlib.LinearAlgebra.Quotient.Pi
Mathlib.Logic.Equiv.PartialEquiv
Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
Mathlib.MeasureTheory.Group.Arithmetic
Mathlib.MeasureTheory.Group.Defs
Mathlib.MeasureTheory.Group.Measure
Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
Mathlib.Order.Filter.Cofinite
Mathlib.RingTheory.AlgebraTower
Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
Mathlib.RingTheory.Henselian
Mathlib.RingTheory.PicardGroup
Mathlib.RingTheory.SimpleModule.IsAlgClosed
Mathlib.RingTheory.SimpleRing.Congr
Mathlib.RingTheory.SimpleRing.Principal
Mathlib.RingTheory.TensorProduct.Basic
Mathlib.RingTheory.TensorProduct.Finite
Mathlib.RingTheory.TensorProduct.Free
Mathlib.RingTheory.TensorProduct.Maps
Mathlib.RingTheory.TwoSidedIdeal.Instances
Mathlib.RingTheory.TwoSidedIdeal.Operations
Mathlib.Tactic.Bound.Init
Mathlib.Tactic.ContinuousFunctionalCalculus
Mathlib.Tactic.NormNum.GCD
Mathlib.Tactic.Positivity.Finset
Mathlib.Topology.Algebra.Algebra.Equiv
Mathlib.Topology.Algebra.Constructions
Mathlib.Topology.Algebra.Group.Units
Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
Mathlib.Topology.Algebra.Module.Equiv.Basic
Mathlib.Topology.Algebra.Module.ModuleTopology
Mathlib.Topology.Algebra.MulAction
Mathlib.Topology.Algebra.RestrictedProduct.Basic
Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
Mathlib.Topology.Bases
Mathlib.Topology.Homeomorph.Lemmas
Mathlib.Topology.Instances.Matrix
```

### Scalar boundary (50 modules)

```text
Mathlib.Algebra.CharZero.Infinite
Mathlib.Algebra.Group.Pi.Units
Mathlib.Algebra.Group.Pointwise.Set.Basic
Mathlib.Algebra.Group.Submonoid.Units
Mathlib.Algebra.Lie.OfAssociative
Mathlib.Algebra.Module.LinearMap.Defs
Mathlib.Algebra.Module.Pi
Mathlib.Algebra.Module.Submodule.Defs
Mathlib.Algebra.Ring.Subring.Basic
Mathlib.CategoryTheory.Category.Init
Mathlib.CategoryTheory.Types.Basic
Mathlib.Data.Nat.Totient
Mathlib.Data.Sym.Sym2.Init
Mathlib.GroupTheory.Index
Mathlib.LinearAlgebra.DFinsupp
Mathlib.LinearAlgebra.Dimension.Free
Mathlib.LinearAlgebra.FreeModule.PID
Mathlib.LinearAlgebra.Matrix.Defs
Mathlib.LinearAlgebra.Quotient.Pi
Mathlib.Logic.Equiv.PartialEquiv
Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
Mathlib.MeasureTheory.Group.Arithmetic
Mathlib.MeasureTheory.Group.Defs
Mathlib.MeasureTheory.Group.Measure
Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
Mathlib.MeasureTheory.Measure.Haar.Unique
Mathlib.NumberTheory.Padics.PadicIntegers
Mathlib.NumberTheory.Padics.ProperSpace
Mathlib.NumberTheory.Padics.RingHoms
Mathlib.Order.Filter.Cofinite
Mathlib.RingTheory.AlgebraTower
Mathlib.RingTheory.Henselian
Mathlib.RingTheory.PicardGroup
Mathlib.RingTheory.SimpleRing.Principal
Mathlib.Tactic.Bound.Init
Mathlib.Tactic.ContinuousFunctionalCalculus
Mathlib.Tactic.NormNum.GCD
Mathlib.Tactic.Positivity.Finset
Mathlib.Topology.Algebra.Algebra.Equiv
Mathlib.Topology.Algebra.Constructions
Mathlib.Topology.Algebra.Group.Units
Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
Mathlib.Topology.Algebra.Module.Equiv.Basic
Mathlib.Topology.Algebra.Module.ModuleTopology
Mathlib.Topology.Algebra.MulAction
Mathlib.Topology.Algebra.RestrictedProduct.Basic
Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
Mathlib.Topology.Bases
Mathlib.Topology.Homeomorph.Lemmas
Mathlib.Topology.Instances.Matrix
```

## Appendix C. Complete private compatibility patch

Apply this patch to the 29 original local files from the pinned source, using
our target environment. It includes the modification notices. No other
original FLT source was changed in the diagnostic adaptation.

```diff
--- a/FLT/HaarMeasure/HaarChar/Padic.lean
+++ b/FLT/HaarMeasure/HaarChar/Padic.lean
@@ -2,6 +2,7 @@
 Copyright (c) 2024 Yaël Dillies, Javier López-Contreras. All rights reserved.
 Released under Apache 2.0 license as described in the file LICENSE.
 Authors: Yaël Dillies, Javier López-Contreras
+Port notice: Worker 90 changed API compatibility details for a private Lean 4.34 audit on 2026-10-21.
 -/
 module
 
@@ -86,8 +87,8 @@
   -- But this is what we proved in `ringHaarChar_padic_padicInt`.
   simp only [eqOn_range, g]
   ext x
-  simp only [MonoidHom.coe_ofClass, Function.comp_apply, MonoidHom.coe_mk,
-    OneHom.coe_mk, Units.val_mk0, coe_nnnorm, PadicInt.norm_coe,
+  simp only [MonoidHom.coe_coe, Function.comp_apply, MonoidHom.coe_mk,
+    OneHom.coe_mk, Units.val_mk0, coe_nnnorm, PadicInt.padic_norm_e_of_padicInt,
     ringHaarChar_padic_padicInt]
 
 @[simp]
--- a/FLT/Mathlib/NumberTheory/Padics/PadicIntegers.lean
+++ b/FLT/Mathlib/NumberTheory/Padics/PadicIntegers.lean
@@ -2,6 +2,7 @@
 Copyright (c) 2024 Yaël Dillies. All rights reserved.
 Released under Apache 2.0 license as described in the file LICENSE.
 Authors: Yaël Dillies, Kevin Buzzard, Pietro Monticone, Ruben Van de Velde
+Port notice: Worker 90 changed API compatibility details for a private Lean 4.34 audit on 2026-10-21.
 -/
 module
 
@@ -32,7 +33,7 @@
 
 lemma coe_injective : Injective ((↑) : ℤ_[p] → ℚ_[p]) := Subtype.val_injective
 
-attribute [simp] coe_inj
+@[simp] lemma coe_inj {x y : ℤ_[p]} : (x : ℚ_[p]) = y ↔ x = y := Subtype.coe_inj
 
 instance : Infinite ℤ_[p] := CharZero.infinite _
 
@@ -55,13 +56,13 @@
     (r : R) : AddSubgroup.comap (algebraMap R A) (r • (1 : Submodule R A).toAddSubgroup) =
     r • (1 : Submodule R R).toAddSubgroup := by
   ext s
-  simp only [AddSubgroup.mem_comap, AddMonoidHom.coe_ofClass,
+  simp only [AddSubgroup.mem_comap, AddMonoidHom.coe_coe,
     AddSubgroup.mem_smul_pointwise_iff_exists, Submodule.mem_toAddSubgroup, Submodule.mem_one,
     exists_exists_eq_and, Ideal.one_eq_top, Submodule.top_toAddSubgroup, AddSubgroup.mem_top,
     smul_eq_mul, true_and]
   apply exists_congr (fun t ↦ ?_)
-  rw [Algebra.smul_def, ← map_mul, Injective.eq_iff]
-  rwa [← faithfulSMul_iff_algebraMap_injective R A]
+  rw [Algebra.smul_def, ← map_mul]
+  exact (FaithfulSMul.algebraMap_injective R A).eq_iff
 
 lemma index_span_p_pow (hx : x ≠ 0) :
     (Submodule.toAddSubgroup (Ideal.span {(p : ℤ_[p]) ^ x.valuation})).index =
--- a/FLT/Mathlib/Topology/Algebra/Module/Quotient.lean
+++ b/FLT/Mathlib/Topology/Algebra/Module/Quotient.lean
@@ -2,11 +2,12 @@
 Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
 Released under Apache 2.0 license as described in the file LICENSE.
 Authors: Salvatore Mercuri, Kevin Buzzard, Pietro Monticone
+Port notice: Worker 90 changed API compatibility details for a private Lean 4.34 audit on 2026-10-21.
 -/
 module
 
 public import Mathlib.LinearAlgebra.Quotient.Pi
-public import Mathlib.Topology.Algebra.Module.Equiv.Basic
+public import Mathlib.Topology.Algebra.Module.Equiv
 
 /-!
 # Quotient
```
