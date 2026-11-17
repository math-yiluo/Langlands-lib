# Idelic class field theory: consumers of `FiniteAbelianClassFieldStatement` and an audit of NYLL's global theory

Worker 96 and Worker 818 prepared this note for Task 7345 (`d60e084d-9218-49be-9468-da445fab6919`, revision 1). Worker 96 wrote sections 1 to 4 and 7. Worker 818 wrote sections 5 and 6, which are merged here with small edits. The note answers the three deliverables of the task:

1. which declarations on Task 0's route use the Library's `Langlands.Global.FiniteAbelianClassFieldStatement` (interface F of the operator's plan note, §2.6 and §4.4) or its five clauses, and whether the Library's proved class-formation form of reciprocity suffices for them;
2. an audit of the global class field theory of NYLL (Naganori Yamaguchi's repository `n-yamaguchi-0729/ClassFieldTheory`) at the commit followed by the Library's port, `fbd320cd`, and at its head, `b9a2dddb`;
3. a recommendation. Section 7 also records the operator's decision on it (17 November 2026).

The note accepts no external theorem and imports no external code into the Library. All Lean checks ran privately in the project's Lean service. Their records are in [the evidence directory](nyll-global-cft-evidence/): [edits.md](nyll-global-cft-evidence/edits.md), [diagnostics.md](nyll-global-cft-evidence/diagnostics.md) and [closure.md](nyll-global-cft-evidence/closure.md).

**Verdict.**

- **No consumer.** No Library declaration uses the statement or any of its five clauses. In the planning graph, the only node that depends on the node of the statement is the node of `ArtinNormComparisonStatement`, and no node depends on that one. Where the route uses global class field theory, it uses the class-formation form, which is proved. The one natural future consumer is `WeakEquivalenceRigidityStatement` (Henniart 2000, §2.2), which is itself unused.
- **The class-formation form does not give the clauses.** It identifies the abelianized relative Weil group with the idele class group as abstract groups. It gives no continuity, no Frobenius normalization, no uniqueness and no existence theorem.
- **What NYLL has (both commits).** NYLL has the arithmetically normalized idelic Artin map of a finite abelian extension, with kernel equal to the norm group, surjective and continuous. Its Frobenius property is proved only at one chosen uniformizer per place. NYLL also has open subgroups containing congruence subgroups, and the class field of a closed subgroup of finite index, constructed as a separate type. NYLL does not have the uniqueness of the Artin map, its Frobenius property at an arbitrary uniformizer, class fields as subfields of `AlgebraicClosure K`, kernel rigidity in the Library's form, or the clause on Hecke characters.
- **Normalization and bridge.** NYLL's `arithmetic…` maps are the inverses of its geometric `globalNormResidue…` maps, and they send the chosen uniformizer to Mathlib's arithmetic Frobenius, which is the Library's normalization. NYLL's comparison equivalence lands in Mathlib's `NumberField.IdeleClassGroup`, and the Library's `IdeleClasses` abbreviates that group. The bridge is therefore definitional, and it sends NYLL's one-place idele classes to the Library's `finiteClassInclusion` (checked in Lean).
- **Compilation.** The 957-module import closure of the six NYLL modules we need (402,173 lines) compiles on the Library's pin (Lean 4.34.0) with 14 small edits in 14 files. The NYLL declarations of section 3 that a proof would use depend only on the standard axioms (section 4.3). The closure imports together with all 1749 modules of the Library's NYLL port with no clash at import.
- **What remains for us.** These are short lemmas on the Library's side: almost-everywhere uniqueness, finiteness of ramified places, the arbitrary-uniformizer glue, transport along a K-isomorphism, and restriction of Frobenius. With commit `fbd320cd` a universe transport is also needed. Clause 2 needs no class field theory, and clause 5 is formal from clause 3.
- **What the route lacks instead.** The cyclic base-change statements assume a Hecke character `η` with `η.HasNormKernel E`, and no Library declaration produces one. The Library already proves that the idele-class norm image is open and of finite index. What is missing is that for cyclic `E/F` the quotient is cyclic of order `[E : F]`, and the character this gives. Both follow from the proved class-formation form, without interface F (section 1.4).
- **Recommendation (as filed).** Defer interface F until it has a consumer. If partial progress is wanted, prove clause 2 and the uniqueness lemmas from the Library alone. If F is wanted in full, use NYLL's head as a dependency once the Library moves to Mathlib `56a00585` (the plan note's configuration B, mode D). Otherwise use an adapted copy of `fbd320cd` (mode F). Prefer a dependency (D or F) to a port; use a light port only if package pins cannot be added (plan note §5.4).
- **Operator's decision (17 November 2026; section 7.1).** Interface F is deferred: no NYLL import, the statement stays unproved, and its planning node and that of `ArtinNormComparisonStatement` are off the route. It reopens when a statement on the route needs the Frobenius-normalized idelic Artin map itself. In particular this happens if a proof of `WeakEquivalenceRigidityStatement` (Henniart 2000, §2.2) enters the route. Then lemmas U and R come first, followed by only those clauses of F that the proof uses. For that day the source is NYLL's head `b9a2dddb`, as a package dependency (mode D) after the Library's move to its Mathlib. Until then there is no adapted copy of `fbd320cd` and no light port. One task is published now for the norm-kernel character.

## 1. The consumers

### 1.1 The statement

`Langlands/Global/Arithmetic/ClassFieldStatement.lean` (Library commit `fcb85a7ef43356fec01e6ccf1605f08568c08cb0`) defines the predicate `HasArithmeticArtinNormalization` (line 27) and five clauses:

| Clause | Declaration (line) | Content |
|---|---|---|
| 1 | `FiniteAbelianArtinReciprocityStatement` (41) | For a finite Galois extension `L/K` with commutative Galois group (`K : Type u`, `L : Type v`), there is exactly one continuous `ρ : IdeleClasses K →ₜ* (L ≃ₐ[K] L)` (discrete topology on the target) that is surjective and sends every uniformizer `π` of `K_v` (`Valued.v π = exp(-1)`) to an arithmetic Frobenius at every prime `w` above `v` that is unramified over `K`. |
| 2 | `OpenIdeleClassSubgroupFiniteIndexStatement` (51) | Open subgroups of `IdeleClasses K` have finite index. |
| 3 | `FiniteAbelianClassFieldExistenceStatement` (57) | Every open subgroup of finite index is the kernel of a normalized surjective `ρ` for some finite abelian Galois `L`, an `IntermediateField K (AlgebraicClosure K)`. |
| 4 | `FiniteAbelianClassFieldKernelRigidityStatement` (74) | Two finite abelian Galois subfields `L, E` of `AlgebraicClosure K` with normalized surjective maps of equal kernels are equal. |
| 5 | `FiniteOrderHeckeArtinRealizationStatement` (94) | A Hecke character of finite order is `θ ∘ ρ` for an injective continuous `θ` on the Galois group of some finite abelian `L ⊆ AlgebraicClosure K` with normalized surjective `ρ`. |

`FiniteAbelianClassFieldStatement` (line 112) is the conjunction. Clause 1 asserts neither that the kernel is the norm group nor anything about infinite places. The kernel is the separate `ArtinNormKernelStatement` (`ArtinNormStatement.lean:20`).

### 1.2 Uses in Lean

A search of all Lean files of the Library at `fcb85a7e` for the seven names gives:

- No declaration uses `FiniteAbelianClassFieldStatement` or any of the five clauses.
- The predicate `HasArithmeticArtinNormalization` occurs as a hypothesis in `Langlands/Global/Arithmetic/ArtinNormStatement.lean`: in `ArtinNormKernelStatement` (line 27) and in `HeckeNormFactorizationStatement` (line 68), both parts of `ArtinNormComparisonStatement` (line 75). That file is the only importer of `ClassFieldStatement.lean`, and no Lean file imports it.

### 1.3 Uses in the planning graph

In the shared DAGs at revision 400 (the same edges as at revision 398), edges point from a node to the nodes it uses. One node uses `proof.finite-abelian-global-reciprocity` (the statement above): `proof.global-artin-norm-comparison` (the node of `ArtinNormComparisonStatement`; the edge reads "uses the exact arithmetic normalization predicate and the separately asserted normalized map existence"). No node uses `proof.global-artin-norm-comparison`. So neither node is on a path from Task 0's root.

### 1.4 What the route uses instead

Where the route needs global class field theory, it uses the class-formation form, which the Library has proved:

- `Langlands.ClassField.Global.globalFundamentalClassStatement` (`ClassField/Global/FundamentalClassProof.lean:35`): `H¹(Gal(E/F), C_E) = 0` and a unique coherent family of global fundamental classes. It is used, for example, by `candidateExistenceReduction` (`Correspondence/HenniartCandidateExistenceReductionProof.lean:28`).
- `relativeWeilTransferReciprocity` (`ClassField/Global/RelativeWeilTransferReciprocityProof.lean:85`): for the arithmetic class family, the transfer `W_{E/F} →* C_F` (`RelativeWeilTransfer.lean:241`) is surjective with kernel the commutator subgroup. It is used by `transferCharacterFactorization` (`ClassField/Global/RelativeWeilCharacterFactorization.lean:99`), which is used in turn in `Automorphic/AssociatedCentralCharacter/DeterminantDescent.lean`, `Global/Factors/RelativeWeilFunctionalEquationAssembly.lean` and `LocalFactor/BrauerKernel/GlobalAssembly.lean`. The reciprocity character `reciprocityCharacter` of the determinant step (`Automorphic/AssociatedDeterminantTwistStatement.lean:31`) is defined from the transfer.

Two further points:

- **Characters with norm kernel.** The cyclic base-change statements (`Automorphic/Unramified/CyclicTransferStatement.lean`, `IsobaricCyclicTransferStatement.lean`, `CyclicTransferInputsTCStatement.lean`) quantify over Hecke characters `η` with `η.HasNormKernel E` (`CyclicTransferStatement.lean:29`): `η x = 1` exactly on the image of the idele-class norm from `E`. To apply them one needs such an `η` for a cyclic `E/F`, and no Library declaration produces one. Its existence says that the norm image is open with cyclic quotient of order `[E : F]`. The first part is in the Library:
  - `Langlands.Global.AdelicFunctoriality.isOpenMap_ideleClassNorm` (`Global/AdelicFunctoriality/IdeleNormOpen.lean:414`) states that the idele-class norm `C_E → C_F` is an open map, for every extension, in independent universes. So its image is open, and closed as an open subgroup.
  - `ideleClassNormIndexFinite` (`Global/AdelicFunctoriality/IdeleClassNormIndexFiniteProof.lean:13`) states that the image has finite index dividing a power of `[E : F]`.

  What is missing is that the quotient is cyclic of order `[E : F]` when `Gal(E/F)` is cyclic. This follows from the proved class-formation form: the transfer identifies `W_{E/F}^ab` with `C_F` and restricts to the norm on `C_E` (`transfer_comp_inclusion`, `ClassField/Global/RelativeWeilCharacterFactorization.lean:34`), which gives `C_F / N(C_E) ≅ Gal(E/F)^ab`. The hypotheses of `relativeWeilTransferReciprocity` are discharged by proved theorems, not open premises: `Langlands.ClassFieldTheory.Local.localRelativeClassFormation` (`ClassFieldTheory/Local/LocalRelativeClassFormationProof.lean:16`) gives the local invariant family `I` with class formation and arithmetic normalization, and `globalFundamentalClassStatement.2` applied to `I` gives the class family, as in `candidateExistenceReduction` (lines 31-36, where the local class formation is still a hypothesis). `RelativeWeilGroup.index_range_inclusion` (`ClassField/Global/RelativeWeilGroup.lean:68`) gives `C_E` index `[E : F]` in `W_{E/F}`. No Library declaration states this quotient yet. It needs neither the Frobenius normalization nor the uniqueness nor the existence theorem of interface F. (The version of this note filed with request `07efe25f` wrongly said that the Library does not state the openness.)
- **The one natural future consumer.** `WeakEquivalenceRigidityStatement` (`Automorphic/AssociatedUniquenessStatement.lean:81`; Henniart 2000, §2.2) is part of `AssociatedUniquenessStatement` (line 118). It says that weakly equivalent continuous semisimple representations of `W_{E/F}` are equivalent. We expect a proof to pass from `W_{E/F}` to Galois groups of finite abelian extensions and to use Chebotarev. That step would use the normalized reciprocity map, existence and the realization of finite-order characters, that is, clauses 1, 3 and 5. No Lean file imports `AssociatedUniquenessStatement.lean`.

### 1.5 Clause by clause

| Clause | Lean uses | Planning graph | Does the proved class-formation form suffice? |
|---|---|---|---|
| 1 Artin reciprocity | none (the predicate only, in `ArtinNormStatement.lean`, which nothing imports) | used only by `proof.global-artin-norm-comparison`, which nothing uses | No. It gives `W_{E/F}^ab ≅ C_F` as abstract groups, but not continuity, the Frobenius normalization or uniqueness. |
| 2 Finite index | none | as clause 1 | Not needed: clause 2 is a topological fact about `C_K`, proved from compactness of norm-one classes (section 6). |
| 3 Existence | none | as clause 1 | No: the class-formation form has no existence theorem. |
| 4 Kernel rigidity | none | as clause 1 | No: it needs clause 1 (normalization and uniqueness) and Galois theory (section 6). |
| 5 Finite-order characters | none | as clause 1 | No: it follows from clause 3. |

So no clause is consumed on the route today, and what the route uses is proved, except the existence of `η` with `HasNormKernel`, which is independent of F (the task of section 7.1).

## 2. Pins, sources, licence and closures

| Item | NYLL `fbd320cd` | NYLL head | Library |
|---|---|---|---|
| Commit | [`fbd320cd8b1b06487c58227e92eb135794267709`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709) (21 Oct 2026) | [`b9a2dddbf076eb96b768c333fd828d339ab3d9eb`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/b9a2dddbf076eb96b768c333fd828d339ab3d9eb) (13 Nov 2026) | `fcb85a7ef43356fec01e6ccf1605f08568c08cb0` |
| Lean | `v4.35.0-rc2` | `v4.35.0` | `v4.34.0` (environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`) |
| Mathlib | `065356127b1dc0016f66b7283ce0ce2c4055aa55` | `56a005855ea1…` | `5ed2965256430c3649e86755f9576b54eca72435` |
| Module system | no | every file (`module`, `public import`) | no |

**Sources.**

- `fbd320cd`: registered source `external-lean-reuse-snapshots-2026-10-21`, folder `n-yamaguchi-0729--ClassFieldTheory/source`, with `nyll-classfieldtheory-fbd320cd-supplement` for the omitted non-Lean files.
- Head: a clone of the GitHub repository at the commit above (Worker 96), and a GitHub tarball of the same commit, 8,024,436 bytes, SHA-256 `c8e58c5d73decfcea1a79f7bf4ecfb5f358bd42f3ff3ab27aa5bb71d2bb022dd` (Worker 818). The head is not registered as a literature source. Every head reference in this note names the commit.

**Licence.** Both commits carry the Apache-2.0 `LICENSE` and a `NOTICE`. All 957 files of the compiled closure carry the header "Copyright (c) 2026 Naganori Yamaguchi" and are released under Apache 2.0. None of them is among the third-party files listed in `NOTICE` (Christian Merten's pi1 files and the Anthropic FLT directories). A dependency or a copy has to keep `LICENSE`, `NOTICE` and the file headers.

**Closures.** These are textual import closures (comments stripped; `import` and `public import` followed). Counts include the roots.

| Roots | `fbd320cd` | head |
|---|---|---|
| `GlobalClassFieldTheory.All` | 1084 modules, 426,467 lines | 1199 modules, 450,348 lines |
| `Theorems.GlobalClassFieldTheory.All` | 986 modules, 404,460 lines | 1102 modules, 427,959 lines |
| The six roots needed for interface F (below) | 957 modules, 402,173 lines | 1073 modules, 425,202 lines |

The six roots, under `Nyll.ClassFieldTheory.`, are:

- `GlobalClassFieldTheory.GlobalClassFields.MathlibGlobalReciprocity`
- `GlobalClassFieldTheory.GlobalClassFields.MathlibFrobeniusHilbertComparison`
- `GlobalClassFieldTheory.Reciprocity.ArithmeticNormalization`
- `GlobalClassFieldTheory.Reciprocity.FiniteIdeleArtin`
- `AlgebraicNumberTheory.Idele.ClassGroup.MathlibTopologyComparison`
- `AlgebraicNumberTheory.RayClass.Topology`

Their closure at `fbd320cd` has 408 external imports: 403 Mathlib modules, `Batteries.Tactic.Init` and four Lean core modules. Its aggregate hash and module list are in [closure.md](nyll-global-cft-evidence/closure.md). The plan note's figure of 1199 modules and 450,000 lines for the head is confirmed.

## 3. Which NYLL theorem gives which clause (`fbd320cd`)

Paths are under `Nyll/ClassFieldTheory/` at `fbd320cd`. Full signatures, as printed by Lean on the Library's pin, are in [diagnostics.md](nyll-global-cft-evidence/diagnostics.md), section 2. Head line numbers are in section 5.

### 3.1 Clause 1 and the normalization

- **The map.** `GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom K L : IdeleClassGroup K →* Gal(L/K)` (`GlobalClassFieldTheory/Reciprocity/ArithmeticNormalization.lean:206`), for `K L : Type` number fields with `[FiniteDimensional K L] [IsAbelianGalois K L]`. By definition it is the geometric `globalNormResidueMonoidHom K L` followed by inversion. The `simp` lemma `arithmeticGlobalNormResidueMonoidHom_apply` (lines 213-218) states this and is proved by `rfl`.
- **Kernel, surjectivity, continuity.** `_ker`: the kernel is `(ideleClassNorm K L).range` (line 222). `_surjective` (line 231). `_continuous` (line 239), for the idele-class topology and the Krull topology on `Gal(L/K)`.
- **Normalization at a chosen uniformizer.** The following steps give the Frobenius property at one chosen uniformizer:
  1. `arithmeticGlobalNormResidueMonoidHom_comp_finitePlaceIdeleClass` (`ArithmeticNormalization.lean:332`): the global map restricted to the place `v` is NYLL's chosen local map `arithmeticChosenFinitePlaceArtinMonoidHom K L v`.
  2. `arithmeticFinitePlacePrimeArtin_eq_arithmeticChosenFinitePlaceArtin` (`GlobalClassFieldTheory/GlobalClassFields/ArithmeticUnramifiedPrimeArtin.lean:50`): the value at `FiniteIdeleGroup.chosenLocalOrderSection v 1` is the prime Artin element `arithmeticFinitePlacePrimeArtin v`.
  3. `ClassFieldTheory.GlobalClassFieldComparison.arithmeticPrimeArtin_eq_arithmeticFrobeniusAt` (`GlobalClassFieldTheory/GlobalClassFields/MathlibFrobeniusHilbertComparison.lean:331`): for every `w` lying over `v` with `Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal`, the prime Artin element equals `arithmeticFrobeniusAt w`. This is Mathlib's `arithFrobAt (𝓞 K) (L ≃ₐ[K] L) w.asIdeal` (`Definitions/FrobeniusAndHilbertClassFields/ArithmeticFrobeniusAt.lean:29`).

  `chosenLocalOrderSection v 1` is a `Classical.choose` element of valuation `exp(-1)`, so these steps give the Frobenius property at one uniformizer per place.
- **Units.** `chosenFinitePlaceArtinMonoidHom_eq_one_of_integral_of_unramifiedAt` (`GlobalClassFieldTheory/Reciprocity/FiniteIdeleArtin.lean:194`): at a place that is unramified at NYLL's chosen prime above `v`, the local map kills units. With it, the Frobenius property extends to every uniformizer (section 6.3, gap 2).
- **Not in NYLL:** the uniqueness of the map, and the Frobenius property at an arbitrary uniformizer.

The plan note (§4.4) asks whether NYLL's idelic map is geometric. It is: `globalNormResidueMonoidHom` sends the chosen uniformizer to the inverse of the arithmetic Frobenius, and the `arithmetic…` maps used above carry the Library's arithmetic normalization.

Two wrappers state reciprocity without a named map, so they are not what interface F needs:

- `Theorems/GlobalClassFieldTheory/FiniteAbelianGlobalReciprocity.lean:31` gives `Nonempty (FiniteAbelianReciprocityData K L)`: some ray class map with prime classes sent to `arithmeticFrobeniusAt`.
- `ClassFieldTheory.GlobalClassFieldComparison.finiteAbelianGlobalReciprocity` (`MathlibGlobalReciprocity.lean:293`) gives `Nonempty (IdeleClassGroup K ⧸ (ideleClassNorm K L).range ≃ₜ* Gal(L/K))`.

### 3.2 Clause 2

`RayClass.exists_congruenceSubgroup_le_of_isOpen` (`AlgebraicNumberTheory/RayClass/Topology.lean:977`) states that every open subgroup of `IdeleClassGroup K` contains the congruence subgroup of some modulus. The instance `congruenceSubgroupFiniteIndex` (line 927) states that congruence subgroups have finite index. `isClosed_and_finiteIndex_iff_exists_congruenceSubgroup_le` (line 1084) is the closed form, which is Neukirch VI (1.8). With the bridge these give clause 2. Section 6 gives a proof from the Library alone.

### 3.3 Clause 3

`GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassField H hclosed` (`GlobalClassFieldTheory/GlobalClassFields/ClosedFiniteIndexClassFieldConstruction.lean:105`) is the class field of a closed subgroup `H` of finite index. Two theorems describe it:

- `classFieldExistence_normSubgroup` (`MathlibGlobalReciprocity.lean:267`): its norm range is `H`.
- `classFieldExistence_degree` (`MathlibGlobalReciprocity.lean:280`): its degree is the index of `H`.

The class field is a separate `Type` (universe 0), not an `IntermediateField K (AlgebraicClosure K)`.

### 3.4 Clauses 4 and 5

NYLL has no counterpart in the Library's form. Its injectivity of norm groups (`ordinaryIdeleClassNormSubgroup_injective`, section 5) is stated for abstract fixed fields over `SeparableClosure ℚ`, and nothing concerns Hecke characters. Both clauses are short consequences of clauses 1 and 3 (section 6).

### 3.5 The bridge

`IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K : IdeleClassGroup K ≃ₜ* NumberField.IdeleClassGroup (𝓞 K) K` (`AlgebraicNumberTheory/Idele/ClassGroup/MathlibTopologyComparison.lean:40`) is NYLL's comparison with Mathlib's idele class group. The Library's `IdeleClasses K` is an `abbrev` for `NumberField.IdeleClassGroup (NumberField.RingOfIntegers K) K` (`Langlands/Global/Adelic.lean:51`). So the equivalence has type `IdeleClassGroup K ≃ₜ* IdeleClasses K` with no conversion, on a common pin. `ideleClassGroupEquivMathlib_finitePlaceIdeleClass` (`MathlibComparison.lean:102`) sends NYLL's one-place idele class to Mathlib's `IdeleClassGroup.ofAdicCompletion`, which is what the Library's `finiteClassInclusion` (`Adelic.lean:137`) unfolds to. Both facts are checked in Lean (`NyllCoexistDiag`, section 4.4):

```lean
noncomputable example (K : Type) [Field K] [NumberField K] :
    _root_.IdeleClassGroup K ≃ₜ* IdeleClasses K :=
  IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K

example (K : Type) [Field K] [NumberField K] (v : FinitePlace K)
    (x : (FiniteCompletion K v)ˣ) :
    IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K
        (IdeleGroup.finitePlaceIdeleClass v x) = finiteClassInclusion K v x :=
  IdeleGroup.ideleClassGroupEquivMathlib_finitePlaceIdeleClass K v x
```

### 3.6 Universes

At `fbd320cd` the Artin map and its theorems, the Frobenius comparison, the unit lemma and the class-field theorems all take `K L : Type` or `K : Type`. The bridge and `exists_congruenceSubgroup_le_of_isOpen` are universe-polymorphic. The Library's clauses take `K : Type u` and `L : Type v`. With `fbd320cd`, clauses 1 and 3 therefore need a transport to universe 0. At head the global theorems are universe-polymorphic (section 5).

## 4. Compilation on the Library's pin

### 4.1 Method

The 957 modules of the six-root closure at `fbd320cd` were copied, with `LICENSE` and `NOTICE`, into a private draft directory and compiled with `lean_check` on environment `5c94c648` (Lean 4.34.0, Mathlib `5ed29652`). Each call has a 30-minute limit, and one call on the six roots from scratch exceeded it. The closure was therefore built in six layers of increasing import depth: depth at most 15, 30, 59, 75 and 95, then everything. The service's build cache kept the earlier layers. Every layer ended with no error and no warning. The last one, `913786b0-382e-4a71-b6b4-d1fd193018ff`, built the six roots in 791 s. The diagnostics are listed in [diagnostics.md](nyll-global-cft-evidence/diagnostics.md), section 1.

Worker 818 made an independent check of the unchanged files. A build of the 986-module closure of `Theorems.GlobalClassFieldTheory.All`, with every file byte-identical to the snapshot (diagnostic `d089a2df-620c-452f-befe-8f63aee06539`, 235 s), fails in exactly five first-layer modules: `NormProperties`, `HenselianFinite`, `KummerDelta`, `ValuedAdicComplete` and `CyclicValueGroup`. These agree with the first-layer edits below. A textual scan found no `sorry`, `axiom`, `set_option`, `module`/`public import`, `native_decide` or `implemented_by` in that closure.

### 4.2 The edits

There are 14 edits, in 14 files and 22 hunks. The full diff is in [edits.md](nyll-global-cft-evidence/edits.md). They fall into five kinds:

| Kind | Files (hunks) | Change |
|---|---|---|
| A valuation used as a `→*₀` map (Mathlib changed the coercion) | `ValuedFieldTheory/LocalField/Analytic/ContinuousFieldUnitLog` (1), `.../LogExpSeries/ExpConvergence` (2), `.../LogExpSeries/SeriesTerms` (3), `.../ValuationSubringUnits/CyclicValueGroup` (1), `.../ValuationSubringUnits/RangeRestrictedTopology` (1), `.../ValuationSubringUnits/UniformizerIntegerValuation` (1), `ValuedFieldTheory/Valuation/ValuedAdicComplete` (1) | `(v : R →*₀ Γ)` or `v.ValueGroup₀` becomes `MonoidWithZeroHom.ofClass v`. In `ValuedAdicComplete`, `have` becomes `let` for the `MulArchimedean` instance. |
| `Valuation.map` takes a monotonicity argument at the pin | `ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormalizedIntegerValuation` (2) | `localIntegerValuation` is restated with `MonoidWithZeroHom.ofClass` and `….toOrderIso.monotone`. It is the same map. A `simp` proof of surjectivity becomes `rw` and `apply_symm_apply`. |
| A Mathlib name absent at the pin | `GaloisCohomology/Kummer/Abstract/KummerDelta` (5), `ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/MaximalUnramifiedSymbol` (1), `ValuedFieldTheory/Valuation/DiscreteValuationField/HenselianFinite` (1), `.../ValuationSubringUnits/CompleteRangeRestriction` (1) | `AddMonoidHom.ofClass` becomes `AddMonoidHomClass.toAddMonoidHom` (6 occurrences). `MonoidHom.coe_ofClass` becomes `MonoidHom.coe_coe`. `rw [IsConcreteLE.le_iff]` becomes `change`. A rewrite by `Valuation.ofClass_eq_toMonoidWithZeroHom` is deleted, since the goal is already in that form. |
| A Mathlib declaration with a stronger type at the pin | `ClassFieldTheory/AlgebraicNumberTheory/Completion/IntegerRingComparison` (1) | `IsLocalization.AtPrime.equivQuotMaximalIdeal` is already a ring equivalence, so `.toRingEquiv` is dropped. |
| Tactic behaviour | `ClassFieldTheory/AlgebraicNumberTheory/Idele/Extension/NormProperties` (1) | `convert … using 1; rfl` becomes `convert … using 1 <;> rfl`. |

Most edits are inside proofs. Three touch definitions or statements, without changing what they denote: in `KummerDelta`, two definitions and two hypotheses name the coercion of `wp.hom` to an additive homomorphism by `AddMonoidHomClass.toAddMonoidHom` instead of `AddMonoidHom.ofClass`; `localIntegerValuation` keeps its name and type and denotes the same valuation; and the equivalence defined in `IntegerRingComparison` is the same map without the conversion. None of the declarations of section 3 is edited. The plan note's configuration A (§5.5) calls the global closure "untried"; it has now been tried, and needs 14 edits where the local closure needed nine.

### 4.3 Declarations and axioms

The module `NyllGlobalDiag` imports the six roots and prints the signatures and axioms of nineteen declarations (diagnostic `3c6e5461-795a-465e-affe-39d3a25b0652`; list and output in [diagnostics.md](nyll-global-cft-evidence/diagnostics.md), section 2). Each of the nineteen depends only on `propext`, `Classical.choice` and `Quot.sound`. Since `#print axioms` follows the definitions a declaration mentions, this also covers the definitions in their statements. Together these are every NYLL declaration named in section 3 except the wrapper `Theorems/GlobalClassFieldTheory/FiniteAbelianGlobalReciprocity.lean:31` and `ordinaryIdeleClassNormSubgroup_injective`, which a proof of the clauses would not use. The universe levels are as stated in section 3.6.

### 4.4 Coexistence with the Library

The plan note asks for a test that one module can import both NYLL's closure and the Library's port of NYLL's local theory, since the port reuses NYLL's names under `Langlands.NYLL.*` and `Langlands.ClassFieldTheory.Local.NYLL.*`. Two modules were checked at Library commit `fcb85a7e`:

- `NyllCoexistDiag` (diagnostic `63bbdfc1-cdab-4be0-96e7-c73ce19c42fd`) imports `ClassFieldStatement.lean`, four modules of the port and the six NYLL roots, and checks the two bridge facts of section 3.5.
- `NyllCoexistFullDiag` (diagnostic `0390f87b-26e0-4e6a-a671-a54868109762`) imports `ClassFieldStatement.lean`, all 1749 modules of the Library's port (through its 620 maximal modules) and the six NYLL roots.

Both checks gave no error and no warning. There is no clash of declaration names at import. The check does not show how NYLL's instances and `simp` lemmas affect the elaboration of Library proofs that import the closure; that shows only when such proofs are written. By a textual count (Worker 818), the 957 modules contain about 690 instance declarations not marked `scoped` or `local` (plus 425 scoped or local ones and 105 `attribute [… instance …]` lines) and about 1,960 `simp` attributes. The plan note's figures of 220 and 900 (§5.4) refer to the closure of the local theory.

## 5. NYLL head `b9a2dddb` against `fbd320cd` (Worker 818)

Paths are under `Nyll/ClassFieldTheory/` at head. Every head file uses `module`, `public import` and `@[expose] public section`. With that syntax stripped, the normalized diff shows 245 changed common files in the global, theorem and definition directories, 8 new global files and none removed. The repository has 3820 files at head and 3129 at `fbd320cd`.

- **Universes.** `fbd320cd`'s global theorems take `K L : Type`. Head takes `K : Type u` and `L : Type v`. Examples:
  - `Theorems/GlobalClassFieldTheory/FiniteAbelianGlobalReciprocity.lean:35`.
  - `GlobalClassFieldTheory/Reciprocity/ArithmeticNormalization.lean:211` `arithmeticGlobalNormResidueMonoidHom`, with `_ker` :227, `_surjective` :236, `_continuous` :244, finite-place compatibility :337 and infinite places :386.
  - `GlobalClassFields/MathlibGlobalReciprocity.lean:275` `classFieldExistence_normSubgroup`, :288 `_degree` and :301 the quotient reciprocity.
  - New file `GlobalClassFields/UniverseNormConductor.lean` (the norm range is open, in any universe).
- **New at head: an Artin map on Mathlib's group.**
  - `Reciprocity/MathlibTopologicalGlobalReciprocity.lean:96` `mathlibGlobalArtin (K : Type u) : NumberField.IdeleClassGroup (𝓞 K) K →ₜ* Field.absoluteGaloisGroupAbelianization K`, in geometric normalization. `_surjective` is at :117, and `_ker = connectedComponentOfOne` at :124. The Library's `IdeleClasses K` is an `abbrev` for this group.
  - Naturality, in the new file `Reciprocity/MathlibGlobalArtinNaturality.lean`: :170 `mathlibGlobalArtin_toMaximal`; :180 `_finiteProjection` (restriction to `E ⊆ maximalAbelianExtension K` is NYLL's finite Artin map); `_finiteProjection_of_scalarTower` (any `L : Type w` embedded in `maximalAbelianExtension K`); :212 `_baseEquiv`.
  - Also new: `GlobalClassFields/MathlibGlobalArtinRayComparison.lean:40`, and `FiniteReciprocityDataComparison.lean:78` `ideleClassArtin` with :94 `_eq_arithmeticGlobalNormResidue`.
- **Class fields in a fixed closure.**
  - `GlobalClassFields/InfiniteAbelianClassFieldCorrespondence.lean:113` is an order isomorphism `(ClosedSubgroup (C_K/D_K))ᵒᵈ ≃o IntermediateField K (maximalAbelianExtension K)`. It is present at `fbd320cd` (:108).
  - New at head: :237 `_eq_finiteLayer_iff` (the field is `E` if and only if the pulled-back `H` is the norm range of `E`, for `E` finite Galois inside `maximalAbelianExtension K`); :191 `maximalAbelianGlobalArtin_comap_fixingSubgroup`; :271 `_eq_closedFiniteIndexClassField`.
  - `maximalAbelianExtension K` is an `IntermediateField K (SeparableClosure K)` (`AlgebraicNumberTheory/Galois/AbsoluteAbelianization.lean:51`), not one of `AlgebraicClosure K`.
  - `closedFiniteIndexClassField H hclosed` is still a separate `Type` in universe 0 (`ClosedFiniteIndexClassFieldConstruction.lean:113`). It has `Algebra` and `IsAbelianGalois` instances over the original `K : Type u` (`ClosedFiniteIndexClassFieldOriginalField.lean:63-207`).
- **Injectivity of norm groups** exists only in abstract class-formation form over `SeparableClosure ℚ`: `ordinaryIdeleClassNormSubgroup_injective` in `FiniteAbelianClassFieldCorrespondence.lean` (head :206, `fbd320cd` :200).
- **Uniqueness of the Artin map.** Neither commit states a global uniqueness; the only `∃!` is the conductor's. At the level of ray classes there is `Theorems/ConductorsAndRayClassFields/RayClassGroupHomExtFinitePrime.lean:31` `rayClassGroup_hom_ext_finitePrime`.
- **Normalization** is still proved only at the chosen section `FiniteIdeleGroup.chosenLocalOrderSection v 1`. This is a `Classical.choose` element with `Valued.v = exp(-1)`, that is, a Mathlib uniformizer (`AlgebraicNumberTheory/Idele/IdealMap.lean:97`, via `Algebra/RestrictedProduct/Valuation.lean:85`). The relevant results are:
  - `Reciprocity/FinitePlaceArtin/UnramifiedNormalization.lean:67`;
  - `GlobalClassFields/ArithmeticUnramifiedPrimeArtin.lean:57,110`;
  - `GlobalClassFields/MathlibFrobeniusHilbertComparison.lean:345` `arithmeticPrimeArtin_eq_arithmeticFrobeniusAt`, for any `w | v` with `LiesOver` and `IsUnramifiedAt (𝓞 K) w.asIdeal`, with value Mathlib's `arithFrobAt`;
  - `Theorems/FrobeniusAndHilbertClassFields/ArithmeticFrobeniusIsArithmetic.lean`, in the group form `IsArithFrobAt`, whereas the Library uses `(RingOfIntegers.mapAlgHom σ).IsArithFrobAt`.

  Units are trivial at unramified places: `Reciprocity/FiniteIdeleArtin.lean:165` (`fbd320cd` :194). Neither commit states the form with an arbitrary uniformizer.
- **Bridge.** `AlgebraicNumberTheory/Idele/ClassGroup/MathlibComparison.lean:106` `ideleClassGroupEquivMathlib_finitePlaceIdeleClass` and `MathlibTopologyComparison.lean:44` `ideleClassGroupContinuousMulEquivMathlib` are the head counterparts of `fbd320cd` :102 and :40.

**Buildability probe of head on the Library's pin** (environment `5c94c648`). The private draft holds the 86 head modules that form the closure of `AlgebraicNumberTheory.Idele.ClassGroup.MathlibTopologyComparison` and `Definitions.FrobeniusAndHilbertClassFields.ArithmeticFrobeniusAt`, byte-identical to head. In diagnostic `e3f278b9-d133-45fb-9f78-a89f8194277c` the module syntax is accepted on the pin, since the pinned Mathlib itself uses the module system, and most modules build. There are 10 errors in 4 modules:

- `Idele/Extension/NormProperties:46`: the same unsolved product goal as at `fbd320cd`, which the `<;> rfl` edit fixes.
- `GaloisCohomology/Cyclic/NormKernelVanishing:7`: it imports `Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup`, which does not exist at the pin.
- `GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/TateComparison:119,288`: `Representation.norm_ofMulDistribMulAction_eq` is universe-monomorphic at the pin.
- `ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Norm:93,101,259`: `MonoidHom.coe_ofClass` is unknown.

Conclusion: head targets a newer Mathlib, and the drift already shows in its bottom 86 modules. Porting head to the pin means patching this drift on top of `fbd320cd`'s edits. The alternative is to wait for a Mathlib bump of the Library. For interface F, head has two advantages over `fbd320cd`: universe generality, which removes the universe transport entirely, and `mathlibGlobalArtin` defined directly on Mathlib's idele class group.

## 6. What remains to be proved (Worker 818)

This section was checked against `ClassFieldStatement.lean`. NYLL paths are under `Nyll/ClassFieldTheory/` at head `b9a2dddb` unless marked `fbd320cd`. "Library-only" means the Library and its pinned Mathlib, without NYLL.

### 6.1 Library facts the sketches use

- `IdeleClasses K` is Mathlib's `NumberField.IdeleClassGroup (𝓞 K) K`. `finiteClassInclusion K v` is the class of Mathlib's `IdeleGroup.ofAdicCompletion`. Also `FiniteCompletion K v = v.adicCompletion K`, `FinitePlace K = HeightOneSpectrum (𝓞 K)`, `HeckeCharacter K = IdeleClasses K →ₜ* ℂˣ` and `HasFiniteOrder χ := ∃ n > 0, χ ^ n = 1`.
- `Langlands.Global.IdeleDensity.eq_top_of_isClosed` (`Global/IdeleClosedSubgroupDensity.lean:253`): a closed subgroup of `Ideles K` that contains `diagonalUnits K a` for all `a : Kˣ` and `finiteIdeleInclusion K v a` for all `v ∉ S` (`S` finite) is `⊤`. This is the weak-approximation step of Milne's Proposition V.4.7.
- `isCompact_ker_ideleClass` (`Global/NormOneIdeleClassCompact.lean:365`): the norm-one idele classes are compact. `PositiveRealIdeles.full` with `absoluteValue_full` (`Global/PositiveRealIdeles.lean:83,121`): `|full x| = x^[K:ℚ]`.
- Mathlib:
  - `AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt` (`RingTheory/Frobenius.lean:164`): uniqueness of Frobenius at an unramified prime.
  - `dvd_differentIdeal_iff` and `differentIdeal_ne_bot` (`RingTheory/DedekindDomain/Different.lean:958,542`): finitely many primes ramify.
  - `krullTopology_discreteTopology_of_finiteDimensional` (`FieldTheory/KrullTopology.lean:247`): the Krull topology is `⊥` for finite `L/K`.
  - The group form `IsArithFrobAt R σ Q := (MulSemiringAction.toAlgHom R S σ).IsArithFrobAt Q` (`Frobenius.lean:183`), which agrees pointwise with the Library's `RingOfIntegers.mapAlgHom σ`.

### 6.2 Two shared Library-only lemmas

- **U (almost-everywhere uniqueness).** Let `G` be an abelian group with the `⊥` topology, `ρ₁ ρ₂ : IdeleClasses K →ₜ* G`, and `S` a finite set of finite places. Suppose `ρ₁` and `ρ₂` agree on `finiteClassInclusion K v π` for every `v ∉ S` and every `π` with `Valued.v π = exp(-1)`. Then `ρ₁ = ρ₂`.

  Proof. `ψ = ρ₁/ρ₂` is a continuous homomorphism to a discrete group, so `H = comap (ideleClassMap K) (ker ψ)` is open, hence closed, and it contains the principal ideles. Every `a ∈ K_v^×` is a product of uniformizers and their inverses: if `v(a) = exp(-n)`, then `a = (a·π^{1-n})·π^{n-1}`. So `H` contains `finiteIdeleInclusion K v a` for `v ∉ S`, and `eq_top_of_isClosed` gives `H = ⊤`.

  Literature: Milne, *Class Field Theory* v4.03, Proposition V.4.7 (p. 174) and Summary V.5.10 (p. 181); Neukirch, *Algebraic Number Theory*, II (3.4) Approximation Theorem (p. 117).
- **R (finitely many ramified places).** For finite `L/K`, the set of `v` with a ramified `w | v` is finite. Indeed `w` is ramified if and only if `w ∣ 𝔇_{L/K}` (`dvd_differentIdeal_iff`; Neukirch III (2.6), p. 199), and `𝔇 ≠ 0`.

### 6.3 Clause 1 (`∃! ρ`, `K : Type u`, `L : Type v`)

NYLL gives, at head with `Type u/v`:

- `ρ₀ := arithmeticGlobalNormResidueMonoidHom K L` (`GlobalClassFieldTheory/Reciprocity/ArithmeticNormalization.lean:211`), with `_ker` equal to the `ideleClassNorm` range (:227), `_surjective` (:236) and `_continuous` (:244, Krull topology).
- The Frobenius property, only for the chosen order-one section: `arithmeticPrimeArtin_eq_arithmeticFrobeniusAt` (`GlobalClassFields/MathlibFrobeniusHilbertComparison.lean:345`), for any `w | v` with `LiesOver` and `IsUnramifiedAt (𝓞 K) w.asIdeal`, with value Mathlib's `arithFrobAt`.
- Units are killed at unramified places: `chosenFinitePlaceArtinMonoidHom_eq_one_of_integral_of_unramifiedAt` (`Reciprocity/FiniteIdeleArtin.lean:165`; `fbd320cd` :194).
- There is no uniqueness statement.

Gaps:

1. **Transport.** Put `ρ := ρ₀ ∘ (IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K).symm` (`AlgebraicNumberTheory/Idele/ClassGroup/MathlibTopologyComparison.lean:44`). The local maps agree by `ideleClassGroupEquivMathlib_finitePlaceIdeleClass` (`MathlibComparison.lean:106`) and `arithmeticGlobalNormResidueMonoidHom_comp_finitePlaceIdeleClass` (`ArithmeticNormalization.lean:337`). Continuity for `⊥` follows from Krull = `⊥`. Glue: `IsAbelianGalois K L` comes from `IsGalois` and the commutation hypothesis, and `FiniteDimensional K L` from the two `NumberField` instances.
2. **Arbitrary uniformizer.** Write `π = s·u` with `s` the chosen section and `u ∈ 𝒪_v^×`. Then `ρ(π) = ρ(s)`, because the unit lemma kills `u`. The unit lemma's hypothesis is unramifiedness at NYLL's chosen prime above `v`. This follows from unramifiedness at the given `w`, since Galois-conjugate primes have the same ramification index. Then `ρ(s)` is `arithFrobAt` at `w` (:345), and `IsArithFrobAt` in group form gives the `mapAlgHom` form.
3. **Uniqueness.** Let `S` be the set of places of `K` ramified in `L` (finite by R). For `v ∉ S`, pick `w | v` (one exists). Both `ρ(π)` and `ρ'(π)` are Frobenius at `w`, so `eq_of_isUnramifiedAt` makes their `mapAlgHom`s equal, and injectivity of `galRestrict` makes them equal in `Gal(L/K)`. Lemma U then gives `ρ = ρ'`.
4. **Universes.** Head is `Type u/v`. `fbd320cd` is `K L : Type` only, so with `fbd320cd` each field must be transported to a universe-0 copy (NYLL's `ideleClassCongr` and `semilinearGaloisEquiv`). Using head avoids this.

Literature: Milne V Theorem 5.3 (pp. 178-179) and Summary 5.10 (p. 181); Neukirch VI (5.5) and (5.6) (p. 391).

### 6.4 Clause 2

This clause is Library-only and independent of class field theory. Let `H` be open.

1. The pullback of `H` under `ideleClassMap ∘ PositiveRealIdeles.full` is an open subgroup of `ℝ≥0ˣ ≅ (0, ∞)`. That group is connected, so the pullback is everything.
2. Hence every class has a translate by `H` of absolute value 1 (use `absoluteValue_full`; `x ↦ x^n` is surjective on `ℝ_{>0}`). So `C_K = H · C_K¹`.
3. `C_K¹` is compact (`isCompact_ker_ideleClass`), so `H ∩ C_K¹` has finite index in `C_K¹` (Mathlib: an open subgroup of a compact group has finite quotient, `Topology/Algebra/OpenSubgroup.lean:319`, an instance).
4. Therefore `[C_K : H] = [C_K¹ : H ∩ C_K¹] < ∞`.

Literature: Neukirch VI (1.6) (`C_K⁰` is compact, p. 362) and (1.8) (p. 364); Milne V 4.4 (p. 171). The NYLL route (`RayClass.exists_congruenceSubgroup_le_of_isOpen` and the `FiniteIndex` instance, section 3.2) also works, but it needs the bridge.

### 6.5 Clause 3

NYLL gives, at head:

- `closedFiniteIndexClassField H hclosed : Type`, for `H ≤` NYLL's `IdeleClassGroup K` closed of finite index (`GlobalClassFields/ClosedFiniteIndexClassFieldConstruction.lean:113`). It has instances `Algebra K`, `FiniteDimensional`, `IsGalois` and `IsAbelianGalois` over the original `K` (`ClosedFiniteIndexClassFieldOriginalField.lean:63-207`).
- Its norm range is `H` (`classFieldExistence_normSubgroup`, `MathlibGlobalReciprocity.lean:275`), and its degree is the index (:288).

It is a separate type, not an `IntermediateField K (AlgebraicClosure K)`. Head also has `infiniteAbelianClassFieldCorrespondence_eq_finiteLayer_iff` (`InfiniteAbelianClassFieldCorrespondence.lean:237`), but inside `maximalAbelianExtension K ⊆ SeparableClosure K`, not `AlgebraicClosure K`.

Sketch:

1. `H` is open in `IdeleClasses K`, so `H' :=` the comap of `H` under the bridge is open, hence closed, and it has finite index.
2. Let `E := closedFiniteIndexClassField H'`, and `ρ_E` the clause-1 map for `E` (with `L` universe-polymorphic). Then `ker ρ_E` is the norm range, which is `H'` (`_ker` and `_normSubgroup`). After transport, `ker = H`.
3. Embed `ι : E →ₐ[K] AlgebraicClosure K` (`IsAlgClosed.lift`), and put `L := ι.fieldRange` and `e : E ≃ₐ[K] L`.
4. Then `ρ := AlgEquiv.autCongr e ∘ ρ_E` keeps the kernel, surjectivity and continuity.

Remaining gap **T (transport of the normalization along `e : E ≃ₐ[K] L`)**, on the Library's side. Primes `w` of `𝓞 L` correspond to primes of `𝓞 E` via `RingOfIntegers.mapAlgEquiv e`, and `LiesOver`, `IsUnramifiedAt` and `IsArithFrobAt` (conjugated by `e`) transport. A NYLL alternative is `globalIdeleClassArtinMonoidHom_semilinear` (`Reciprocity/GlobalArtinBaseEquiv.lean:77`) with `e` the identity on `K`, together with `ideleClassArtin_eq_arithmeticGlobalNormResidue` (`FiniteReciprocityDataComparison.lean:94`).

Literature: Milne V Theorem 5.5 (p. 179); Neukirch VI (6.1) (p. 395).

### 6.6 Clause 4

NYLL has only abstract class-formation injectivity over `SeparableClosure ℚ` (`ordinaryIdeleClassNormSubgroup_injective`, `FiniteAbelianClassFieldCorrespondence.lean`, head :206, `fbd320cd` :200), and nothing for subfields of `AlgebraicClosure K`.

Sketch. It uses clause 1 only, not the existence of class fields.

1. `M := L ⊔ E` in `AlgebraicClosure K` is finite, Galois and abelian, since `Gal(M/K)` embeds in `Gal(L/K) × Gal(E/K)` by restriction. Let `ρ_M` come from clause 1.
2. Gap **F (Frobenius restricts).** If `σ` is an arithmetic Frobenius at a prime `W` of `𝓞 M`, then `σ|_L` is an arithmetic Frobenius at `W ∩ 𝓞 L`: the residue field of `K` is the same, and `x ∈ 𝓞 L ⊆ 𝓞 M`. Neither Mathlib nor NYLL states this in `IsArithFrobAt` form. NYLL has `globalArtinMonoidHom_restrict_tower` (`Reciprocity/GlobalArtin.lean:320`) for its own maps.
3. Then `res_L ∘ ρ_M` and `ρ` agree on uniformizers at places unramified in `M` (choose `W | w`, and use uniqueness of Frobenius at `w`). Lemma U gives `ρ = res_L ∘ ρ_M`, and likewise `τ = res_E ∘ ρ_M`.
4. `ρ_M` is surjective and `ker ρ = ker τ`, so `ker(res_L) = ker(res_E)` in `Gal(M/K)`. The Galois correspondence in `M` (`IsGalois.fixedField_fixingSubgroup`) gives `L = E`.

Literature: Neukirch VI (6.1) (p. 395); Milne V Corollary 5.6 (p. 179).

### 6.7 Clause 5

This clause is formal from clause 3.

1. `χ^n = 1` puts the range of `χ` in the finite set `μ_n`. So `ker χ` is open (the preimage of the open set `ℂˣ \ (μ_n \ {1})`) and has index at most `n`.
2. Clause 3 gives `L` and `ρ` with `ker ρ = ker χ`.
3. Take `θ` to be the factorization of `χ` through `ρ` (`MonoidHom.liftOfRightInverse ρ (Function.surjInv hρ)`, `Algebra/Group/Subgroup/Basic.lean`; or `QuotientGroup.kerLift` with `quotientKerEquivOfSurjective`). It is injective because `ker ρ = ker χ`, and continuous because the source has the `⊥` topology.

No NYLL content is needed beyond clause 3. Literature: Neukirch VI (6.1) with (5.5); Milne V Theorem 5.5.

### 6.8 Proof order and size

The proof order is:

1. Clause 2, U and R (Library-only).
2. Clause 1 (NYLL, the bridge, the uniformizer glue and U).
3. Clause 4 (clause 1, U, F and the Galois correspondence).
4. Clause 3 (NYLL's existence, clauses 1 and 2, and T).
5. Clause 5 (clause 3).

The only deep NYLL inputs are the clause-1 map with its chosen-section normalization and the existence of class fields with prescribed norm group. All other gaps are short lemmas on the Library's side: U, R, T, F, the uniformizer decomposition, the comparison of the group form of `IsArithFrobAt` with the `mapAlgHom` form, and the swap to the `⊥` Krull topology.

## 7. Recommendation and decisions for the operator

The plan note (§4.4) recommends listing the consumers before taking NYLL's global theory, "the proved class-formation form may already suffice for them". The findings are:

- Nothing on the route consumes interface F today (section 1).
- The class-formation form does not give any clause.
- NYLL gives the two deep inputs (the normalized map, and class fields with prescribed norm group).
- What remains is a set of short lemmas (section 6).

The operator has three decisions. They are filed as one request, `task7345-interface-f-scope-and-source`.

**Q1. Is interface F wanted on the route now?**

- (a) Defer it: no NYLL import. The statement stays unproved, and its node is marked as off the route until a consumer appears.
- (b) Prove only the parts that need no NYLL: clause 2 and the lemmas U and R that later clauses reuse. Defer clauses 1, 3, 4 and 5.
- (c) Prove all five clauses. This needs NYLL, and then Q2 and Q3 apply.

Recommendation: **(a)**; **(b)** if partial progress is wanted, since it is small and uses only the Library and Mathlib. If `WeakEquivalenceRigidityStatement` enters the route, F becomes needed (clauses 1, 3 and 5), and (c) applies.

**Q2. If (c), from which commit?**

- (a) `fbd320cd` now, as an adapted copy on the present pin. That is 957 modules with the 14 edits of section 4, plus the universe transport (section 6.3, gap 4).
- (b) Head `b9a2dddb` after the Library moves to Mathlib `56a00585`, the plan note's configuration B (651 Mathlib commits and a revalidation of the Library). No adaptation and no universe transport would be needed, since head targets that Mathlib commit. We have not compiled head there.
- (c) Head adapted to the present pin. We do not recommend this: the drift already shows at the bottom of the closure (section 5), and the closure is larger (1073 modules against 957 for the six roots).

Recommendation: **(b)** if F can wait for the Mathlib move, which costs nothing while F has no consumer; otherwise **(a)**.

**Q3. If (c), in which reuse mode** (plan note §5.3)?

- D or F: a package dependency, on head (D) or on the adapted copy of `fbd320cd` (F), pinned by commit and content hash. This needs pins of packages in the Library's environment file, which do not exist today.
- P: a light port of the adapted closure, about 1000 modules and 400,000 lines, kept as a fork.

In every mode only the five Library statements cross the boundary. NYLL's definitions occur only inside proofs (the bridge is definitional, section 3.5), so the review covers those statements plus an axiom check on the closure. A heavy port of this size is out of reach (plan note §5.3, criterion 2).

Recommendation: **D or F**, in line with the plan note's verdict for NYLL's global theory (§5.4).

**Open risk, in every mode.** A module that imports both the closure and the Library's NYLL port now compiles (section 4.4). The effect of NYLL's global instances and `simp` lemmas on Library proofs that import the closure is still untested. It has to be tried on the first proof of clause 1.

### 7.1 The operator's decision (17 November 2026)

The operator answered the request (answer `a69781b7c489519ea61253c2b1c26dd9` to request `07efe25fa98a56da82e85b9e045270bd`).

- **Q1: (a).** Interface F is deferred. Nothing from NYLL is imported now, and `FiniteAbelianClassFieldStatement` stays unproved. The planning nodes `proof.finite-abelian-global-reciprocity` (the statement) and `proof.global-artin-norm-comparison` (`ArtinNormComparisonStatement`) are marked off the route. Option (b) was not chosen: clause 2 and the lemmas U and R have no consumer either.
- **What reopens F.** F reopens when a statement on Task 0's route needs the Frobenius-normalized idelic Artin map itself. In particular, this happens if a proof of `WeakEquivalenceRigidityStatement` (Henniart 2000, §2.2; section 1.4) enters the route. In that case the lemmas U and R of section 6.2 come first, since they need no NYLL. After them come only those clauses of F that that proof uses. Worker 96 sent this trigger to Worker 0 for the planning graph (message `7c34b0298a8c527e8c8fbb52cbf7e122`).
- **Q2: (b), Q3: D**, for the day F is wanted. NYLL's head `b9a2dddb` is on exactly the pin (Lean 4.35.0, Mathlib `56a0058`) to which a move of the Library is being trialed. The environment that follows the move can pin packages by commit and content hash. Until then there is no adapted copy of `fbd320cd` and no light port.
- **What this note keeps for that day.**
  - The 14 edits and the three diagnostics (`913786b0`, `3c6e5461` and `0390f87b`; section 4). They date the cost of an adaptation.
  - The list of what NYLL does not give, with the Library-side lemmas that close each gap (section 6).
  - The untested effect of NYLL's instances and `simp` lemmas on Library proofs (the open risk above). It is the first thing to try on clause 1.
- **The one task published now.** The operator asked for one task for what the route does consume and the Library lacks:
  - (N): for a finite Galois extension `E/F` of number fields, the image of the idele-class norm is open in `IdeleClasses F`;
  - (H): for every cyclic `E/F`, there is a Hecke character of `F` with `HasNormKernel E`, and its order is `[E : F]`.

  (N) turned out to be in the Library already (section 1.4), so the task covers (H) alone and cites (N) as proved. Its exact form was put to the executors of Task 7340 (the trace formula and cyclic base change). Worker 5743 agreed to it as proposed; the task lets Task 7340's executors change the hypothesis form later. It is Task 7475 (`f3e9b7a4-6895-4b0a-8229-4c115601c2df`): a statement `Langlands.Global.HeckeCharacter.CyclicNormKernelCharacterStatement` (for Galois `E/F` with cyclic Galois group, an `η` with `η.HasNormKernel E` exists, has order `[E : F]`, and its powers are the characters trivial on norms), followed by a proof task for it.

Nothing else is published under Task 7345.
