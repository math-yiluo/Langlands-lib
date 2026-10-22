# NYLL finite local reciprocity: source audit and port plan

Worker 215 prepared this audit for task `b66bd2bc-abd3-4ea5-ae34-af7cdbeac0a3` (revision 2). It audits `ClassFieldTheory.finiteAbelianLocalReciprocity` and the underlying `LocalClassFieldTheory.abelianLocalArtinMap` in Naganori Yamaguchi's NYLL ClassFieldTheory library. It compares them with our `Langlands/ClassFieldTheory/Local/FiniteReciprocityStatement.lean` and `ReciprocitySystemStatement.lean`, and, in section 5, with the Library's existing local class-field declarations. This note does not accept any external theorem, and it imports no external code into the Library.

**Verdict: adapt.** NYLL constructs one concrete Artin map, `abelianLocalArtinMap`. Its sign convention is our geometric convention: a uniformizer goes to geometric Frobenius. Separate NYLL theorems about this same map give tower restriction, the norm square, unramified normalization and an inertia description. Together they cover the clauses of `FiniteAbelianReciprocityTheorems`, with two gaps:

- **Ramified residue normalization.** No NYLL theorem gives the residue action of this map for a ramified extension. `finiteAbelianLocalReciprocity_family_ext` only proves that two coherent families of maps with norm kernels are equal when both are normalized on their unramified members. A residue-action theorem for ramified extensions is a separate bridge (section 2.7).
- **Universes.** The Artin map and every theorem about it take `K L : Type`, that is, universe 0. Some supporting declarations are universe-polymorphic, for example the norm vocabulary (`fieldNormSubgroup`, `IsFieldNorm`, `FieldNormQuotient`) and `finiteAbelianLocalReciprocity_quotientEquiv_of_artin`. Our statements need the map itself in arbitrary universes.

The Library already has conditional reciprocity constructors, normalization predicates and statement targets for the same objects. It has no reciprocity map that is defined without a supplied map or cohomology class (section 5). NYLL's map is defined without such inputs.

The required closures are large (258 to 402 modules). They target a newer Lean and Mathlib, and we have not built or kernel-checked them in our environment. Nothing here supports the Weil-group system in `ReciprocitySystemStatement.lean`.

Section 2 summarizes the declarations. Appendix A gives their full types verbatim, with section variables.

## 1. Pins, sources, dependency closure and missing inputs

| Item | NYLL | Project |
|---|---|---|
| Source commit | [`fbd320cd8b1b06487c58227e92eb135794267709`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709) | Library commit `2e31df852eed5b4c1a45eca581f8480418360a34` (every Library file cited in this note, except `UnramifiedArithmeticProof.lean`, which is new at this commit, is byte-identical to its version at `0686b4fa`, where the audit began) |
| Lean | `v4.35.0-rc2` (`lean-toolchain`) | `4.34.0` (environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`) |
| Mathlib | `065356127b1dc0016f66b7283ce0ce2c4055aa55` (`lakefile.toml`, `lake-manifest.json`; committed 2026-09-16) | `5ed2965256430c3649e86755f9576b54eca72435` |

The other manifest packages (plausible, LeanSearchClient, importGraph, proofwidgets, aesop, Qq, batteries, Cli) come in through Mathlib.

**Sources used.**

- **Main snapshot.** Registered source `external-lean-reuse-snapshots-2026-10-21` (fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`), folder `n-yamaguchi-0729--ClassFieldTheory`. All 3142 retained files match the git blob SHA-1s in its `tree.json` at the pinned commit.
- **Files missing from the snapshot.** The tree has 68 non-Lean files. The snapshot keeps six of them (`LICENSE`, `NOTICE`, `README.md`, `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`) and omits the other 62. I fetched the 30 omitted files needed for this audit, and each one's blob SHA-1 matches `tree.json`. They are:
  - the five `ANTHROPIC_FLT_{ATTRIBUTION.md,NOTICE,SOURCE.md}` triples;
  - the pi1 `ATTRIBUTION.md`, `LICENSE`, `README.md` and `UPSTREAM.json`;
  - `.github/workflows/lean.yml` and the ten files of `.github/verification`.

  They are registered as `nyll-classfieldtheory-fbd320cd-supplement` (SHA-256 `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`), together with GitHub API records of NYLL's Mathlib commit and of the comparison from our Mathlib pin to it. The supplement's `MANIFEST.md` lists them.
- **CI records.** The author's CI run records are registered as `nyll-classfieldtheory-fbd320cd-ci-run-records`.
- **Two Mathlib files at NYLL's pin.** For the universe question in section 5, I fetched `Mathlib/RepresentationTheory/Rep/Basic.lean` and `Mathlib/RepresentationTheory/Homological/TateCohomology/Basic.lean` at Mathlib `065356127b` from `raw.githubusercontent.com/leanprover-community/mathlib4`. Both are byte-identical to the files in our Mathlib (SHA-256 `aafa42cc42af566b4ac74527b5e1dfbade4fb3e896134da61100ad7f3881fbf2` and `296dabdbf04196374a3378c9d1c9ad80b74adb25961757954b92181c71fc620f`).

**Dependency closures.** I followed `import` lines after stripping comments. This is a textual traversal, not Lean elaboration. Module counts include the root. In the table, `.../LocalReciprocity/` abbreviates `LocalClassFieldTheory/Finite/LocalReciprocity/`, and reader `...X` is `Theorems/LocalClassFieldTheory/FiniteAbelianLocalReciprocityX`:

| Root module (under `Nyll/ClassFieldTheory/` unless it starts with `Nyll/`) | Local modules |
|---|---|
| `Theorems/LocalClassFieldTheory/FiniteAbelianLocalReciprocity` (wrapper; it imports `MathlibInterface`, which also pulls in existence and profinite layers) | 502 (204,454 raw lines) |
| `LocalClassFieldTheory/Finite/LocalReciprocity/NormResidue` (defines the Artin map) | 258 (115,017 raw lines) |
| `.../LocalReciprocity/UnramifiedNormalization` | 265 |
| `.../LocalReciprocity/GeneralTowerNaturality` | 262 |
| `.../LocalReciprocity/FixedFieldIntrinsicReciprocity/NormRestriction` | 280 |
| `.../LocalReciprocity/Filtered/FiniteAbelian` (inertia, via Lubin–Tate) | 402 |
| Reader theorem `...UnramifiedNormalization`, reader `...Tower` | 268, 265 |
| Reader `...Family`, `...FamilyExt` | 265, 290 |
| Reader `...QuotientEquivOfArtin` | 4 |
| `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ShrinkTransport` (universe transport, section 5) | 33 |
| Union of `Theorems/LocalClassFieldTheory/All`, `Filtered/FiniteAbelian` and `NormRestriction` | 639 (240,110 comment-stripped lines) |

- The union contains only `ClassFieldTheory`, `GaloisCohomology` and `ValuedFieldTheory` modules, including the `Shrink*` transport modules. No module is missing from the snapshot.
- It has 304 external imports. The 299 Mathlib modules and `Batteries.Tactic.Init` all exist in our Mathlib checkout and its Batteries package; the other four are Lean core `Lean.Elab.Tactic` modules.
- It has no `module`/`public import` syntax and no `maxHeartbeats` options. It contains four `grind` calls, in two modules: `Nyll/ValuedFieldTheory/Valuation/AbsoluteValue/Ostrowski.lean` (lines 711, 713 and 715) and `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/FixedFieldRamificationIndex.lean` (line 427).

**Missing inputs.**

- No build artifacts.
- No Lean 4.35.0-rc2 toolchain in our environment.
- The author's CI verification artifact needs authentication, so I did not download it.
- Under the task rules no external build was run. Only the project's Lean service was used (section 4).

## 2. Declarations, construction and meaning

All NYLL paths in this section are relative to `Nyll/ClassFieldTheory/` unless they start with `Nyll/`, and `.../LocalReciprocity/` abbreviates `LocalClassFieldTheory/Finite/LocalReciprocity/`.

### 2.1 The wrapper

Verbatim from `Theorems/LocalClassFieldTheory/FiniteAbelianLocalReciprocity.lean:33-42`, inside `namespace ClassFieldTheory`:

```lean
theorem finiteAbelianLocalReciprocity
    (K L : Type)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    ∃ artin : Kˣ →ₜ* (L ≃ₐ[K] L),
      Function.Surjective artin ∧
      ∀ x : Kˣ, artin x = 1 ↔ IsFieldNorm K L x := by
  exact LocalCFT.finiteAbelianLocalReciprocity K L
```

- **Witness.** `ClassFieldTheory.LocalCFT.finiteAbelianLocalReciprocity`, in `LocalClassFieldTheory/Finite/LocalReciprocity/MathlibInterface.lean`, has the same type. Its proof (appendix A.1) uses the witness `LocalClassFieldTheory.abelianLocalArtinMap K L`. The wrapper file's module docstring leaves "the usual uniformizer normalization and tower functoriality to separate compatibility theorems" and "does not claim that the displayed witness is uniquely determined".
- **Kernel.** `IsFieldNorm K L x` is membership in `fieldNormSubgroup K L`, the range of `Units.map (Algebra.norm K)` (A.5). Our probe theorem `fieldNormSubgroup_eq` (section 4) checks by `rfl` that this is literally our `(Units.map (Algebra.norm F.Carrier (S := E.Carrier))).range`.
- **The existence wrappers hide the map.** Eight reader-facing theorems only assert that suitable maps or equivalences exist: the wrapper, `_quotient`, `_quotientEquiv_mk`, `_unramifiedNormalization`, `_tower`, `_family`, `_family_unramifiedNormalization` and `_family_arithmeticFrobenius` (each name prefixed by `finiteAbelianLocalReciprocity`). Two separate existentials cannot be combined into one map. A port must therefore use the named map and the underlying `LocalClassFieldTheory`/`ClassFieldTheory` lemmas below. The uniqueness theorems `_family_ext`, `_unramified_family_ext` and `_unramified_hom_ext`, and `_quotientEquiv_of_artin`, are different: they take the maps as arguments.
- **Other results in the same file.** `MathlibInterface.lean` also has `finiteAbelianLocalReciprocity_quotient` (`Nonempty (FieldNormQuotient K L ≃ₜ* (L ≃ₐ[K] L))`), `isOpen_fieldNormSubgroup`, `fieldNormSubgroup_finiteIndex` and `fieldNormSubgroup_index_eq_finrank`. The finite existence and order-isomorphism theorems are context only.

### 2.2 The construction

1. **The Artin map.** `LocalClassFieldTheory.abelianLocalArtinMap K L : Kˣ →ₜ* Gal(L / K)` is defined in `.../LocalReciprocity/NormResidue.lean:78` (A.2). Its section variables make `K` a nonarchimedean local field and `L/K` finite abelian; `L` gets no other structure. It is `topologicalAbelianizationEquivSelf K L` composed with `localArtinMap K L`. Its algebraic form is `abelianLocalArtinMonoidHom` (`abelianLocalArtinMap_toMonoidHom`), with kernel `LocalFieldTheory.localNormSubgroup K L` and surjectivity proved there. `localArtinMap` (`TopologicalReciprocity.lean`, A.3) is `localReciprocityEquiv` composed with the continuous norm class map.
2. **The isomorphism behind it.** `localArtinMonoidHom K L` is `(abelianizationEquivNormQuotient K L).symm.toMonoidHom.comp (normClass K L)` (`.../LocalReciprocity/Main.lean:66`, A.4). For every finite **Galois** `L/K`, `abelianizationEquivNormQuotient K L : Abelianization Gal(L / K) ≃* NormQuotient K L` is `concreteReciprocityEquiv K L (localResidueDatum K) (localHenselianValuation K) (separableClosureUnits_isClassFormation K)`. This is the Neukirch-style abstract class-field-theory construction, with these inputs:
   - the class formation `(SeparableClosure K)ˣ`, as a `Rep ℤ` of the absolute Galois group;
   - Henselian valuation `valuationMap K`;
   - a degree map built from the residue algebraic closure.
3. **Reciprocity direction.** The map runs from `Kˣ` to Gal(L/K). It is the inverse of `Gal(L/K)^ab ≃ Kˣ/N` composed with the quotient map.
4. **Choice of separable closure.** The construction uses Mathlib's `SeparableClosure K`. `localArtinMonoidHom_eq_of_embedding` (A.4) shows that the map is the same for every `i : L →ₐ[K] SeparableClosure K`.
5. **Topology.** `Kˣ` has Mathlib's units topology, coming from the `[TopologicalSpace K]` instance, which must fit `IsNonarchimedeanLocalField K`. `NormQuotient K L` gets the quotient topology through the local instance `normQuotientTopologicalSpace`, and `localNormSubgroup_isOpen` and `normQuotient_discrete` make it discrete (A.3). `Gal(L/K)` has Mathlib's Krull topology, which is discrete here. `L` carries no topology in the wrapper.

### 2.3 Valuation sign and Frobenius normalization

**NYLL's valuation is minus our order.**

- NYLL's `LocalFieldTheory.IsNonarchimedeanLocalField.v K` equals `valuationMap K`, and it is **minus** the order (definitions in A.6). `LocalFieldTheory.v_integerRingIrreducibleFieldUnit` (`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/IdealQuotients.lean:212`) gives a prime element the value −1.
- Our probe proves the comparison: `NyllProbe.nyll_v_eq_neg_ord` shows `v = -T.ord` for our `TopologicalData`.

**Normalization of the map.** `ClassFieldTheory.finiteAbelianLocalArtinMap_eq_frobenius_zpow` is in `.../LocalReciprocity/UnramifiedNormalization.lean:515` (full type in A.7). Its hypotheses are:

- local-field structure on `K`, and on `L` through `ValuativeRel L`, `UniformSpace L`, `IsUniformAddGroup L` and `IsNonarchimedeanLocalField L`;
- a finite abelian extension `L/K`;
- `Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)`;
- `IsUnramifiedValuedExtension K L`, which says that the ramification index of `𝓂[L]` over `𝒪[K]` is 1.

For `x : Kˣ` it states `abelianLocalArtinMap K L x = arithmeticFrobeniusOfUnramifiedValuation K L ^ valuationMap K (Additive.ofMul x)`.

- **Consequence.** The map sends `x` to arithmetic Frobenius to the power −ord x. So a genuine uniformizer goes to **geometric** Frobenius, as in our convention.
- **Misleading name.** `finiteAbelianLocalArtinMap_uniformizer` (line 540) assumes `valuationMap K π = 1`. That makes π an **inverse** uniformizer.
- **Residue form.** `finiteAbelianLocalArtinMap_inverseUniformizer_residue_pow` (line 561) says: for such an inverse uniformizer π and every `x : 𝒪[L]`, the image of `x` under the map at π reduces to `residue x ^ Nat.card 𝓀[K]`.
- **Reader-facing version.** `ClassFieldTheory.finiteAbelianLocalReciprocity_unramifiedNormalization` replaces the unramified class by a hypothesis `hUnram` on the ramification index. It asserts that some surjective `artin` with kernel `fieldNormSubgroup K L` sends the inverse of every Mathlib uniformizer `π : 𝒪[K]` to an element acting as the `Nat.card 𝓀[K]`-power map on residues. This has the shape of clause (i) of our `FiniteAbelianReciprocity` for **unramified** `E`, because `r([π])⁻¹ = r([π⁻¹])`. Being existential, it is not the version a port uses.

### 2.4 Restriction, norm and transfer

**Restriction.** `ClassFieldTheory.finiteAbelianLocalArtinMap_restrict_tower` is in `.../LocalReciprocity/GeneralTowerNaturality.lean:468` (A.8). It takes a tower `K → E → L` with `IsScalarTower K E L` and with `E/K` and `L/K` both finite abelian. Only `K` needs local-field instances. It states:

`(AlgEquiv.restrictNormalHom E).comp (abelianLocalArtinMap K L).toMonoidHom = (abelianLocalArtinMap K E).toMonoidHom`

It has the shape of our `FiniteAbelianRestriction`.

**Norm square.** `LocalClassFieldTheory.abelianLocalArtinMonoidHom_norm_restriction (K K' L L' : Type)` is in `.../LocalReciprocity/FixedFieldIntrinsicReciprocity/NormRestriction.lean:686` (A.9). It lies outside the wrapper closure.

- **Hypotheses**, in summary:
  - local-field instances on both `K` and `K'`;
  - the five algebras `K → K'`, `K → L`, `K → L'`, `K' → L'` and `L → L'`, with the scalar towers `IsScalarTower K K' L'` and `IsScalarTower K L L'`;
  - `FiniteDimensional K K'` and `Algebra.IsSeparable K K'`;
  - `Valuation.HasExtension (valuation K) (valuation K')`;
  - finite abelian `L/K` and `L'/K'`.
- **Conclusion:** `((AlgEquiv.restrictNormalHom L).comp (AlgEquiv.restrictScalarsHom K)).comp (abelianLocalArtinMonoidHom K' L') = (abelianLocalArtinMonoidHom K L).comp (normUnits K K')`.
- **Specialization to our statement.** Take `K = F`, `K' = E` and `L = L'`, so that `L → L` is the identity algebra. Then `AlgEquiv.restrictNormalHom_id`, which our Mathlib has, removes the restriction. This gives the norm clause of `FiniteAbelianNormTransfer`.

**Transfer.** NYLL has no transfer theorem for `abelianLocalArtinMap` or `localArtinMap` on standalone fields. It does prove transfer–inclusion naturality in a fixed-field presentation (A.13):

- `LocalClassFieldTheory.LocalFixedFieldTransferTower.transfer_inclusion_commutes` is in `.../LocalReciprocity/FixedFieldNormResidueNaturality.lean:728`, inside the 280-module `NormRestriction` closure.
- Its continuous form `transfer_inclusion_commutes_continuous` is in `.../LocalReciprocity/FixedFieldContinuousNaturality.lean:902`. That module has a 261-module closure and lies outside the 639-module union of section 1.

A `LocalFixedFieldTransferTower k` consists of three closed subgroups of `Gal(SeparableClosure k / k)`, with a finite Galois total extension that need not be abelian. The squares use fixed-field norm-residue symbols into algebraic abelianizations. These symbols are built from the same class-formation inputs as `abelianizationEquivNormQuotient` (A.4). For the norm square, `NormRestriction.lean` transports the analogous fixed-field square (`abstractFixedFieldNormResidueSymbol_norm_restriction`, `FixedFieldNormResidueNaturality.lean:176`) to standalone fields through `AmbientEmbeddedFixedFieldPresentation.fixedFieldNormResidueTransport` (`NormRestriction.lean:190`). A case-insensitive search for `transfer` in NYLL's `LocalClassFieldTheory` and `Theorems/LocalClassFieldTheory` trees finds no such transport for the transfer square.

In the abelian case our transfer clause follows from the norm clause, because `N_{E/F}(a) = a^[E:F]` for `a ∈ F`. The probe proves this: `NyllProbe.transfer_of_norm` in section 4.

### 2.5 Inertia

`LocalClassFieldTheory.finiteAbelian_filteredLocalReciprocity` is in `.../LocalReciprocity/Filtered/FiniteAbelian.lean:41` (A.10). It needs only a local field `K`, a finite abelian `L/K`, and `t : ℝ` with `0 ≤ t`. Its proof goes through a Lubin–Tate compositum. It states:

`artinPrincipalUnitStepGroup K L t = localUpperRamificationGroup K L t`

At `t = 0` the left side reduces as follows (definitions in A.10):

1. `natCeilStepFiltration` uses `⌈0⌉₊ = 0`, so the left side is `artinPrincipalUnitGroup K L 0`.
2. That group is `(fieldPrincipalUnits K 0).map (abelianLocalArtinMonoidHom K L)`.
3. Since `principalUnits_zero` gives the whole group, this is the image of `𝒪[K]ˣ`.

The right side is handled by `RamificationTheory.LocalField.localUpperRamificationGroup_zero_eq_residue_ker` (`Nyll/ValuedFieldTheory/Ramification/LocalField/ResidueInertia.lean:97`, inside the 402-module closure). It identifies `localUpperRamificationGroup K L 0` with the kernel of `galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L : Gal(L / K) →* (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L])`, the residue action. Its hypotheses, in summary:

- local-field instances on `K`, and on `L` through `ValuativeRel L`, `TopologicalSpace L` and `IsNonarchimedeanLocalField L`;
- a finite Galois `L/K`;
- `Valuation.HasExtension (valuation K) (valuation L)`;
- `IsIntegralClosure 𝒪[L] 𝒪[K] L` and `Module.Finite 𝒪[K] 𝒪[L]`.

By `galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_sub_mem_maximalIdeal`, σ is in this kernel exactly when `σ x - x ∈ 𝓂[L]` for every `x : 𝒪[L]`.

Together these give clause (ii) of our `FiniteAbelianReciprocity`, after two translations into our valuations: from units to `ord = 0`, and from the residue kernel to our `discreteValuation` inequality.

### 2.6 Family theorems and the common-closure system

**The family.** The family results are in `Theorems/LocalClassFieldTheory/FiniteAbelianLocalReciprocityFamily*.lean`. They index over `ClassFieldTheory.FiniteAbelianLocalExtension K`, the subtype of finite-dimensional abelian Galois `IntermediateField K (SeparableClosure K)` (A.11). The witness is always `abelianLocalArtinMap K E.1`.

- **`finiteAbelianLocalReciprocity_family`** asserts that one family exists with norm kernels and whose members agree on included subfields.
- **`finiteAbelianLocalReciprocity_family_ext`** (290-module closure; full type in A.11) takes two families `f` and `g` and concludes `f = g`. It assumes that both families satisfy:
  - the norm-kernel condition;
  - inclusion coherence;
  - a residue normalization on the unramified members. For every member `E` with a valued realization (`ValuativeRel E.1`, `UniformSpace E.1`, `IsUniformAddGroup E.1`, `IsNonarchimedeanLocalField E.1`, `HasExtension`) in which the ramification index is 1, the inverse of every uniformizer must act as the `Nat.card 𝓀[K]`-power map on residues.

  Equality of whole families includes the ramified members, but the theorem gives no residue-action formula for them. NYLL's module docstring for the family theorem says that it "currently uses the source construction at `Type 0`; arbitrary-universe transport remains separate."
- **`_unramified_family_ext` and `_unramified_hom_ext`** are related uniqueness variants for unramified members.

**No component for `ReciprocitySystemStatement.lean`.** NYLL supplies nothing usable directly for `CommonClosureReciprocityExistence` or `CommonClosureReciprocityUniqueness`. Those quantify over every finite intermediate field of `AlgebraicClosure F.Carrier`, including non-normal ones. They use Weil-group abelianizations `TopologicalAbelianization (pullbackFixingSubgroup …) ≃ₜ* E.fieldˣ` with norm, transfer, conjugation, density, completion and absolute-value normalization relations. NYLL has no Weil group. A case-insensitive search finds `Weil` nowhere in its `ClassFieldTheory`, `ValuedFieldTheory` and `GaloisCohomology` trees. Repository-wide it finds no `WeilGroup`, "Weil group" or Weil–Deligne; the remaining hits are Weil differentials and Weil reciprocity for algebraic curves. Its profinite theorem (`ProfiniteLocalReciprocity`) is context only and was not audited.

### 2.7 Correspondence with `FiniteReciprocityStatement.lean`

| Our clause | NYLL source for the same map | Remaining bridge |
|---|---|---|
| quotient `≃ₜ*` in all three Props | `abelianLocalArtinMap` with its kernel and surjectivity; `finiteAbelianLocalReciprocity_quotientEquiv_of_artin` (A.12). The Library's `finiteNormResidueEquiv` uses the same mechanism (section 5). | Identify `localNormSubgroup K L` with the norm subgroup in our Props; both are the range of `Units.map (Algebra.norm K)`. Then apply the first isomorphism theorem. NYLL's theorem applies directly to standalone fields in independent universes, and it compiled unchanged in our environment with its 4-module closure (section 4). Its three `FieldNorm*` modules are outside the `NormResidue`, tower, normalization, norm-square and inertia closures, so using it adds one more norm vocabulary. The Library's `finiteNormResidueEquiv` needs `E` replaced by an intermediate field of `AlgebraicClosure F.Carrier`, and the Library states no evaluation lemma for it. A direct use of Mathlib's `QuotientGroup.quotientKerEquivOfSurjective`, as inside `finiteNormResidueEquiv`, needs neither. Small. |
| `FiniteAbelianRestriction` | `finiteAbelianLocalArtinMap_restrict_tower` | Universe transport and instance matching only. Small. |
| `FiniteAbelianNormTransfer`, norm clause | `abelianLocalArtinMonoidHom_norm_restriction` with `K' = E` and `L = L'` | Get `HasExtension` and the local-field instances on `E` from `TE`. Get `Algebra.IsSeparable F E` from characteristic 0 and `IsAbelianGalois E L` from the tower. Small to medium. |
| `FiniteAbelianNormTransfer`, transfer clause | none for this map; NYLL's transfer square is stated only for fixed fields (section 2.4) | `NyllProbe.transfer_of_norm` (compiled in the shared draft, section 4). Small. |
| `FiniteAbelianReciprocity` (i), unramified `E` | `finiteAbelianLocalArtinMap_inverseUniformizer_residue_pow` | Show `TF.ord a = 1` is the same as `v a = −1`, which `nyll_v_eq_neg_ord` does. Match `TF.residueCardinality` with `Nat.card 𝓀[K]`. Restate residue reduction as our `TE.discreteValuation` inequality. Medium. |
| (i), ramified `E` | None. No NYLL theorem gives the residue action for ramified `E`; `_family_ext` is only a uniqueness theorem. Mathematically, (i) follows by restricting to the maximal unramified subextension `E₀` (tower theorem), because `E` and `E₀` have the same residue field. | A new statement and proof about the maximal unramified subextension and the residue field. Medium. |
| (ii) inertia | `finiteAbelian_filteredLocalReciprocity` at `t = 0` and `localUpperRamificationGroup_zero_eq_residue_ker` | Translate the valuation and residue kernel as above. Supply the `IsIntegralClosure`/`Module.Finite` instances. Medium. |
| universes `PadicField.{u,v,w}` | The Artin map and its theorems are at `Type`. NYLL's `Shrink` transport covers only its existence theorem. | Transport along field isomorphisms to universe-0 models, as in section 5. Medium to large. |

## 3. Licenses, notices and attribution

- **License.** NYLL is Apache-2.0 (root `LICENSE`).
- **NOTICE.** Its root `NOTICE` (1138 lines) holds the inventories and preserved upstream notices for 926 included files adapted from [pi1](https://github.com/chrisflav/pi1) and Anthropic's Fermat's Last Theorem project.
- **README credits.** Line 81 of the README says "All original code in this library is written by OpenAI Codex". Yamaguchi sets the goals and maintains the library. Around line 91 it says the pi1 and Anthropic adaptations "retain their source-specific copyrights and authors".
- **Headers of the audited closure.** All 639 modules in the union closure carry the same header: "Copyright (c) 2026 Naganori Yamaguchi … Released under Apache 2.0 license … Authors: Naganori Yamaguchi (assisted by OpenAI Codex)".
- **No pi1 or Anthropic files in the closure.** I compared module paths textually. No closure module appears among NOTICE's 926 files or among the 908 modules in the five `ANTHROPIC_FLT_SOURCE.md` tables, and the closure contains no `EtaleFundamentalGroups.Pi1` module. Those adapted files do exist elsewhere in the repository.

**Obligations for any port:**

- keep each copied file's header and author line;
- ship NYLL's `LICENSE` and `NOTICE` with the port;
- if a later closure reaches NOTICE-listed files, keep their upstream copyrights and authors.

## 4. Kernel and axiom evidence

**Obtained in our environment.** All runs used `lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, with Lean 4.34.0 and Mathlib `5ed2965`. They are development checks of a task draft. They do not make any NYLL theorem an accepted Library result.

- **Where the evidence is.** The compiled files and the verbatim run records are in the immutable shared task draft, revision 2:
  `/home/taskhub/pilot/drafts/b66bd2bc-abd3-4ea5-ae34-af7cdbeac0a3/revision-2-be21ccfa15f601569a88da87b57effd5cd1303ee0054cfb4c2815958debe5a7d/files`
  (manifest SHA-256 `f4ef042dfec477193bcbf9eb788a4dcddd0acfb8253d4d5493cc90b4f0c81844`). Its `NyllProbe/Bridge.md` describes the files and lists every run, and `receipts/<run>.md` reproduces each `lean_check` record. Revision 1 (`.../revision-1-2ff5490ad7f4ccaaebae891918abad774e4bd340d097fb7605d4f8c5aeb40960`, manifest SHA-256 `9a74687309136264117a55d233e93409cff5562b63cf4fd56c5960f5c0353968`) has the first seven runs. The draft is readable evidence for this section, not an accepted mathematical dependency.
- **What compiled.** The draft contains eleven NYLL modules, copied byte for byte with their headers. Its `LICENSE.md` and `NOTICE.md` reproduce NYLL's `LICENSE` and `NOTICE` verbatim inside code blocks, because drafts accept only `.lean` and `.md` files. The modules are:
  - nine leaf modules: `ValuedFieldTheory/LocalField/NonarchimedeanLocalField/{Basic,PrincipalUnits,PrincipalUnitQuotients,IdealQuotients,NormQuotient}`, `ValuedFieldTheory/LocalField/NormUnits` and `ClassFieldTheory/Definitions/LocalClassFieldTheory/{FieldNormHom,FieldNormSubgroup,IsFieldNorm}`;
  - `ClassFieldTheory/Definitions/LocalClassFieldTheory/FieldNormQuotient` and `ClassFieldTheory/Theorems/LocalClassFieldTheory/FiniteAbelianLocalReciprocityQuotientEquivOfArtin`. With `FieldNormHom` and `FieldNormSubgroup` these form the whole NYLL closure of `finiteAbelianLocalReciprocity_quotientEquiv_of_artin`.

  It also contains `NyllProbe/Bridge.lean` (SHA-256 `9ca80cc37862f539233d4bfa99cb595800e141025ada2a2f698f0cfb95171549`) with four theorems: `nyll_v_eq_neg_ord`, `ord_prime_eq_one`, `fieldNormSubgroup_eq` (by `rfl`) and `transfer_of_norm`. The nine leaf modules and the bridge built unchanged with 0 errors and 0 warnings in run `6639672a-c115-4bab-9bbe-585dc22ff451`, rechecked as run `c673766a-26b7-4749-b60b-5c487bdc01e3`. With the two further modules, run `8a578284-61c1-4f17-baee-755f538a837b` and its recheck `40a694c4-cdd0-4d79-9554-1ca322f600b4` also finished with 0 errors and 0 warnings. The quotient-equivalence module has SHA-256 `313cf68dcc8db62673ae6e182d03c9fc22b4556078a031ef700966c771aafa23` in those records.
- **Axiom checks.**
  - Inspecting `NyllProbe.ord_prime_eq_one` (run `c842fac0-87dc-456f-8ad9-bb460feeea66`) and `NyllProbe.transfer_of_norm` (run `c673766a`) shows exactly `propext`, `Classical.choice` and `Quot.sound`. `ord_prime_eq_one` uses NYLL's `LocalFieldTheory.v_integerRingIrreducibleFieldUnit`, so that lemma and its leaf closure were checked by the kernel in our environment.
  - Inspecting `ClassFieldTheory.finiteAbelianLocalReciprocity_quotientEquiv_of_artin` (run `8a578284`) shows the same three axioms, with level parameters `u` and `v`.
  - Four further runs (`6a36db84`, `96477188`, `9db1f396`, `1ce0c59c`) inspected the four bridge theorems with the same result. `Bridge.md` lists them.
- **Not obtained.** We have no build, kernel or axiom result for the 258–502-module Artin-map closures in any environment. Their compatibility with our Mathlib is untested.

**Textual checks (not kernel evidence).**

- After comment stripping, none of the closures contains `sorry`, `admit`, `axiom`, `opaque`, `native_decide`, `implemented_by` or `extern`.
- Repository-wide, the only `opaque` hits are in `GlobalClassFieldTheory/Reciprocity/LocalGlobalArtinCompatibility`, which lies outside these closures.

**Author report (not reproduced).** GitHub Actions workflow "Lean", run 39531661716 (workflow_dispatch, 2026-10-21) at the pinned commit, succeeded in all jobs.

- Its verify step is described as "Build, audit all declarations, check NanoDa, and replay the Lean kernel". The supplement's `.github/verification/verify.py` allows only the three standard axioms.
- `main-declarations.json` lists `ClassFieldTheory.finiteAbelianLocalReciprocity`, checking only that it exists and what kind of declaration it is; it "does not compare theorem statements".

## 5. Overlap with current Mathlib and the Library, and version problems

**Mathlib version gap.**

- NYLL's Mathlib pin is 69 commits **ahead** of ours; ours is an ancestor of it.
- The GitHub compare caps its file list at 300 files. Even so, it shows 17 changed modules among the 261 Mathlib modules imported directly by the wrapper closure, and 19 among the 299 imported by the union. Those 19 include:
  - `Subgroup.{Defs,Ker,Lattice,Map,Pointwise}`;
  - `ModuleCat.Basic`;
  - `Galois.Basic` and `Galois.IsGaloisGroup`;
  - `IntermediateField.Adjoin.Basic`;
  - `PurelyInseparable.Basic`;
  - `FiniteAbelian.{Basic,Duality}`;
  - `Int.WithZero`;
  - `ZMod.Basic`.
- Expect lemma-name and simp-set breakage in a port. The Lean version also differs (4.35.0-rc2 against 4.34.0).

**Mathlib overlap.** Our Mathlib has the classes NYLL builds on: `ValuativeRel`, `IsNonarchimedeanLocalField`, `Valuation.HasExtension`, `Valuation.IsUniformizer`, `IsAbelianGalois`, `AlgEquiv.restrictNormalHom` and `restrictNormalHom_id`, and the Krull topology. NYLL and the Library both build on its `Algebra.norm`, `groupCohomology`, `tateCohomology` and finite-field Frobenius `FiniteField.frobeniusAlgEquivOfAlgebraic` (`Mathlib/FieldTheory/Finite/Basic.lean:363`). Our Mathlib has no local reciprocity map, no class formation and no upper-numbering filtration: case-insensitive searches for `class formation`, `upper numbering`, `upperRamification` and `Herbrand` find nothing.

**Library overlap, by declaration.** The comparison below uses the Library commit of section 1. Library files are in `Langlands/ClassFieldTheory/Local/` unless a path is given. `LCF.` abbreviates the namespace `Langlands.LocalClassField`, and `CFT.` abbreviates `Langlands.ClassFieldTheory.Local`. The public note [Local class-field theory: constructions and statement coverage](../class-field-theory/local-coverage.md) maps many of these declarations, and records that "No canonical reciprocity map is defined." Each item names the NYLL component a port would use.

1. **Norm map, norm subgroup and norm quotient.**
   - NYLL: `LocalFieldTheory.localNormSubgroup` and `NormQuotient`, with `K` and `L` in one universe, and `LocalFieldTheory.normUnits`, `fieldNormHom`, `fieldNormSubgroup`, `IsFieldNorm` and `FieldNormQuotient`, with independent universes (A.5).
   - Library: `LCF.normUnits`, `normSubgroup`, `NormQuotient`, `normQuotientProjection`, `normQuotientTowerProjection` and `normQuotientTowerNorm` (`Norms.lean:23-69`), in independent universes; the continuous versions `localNorm`, `localNormSubgroup` and `LocalNormQuotient` (`Norms.lean:108-140`).
   - Comparison: all of these are built from `Units.map (Algebra.norm K)`, and unfolding `normSubgroup` gives the subgroup written out in `FiniteReciprocityStatement.lean`. A port keeps NYLL's vocabulary inside the copied modules, because their proofs use it, and connects to ours by unfolding, as `NyllProbe.fieldNormSubgroup_eq` does (section 4).
2. **Quotient equivalence from a given map.**
   - NYLL: `finiteAbelianLocalReciprocity_quotientEquiv_of_artin` (A.12).
   - Library: `LCF.finiteNormQuotientMap` (`FiniteArtin.lean:62`), for maps that kill the norm subgroup, and `LCF.finiteNormResidueEquiv` (`FiniteArtin.lean:73`), for maps satisfying `FiniteNormResidueRelation` (`FiniteArtin.lean:31`). `finiteArtinCharacterEquiv` (`FiniteArtin.lean:132`) is built on the latter. These are conditional constructors.
   - Same mechanism: both build the group isomorphism as Mathlib's `QuotientGroup.quotientKerEquivOfSurjective` after `QuotientGroup.quotientMulEquivOfEq`, and both get continuity of the inverse from the discrete finite Galois group.
   - Different scope: the Library takes `K : Type u` with `[Field K] [TopologicalSpace K] [IsTopologicalRing K]` and no local-field instance, and `L : FiniteAbelianExtension K`. That is a finite Galois intermediate field of `AlgebraicClosure K` with commutative Galois group (`Galois.lean:98`), so it lives in the universe of `K`. NYLL takes standalone `K : Type u` and `L : Type v` with `[FiniteDimensional K L] [IsAbelianGalois K L]` and local-field instances on `K`.
   - Different form: the Library returns the equivalence as data and states no evaluation or uniqueness lemma for it. NYLL proves `∃! e, ∀ x, e (QuotientGroup.mk' _ x) = artin x`.
   - Neither applies verbatim to our Props. Section 2.7 compares the routes.
3. **The reciprocity isomorphism itself.**
   - NYLL: `abelianizationEquivNormQuotient`, that is `concreteReciprocityEquiv` (A.4). Its inputs are a `DegreeData` (`AbstractClassFieldTheory/Degree/Fields.lean:40`), a `ValuationData` (`AbstractClassFieldTheory/Degree/Valuation.lean:161`) and `SatisfiesClassFieldAxiom` (`AbstractClassFieldTheory/Reciprocity/ClassFieldAxiom.lean:60`), all under `Nyll/ClassFieldTheory/`. The axiom is proved for local fields by `separableClosureUnits_isClassFormation` (`.../LocalReciprocity/LocalClassFieldAxiom.lean:147`).
   - Library: `CFT.abelianizationCupEquiv`, `CFT.arithmeticReciprocityOfCup` and `CFT.geometricReciprocityOfCup` (`TateAbelianization.lean:66, 82, 99`), for standalone `K : Type v` and finite Galois `L : Type u`. They are built from `relativeTateCup` (`TateCup.lean:21`), `integralTateMinusTwoEquiv` (`TateAbelianization.lean:16`) and `tateZeroEquivNormQuotient` (`TateNormQuotient.lean:82`). The class-formation layer around them includes `multiplicativeFormation` (`MultiplicativeFormation.lean:33`), `InvariantFamily` (`Invariants.lean:19`), `IsFundamentalClass` and `HasUniqueFundamentalClass` (`FundamentalClasses.lean:24, 30`), `RelativeClassFormation` (`ClassFormation.lean:103`) and `FundamentalClassTateIsomorphisms` (`TateCup.lean:35`), with the targets `LocalRelativeClassFormationStatement` and `LocalCompatibleClassFormationStatement` (`ClassFormationStatement.lean:20, 36`).
   - Status in the Library: the three constructors take a class `c : relativeCohomology K L 2` and a proof `h` that `relativeTateCup K L (-2) c` is bijective. They return algebraic `≃*` equivalences without topology. `TateAbelianization.md` says that "no choice of an unconditional local reciprocity map is made". No Library theorem proves that a fundamental class exists or that its cup map is bijective.
   - Different routes: the Library follows Serre's cohomological route, where reciprocity is the inverse of the cup product with a fundamental class. NYLL follows a Neukirch-style abstract route: a continuous surjective degree map to `ℤ̂`, a Henselian valuation, and the class-field axiom `#Ĥ⁰ = [L:K]`, `#Ĥ⁻¹ = 1` for cyclic extensions. NYLL has no cup product or fundamental class. In its `ClassFieldTheory` and `GaloisCohomology` trees, searches find no whole word `cup`, no `Cup` or `cupProduct`, and, ignoring case, no `fundamental class` or `fundamentalClass`. So NYLL cannot supply `c` and `h`, and the Library proves no class-field axiom.
   - Consequence: a port adds a second, independent construction of the reciprocity map next to the cohomological route of tasks `c7513fdc` (class-formation statements) and `d173a3b0` (cup and transfer construction). No theorem in either project compares the two maps.
4. **Coefficients and universes.**
   - NYLL: `IntegralRepGroupType := Type 0` (`Nyll/GaloisCohomology/Cyclic/IntegralRepUniverse.lean:18`), `Rep ℤ G` and Mathlib's `tateCohomology`.
   - Library: `CFT.IntegerScalars := ULift ℤ` (`Cohomology.lean:22`) with `integerScalarsEquiv` (`:25`), and `unitsRepresentation (K : Type v) (L : Type u) : Rep.{u} IntegerScalars.{u} Gal(L/K)` (`:28`). On these coefficients it defines `absoluteCohomology`, `relativeCohomology`, `relativeTateCohomology` and `integralTateCohomology` (`:90-108`). `relativeH2Equiv` (`RelativeH2Transport.lean:184`) transports relative H² along a `K`-algebra isomorphism `L ≃ₐ[K] M` between fields in independent universes. Hilbert 90 is proved as `finiteRelativeH1Vanishing` (`RelativeH1Proof.lean:9`, independent universes) and `absoluteH1Vanishing` (`AbsoluteH1Proof.lean:30`).
   - Comparison: the Library meets Mathlib's common-universe requirement by lifting the coefficient ring, so its relative cohomology works for fields in arbitrary universes. `Cohomology.md` notes that its tower maps still use one shared carrier universe. Moving NYLL onto these coefficients would remove its universe-0 restriction, but it means rewriting NYLL's `GaloisCohomology` and abstract class-field modules rather than copying them (API problem 1 below).
5. **Unramified normalization.**
   - NYLL: `IsUnramifiedValuedExtension`, `arithmeticFrobeniusOfUnramifiedValuation` (`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/UnramifiedFrobenius.lean:129`), `finiteAbelianLocalArtinMap_eq_frobenius_zpow` and `finiteAbelianLocalArtinMap_inverseUniformizer_residue_pow` (A.7).
   - Library: in `ResidueNormalization.lean`, the constructed class `LCF.ResidueNormalization.geometricFrobeniusClass K L : Gal(L/K) ⧸ LocalGalois.inertia K L` (`:30`), which is an element of the Galois group modulo inertia, not a predicate. Also the predicates `HasGeometricResidueAction` (`:44`), `GeometricNormalization` (`:80`) and `Canonical.GeometricNormalization` (`:161`), and the lemmas `hasGeometricResidueAction_iff_inverse_power`, `normalized_uniformizer` and `normalized_unit` (`:59-106`). They are stated through `Langlands.LocalGalois.residueHom` and `inertia` (`Langlands/Galois/Local/SpectralDefinitions.lean:64`) and the proved `residueQuotientEquiv` (`Langlands/Galois/Local/SpectralProof.lean:267`). Also `CFT.IsArithmeticUnramifiedCoordinate` (`Invariants.lean:47`), whose existence for unramified extensions is the proposition `ArithmeticUnramifiedCoordinateExistence` (`UnramifiedArithmeticStatement.lean:22`), proved as `arithmeticUnramifiedCoordinateExistence` (`UnramifiedArithmeticProof.lean:150`). It supplies an arithmetic Frobenius coordinate on `Gal(E/F)`, not a reciprocity map. The proved theorems `unramifiedUnitNorms`, `unramifiedNormMembership`, `unramifiedCyclicNormQuotient` and `relativeNormOrderLaws` (in `UnitNormProof.lean`, `UnramifiedNormMembershipProof.lean`, `UnramifiedCyclicNormQuotientProof.lean` and `NormOrderProof.lean`) concern norms and orders, not a reciprocity map.
   - Comparison: `GeometricNormalization` states that a supplied map is geometrically normalized, for any Galois `L/K` including ramified ones, with residue fields taken from the spectral valuation. NYLL's theorems normalize only its own map and only for unramified `L/K`, with the residue fields `𝓀[L]` of `ValuativeRel` and integral-closure instances. Both use Mathlib's `FiniteField.frobeniusAlgEquivOfAlgebraic` as residue Frobenius: NYLL in `residueExtensionArithmeticFrobeniusOfValuationExtension` (`UnramifiedFrobenius.lean:36`), and the Library in `Langlands.Galois.FiniteField.arithmetic` (`Langlands/Galois/FiniteField/Frobenius.lean:28`), whose inverse `geometric` defines `geometricFrobeniusClass`. The bridge restates NYLL's conclusion as `GeometricNormalization`, which needs a comparison of the two residue fields.
6. **Tower restriction, norm square and transfer.**
   - NYLL: `finiteAbelianLocalArtinMap_restrict_tower` (A.8) and `abelianLocalArtinMonoidHom_norm_restriction` (A.9), for standalone fields at `Type`. NYLL also states norm and transfer squares in a fixed-field presentation, in particular `LocalFixedFieldNormRestrictionSquare.norm_restriction_commutes` and `LocalFixedFieldTransferTower.transfer_inclusion_commutes` (section 2.4, A.13).
   - Library, restriction and system relations: `LCF.FiniteArtinRestrictionRelation` and `FiniteArtinSystemRelation` (`FiniteArtin.lean:37, 43`) are relations on a supplied `FiniteArtinFamily K` (`:24`). That is a family of maps `Kˣ →ₜ* L.galoisGroup` indexed by `L : FiniteAbelianExtension K`, for `K : Type u` from the section variables at `FiniteArtin.lean:20`. The index consists of the finite Galois intermediate fields of `AlgebraicClosure K` with commutative Galois group (`Galois.lean:98`). Restriction is the constructed map `FiniteAbelianExtension.restrictionOfLE` (`Galois.lean:137`).
   - Library, norm and transfer squares: `FiniteNormCompatibility` and `FiniteTransferCompatibility` (`FiniteArtin.lean:198, 207`) are in the separate `FiniteTower` section. Its variables (`FiniteArtin.lean:165-166`) are `{K : Type u} {M : Type v} [Field K] [Field M] [Algebra K M] [FiniteDimensional K M] (E : IntermediateField K M)`. So `M/K` is any finite extension, in an independent universe, and need not be Galois or abelian. Neither `AlgebraicClosure` nor `FiniteAbelianExtension` occurs in these definitions. The predicates relate supplied algebraic homomorphisms `aK : Kˣ →* TopologicalAbelianization Gal(M/K)` and `aE : Eˣ →* TopologicalAbelianization Gal(M/E)`:
     - the norm square is `aK.comp (normUnits K E) = (finiteGaloisAbelianInclusion E).toMonoidHom.comp aE`;
     - the transfer square is `aE.comp (Units.map (algebraMap K E).toMonoidHom) = (finiteGaloisAbelianTransfer E).toMonoidHom.comp aK`.

     The maps `finiteGaloisInclusion`, `finiteGaloisAbelianInclusion` and `finiteGaloisAbelianTransfer` (`FiniteArtin.lean:177, 185, 191`) are constructed. `FiniteArtin.md` says these constructions work for any finite overfield, and that class-field applications use a Galois one. No Library statement target uses the two predicates, and `FiniteArtin.lean` contains no theorems.
   - Comparison for the restriction and system relations: NYLL's tower theorem has the shape of `FiniteArtinRestrictionRelation`. `restrictionOfLE` is `AlgEquiv.restrictNormalHom` for the algebra given by the inclusion of intermediate fields, so the theorem applies to the carriers of two index members. These carriers are in the universe of `K`, so NYLL's maps need `K : Type` here. Our `FiniteAbelianRestriction` is stated for standalone fields and matches NYLL's theorem without this index (section 2.7). The index matters only when passing between standalone fields and intermediate fields of `AlgebraicClosure K`, as for `finiteNormResidueEquiv` (item 2), which is the transport of item 9.
   - Comparison for the norm and transfer squares: no passage into `AlgebraicClosure K` is involved. Take `M = L` finite Galois over `K`. Then the type of `aK` is the type of the underlying homomorphism of NYLL's `localArtinMap K L : Kˣ →ₜ* TopologicalAbelianization Gal(L / K)` (A.3), which NYLL defines for every finite Galois `L/K`, not only abelian ones. However, for standalone fields NYLL proves its norm square only for `abelianLocalArtinMonoidHom`, that is, for abelian `L/K`. Using it there needs three separate comparisons:
     - **Intermediate-field presentation.** NYLL's theorem takes a standalone field `K'` with its own `ValuativeRel`, topology, `IsNonarchimedeanLocalField` and `Valuation.HasExtension` instances. For the Library predicate these must be supplied on the subtype `↥E` of `L`. Our Props take standalone `F`, `E` and `L`, so passing between the two forms needs `E` identified with its image in `L`, an `IntermediateField F L`.
     - **Abelianization.** The Library uses `TopologicalAbelianization` of the Galois groups; NYLL's abelian map and our Props use `Gal(L/K)` itself. For abelian `L/K`, NYLL's `topologicalAbelianizationEquivSelf` (A.2) identifies the two, and `abelianLocalArtinMap` is `localArtinMap` followed by it. Under these identifications `finiteGaloisAbelianInclusion E` must agree with `AlgEquiv.restrictScalars K`, the map in NYLL's square. This holds by unfolding: `finiteGaloisInclusion` (`FiniteArtin.lean:177`) uses the inverse of Mathlib's `IntermediateField.fixingSubgroupEquiv` (`Mathlib/FieldTheory/Galois/Basic.lean:268`), which is `ϕ ↦ ϕ.restrictScalars _`. Neither project states it as a lemma, and I did not check it in Lean.
     - **Universes.** These predicates allow `K : Type u` and `M : Type v`, while NYLL's maps need `K L : Type`. The universe transport of API problem 1 is still needed, but not the closure transport.

     Transfer: in the abelian case `FiniteTransferCompatibility` would follow from the norm square. For `a ∈ K`, `N_{E/K}(a) = a^[E:K]`. Mathlib's `MonoidHom.transfer_eq_pow` (`Mathlib/GroupTheory/Transfer.lean:206`) makes inclusion after transfer the power by the index `[Gal(L/K) : Gal(L/E)] = [E:K]`. And `finiteGaloisAbelianInclusion E` is injective when `Gal(L/K)` is abelian. The probe's `NyllProbe.transfer_of_norm` proves only the degree-power form used in our Prop, not the Library predicate. For nonabelian Galois `L/K`, NYLL states no norm or transfer square for `localArtinMap`. Its fixed-field squares (A.13) allow nonabelian finite Galois extensions. With base `K`, intermediate field `E` and top field `L`, they have the shapes of the two Library predicates. Applying them would need one more comparison: from NYLL's fixed fields in `SeparableClosure K`, with algebraic abelianizations, to `E : IntermediateField K L` and `TopologicalAbelianization`. NYLL makes such a comparison only for the abelian norm square (section 2.4). I did not check whether its fixed-field symbols agree with `localArtinMap`. NYLL's abstract transfer–norm modules (`MainTransfer.lean` and `TransferNaturality.lean` in `AbstractClassFieldTheory/Reciprocity/Construction/`) were not audited.
   - Our `FiniteAbelianNormTransfer` uses neither Library predicate. It states the norm clause with `restrictScalars` and the transfer clause as the degree power, for standalone `F`, `E` and `L` and plain Galois groups. The Library predicates are therefore an additional possible target for NYLL's maps, not a step towards our Props.
7. **Inertia.**
   - NYLL: `finiteAbelian_filteredLocalReciprocity` and `localUpperRamificationGroup_zero_eq_residue_ker` (A.10).
   - Library: `Langlands.LocalGalois.inertia` (item 5), and `Langlands.Ramification.Padic.inertia`, `lowerRamificationGroup` (`Langlands/LocalFactor/Ramification/Galois.lean:137, 140`) and `upperRamificationGroup` (`Langlands/LocalFactor/Ramification/Herbrand/Finite.lean:175`). The image statements are targets: `FiniteReciprocityInertiaImages` (`FiniteConductorStatement.lean:41`), and `FiniteReciprocityHigherUnitImages` and `FiniteReciprocityRealUnitImages` (`UpperReciprocityStatement.lean:22, 40`).
   - Comparison: clause (ii) needs NYLL's case `t = 0`. For `t > 0` NYLL's theorem has the shape of the Library's upper-unit targets, but those are stated for profinite maps satisfying `GeometricProfiniteReciprocityRelation` and use the Library's own ramification groups. Identifying the two filtrations is a further bridge, outside this audit.
8. **Family index and uniqueness.**
   - NYLL: `ClassFieldTheory.FiniteAbelianLocalExtension` in `SeparableClosure K`, with `finiteAbelianLocalReciprocity_family` and `finiteAbelianLocalReciprocity_family_ext` (A.11).
   - Library: `LCF.FiniteAbelianExtension` in `AlgebraicClosure K` (`Galois.lean:98`), the family type `FiniteArtinFamily` (`FiniteArtin.lean:24`), the relations `FiniteArtinSystemRelation`, `ProfiniteNormResidueRelation` (`FiniteArtin.lean:43, 54`) and `GeometricProfiniteReciprocityRelation` (`ProfiniteReciprocityStatement.lean:21`), and the target `ProfiniteReciprocityExistenceUniqueness` (`ProfiniteReciprocityStatement.lean:47`).
   - Comparison: the index types differ in the closure, the bundling, and `IsMulCommutative` against `IsAbelianGalois`. `_family_ext` is the kind of uniqueness these targets need, but it is stated for NYLL's index at `Type`.
9. **Field and universe transport.**
   - NYLL: `nonarchimedeanLocalField_small`, the `ShrinkTransport` module and `shrinkUnitsContinuousMulEquiv` (API problem 1).
   - Library: `LCF.extensionFiniteIntermediate`, `extensionIntermediateContinuousAlgEquiv` and `extensionIntermediateUnitsEquiv` (`ExtensionFieldTransport.lean:26, 57, 75`); `extensionIntermediate_residueCardinality`, `extensionIntermediate_ord` and `extensionIntermediate_discreteValuation` (`ExtensionValuationTransport.lean:24, 30, 39`); `CFT.galoisConjugacy` (`Conjugacy.lean:49`).
   - Comparison: given `f : F.Carrier →ₐ[Padic p] E.Carrier`, the Library moves a standalone extension `E` to its image in `AlgebraicClosure F.Carrier`. It preserves the topology, units, order, discrete valuation and residue cardinality. This is the step between our standalone Props and the `FiniteAbelianExtension K` index used by `FiniteArtinFamily`, `finiteNormResidueEquiv` and the restriction and system relations of `FiniteArtin.lean`. The norm and transfer predicates of that file take intermediate fields of an arbitrary finite `M/K` and do not need it (item 6). It stays in the universe of `F`, and the Library has no `Small` or `Shrink` transport of local fields to universe 0.

**What the Library does not have.** Each Library construction of a reciprocity map or equivalence takes the decisive data as input:

- a map with its kernel certificate (`finiteNormResidueEquiv`);
- a degree-two class with a proof of cup bijectivity (`abelianizationCupEquiv` and its inverses);
- a supplied candidate family (`extensionReciprocityCandidate`, `ReciprocityTransport.lean:77`).

No Library declaration defines a map `Kˣ → Gal(L/K)`, or an equivalence between the norm quotient and the Galois group, without such inputs. In particular there is no normalized map: `GeometricNormalization` and `GeometricProfiniteReciprocityRelation` are predicates on supplied maps. None of the targets in `FiniteReciprocityStatement.lean`, `ProfiniteReciprocityStatement.lean`, `UpperReciprocityStatement.lean` or `ClassFormationStatement.lean` is proved. NYLL's `abelianLocalArtinMap` needs no such inputs, and supplying such a map is the purpose of a port.

**API problems.**

1. **Universes.**
   - **Where NYLL fixes universe 0.** `Nyll/GaloisCohomology/Cyclic/IntegralRepUniverse.lean` declares `abbrev IntegralRepGroupType := Type 0`. The class-field axiom in `AbstractClassFieldTheory/Reciprocity/ClassFieldAxiom.lean:29-62` takes `G : IntegralRepGroupType`, a module `A : Rep ℤ G` and Mathlib's `tateCohomology`. The local construction uses the absolute Galois group of `K` for `G` and the units of `SeparableClosure K` for `A` (A.4), so it needs `K : Type`.
   - **NYLL's stated reason is inaccurate.** Comments in both files say that Mathlib's `Rep ℤ G` puts the coefficient ring and the group in one universe. It does not. In our Mathlib, `structure Rep (k : Type u) (G : Type v)` has independent universes and a carrier `V : Type w` (`Mathlib/RepresentationTheory/Rep/Basic.lean:24-33`). The file is byte-identical at NYLL's pin (section 1).
   - **The actual constraint.** The shared universe comes from Mathlib's cohomology APIs. Examples are `variable {R G : Type u}` at `Mathlib/RepresentationTheory/Homological/TateCohomology/Basic.lean:57` (also byte-identical at NYLL's pin) and `variable {k G : Type u}` at `Mathlib/RepresentationTheory/Homological/GroupCohomology/Basic.lean:75`. With coefficients `ℤ : Type 0`, these APIs force `G : Type 0`.
   - **The Library's coefficient lift.** The Library already avoids this constraint by lifting the coefficient ring: `CFT.IntegerScalars := ULift ℤ`, with `unitsRepresentation (K : Type v) (L : Type u) : Rep.{u} IntegerScalars.{u} Gal(L/K)` (Library overlap, item 4). Rebuilding NYLL's class-formation layer on such coefficients would remove its universe-0 restriction. That is a rewrite of NYLL's cohomology modules, and I did not estimate its size. Transport through universe-0 models is proposed below as the practical route, not as the only one.
   - **NYLL's existing transport.** `LocalFieldTheory.nonarchimedeanLocalField_small` (`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Small.lean:30`) gives `Small.{0} K` for a local field `K : Type u`. `ShrinkTransport.lean` in the same folder moves the valuative relation, the topology and `IsNonarchimedeanLocalField` to `Shrink.{0} K`, and its `hasExtension_comap_ringEquivs` moves `Valuation.HasExtension` along ring equivalences. `LocalClassFieldTheory/Finite/Existence/ShrinkOpenSubgroups.lean:30` gives `shrinkUnitsContinuousMulEquiv K : (Shrink.{0} K)ˣ ≃ₜ* Kˣ`. NYLL uses these to make its existence classification universe-polymorphic (`finiteAbelianLocalExistence (K : Type u)`), but not its Artin map. `ShrinkTransport` has a 33-module closure. I read only the statements of these modules.
   - **Our options.** Either port NYLL's `Shrink` transport, or build universe-0 models ourselves, for example as images of embeddings into `AlgebraicClosure (Padic p)`, transported along algebra isomorphisms. The Library's `extensionFiniteIntermediate` transport (Library overlap, item 9) already moves an extension to its image in `AlgebraicClosure F.Carrier`, with its topology, units and valuation, but it stays in the universe of `F`. `ReciprocityTransport.lean` uses it to transport Weil candidates.
2. **Instances.**
   - Base field: our `TopologicalData` supplies `topology`, `valuativeRel` and `localField`, which are exactly NYLL's instances on `K`. NYLL's `IsNonarchimedeanLocalField` is Mathlib's class. The probe uses these instances directly.
   - Extension field: normalization, inertia and the norm square also need `UniformSpace`, `IsUniformAddGroup` and `Valuation.HasExtension (valuation F) (valuation E)` on the extension. We would derive these from `TE` using uniqueness of extended valuations.
   - Arguments found by instance search: in the unramified statements (A.7), `IsUnramifiedValuedExtension K L` and `arithmeticFrobeniusOfUnramifiedValuation K L` also need `TopologicalSpace L`, `Module.Finite 𝒪[K] 𝒪[L]` and `IsIntegralClosure 𝒪[L] 𝒪[K] L`. These are not binders of the theorems. `TopologicalSpace L` comes from `UniformSpace L`. NYLL declares instances for the other two, such as the global `LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite` (`.../LocalReciprocity/UnramifiedComparison.lean:145`) and the private `normalizationIntegerRingIsIntegralClosure` (`UnramifiedNormalization.lean:173`). A port must keep such instances or supply the arguments explicitly. I did not elaborate these statements, so I have not confirmed which instances Lean selects.
3. **Formulation.** Our clauses use `TE.discreteValuation` inequalities and `TF.residueCardinality`. NYLL uses `𝒪[L]` residues and `Nat.card 𝓀[K]`.
4. **Common-closure index.** NYLL's family index is in `SeparableClosure K`; our common-closure index is in `AlgebraicClosure F.Carrier`. They are equivalent in characteristic 0, but the index types differ.

## 6. Verdict and smallest next units

**Adapt.** Do not use NYLL directly, and do not import the repository as a whole. Do not reject it for the finite statements: one map, `abelianLocalArtinMap`, has the norm kernel, geometric sign, tower restriction, norm square and inertia image that `FiniteAbelianReciprocityTheorems` needs. The Library has no map defined without supplied data (section 5). The quotient step is already in reach. It is the first isomorphism theorem, as in the Library's `finiteNormResidueEquiv`, and NYLL's `finiteAbelianLocalReciprocity_quotientEquiv_of_artin` compiled unchanged in our environment with the three standard axioms (section 4). The remaining obstacles are listed in sections 2.7 and 5:

- universe transport;
- the extension-field valuation instances;
- the ramified residue normalization;
- an untested port of at least 258 modules across a Lean/Mathlib gap;
- the port's construction would sit next to the Library's cohomological route (section 5, item 3), so it needs the agreement of that route's owners.

**Reject for `ReciprocitySystemStatement.lean`.** NYLL supplies no Weil-group component. At most, its finite abelian Galois-side maps could later feed the finite norm-residue relations.

**Smallest next units.** Each unit except the owner decision needs its own authorized task, with published statement targets, normal validation and independent review. They are listed in dependency order:

1. **Port-feasibility build.** Copy the 258-module `NormResidue` closure verbatim into a private draft and `lean_check` it in environment `3b864ddf`. Record every break caused by the Mathlib/Lean gap. Then extend it to the `GeneralTowerNaturality`, `UnramifiedNormalization`, `NormRestriction` and `Filtered/FiniteAbelian` closures (262, 265, 280 and 402 modules), and to the 33-module `ShrinkTransport` closure if NYLL's transport is chosen. This decides whether a focused port with original headers, `LICENSE` and `NOTICE` is feasible.
2. **Owner decision.** With the result of unit 1, the owners named in this task's context decide whether the Library should carry NYLL's construction next to the cohomological route, or use NYLL only as a proof route. They own the local class-field construction (tasks `6abce376-f18c-478f-9309-c0c1010f7a99` and `7b4a513d-a3bc-4cb7-af3c-03c4580608f7`), the class-formation statements (`c7513fdc-eb44-48b5-8734-001f18050403`) and the cup and transfer construction (`d173a3b0-7ea1-4c57-afe4-d5d37694635e`).
3. **Statements.** Publish, as new Prop targets with the existing owners' agreement:
   - **(a)** the universe-0 instances `FiniteAbelianReciprocity.{0,0}`, `FiniteAbelianNormTransfer.{0,0,0}` and `FiniteAbelianRestriction.{0,0,0}`;
   - **(b)** the universe-transport implication from those instances to the arbitrary-universe Props;
   - **(c)** the ramified residue normalization through the maximal unramified subextension.
4. **Proofs, in order.** These need the port from unit 1.
   - The quotient equivalences, by the first isomorphism theorem as inside `finiteNormResidueEquiv`, or from `finiteAbelianLocalReciprocity_quotientEquiv_of_artin` (section 2.7).
   - Universe-0 `FiniteAbelianRestriction`, from `finiteAbelianLocalArtinMap_restrict_tower`.
   - `FiniteAbelianNormTransfer`, from `abelianLocalArtinMonoidHom_norm_restriction` and `transfer_of_norm`.
   - Clause (i), unramified first and ramified second.
   - Clause (ii), from the `t = 0` filtered theorem.
   - Finally the transport (3b).

Until unit 1 succeeds, NYLL serves only as a proof route and naming reference. Apart from the eleven modules compiled in section 4, none of its theorems has been checked in our environment, and none is established in this project.

## Appendix A. Full declaration types

The blocks below are copied verbatim from the snapshot at commit `fbd320cd`. Each label gives the path relative to `Nyll/`, the line range and the enclosing namespace. The wrapper itself is in section 2.1.

- A `variable` block is the section context of the later blocks from the same file. It supplies their binders.
- The universe variables `u` and `v` are declared by `universe` commands at the top of their files.
- Theorem blocks stop at `:=` or `:= by`, so the proofs are not reproduced; the exception is the short proof in A.1. Definition blocks include their bodies, except that the proof fields of two definitions written with `where` (`principalUnits` and `galoisGroupResidueAlgEquivHomOfIsIntegralClosure`) are replaced by a comment.
- Fully qualified names of the unqualified references:
  - in `LocalFieldTheory`: `localNormSubgroup`, `NormQuotient`, `normClass`, `normUnits`, `principalUnits`, `fieldPrincipalUnits` and `galoisGroupResidueAlgEquivHomOfIsIntegralClosure`;
  - in `LocalFieldTheory.IsNonarchimedeanLocalField`: `v`, `valuationMap`, `integerUnitsToFieldUnits` and `IsUnramifiedValuedExtension`;
  - in `RamificationTheory`: `natCeilStepFiltration`; in `RamificationTheory.LocalField`: `localUpperRamificationGroup`;
  - in `ClassFieldTheory`: `fieldNormHom`, `fieldNormSubgroup`, `IsFieldNorm`, `FieldNormQuotient` and `FiniteAbelianLocalExtension`.
- From Mathlib: `IsNonarchimedeanLocalField`, `ValuativeRel`, `Valuation.HasExtension`, `TopologicalAbelianization`, `Abelianization.equivOfComm` and the notation `Gal(L / K)` for `L ≃ₐ[K] L`. The scoped `ValuativeRel` notations `𝒪[K]`, `𝓂[K]` and `𝓀[K]` denote the valuation ring, its maximal ideal and its residue field (`Mathlib/Topology/Algebra/Valued/ValuativeRel.lean:88-94`).

### A.1 Wrapper interface

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/MathlibInterface.lean:72-87` (namespace `ClassFieldTheory.LocalCFT`)

```lean
theorem finiteAbelianLocalReciprocity
    (K L : Type)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    ∃ artin : Kˣ →ₜ* (L ≃ₐ[K] L),
      Function.Surjective artin ∧
      ∀ x : Kˣ, artin x = 1 ↔ IsFieldNorm K L x := by
  refine ⟨LocalClassFieldTheory.abelianLocalArtinMap K L,
    LocalClassFieldTheory.abelianLocalArtinMap_surjective K L, ?_⟩
  intro x
  change x ∈ (LocalClassFieldTheory.abelianLocalArtinMap K L).toMonoidHom.ker ↔
    x ∈ fieldNormSubgroup K L
  rw [LocalClassFieldTheory.abelianLocalArtinMap_ker]
  rfl
```

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/MathlibInterface.lean:90-97` (namespace `ClassFieldTheory.LocalCFT`)

```lean
theorem finiteAbelianLocalReciprocity_quotient
    (K L : Type)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    Nonempty
      (FieldNormQuotient K L ≃ₜ* (L ≃ₐ[K] L)) := by
```

### A.2 The named Artin map

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/NormResidue.lean:29-31` (namespace `LocalClassFieldTheory`)

```lean
variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [FiniteDimensional K L] [IsAbelianGalois K L]
```

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/NormResidue.lean:35-38` (namespace `LocalClassFieldTheory`)

```lean
noncomputable def abelianLocalArtinMonoidHom :
    Kˣ →* Gal(L / K) :=
  ((Abelianization.equivOfComm (H := Gal(L / K))).symm).toMonoidHom.comp
    (localArtinMonoidHom K L)
```

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/NormResidue.lean:41-42` (namespace `LocalClassFieldTheory`)

```lean
theorem abelianLocalArtinMonoidHom_surjective :
    Function.Surjective (abelianLocalArtinMonoidHom K L) :=
```

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/NormResidue.lean:48-50` (namespace `LocalClassFieldTheory`)

```lean
theorem abelianLocalArtinMonoidHom_ker :
    MonoidHom.ker (abelianLocalArtinMonoidHom K L) =
      localNormSubgroup K L := by
```

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/NormResidue.lean:64-74` (namespace `LocalClassFieldTheory`)

```lean
noncomputable def topologicalAbelianizationEquivSelf :
    TopologicalAbelianization Gal(L / K) ≃ₜ* Gal(L / K) := by
  letI : DiscreteTopology (TopologicalAbelianization Gal(L / K)) :=
    QuotientGroup.discreteTopology (isOpen_discrete _)
  let e : TopologicalAbelianization Gal(L / K) ≃* Gal(L / K) :=
    (topologicalAbelianization_finite_equiv K L).symm.trans
      (Abelianization.equivOfComm (H := Gal(L / K))).symm
  exact
    { e with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
```

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/NormResidue.lean:78-82` (namespace `LocalClassFieldTheory`)

```lean
noncomputable def abelianLocalArtinMap :
    Kˣ →ₜ* Gal(L / K) :=
  (ContinuousMonoidHom.toContinuousMonoidHom
      (topologicalAbelianizationEquivSelf K L)).comp
    (localArtinMap K L)
```

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/NormResidue.lean:86-88` (namespace `LocalClassFieldTheory`)

```lean
theorem abelianLocalArtinMap_toMonoidHom :
    (abelianLocalArtinMap K L).toMonoidHom =
      abelianLocalArtinMonoidHom K L := by
```

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/NormResidue.lean:98-99` (namespace `LocalClassFieldTheory`)

```lean
theorem abelianLocalArtinMap_surjective :
    Function.Surjective (abelianLocalArtinMap K L) :=
```

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/NormResidue.lean:105-107` (namespace `LocalClassFieldTheory`)

```lean
theorem abelianLocalArtinMap_ker :
    (abelianLocalArtinMap K L).toMonoidHom.ker =
      localNormSubgroup K L := by
```

### A.3 Topological reciprocity layer

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/TopologicalReciprocity.lean:36-41` (namespace `LocalClassFieldTheory`)

```lean
noncomputable local instance normQuotientTopologicalSpace
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [TopologicalSpace K] :
    TopologicalSpace (NormQuotient K L) := by
  change TopologicalSpace (Kˣ ⧸ localNormSubgroup K L)
  infer_instance
```

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/TopologicalReciprocity.lean:220-225` (namespace `LocalClassFieldTheory`)

```lean
theorem localNormSubgroup_isOpen
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    IsOpen (localNormSubgroup K L : Set Kˣ) := by
```

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/TopologicalReciprocity.lean:334-339` (namespace `LocalClassFieldTheory`)

```lean
theorem normQuotient_discrete
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    DiscreteTopology (NormQuotient K L) := by
```

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/TopologicalReciprocity.lean:349-351` (namespace `LocalClassFieldTheory`)

```lean
variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [FiniteDimensional K L] [IsGalois K L]
```

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/TopologicalReciprocity.lean:363-368` (namespace `LocalClassFieldTheory`)

```lean
noncomputable def topologicalAbelianization_finite_equiv :
    Abelianization (Gal(L / K)) ≃* TopologicalAbelianization (Gal(L / K)) := by
  let h : Subgroup.topologicalClosure (commutator (Gal(L / K))) =
      commutator (Gal(L / K)) :=
    commutator_topologicalClosure_eq (Gal(L / K))
  exact QuotientGroup.quotientMulEquivOfEq h.symm
```

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/TopologicalReciprocity.lean:372-383` (namespace `LocalClassFieldTheory`)

```lean
noncomputable def localReciprocityEquiv :
    NormQuotient K L ≃ₜ* TopologicalAbelianization (Gal(L / K)) := by
  letI : DiscreteTopology (NormQuotient K L) := normQuotient_discrete K L
  letI : DiscreteTopology (TopologicalAbelianization (Gal(L / K))) :=
    QuotientGroup.discreteTopology (isOpen_discrete _)
  let e : NormQuotient K L ≃* TopologicalAbelianization (Gal(L / K)) :=
    (abelianizationEquivNormQuotient K L).symm.trans
      (topologicalAbelianization_finite_equiv K L)
  exact
    { e with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
```

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/TopologicalReciprocity.lean:395-398` (namespace `LocalClassFieldTheory`)

```lean
noncomputable def normClassContinuous :
    Kˣ →ₜ* NormQuotient K L :=
  { normClass K L with
    continuous_toFun := QuotientGroup.continuous_mk }
```

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/TopologicalReciprocity.lean:401-404` (namespace `LocalClassFieldTheory`)

```lean
noncomputable def localArtinMap :
    Kˣ →ₜ* TopologicalAbelianization (Gal(L / K)) :=
  (ContinuousMonoidHom.toContinuousMonoidHom (localReciprocityEquiv K L)).comp
    (normClassContinuous K L)
```

### A.4 Abstract reciprocity isomorphism

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/Main.lean:29-31` (namespace `LocalClassFieldTheory`)

```lean
variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [FiniteDimensional K L] [IsGalois K L]
```

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/Main.lean:40-45` (namespace `LocalClassFieldTheory`)

```lean
noncomputable def abelianizationEquivNormQuotient :
    Abelianization (Gal(L / K)) ≃* NormQuotient K L :=
  concreteReciprocityEquiv K L
    (localResidueDatum K)
    (localHenselianValuation K)
    (separableClosureUnits_isClassFormation K)
```

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/Main.lean:66-69` (namespace `LocalClassFieldTheory`)

```lean
noncomputable def localArtinMonoidHom :
    Kˣ →* Abelianization (Gal(L / K)) :=
  (abelianizationEquivNormQuotient K L).symm.toMonoidHom.comp
    (normClass K L)
```

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/Main.lean:75-81` (namespace `LocalClassFieldTheory`)

```lean
theorem localArtinMonoidHom_eq_of_embedding
    (i : L →ₐ[K] SeparableClosure K) :
    localArtinMonoidHom K L =
      concreteNormResidueSymbolOfEmbedding K L i
        (localResidueDatum K)
        (localHenselianValuation K)
        (separableClosureUnits_isClassFormation K) := by
```

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ConcreteReciprocityTransport.lean:38-39` (namespace `LocalClassFieldTheory`)

```lean
variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
```

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ConcreteReciprocityTransport.lean:41-42` (namespace `LocalClassFieldTheory`)

```lean
private abbrev G (K : Type) [Field K] :=
  intrinsicAbsoluteGalois K
```

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ConcreteReciprocityTransport.lean:44-45` (namespace `LocalClassFieldTheory`)

```lean
private abbrev A (K : Type) [Field K] : Rep ℤ (G K) :=
  intrinsicAbsoluteUnits K
```

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ConcreteReciprocityTransport.lean:131-136` (namespace `LocalClassFieldTheory`)

```lean
def concreteReciprocityEquiv
    (D : DegreeData (G K)) (v : ValuationData D (A K))
    (hcf : SatisfiesClassFieldAxiom (A K)) :
    Abelianization Gal(L / K) ≃* NormQuotient K L :=
  concreteReciprocityEquivOfEmbedding K L
    (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L) D v hcf
```

### A.5 Norm vocabulary

`ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean:27-28` (namespace `LocalFieldTheory`)

```lean
def localNormSubgroup (K L : Type u) [Field K] [Field L] [Algebra K L] : Subgroup Kˣ :=
  (normUnits K L).range
```

`ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean:31-32` (namespace `LocalFieldTheory`)

```lean
def NormQuotient (K L : Type u) [Field K] [Field L] [Algebra K L] : Type u :=
  Kˣ ⧸ localNormSubgroup K L
```

`ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean:50-54` (namespace `LocalFieldTheory`)

```lean
def normClass (K L : Type u) [Field K] [Field L] [Algebra K L] :
    Kˣ →* NormQuotient K L := by
  change Kˣ →* Kˣ ⧸ localNormSubgroup K L
  let N := localNormSubgroup K L
  exact QuotientGroup.mk' N
```

`ValuedFieldTheory/LocalField/NormUnits.lean:21-24` (namespace `LocalFieldTheory`)

```lean
universe u v w

variable (K : Type u) (L : Type v)
variable [Field K] [Field L] [Algebra K L]
```

`ValuedFieldTheory/LocalField/NormUnits.lean:33-34` (namespace `LocalFieldTheory`)

```lean
def normUnits : Lˣ →* Kˣ :=
  Units.map (Algebra.norm K)
```

`ClassFieldTheory/Definitions/LocalClassFieldTheory/FieldNormHom.lean:20-24` (namespace `ClassFieldTheory`)

```lean
def fieldNormHom
    (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] :
    Lˣ →* Kˣ :=
  Units.map (Algebra.norm K)
```

`ClassFieldTheory/Definitions/LocalClassFieldTheory/FieldNormSubgroup.lean:20-24` (namespace `ClassFieldTheory`)

```lean
def fieldNormSubgroup
    (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] :
    Subgroup Kˣ :=
  (fieldNormHom K L).range
```

`ClassFieldTheory/Definitions/LocalClassFieldTheory/IsFieldNorm.lean:20-24` (namespace `ClassFieldTheory`)

```lean
def IsFieldNorm
    (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (x : Kˣ) : Prop :=
  x ∈ fieldNormSubgroup K L
```

`ClassFieldTheory/Definitions/LocalClassFieldTheory/FieldNormQuotient.lean:23-26` (namespace `ClassFieldTheory`)

```lean
abbrev FieldNormQuotient
    (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] :=
  Kˣ ⧸ fieldNormSubgroup K L
```

### A.6 Valuation sign

`ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean:29-37` (namespace `LocalFieldTheory.IsNonarchimedeanLocalField`)

```lean
noncomputable def v (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Additive Kˣ → Int :=
  fun x =>
    Multiplicative.toAdd
      (WithZero.unzero
        (x := (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)
          (ValuativeRel.valuation K ((Additive.toMul x : Kˣ) : K)))
        ((map_ne_zero (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)).2
          ((Valuation.ne_zero_iff (ValuativeRel.valuation K)).2 (Additive.toMul x).ne_zero)))
```

`ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuationExactSequence.lean:39-41` (namespace `LocalFieldTheory.IsNonarchimedeanLocalField`)

```lean
noncomputable def valuationMap (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] : Additive Kˣ →+ Int :=
  MonoidHom.toAdditive (valuationUnitsMulHom K)
```

`ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuationExactSequence.lean:51-54` (namespace `LocalFieldTheory.IsNonarchimedeanLocalField`)

```lean
theorem valuationMap_apply (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (x : Additive Kˣ) :
    valuationMap K x = v K x :=
  rfl
```

`ValuedFieldTheory/LocalField/NonarchimedeanLocalField/IdealQuotients.lean:212-216` (namespace `LocalFieldTheory`)

```lean
theorem v_integerRingIrreducibleFieldUnit
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (u : Kˣ) (hu : (u : K) = ((ϖ : 𝒪[K]) : K)) :
    LocalFieldTheory.IsNonarchimedeanLocalField.v K (Additive.ofMul u) = -1 := by
```

### A.7 Unramified normalization

`ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteUnramified.lean:36-44` (namespace `LocalFieldTheory.IsNonarchimedeanLocalField`)

```lean
class IsUnramifiedValuedExtension (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]] : Prop where
  /-- The maximal ideal of `𝒪[L]` has ramification index one over `𝒪[K]`. -/
  maximalIdeal_ramificationIdx_eq_one :
    (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] = 1
```

`ValuedFieldTheory/LocalField/NonarchimedeanLocalField/UnramifiedFrobenius.lean:129-139` (namespace `LocalFieldTheory`)

```lean
noncomputable def arithmeticFrobeniusOfUnramifiedValuation
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Gal(L / K) :=
  (galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure K L).symm
    (residueExtensionArithmeticFrobeniusOfValuationExtension K L)
```

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedNormalization.lean:515-529` (namespace `ClassFieldTheory`)

```lean
theorem finiteAbelianLocalArtinMap_eq_frobenius_zpow
    (K L : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (x : Kˣ) :
    LocalClassFieldTheory.abelianLocalArtinMap K L x =
      (LocalFieldTheory.arithmeticFrobeniusOfUnramifiedValuation K L) ^
        LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
          (Additive.ofMul x) := by
```

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedNormalization.lean:540-554` (namespace `ClassFieldTheory`)

```lean
theorem finiteAbelianLocalArtinMap_uniformizer
    (K L : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (π : Kˣ)
    (hπ : LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
      (Additive.ofMul π) = 1) :
    LocalClassFieldTheory.abelianLocalArtinMap K L π =
      LocalFieldTheory.arithmeticFrobeniusOfUnramifiedValuation K L := by
```

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedNormalization.lean:561-578` (namespace `ClassFieldTheory`)

```lean
theorem finiteAbelianLocalArtinMap_inverseUniformizer_residue_pow
    (K L : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (π : Kˣ)
    (hπ : LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
      (Additive.ofMul π) = 1)
    (x : 𝒪[L]) :
    ∃ z : 𝒪[L],
      (z : L) = (LocalClassFieldTheory.abelianLocalArtinMap K L π) (x : L) ∧
        IsLocalRing.residue 𝒪[L] z =
          (IsLocalRing.residue 𝒪[L] x) ^ Nat.card 𝓀[K] := by
```

`ClassFieldTheory/Theorems/LocalClassFieldTheory/FiniteAbelianLocalReciprocityUnramifiedNormalization.lean:33-53` (namespace `ClassFieldTheory`)

```lean
theorem finiteAbelianLocalReciprocity_unramifiedNormalization
    (K L : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    (hUnram : (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] = 1) :
    ∃ artin : Kˣ →ₜ* (L ≃ₐ[K] L),
      Function.Surjective artin ∧
        artin.toMonoidHom.ker = fieldNormSubgroup K L ∧
        ∀ (π : 𝒪[K])
          (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
          (x : 𝒪[L]),
          ∃ z : 𝒪[L],
            (z : L) =
                (artin ((Units.mk0 (π : K) hπ.ne_zero)⁻¹)) (x : L) ∧
              IsLocalRing.residue 𝒪[L] z =
                (IsLocalRing.residue 𝒪[L] x) ^ Nat.card 𝓀[K] := by
```

### A.8 Tower restriction

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/GeneralTowerNaturality.lean:468-479` (namespace `ClassFieldTheory`)

```lean
theorem finiteAbelianLocalArtinMap_restrict_tower
    (K E L : Type)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional K L]
    [IsAbelianGalois K E] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    (AlgEquiv.restrictNormalHom E).comp
        (LocalClassFieldTheory.abelianLocalArtinMap K L).toMonoidHom =
      (LocalClassFieldTheory.abelianLocalArtinMap K E).toMonoidHom := by
```

### A.9 Norm square

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/NormRestriction.lean:686-705` (namespace `LocalClassFieldTheory`)

```lean
theorem abelianLocalArtinMonoidHom_norm_restriction
    (K K' L L' : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field K'] [ValuativeRel K'] [TopologicalSpace K']
    [IsNonarchimedeanLocalField K']
    [Field L] [Field L']
    [Algebra K K'] [Algebra K L] [Algebra K L']
    [Algebra K' L'] [Algebra L L']
    [IsScalarTower K K' L'] [IsScalarTower K L L']
    [FiniteDimensional K K'] [Algebra.IsSeparable K K']
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation K')]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [FiniteDimensional K' L'] [IsAbelianGalois K' L'] :
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K)).comp
        (abelianLocalArtinMonoidHom K' L') =
      (abelianLocalArtinMonoidHom K L).comp
        (normUnits K K') := by
```

### A.10 Inertia at t = 0

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/Filtered/FiniteAbelian.lean:41-48` (namespace `LocalClassFieldTheory`)

```lean
theorem finiteAbelian_filteredLocalReciprocity
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (t : ℝ) (ht : 0 ≤ t) :
    artinPrincipalUnitStepGroup K L t =
      localUpperRamificationGroup K L t := by
```

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/Filtered/Core.lean:29-35` (namespace `LocalClassFieldTheory`)

```lean
def artinPrincipalUnitGroup
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (n : ℕ) : Subgroup (Gal(L / K)) :=
  (LocalFieldTheory.fieldPrincipalUnits K n).map (abelianLocalArtinMonoidHom K L)
```

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/Filtered/Core.lean:107-113` (namespace `LocalClassFieldTheory`)

```lean
def artinPrincipalUnitStepGroup
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (t : ℝ) : Subgroup (Gal(L / K)) :=
  natCeilStepFiltration (artinPrincipalUnitGroup K L) t
```

`ValuedFieldTheory/Ramification/Filtration.lean:24` (namespace `RamificationTheory`)

```lean
variable {G : Type*} [Group G]
```

`ValuedFieldTheory/Ramification/Filtration.lean:29-31` (namespace `RamificationTheory`)

```lean
def natCeilStepFiltration
    (F : ℕ → Subgroup G) (t : ℝ) : Subgroup G :=
  F ⌈t⌉₊
```

`ValuedFieldTheory/LocalField/NonarchimedeanLocalField/StandardOpenSubgroups.lean:32-34` (namespace `LocalFieldTheory`)

```lean
def fieldPrincipalUnits
    (K : Type u) [Field K] [ValuativeRel K] (n : ℕ) : Subgroup Kˣ :=
  (principalUnits K n).map (integerUnitsToFieldUnits K)
```

`ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnits.lean:24-26` (namespace `LocalFieldTheory`)

```lean
def principalUnits (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    Subgroup 𝒪[K]ˣ where
  carrier := {u | ((u : 𝒪[K]) - 1) ∈ (𝓂[K] ^ n : Ideal 𝒪[K])}
  -- proof fields one_mem', mul_mem', inv_mem' not shown
```

`ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnits.lean:73-74` (namespace `LocalFieldTheory`)

```lean
@[simp] theorem principalUnits_zero (K : Type u) [Field K] [ValuativeRel K] :
    principalUnits K 0 = ⊤ := by
```

`ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean:183-184` (namespace `LocalFieldTheory.IsNonarchimedeanLocalField`)

```lean
def integerUnitsToFieldUnits (K : Type u) [Field K] [ValuativeRel K] : 𝒪[K]ˣ →* Kˣ :=
  Units.map (algebraMap 𝒪[K] K).toMonoidHom
```

`ValuedFieldTheory/Ramification/LocalField/Core.lean:104-113` (namespace `RamificationTheory.LocalField`)

```lean
noncomputable def localUpperRamificationGroup
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (t : ℝ) : Subgroup Gal(L / K) :=
  Higher.upperRamificationGroupOfUniqueExtension
    (base := (localCompleteDVF K).toDVF)
    (target := (chosenLocalExtensionCompleteDVF K L).toDVF)
    (chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension K L) t
```

`ValuedFieldTheory/Ramification/LocalField/ResidueInertia.lean:97-109` (namespace `RamificationTheory.LocalField`)

```lean
theorem localUpperRamificationGroup_zero_eq_residue_ker
    (K L : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]] :
    localUpperRamificationGroup K L 0 =
      (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker := by
```

`ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueGalois.lean:97-102` (namespace `LocalFieldTheory`)

```lean
def galoisGroupResidueAlgEquivHomOfIsIntegralClosure (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    Gal(L / K) →* (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]) where
  toFun := galoisGroupResidueAlgEquivOfIsIntegralClosure K L
  -- proof fields map_one', map_mul' not shown
```

`ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueGalois.lean:277-285` (namespace `LocalFieldTheory`)

```lean
theorem galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_sub_mem_maximalIdeal
    (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L/K)) :
    σ ∈ (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker ↔
      ∀ x : 𝒪[L],
        galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ x - x ∈
          (𝓂[L] : Ideal 𝒪[L]) := by
```

### A.11 Family uniqueness

`ClassFieldTheory/Definitions/LocalClassFieldTheory/FiniteAbelianLocalExtension.lean:23-26` (namespace `ClassFieldTheory`)

```lean
abbrev FiniteAbelianLocalExtension
    (K : Type u) [Field K] :=
  { E : IntermediateField K (SeparableClosure K) //
      FiniteDimensional K E ∧ IsAbelianGalois K E }
```

`ClassFieldTheory/Definitions/LocalClassFieldTheory/FiniteAbelianLocalExtension.lean:30` (namespace `ClassFieldTheory.FiniteAbelianLocalExtension`)

```lean
variable {K : Type u} [Field K]
```

`ClassFieldTheory/Definitions/LocalClassFieldTheory/FiniteAbelianLocalExtension.lean:43-44` (namespace `ClassFieldTheory.FiniteAbelianLocalExtension`)

```lean
def normSubgroup (E : FiniteAbelianLocalExtension K) : Subgroup Kˣ :=
  fieldNormSubgroup K E.1
```

`ClassFieldTheory/Theorems/LocalClassFieldTheory/FiniteAbelianLocalReciprocityFamilyExt.lean:39-84` (namespace `ClassFieldTheory`)

```lean
theorem finiteAbelianLocalReciprocity_family_ext
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f g : (E : FiniteAbelianLocalExtension K) →
      Kˣ →ₜ* (E.1 ≃ₐ[K] E.1))
    (hfker : ∀ E : FiniteAbelianLocalExtension K,
      (f E).toMonoidHom.ker = E.normSubgroup)
    (hgker : ∀ E : FiniteAbelianLocalExtension K,
      (g E).toMonoidHom.ker = E.normSubgroup)
    (hfcoh : ∀ (E F : FiniteAbelianLocalExtension K)
      (hEF : E.1 ≤ F.1) (x : Kˣ) (y : E.1),
      IntermediateField.inclusion hEF ((f E x) y) =
        (f F x) (IntermediateField.inclusion hEF y))
    (hgcoh : ∀ (E F : FiniteAbelianLocalExtension K)
      (hEF : E.1 ≤ F.1) (x : Kˣ) (y : E.1),
      IntermediateField.inclusion hEF ((g E x) y) =
        (g F x) (IntermediateField.inclusion hEF y))
    (hfrob : ∀ (E : FiniteAbelianLocalExtension K)
      [ValuativeRel E.1] [UniformSpace E.1] [IsUniformAddGroup E.1]
      [IsNonarchimedeanLocalField E.1]
      [Valuation.HasExtension (ValuativeRel.valuation K)
        (ValuativeRel.valuation E.1)],
      (𝓂[E.1] : Ideal 𝒪[E.1]).ramificationIdx 𝒪[K] = 1 →
      ∀ (π : 𝒪[K])
        (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
        (x : 𝒪[E.1]),
        ∃ z : 𝒪[E.1],
          (z : E.1) =
            (f E ((Units.mk0 (π : K) hπ.ne_zero)⁻¹)) (x : E.1) ∧
          IsLocalRing.residue 𝒪[E.1] z =
            (IsLocalRing.residue 𝒪[E.1] x) ^ Nat.card 𝓀[K])
    (hgrob : ∀ (E : FiniteAbelianLocalExtension K)
      [ValuativeRel E.1] [UniformSpace E.1] [IsUniformAddGroup E.1]
      [IsNonarchimedeanLocalField E.1]
      [Valuation.HasExtension (ValuativeRel.valuation K)
        (ValuativeRel.valuation E.1)],
      (𝓂[E.1] : Ideal 𝒪[E.1]).ramificationIdx 𝒪[K] = 1 →
      ∀ (π : 𝒪[K])
        (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
        (x : 𝒪[E.1]),
        ∃ z : 𝒪[E.1],
          (z : E.1) =
            (g E ((Units.mk0 (π : K) hπ.ne_zero)⁻¹)) (x : E.1) ∧
          IsLocalRing.residue 𝒪[E.1] z =
            (IsLocalRing.residue 𝒪[E.1] x) ^ Nat.card 𝓀[K])
    : f = g := by
```

### A.12 Quotient equivalence from a given map

`ClassFieldTheory/Theorems/LocalClassFieldTheory/FiniteAbelianLocalReciprocityQuotientEquivOfArtin.lean:32-42` (namespace `ClassFieldTheory`)

```lean
theorem finiteAbelianLocalReciprocity_quotientEquiv_of_artin
    (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (artin : Kˣ →ₜ* (L ≃ₐ[K] L))
    (hsurj : Function.Surjective artin)
    (hker : artin.ker = fieldNormSubgroup K L) :
    ∃! e : FieldNormQuotient K L ≃ₜ* (L ≃ₐ[K] L),
      ∀ x : Kˣ, e (QuotientGroup.mk' (fieldNormSubgroup K L) x) = artin x := by
```

### A.13 Fixed-field norm and transfer squares (context only)

These declarations are cited in sections 2.4 and 5 (item 6) as context. They are not part of the port plan. The first nine blocks are in `FixedFieldNormResidueNaturality.lean`, the last two in `FixedFieldContinuousNaturality.lean`. In the first file, the symbols, norm, restriction, inclusion and transfer maps of the two structures (`:523-562` and `:683-722`) apply `abstractFixedFieldNormResidueSymbol`, `abstractFixedFieldNormUnits` (`:98`), `abstractFixedFieldAbelianizedRestriction` (`:110`), `abstractFixedFieldUnitsInclusion` (`:34`) and `abstractFixedFieldAbelianizedTransfer` (`:290`) to the subgroups of `T`, in the way that `baseNormResidueSymbol` does. In the second file, `baseNormResidueMap`, `intermediateNormResidueMap`, `unitsInclusionMap` and `abelianizedTransferMap` (`:750, 791, 833, 884`) are continuous versions. The `@[simp]` lemmas `*_toMonoidHom` (`:776, 817, 861, 895`) identify their underlying homomorphisms with the algebraic maps, written multiplicatively.

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldNormResidueNaturality.lean:30` (namespace `LocalClassFieldTheory`)

```lean
variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
```

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldNormResidueNaturality.lean:64-95` (namespace `LocalClassFieldTheory`)

```lean
noncomputable def abstractFixedFieldNormResidueSymbol
    (D : DegreeData (Gal(Ω/k)))
    (v : ValuationData D (galoisAmbientUnitsRep k Ω))
    (hcf : SatisfiesClassFieldAxiom
      (galoisAmbientUnitsRep k Ω))
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup K L hLK).Normal]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [hKabsolute : Finite
      ((baseField (Gal(Ω/k))).toSubgroup ⧸
        extensionSubgroup (baseField (Gal(Ω/k))) K
          (le_baseField K))] :
    Additive (abstractFixedField k Ω K)ˣ →+
      Additive (Abelianization
        Gal(abstractRelativeFixedField k Ω hLK /
          abstractFixedField k Ω K)) := by
  let KF : FiniteAbstractField (Gal(Ω / k)) :=
    ⟨K, hKabsolute⟩
  let E : FiniteGaloisSubextension KF.field :=
    ⟨L, hLK, hnormal, hfinite⟩
  exact
    (MulEquiv.toAdditive
      (abstractExtensionQuotientEquivGaloisGroup
        k Ω K L hLK hnormal).abelianizationCongr).toAddMonoidHom.comp
      ((D.normResidueSymbol (galoisAmbientUnitsRep k Ω)
        v hcf KF E).toAddMonoidHom.comp
        ((finiteNormClassHom (galoisAmbientUnitsRep k Ω)
          K L hLK).comp
          (abstractFixedFieldUnitsEquivGaloisFixed
            k Ω K).toAddMonoidHom))
```

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldNormResidueNaturality.lean:457-499` (namespace `LocalClassFieldTheory`)

```lean
structure LocalFixedFieldNormRestrictionSquare
    (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] where
  /-- The subgroup fixing the lower base field. -/
  lowerBase : ClosedSubgroup (Gal(SeparableClosure k / k))
  /-- The subgroup fixing the upper base field. -/
  upperBase : ClosedSubgroup (Gal(SeparableClosure k / k))
  /-- The subgroup fixing the top field of the lower horizontal extension. -/
  lowerTop : ClosedSubgroup (Gal(SeparableClosure k / k))
  /-- The subgroup fixing the top field of the upper horizontal extension. -/
  upperTop : ClosedSubgroup (Gal(SeparableClosure k / k))
  /-- The lower top subgroup lies in the lower base subgroup. -/
  lowerTop_le_lowerBase : lowerTop.toSubgroup ≤ lowerBase.toSubgroup
  /-- The upper top subgroup lies in the upper base subgroup. -/
  upperTop_le_upperBase : upperTop.toSubgroup ≤ upperBase.toSubgroup
  /-- The upper base subgroup lies in the lower base subgroup. -/
  upperBase_le_lowerBase : upperBase.toSubgroup ≤ lowerBase.toSubgroup
  /-- The upper top subgroup lies in the lower top subgroup. -/
  upperTop_le_lowerTop : upperTop.toSubgroup ≤ lowerTop.toSubgroup
  /-- The lower horizontal extension subgroup is normal. -/
  lowerNormal :
    (extensionSubgroup lowerBase lowerTop lowerTop_le_lowerBase).Normal
  /-- The upper horizontal extension subgroup is normal. -/
  upperNormal :
    (extensionSubgroup upperBase upperTop upperTop_le_upperBase).Normal
  /-- The lower horizontal extension has finite Galois group. -/
  lowerFinite :
    Finite (lowerBase.toSubgroup ⧸
      extensionSubgroup lowerBase lowerTop lowerTop_le_lowerBase)
  /-- The upper horizontal extension has finite Galois group. -/
  upperFinite :
    Finite (upperBase.toSubgroup ⧸
      extensionSubgroup upperBase upperTop upperTop_le_upperBase)
  /-- The vertical base extension has finite degree. -/
  baseFinite :
    Finite (lowerBase.toSubgroup ⧸
      extensionSubgroup lowerBase upperBase upperBase_le_lowerBase)
  /-- The lower base field is finite over the original local field. -/
  lowerAbsoluteFinite :
    Finite
      ((baseField (Gal(SeparableClosure k / k))).toSubgroup ⧸
        extensionSubgroup (baseField (Gal(SeparableClosure k / k)))
          lowerBase (le_baseField lowerBase))
```

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldNormResidueNaturality.lean:503-504` (namespace `LocalClassFieldTheory.LocalFixedFieldNormRestrictionSquare`)

```lean
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
```

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldNormResidueNaturality.lean:569-572` (namespace `LocalClassFieldTheory.LocalFixedFieldNormRestrictionSquare`)

```lean
theorem norm_restriction_commutes
    (T : LocalFixedFieldNormRestrictionSquare k) :
    (abelianizedRestriction T).comp (upperNormResidueSymbol T) =
      (lowerNormResidueSymbol T).comp (normUnits T) := by
```

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldNormResidueNaturality.lean:597-624` (namespace `LocalClassFieldTheory`)

```lean
structure LocalFixedFieldTransferTower
    (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] where
  /-- The subgroup fixing the base field of the tower. -/
  base : ClosedSubgroup (Gal(SeparableClosure k / k))
  /-- The subgroup fixing the intermediate field of the tower. -/
  intermediate : ClosedSubgroup (Gal(SeparableClosure k / k))
  /-- The subgroup fixing the top field of the tower. -/
  top : ClosedSubgroup (Gal(SeparableClosure k / k))
  /-- The top subgroup lies in the intermediate subgroup. -/
  top_le_intermediate : top.toSubgroup ≤ intermediate.toSubgroup
  /-- The intermediate subgroup lies in the base subgroup. -/
  intermediate_le_base : intermediate.toSubgroup ≤ base.toSubgroup
  /-- The total extension subgroup is normal in the base subgroup. -/
  totalNormal :
    (extensionSubgroup base top
      (top_le_intermediate.trans intermediate_le_base)).Normal
  /-- The total extension has finite Galois group. -/
  totalFinite :
    Finite (base.toSubgroup ⧸
      extensionSubgroup base top
        (top_le_intermediate.trans intermediate_le_base))
  /-- The base field is finite over the original local field. -/
  baseAbsoluteFinite :
    Finite
      ((baseField (Gal(SeparableClosure k / k))).toSubgroup ⧸
        extensionSubgroup (baseField (Gal(SeparableClosure k / k)))
          base (le_baseField base))
```

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldNormResidueNaturality.lean:628-629` (namespace `LocalClassFieldTheory.LocalFixedFieldTransferTower`)

```lean
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
```

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldNormResidueNaturality.lean:683-693` (namespace `LocalClassFieldTheory.LocalFixedFieldTransferTower`)

```lean
noncomputable def baseNormResidueSymbol
    (T : LocalFixedFieldTransferTower k) := by
  letI := T.totalNormal
  letI := T.totalFinite
  letI := T.baseAbsoluteFinite
  exact
    abstractFixedFieldNormResidueSymbol k (SeparableClosure k)
      (localResidueDatum k) (localHenselianValuation k)
      (separableClosureUnits_isClassFormation k)
      T.base T.top
      (T.top_le_intermediate.trans T.intermediate_le_base)
```

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldNormResidueNaturality.lean:728-731` (namespace `LocalClassFieldTheory.LocalFixedFieldTransferTower`)

```lean
theorem transfer_inclusion_commutes
    (T : LocalFixedFieldTransferTower k) :
    (abelianizedTransfer T).comp (baseNormResidueSymbol T) =
      (intermediateNormResidueSymbol T).comp (unitsInclusion T) := by
```

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldContinuousNaturality.lean:746-747` (namespace `LocalClassFieldTheory.LocalFixedFieldTransferTower`)

```lean
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
```

`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldContinuousNaturality.lean:902-922` (namespace `LocalClassFieldTheory.LocalFixedFieldTransferTower`)

```lean
theorem transfer_inclusion_commutes_continuous
    (T : LocalFixedFieldTransferTower k) :
    letI : FiniteDimensional k
        (abstractFixedField k (SeparableClosure k) T.base) :=
      abstractFixedField_finiteDimensional
        k (SeparableClosure k) T.base T.baseAbsoluteFinite
    letI : FiniteDimensional k
        (abstractFixedField k (SeparableClosure k) T.intermediate) :=
      abstractFixedField_finiteDimensional
        k (SeparableClosure k) T.intermediate
          (intermediateAbsoluteFinite T)
    letI : NontriviallyNormedField
        (abstractFixedField k (SeparableClosure k) T.base) :=
      finiteExtensionSpectralNormedField k
        (abstractFixedField k (SeparableClosure k) T.base)
    letI : NontriviallyNormedField
        (abstractFixedField k (SeparableClosure k) T.intermediate) :=
      finiteExtensionSpectralNormedField k
        (abstractFixedField k (SeparableClosure k) T.intermediate)
    (abelianizedTransferMap T).comp (baseNormResidueMap T) =
      (intermediateNormResidueMap T).comp (unitsInclusionMap T) := by
```
