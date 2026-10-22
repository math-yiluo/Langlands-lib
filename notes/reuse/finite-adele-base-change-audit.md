# Finite-adele base change: Imperial and Anthropic FLT audit

Worker 217 and Worker 248 wrote this audit for task `cb8ff701` (revision 2). It audits Imperial FLT's finite-adele base change `IsDedekindDomain.FiniteAdeleRing.baseChangeAlgEquiv` and `baseChangeContinuousAlgEquiv` together with the derivative retained in Anthropic's FLT repository, and compares both with our Mathlib and with the Library's `Langlands/Global/AdelicFunctoriality/`. It ends with a port plan for our number-field finite adeles. The audit establishes no external theorem and adds or changes no Lean target. Its Lean evidence comes from private `lean_check` runs in environment `3b864ddf`, cited by diagnostic ID; none of it is an accepted Library result.

**Verdict: adapt.** Do not import either repository. Port the originating Imperial construction as a series of separately authorized tasks, and use the Anthropic derivative only as provenance. Four findings support this verdict:

- At our pin, the 37-module Imperial import closure builds after four small patches (§5.3). Its main declarations depend only on `propext`, `Classical.choice` and `Quot.sound` (§4).
- For number fields, Imperial's map `FiniteAdeleRing.mapRingHom (𝓞 K) K L (𝓞 L)` equals the Library's `finiteAdeleInclusion` by `rfl` at default transparency. With the algebra structure `finiteAdeleInclusion.toAlgebra`, the construction instantiates to `L ⊗[K] FiniteAdeleRing (𝓞 K) K ≃A[L] FiniteAdeleRing (𝓞 L) L` (§2.6).
- The Anthropic derivative does not build at our pin (9 errors in 4 modules), and it contains no fix for Imperial's two proof failures.
- The Library already proves the local field-level comparison (`completedTensorComparison`). A port therefore needs only the integral local comparison, the commutation of tensor products with restricted products, and the global statements (§6).

A base-change equivalence is not a norm theorem. It extends scalars. The Library's field norm `finiteAdeleNorm` is a separate map, owned by task `51d4331f`, and this audit asserts nothing about it.

## 1. Pins, source closure and missing inputs

**Pins.**

| Project | Commit | Lean | Mathlib |
|---|---|---|---|
| [ImperialCollegeLondon/FLT](https://github.com/ImperialCollegeLondon/FLT/tree/923d45174c500aa1d994ba973bac38ea39eacbf7) | `923d45174c500aa1d994ba973bac38ea39eacbf7` (2026-10-21, "chore: bump mathlib to 1f41440 (v4.35.0-rc4), fix breaking changes (#1204)") | `leanprover/lean4:v4.35.0-rc4` | `1f414401f69059aa7eead47b53ee40bd38455eeb` |
| [anthropics/fermats-last-theorem](https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2) | `6e837e75355538c7f80bab5b956861e86c4eacc2` | 4.33.1 | `db584cd6d46c92f209a44c0f1c829460d327499d` |
| This project, environment `3b864ddf` | Library `55cf6172e313c02aa8f5978501d957bfa08de20d` | 4.34.0 | `5ed2965256430c3649e86755f9576b54eca72435` |

Imperial's `lake-manifest.json` also pins `checkdecls` at `3d425859e73fcfbef85b9638c2a91708ef4a22d4`; Anthropic's manifest has no `checkdecls`. Imperial's `lakefile.toml` sets the `leanOptions` `pp.unicode.fun = true`, `autoImplicit = false`, `relaxedAutoImplicit = false`, `maxSynthPendingDepth = 3`, `weak.linter.flexible = true`, `weak.linter.mathlibStandardSet = true` and `warn.sorry = false`. The Lean service's generated lakefile sets none of them, so every build in this audit ran without `maxSynthPendingDepth = 3`.

**Sources read.**

- **Snapshot:** registered source `external-lean-reuse-snapshots-2026-10-21` (fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`). Its folder `ImperialCollegeLondon--FLT` holds an untruncated tree with 271 Lean files. Its folder `anthropics--fermats-last-theorem` comes from a truncated recursive tree and retains 890 Lean files.
- **Supplement:** the Anthropic snapshot holds only 7 of the 21 local modules that the derivative imports. Worker 217 fetched the other 14 at `6e837e75` from raw.githubusercontent.com and checked each file's git blob SHA1 against the snapshot's `tree.json`; all 14 match. They are registered as `anthropic-flt-6e837e75-basechange-closure-supplement`, whose `MANIFEST.md` lists the blob SHA1, sha256 and line count of each file. Worker 248 fetched the same 14 files independently, with the same blob check, and their copies are byte-identical (`cmp`) to the registered ones.

**Imperial closure.** We computed the import closure of `FLT.DedekindDomain.FiniteAdeleRing.BaseChange` from its `import` lines. It has 37 local modules (7,596 lines) and imports 87 distinct external Mathlib modules, with no umbrella `import Mathlib`. The 37 local modules are:

- `FLT.DedekindDomain.`: `AdicValuation`, `IntegralClosure`, `Completion.BaseChange`, `FiniteAdeleRing.{TensorPi, IsDirectLimitRestricted, TensorRestrictedProduct, BaseChange}`;
- `FLT.Mathlib.Algebra.`: `Algebra.{Hom, Tower, Bilinear, Pi}`, `Module.Submodule.Basic`, `IsDirectLimit`;
- `FLT.Mathlib.RingTheory.`: `LocalRing.MaximalIdeal.Basic`, `Valuation.ValuationSubring`, `DedekindDomain.{AdicValuation, FiniteAdeleRing}`, `Localization.BaseChange`, `TensorProduct.Basis`, `RamificationInertia.Basic`;
- `FLT.Mathlib.Topology.`: `Algebra.Module.{ModuleTopology, Quotient}`, `Algebra.UniformRing`, `Algebra.RestrictedProduct.{Basic, Equiv, TopologicalSpace, Module, Algebra}`, `Algebra.{MulAction, ContinuousMonoidHom}`, `Algebra.Group.Units`, `Algebra.Algebra.Hom`, `Bases`;
- `FLT.Mathlib.LinearAlgebra.Pi`, `FLT.Mathlib.Order.Filter.Cofinite`, `FLT.Hacks.RightActionInstances` and `FLT.Deformations.ContinuousRepresentation.IsTopologicalModule`.

The largest files are `DedekindDomain/Completion/BaseChange.lean` (870 lines), `Mathlib/Topology/Algebra/RestrictedProduct/TopologicalSpace.lean` (739), `.../RestrictedProduct/Equiv.lean` (657), `DedekindDomain/AdicValuation.lean` (606) and `Mathlib/Topology/Algebra/Module/ModuleTopology.lean` (540). `FiniteAdeleRing/BaseChange.lean` itself has 367 lines. This is the closed import set of the file as written; we did not try to prune unneeded imports. It contains neither `FLT.Assumptions.KnownIn1980s` nor `FLT.Proof`. Exactly one external import is absent at our pin: `Mathlib.Topology.Algebra.Module.Equiv.Basic`, imported by `FLT.Mathlib.Topology.Algebra.Module.Quotient`; our Mathlib has `Mathlib.Topology.Algebra.Module.Equiv` instead. Appendix B lists every file with its copyright line and authors.

**Anthropic closure.** `Definitions.Def_DedekindDomain_FiniteAdeleRing_BaseChange` imports 21 local modules transitively (5,931 lines). Seven are in the snapshot: the root, `Def_DedekindDomain_FiniteAdeleRing_{TensorRestrictedProduct, TensorPi, IsDirectLimitRestricted}` and `Def_Mathlib_Topology_Algebra_RestrictedProduct_{Basic, Equiv, TopologicalSpace}`. The other 14 are in the supplement. The external imports are the umbrella `import Mathlib` and 10 named Mathlib modules, all present at our pin.

**Inputs that remain missing.**

- **No upstream build:** neither upstream toolchain is the approved environment, and an external build is not permitted. Every build here is an adaptation at our pin, and upstream CI results remain author reports (§4).
- **Two adelic inputs:** the general construction takes the algebra structure `[Algebra 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]]` and the coherence class `[ComapFiberwiseSMul A K L B]` as hypotheses (§2.4). Imperial supplies them only for number fields, as scoped instances in namespace `NumberField.AdeleRing` (`FLT/NumberField/AdeleRing.lean:364` and `:369–370`), outside the closure. Our probes use instances built from the Library instead (§2.6).

## 2. Selected declarations, definitions and meaning

### 2.1 Context

All selected declarations are in namespace `IsDedekindDomain.FiniteAdeleRing` of `FLT/DedekindDomain/FiniteAdeleRing/BaseChange.lean`. They share the variables of lines 44–47:

```lean
variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L] [Module.Finite A B]
    [IsDedekindDomain B] [IsFractionRing B L]
```

The module docstring (lines 25–26) speaks of a finite separable extension `L/K` with `B` the integral closure of `A` in `L`. The Lean declarations assume neither separability nor that `B` is the integral closure. They assume that `A` and `B` are Dedekind domains with fraction fields `K` and `L`, that `B` is a finite `A`-module, and both scalar towers. Each main declaration adds `[FiniteDimensional K L]`. `mapRingHom` derives `FaithfulSMul A B` in its body from Mathlib's `FaithfulSMul.of_field_isFractionRing`.

### 2.2 Complete types

Diagnostic `8d7603c1` printed the types (`#check @…`) at our pin. The complete type of `baseChangeContinuousAlgEquiv`, with binder names dropped, is

```lean
IsDedekindDomain.FiniteAdeleRing.baseChangeContinuousAlgEquiv
    (A : Type u_1) (K : Type u_2) (L : Type u_3) (B : Type u_4)
    [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L] [Algebra A K]
    [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A] [Algebra K L] [Algebra A L]
    [IsScalarTower A B L] [IsScalarTower A K L] [Module.Finite A B] [IsDedekindDomain B]
    [IsFractionRing B L]
    [Algebra (FiniteAdeleRing A K) (FiniteAdeleRing B L)]
    [FiniteAdeleRing.ComapFiberwiseSMul A K L B]
    [FiniteDimensional K L] :
    L ⊗[K] FiniteAdeleRing A K ≃A[L] FiniteAdeleRing B L
```

The other declarations have the same first 20 binders (the four types and the 16 instances of §2.1), followed by:

| Declaration (line) | Further binders | Type |
|---|---|---|
| `mapRingHom` (75) | none | `FiniteAdeleRing A K →+* FiniteAdeleRing B L` |
| `mapSemialgHom` (83) | none | `FiniteAdeleRing A K →SA[algebraMap K L] FiniteAdeleRing B L` |
| `ComapFiberwiseSMul` (111) | `[Algebra (FiniteAdeleRing A K) (FiniteAdeleRing B L)]` | `Prop` (a class) |
| `baseChange_bijective` (229) | the three binders displayed above | `Function.Bijective ⇑(FiniteAdeleRing.mapSemialgHom A K L B).baseChangeOfAlgebraMap` |
| `baseChangeAlgEquiv` (256) | the same three | `L ⊗[K] FiniteAdeleRing A K ≃ₐ[L] FiniteAdeleRing B L` |
| `baseChangeAdeleAlgEquiv` (262) | the same three | `L ⊗[K] FiniteAdeleRing A K ≃ₐ[FiniteAdeleRing A K] FiniteAdeleRing B L` |
| `baseChangeAdeleContinuousAlgEquiv` (357) | the same three | `L ⊗[K] FiniteAdeleRing A K ≃A[FiniteAdeleRing A K] FiniteAdeleRing B L` |
| `baseChangeContinuousAlgEquiv` (362) | the same three | displayed above |

`𝔸ᶠ[A, K]` is Mathlib's notation for `FiniteAdeleRing A K`. The continuous types need a topology on `L ⊗[K] 𝔸ᶠ[A, K]`, and Mathlib has none: a textual search of our Mathlib found no `TopologicalSpace` instance on tensor products. Imperial supplies a scoped instance in namespace `TensorProduct.RightActions` (`FLT/Hacks/RightActionInstances.lean:150`). It is the module topology for the action of `𝔸ᶠ[A, K]` on the right tensor factor, an action given by the scoped instance `Algebra S (B ⊗[R] S)` (line 82). It requires `Module.Finite K L`. To write these types, a user must `open scoped TensorProduct.RightActions`.

### 2.3 Underlying definitions

- **Local map.** For `w : v.Extension B`, `Extension.adicCompletionSemialgHom K L w : v.adicCompletion K →ₛₐ[algebraMap K L] w.1.adicCompletion L` (`Completion/BaseChange.lean:182`) is the continuous extension of `algebraMap K L` to the completions. Here `v.Extension B` is `{w : HeightOneSpectrum B // w.under A = v}` (`IntegralClosure.lean:41`). The definition applies the FLT-local `UniformSpace.Completion.mapSemialgHom` (`FLT/Mathlib/Topology/Algebra/UniformRing.lean`) to `algebraMap` between the `WithVal` type synonyms. It then transports the result along `adicCompletion.algEquiv`, which identifies each adic completion with the completion of its `WithVal` synonym. The lemma `valued_adicCompletionSemialgHom` (line 206) gives `Valued.v (i x) = Valued.v x ^ e`, where `e` is the ramification index. Line 238 makes the map a **global** instance, `Algebra (v.adicCompletion K) (w.1.adicCompletion L) := (w.adicCompletionSemialgHom K L).toAlgebra`.
- **Global map.** `mapRingHom` (line 75) is `RestrictedProduct.mapAlongRingHom` along `under A : HeightOneSpectrum B → HeightOneSpectrum A`. Its coordinate at `w` is `adicCompletionSemialgHom K L ⟨w, rfl⟩` applied to `x (under A w)`. The cofinite condition `tendsTo_comap_cofinite` (line 56) comes from the finiteness of the fibres (`Extension.finite`), and the integrality condition holds at every place. `mapSemialgHom` (line 83) is the same map as a continuous semialgebra map over `algebraMap K L`. Its continuity comes from `RestrictedProduct.mapAlong_continuous`, and `mapSemialgHom_apply` (line 97) holds by `rfl`.
- **The two inputs.** Line 102 takes an arbitrary instance `[Algebra 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]]`. Lines 111–115 take `[ComapFiberwiseSMul A K L B]`, a `Prop`-valued class that extends `RestrictedProduct.FiberwiseSMul (under A) …` (`FLT/Mathlib/LinearAlgebra/Pi.lean:74`). Its field is `map_smul : (r • x) σ = r b • x σ` for `σ : {w // under A w = b}`, where the right-hand side uses the local instance of line 238. `ComapFiberwiseSMul.map_smul'` (line 119) restates it as `(x • y) w.1 = x v • y w.1` for `w : v.Extension B`. From it, `BaseChange.algebraMap_apply` (line 124) proves `algebraMap 𝔸ᶠ[A, K] 𝔸ᶠ[B, L] x w = adicCompletionSemialgHom K L ⟨w, rfl⟩ (x (under A w))`. So any instance satisfying the class has, pointwise, the same `algebraMap` as `mapRingHom`. With Mathlib's `Algebra.algebra_ext`, it follows that any two instances satisfying the class are propositionally equal; the class does not make them definitionally equal. This consequence is our inference and was not checked in Lean.
- **Bijectivity** (section `bijection`, lines 129–275). The proof composes four linear equivalences:
  1. `tensorEquivTensor` (133), `L ⊗[K] 𝔸ᶠ[A, K] ≃ₗ[B] B ⊗[A] 𝔸ᶠ[A, K]`, from `linearEquivTensorProductModuleLeft` (`IntegralClosure.lean:256`);
  2. `tensorEquivRestrictedProduct` (143), which moves `B ⊗[A] −` inside the restricted product by `RestrictedProduct.lTensorEquivLeft` (`TensorRestrictedProduct.lean:240`, for `Module.Flat` and `Module.FinitePresentation`);
  3. `restrictedProductTensorProductEquivRestrictedProductProd` (165), the local integral comparison at each `v`, from `integerBaseChangeLinearEquiv` (`Completion/BaseChange.lean:810`) and `integerBaseChangeLinearEquiv_bijOn` (854);
  4. `restrictedProductProdEquiv` (183), which flattens `Πʳ v, Π (w : v.Extension B), …` into `Πʳ w, …` (`flattenEquiv'`).

  `baseChangeLinearEquiv` (205) composes them and extends scalars from `B` to `L` (`LinearEquiv.extendScalarsOfIsLocalization`). `baseChange_bijective` (229) identifies its function with `(mapSemialgHom A K L B).baseChangeOfAlgebraMap`; this is the step that uses `BaseChange.algebraMap_apply`, hence `ComapFiberwiseSMul`. `baseChangeAlgEquiv` (256) is `AlgEquiv.ofBijective` of that map. `baseChangeAdeleAlgEquiv` (262) is the same map as an `𝔸ᶠ[A, K]`-algebra equivalence (`SemialgHom.baseChangeRightOfAlgebraMap`). Line 272 deduces the instance `Module.Finite 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]`.
- **Topology** (section `moduleTopology`, lines 277–354). `restrictedProductPiEquiv` (319) is a continuous `𝔸ᶠ[A, K]`-linear equivalence, built with `flattenHomeomorph'`. It relates `𝔸ᶠ[B, L]` to the restricted product over `v` of the finite products `Π (w : v.Extension B), w.1.adicCompletion L`. `restrictedProduct_pi_isModuleTopology` (336) shows that this restricted product carries the module topology, using the FLT-local `RestrictedProduct.isModuleTopology`. The instance `IsModuleTopology 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]` (350) then follows by `IsModuleTopology.iso`. `baseChangeAdeleContinuousAlgEquiv` (357) applies `IsModuleTopology.continuousAlgEquivOfAlgEquiv` to `baseChangeAdeleAlgEquiv`: an algebra equivalence between modules with the module topology is continuous both ways. `baseChangeContinuousAlgEquiv` (362) combines the `L`-algebra equivalence `baseChangeAlgEquiv` with the continuity fields of `baseChangeAdeleContinuousAlgEquiv`. Both have the same underlying function.

### 2.4 Hypotheses: constructed or input

| Hypothesis | In the general file | For number fields (`A = 𝓞 K`, `B = 𝓞 L`) |
|---|---|---|
| `IsDedekindDomain A`, `IsDedekindDomain B`, `IsFractionRing A K`, `IsFractionRing B L`, `Module.Finite A B`, both scalar towers, `FiniteDimensional K L` | typeclass inputs | found by Mathlib's instances: the probes `8d7603c1` and `264816ba` elaborate without further arguments |
| separability of `L/K`; `B` is the integral closure of `A` | not assumed | not needed |
| `Algebra (v.adicCompletion K) (w.1.adicCompletion L)` | constructed: global instance, `Completion/BaseChange.lean:238` | the Library has its own scoped instance (§2.6) |
| topology on `L ⊗[K] 𝔸ᶠ[A, K]` | constructed: scoped instance, `RightActionInstances.lean:150` | same |
| `[Algebra 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]]` | input, never constructed | Imperial: scoped `(FiniteAdeleRing.mapRingHom _ K L _).toAlgebra` (`FLT/NumberField/AdeleRing.lean:364`); our probe: `finiteAdeleInclusion.toAlgebra` |
| `[ComapFiberwiseSMul A K L B]` | input, a `Prop`, never constructed | Imperial: scoped instance proved by `obtain ⟨a, rfl⟩ := σ; rfl` (`AdeleRing.lean:369–370`); our probe: the same proof for the Library-built algebra |

### 2.5 Meaning, and four notions kept apart

Write `ι x` for `mapRingHom A K L B x`. Its coordinate at `w` is the image of `x` at `v = w.under A` under `K_v → L_w`. `baseChangeAlgEquiv` is the map `l ⊗ x ↦ l · ι x`. For number fields, diagnostic `8d7603c1` checks `baseChangeAlgEquiv (𝓞 K) K L (𝓞 L) (l ⊗ₜ x) = algebraMap L _ l * mapSemialgHom (𝓞 K) K L (𝓞 L) x`, via `SemialgHom.baseChange_of_algebraMap_tmul`. Mathematically this is the classical isomorphism `L ⊗_K 𝔸_K^∞ ≅ 𝔸_L^∞`. It is assembled from the local isomorphisms `L ⊗_K K_v ≅ Π_{w above v} L_w` and from their integral versions `B ⊗_A 𝒪_v ≅ Π_{w above v} 𝒪_w`, which Imperial proves at every place.

Four notions must be kept apart:

1. **Extension-of-scalars map:** `mapRingHom` and `mapSemialgHom` (for number fields, the Library's `finiteAdeleInclusion`). This ring homomorphism `𝔸ᶠ_K → 𝔸ᶠ_L` makes `𝔸ᶠ_L` an `𝔸ᶠ_K`-algebra.
2. **Algebra equivalence:** `baseChangeAlgEquiv` (`≃ₐ[L]`) and `baseChangeAdeleAlgEquiv` (`≃ₐ[𝔸ᶠ_K]`). No topology is involved.
3. **Continuous algebra equivalence:** `baseChangeContinuousAlgEquiv` (`≃A[L]`) and `baseChangeAdeleContinuousAlgEquiv` (`≃A[𝔸ᶠ_K]`). The source carries the module topology of §2.2 and the target its restricted-product topology. The content is the instance `IsModuleTopology 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]`: the restricted-product topology on `𝔸ᶠ_L` is its module topology over `𝔸ᶠ_K`.
4. **Field norm `𝔸ᶠ_L → 𝔸ᶠ_K`:** none of the audited declarations involves a norm map. Relating `Algebra.norm 𝔸ᶠ_K` on `𝔸ᶠ_L`, which (2) makes available, to the product of local norms or to the Library's `finiteAdeleNorm` (`Norm.lean:79`) would be a new statement. This audit asserts no norm theorem.

### 2.6 Correspondence with the Library

The Library's number-field functoriality is in `Langlands/Global/AdelicFunctoriality/`. Its `finiteAdeleInclusion : FiniteAdeleRing (𝓞 K) K →+* FiniteAdeleRing (𝓞 L) L` (`Inclusion.lean:45`) is also `RestrictedProduct.mapAlongRingHom` along `under`. Its local maps are `FiniteExtension.completionMap p q` (`Extension.lean:65`). `Extension.lean:90` makes `(completionMap p q).toAlgebra` a scoped instance in namespace `Langlands.Global.AdelicFunctoriality.FiniteExtension`, under the hypothesis `[q.asIdeal.LiesOver p.asIdeal]`. We compared them with Imperial's patched closure at our pin:

| Comparison | Result | Diagnostic |
|---|---|---|
| `FiniteAdeleRing.mapRingHom (𝓞 K) K L (𝓞 L) x q = finiteAdeleInclusion x q` | `rfl` | `264816ba` |
| `FiniteAdeleRing.mapRingHom (𝓞 K) K L (𝓞 L) = finiteAdeleInclusion`, as ring homomorphisms | `rfl` at default transparency, without `ext`; also `RingHom.ext fun _ => FiniteAdeleRing.ext L fun _ => rfl`; fails with `with_reducible_and_instances rfl` | `173c090c`, `264816ba` |
| `Extension.adicCompletionSemialgHom K L w x = FiniteExtension.completionMap p w.1 x`, given `[w.1.asIdeal.LiesOver p.asIdeal]` | `rfl` | `bca04899` |
| Imperial's instance of line 238 `= (FiniteExtension.completionMap p w.1).toAlgebra`, same hypothesis | `rfl` at default transparency; fails with `with_reducible_and_instances rfl` | `bca04899`, `173c090c` |
| `baseChangeContinuousAlgEquiv (𝓞 K) K L (𝓞 L)`, with local instances `finiteAdeleInclusion.toAlgebra` and `ComapFiberwiseSMul` (proved by `obtain ⟨a, rfl⟩ := σ; rfl`) | elaborates with type `L ⊗[K] FiniteAdeleRing (𝓞 K) K ≃A[L] FiniteAdeleRing (𝓞 L) L`; `baseChangeAlgEquiv (l ⊗ₜ x) = algebraMap L _ l * finiteAdeleInclusion x` | `264816ba` |
| with `letI := finiteAdeleInclusion.toAlgebra`: `(x • y) q = completionMap (q.under _) q (x (q.under _)) * y q` | `rfl` | `52fd0d30` (Worker 248) |

The probe theorems of `264816ba`, `bca04899` and `173c090c` depend only on `propext`, `Classical.choice` and `Quot.sound`. Appendix C gives the probe sources.

**Consequence for a port.** Both pairs agree at default transparency, so there is no data diamond. In particular, the Library-built algebra satisfies Imperial's coherence class. They do not agree at instance-reducible transparency, which `with_reducible_and_instances rfl` tests and Mathlib uses for instance diamonds. If Imperial's global instance and the Library's scoped instance were both in scope, `simp`, `rw` and instance search could fail to identify terms elaborated with different instances. A port must keep exactly one. It should restate the local statements over the Library's `completionMap` and `FinitePlacesAbove` and should not port line 238 as a global instance.

The index types differ too. Imperial uses `v.Extension B = {w // w.under A = v}`, and the Library uses `FinitePlacesAbove L p = {q : HeightOneSpectrum (𝓞 L) // q.asIdeal.LiesOver p.asIdeal}` (`Norm.lean:19`). The Library's `finitePlacesAbove_under` (`Norm.lean:39`, `q.1.under (𝓞 K) = p`) and its instance `liesOver_under` (`Inclusion.lean:27`) give the two directions of an equivalence between them. A port must construct that equivalence; we did not.

## 3. Licenses, notices and attribution

**Imperial.** `LICENSE` is the Apache License, Version 2.0, and there is no `NOTICE` file. Each of the 37 closure files has the header "Released under Apache 2.0 license as described in the file LICENSE.", with a copyright line and an author list (Appendix B). `FiniteAdeleRing/BaseChange.lean` is "Copyright (c) 2025 Kevin Buzzard", authors Kevin Buzzard and Matthew Jasper. `Completion/BaseChange.lean` is "Copyright (c) 2025 Kevin Buzzard", authors Kevin Buzzard, Andrew Yang and Matthew Jasper.

**Anthropic.** `LICENSE` is Apache-2.0, and `NOTICE` opens with the title line "Fermat's Last Theorem in Lean 4", followed by "Copyright 2026 Anthropic, PBC". Its item 1 is the Imperial FLT project: material from Imperial's `main` branch as of 2026-05-21, two files from commit `8387d589441c1097d606ea89370c4165147255d5` (2026-05-27) and one from commit `7a87d3b25db19d008cd45b29edd2b92803e785b1`. The NOTICE says the Lean files carry no attribution headers, apart from five files that retained an FLT-project notice and the Mathlib provenance header of `Definitions/Def_Compat_Mathlib430.lean`, and that `ATTRIBUTION.md` reproduces the per-file notices of the others.

`ATTRIBUTION.md` line 19 attributes `Definitions/Def_DedekindDomain_FiniteAdeleRing_BaseChange.lean` ("whole file") to Imperial's `FLT/DedekindDomain/FiniteAdeleRing/BaseChange.lean` at commit `8387d589` (© 2025 Kevin Buzzard; authors Kevin Buzzard, Matthew Jasper). The same row adds `FLT/Mathlib/Topology/Algebra/RestrictedProduct/Module.lean`, `FLT/Mathlib/Topology/Algebra/Algebra/Hom.lean`, `FLT/Mathlib/LinearAlgebra/Pi.lean`, `FLT/Mathlib/Algebra/Algebra/Hom.lean` and `FLT/Mathlib/RingTheory/DedekindDomain/FiniteAdeleRing.lean`, each with its copyright holder and authors. Line 18 does the same for `Def_DedekindDomain_Completion_BaseChange.lean`. Line 183 (§5) says the copies of these two ports lost their notices, so their copyright and author lines were read from the upstream files at `8387d589`. The audited derivative file indeed has no header.

**Port obligations.** A port of Imperial files must keep each file's Apache-2.0 header, copyright line and authors. Each modified file must also carry a prominent notice of the change (Apache-2.0 §4(b)); the patches of §5.3 modify three files. The port needs no material from the Anthropic derivative. If any were used, the attribution notices in Anthropic's `NOTICE` would also have to be carried (§4(d)).

## 4. Kernel and axiom evidence

**Lean checks run for this audit.** All are private `lean_check` runs in environment `3b864ddf`, with the closure patched as in §5.3 and without `leanOptions`:

| Diagnostic | Check | Result |
|---|---|---|
| `8be90130` | lake build of the 37-module closure | 0 errors, 0 warnings |
| `8d7603c1` | `FLT/AuditCheck.lean`: `#check @` of the 8 declarations of §2.2, `#print axioms` of `baseChange_bijective`, `baseChangeAlgEquiv`, `baseChangeAdeleContinuousAlgEquiv` and `baseChangeContinuousAlgEquiv`, number-field instantiation with Imperial-style instances | 0 errors; each of the four depends on `[propext, Classical.choice, Quot.sound]` |
| `264816ba`, `bca04899`, `173c090c` | the Library comparisons of §2.6 | 0 errors; the probe theorems depend on the same three axioms |
| `99069b72` | an earlier form of `173c090c`, without `fail_if_success` | the two expected errors: `with_reducible_and_instances rfl` fails for both comparisons |
| `1103b363` | lake build of the unmodified 21-module Anthropic closure | fails: 9 errors, 42 warnings (§5.3) |
| `644dad01`, `cd82450e`, `415d40d7`, `34cc16be`, `13e7c29b` | builds before and during patching | the failures that patches (a)–(d) fix |

Lean's kernel checks each declaration when it is compiled. `#print axioms` collects, transitively, the axioms of every constant a declaration uses, and would list `sorryAx` if any proof it depends on used `sorry`. No independent replay (`lean4checker`, comparator) was run. These results are about the patched closure at our pin; the unpatched source was not built at Imperial's own pin.

**Textual checks.** These are scans of source text and establish no axiom result.

- **Imperial closure (37 files):** no `sorry`, `admit`, `knownin1980s`, `native_decide`, `implemented_by`, `unsafe`, `@[extern]`, `opaque`, `sorryAx`, `ofReduceBool` or `skipKernelTC`, and no `maxHeartbeats` or `synthInstance` options. The word "axiom" occurs only in two doc comments (`FiniteAdeleRing/TensorPi.lean:109` and `:131`). `Classical.choice inferInstance` occurs once (`RestrictedProduct/Basic.lean:254`). The files contain 46 `set_option backward.isDefEq.respectTransparency…` options.
- **Anthropic closure (21 files):** no `sorry`, `axiom` or `knownin1980s`. The derivative's root file sets `maxSynthPendingDepth 3` and `Elab.async false` (lines 5–6). Its nine `set_option … in` options of each kind raise `synthInstance.maxHeartbeats` up to 160000 and `maxHeartbeats` up to 800000 (lines 693 and 695). Two supplement files set file-wide `maxHeartbeats 1200000` and `synthInstance.maxHeartbeats 400000`: `Def_DedekindDomain_AdicValuation_InlineSpecific.lean:11–12` and `Def_DedekindDomain_Completion_BaseChange.lean:7–8`. The closure thus has 11 options of each kind.

**Author reports, not reproduced here.** The [external Lean reuse survey](external-lean-survey-2026-10-21.md) records three relevant points. Anthropic's README reports a complete FLT proof with kernel and comparator checks. Imperial's `FLT/Proof.lean` still has `B4_proof := sorry`, and `FLT/Assumptions/KnownIn1980s.lean` declares an axiom. Neither Imperial file is in the closure. Imperial's lakefile sets `warn.sorry = false`, so an upstream build log would not show `sorry` warnings; the axiom check above does not depend on warnings.

## 5. Overlap with Mathlib and the Library; version and API problems

This section merges Worker 248's comparison, which was made against Library `2f8d1873fbaeb581719bc35dbf6f5c9f2d4a8df4`. `Langlands/Global/AdelicFunctoriality/` is byte-identical at `2f8d1873`, `bb7700ac`, `dd9f9be5` and the current `55cf6172`, so the line numbers and probes cited here apply to all four.

### 5.1 Mathlib `5ed2965256430c3649e86755f9576b54eca72435`

- **Present and used:** the notation `𝔸ᶠ[R, K]` for `IsDedekindDomain.FiniteAdeleRing R K` (`RingTheory/DedekindDomain/FiniteAdeleRing.lean:111`), `RestrictedProduct.mapAlongRingHom`, `RestrictedProduct.mapAlong_continuous`, `FaithfulSMul.of_field_isFractionRing`, `LinearEquiv.extendScalarsOfIsLocalization`, `IsModuleTopology.iso`, `UniformSpace.Completion.mapRingHom_coe` and `RestrictedProduct.singleAddMonoidHom`. The last has no textual occurrence: `@[to_additive]` generates it from `RestrictedProduct.mulSingleMonoidHom` (`Topology/Algebra/RestrictedProduct/Basic.lean:574–576`).
- **Absent** (no occurrence in the Mathlib sources): `SemialgHom`, `ContinuousSemialgHom`, `RestrictedProduct.FiberwiseSMul`, `IsBiscalar`, `RestrictedProduct.lTensorEquivLeft`, `RestrictedProduct.mapAlongLinearMap`, `RestrictedProduct.flattenEquiv'`, `RestrictedProduct.flattenHomeomorph'`, `LinearEquiv.restrictedProductCongrRight`, `linearEquivTensorProductModuleLeft`, `IsModuleTopology.continuousAlgEquivOfAlgEquiv`, `RestrictedProduct.isModuleTopology`, `UniformSpace.Completion.mapSemialgHom` and `adicCompletionSemialgHom`. Each comes from an FLT-local file in the closure.
- **No base change:** none of the three files under `Topology/Algebra/RestrictedProduct/`, and neither of the two `FiniteAdeleRing.lean` files, mentions tensor products. Mathlib therefore has no form of `L ⊗[K] 𝔸ᶠ_K ≃ 𝔸ᶠ_L` and no commutation of tensor products with restricted products. It also has no algebra instance between adic completions at finite places: `NumberTheory/NumberField/Completion/LiesOverInstances.lean:46` provides scoped instances for infinite places only.

### 5.2 Library `Langlands/Global/AdelicFunctoriality/`

| Imperial (`923d4517`) | Library (`55cf6172`) | Relation |
|---|---|---|
| `IsDedekindDomain.HeightOneSpectrum.Extension B v := {w // w.under A = v}` (`FLT/DedekindDomain/IntegralClosure.lean:41`) | `FinitePlacesAbove L p := {q : HeightOneSpectrum (𝓞 L) // q.asIdeal.LiesOver p.asIdeal}` (`Norm.lean:19`) | The same primes above `p`, as different index types. A port needs an explicit equivalence (§2.6). |
| `Extension.adicCompletionSemialgHom K L w : v.adicCompletion K →ₛₐ[algebraMap K L] w.1.adicCompletion L` (`Completion/BaseChange.lean:182`), made a GLOBAL `Algebra` instance at `:238` | `FiniteExtension.completionMap p q : p.adicCompletion K →+* q.adicCompletion L` (`Extension.lean:65`), from `UniformSpace.Completion.mapRingHom` through `adicCompletion.equiv`; SCOPED `Algebra` instance (`Extension.lean:90`) for `[q.asIdeal.LiesOver p.asIdeal]` | Both are the continuous extension of `K → L`. The maps agree pointwise by `rfl`; the instances agree by `rfl` at default transparency only (§2.6). Keep the Library's instance. |
| `FiniteAdeleRing.mapRingHom A K L B : 𝔸ᶠ[A, K] →+* 𝔸ᶠ[B, L]` (`FiniteAdeleRing/BaseChange.lean:75`) | `finiteAdeleInclusion : FiniteAdeleRing (𝓞 K) K →+* FiniteAdeleRing (𝓞 L) L` (`Inclusion.lean:45`), with `finiteAdeleInclusion_apply` (`rfl`, `:52`) and `continuous_finiteAdeleInclusion` (`:57`) | Equal by `rfl` for number fields (§2.6). The Library has no `→SA[algebraMap K L]` form and no `Algebra 𝔸ᶠ_K 𝔸ᶠ_L` instance. |
| `HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L B v : L ⊗[K] v.adicCompletion K ≃ₐ[L] Π w : v.Extension B, w.1.adicCompletion L` (`Completion/BaseChange.lean:795`), proved by surjectivity and the dimension equality `finrank_tensorProduct_adicCompletion_eq_finrank_pi_adicCompletion` (`:772`, `baseChange_bijective` `:787`) | `finiteTensorMap p : p.adicCompletion K ⊗[K] L →ₐ[p.adicCompletion K] ((q : FinitePlacesAbove L p) → q.1.adicCompletion L)` (`Norm.lean:178`), bijective at every finite place by the proved `completedTensorComparison : CompletedTensorComparison` (`CompletedTensorComparisonProof.lean:15`; statement `NormStatement.lean:14`), through `finiteTensorMap_surjective` (`FiniteComparisonReduction.lean:68`), `finitePlacesAbove_sum_ramification_inertia` (`:119`) and `completedLocalDegreeLowerBound` (`CompletedLocalDegreeProof.lean:65`) | The same local field-level comparison, proved by a similar route. The tensor factors are in opposite order, and the linearity differs (`L` versus `p.adicCompletion K`). Reuse the Library's proof; porting Imperial's field-level part would duplicate it. |
| `integerBaseChangeLinearEquiv_bijOn` (`Completion/BaseChange.lean:854`): the image of `B ⊗[A] v.adicCompletionIntegers K` is `Π w, w.1.adicCompletionIntegers L`; proved through `tensorAdicCompletionIntegersTo` (`:364`) and `range_baseChange_comp_tensorAdicCompletionTo_eq_pi` (`:535`) | only `completionIntegersMap` (`CompletedRamification.lean:43`) and a scoped `Algebra (p.adicCompletionIntegers K) (q.adicCompletionIntegers L)` (`:51`) | MISSING: the Library has no integral tensor comparison. It is the main local input of the global equivalence. |
| `RestrictedProduct.lTensorEquivLeft` (`FiniteAdeleRing/TensorRestrictedProduct.lean:240`; `[Module.Flat R M] [Module.FinitePresentation R M]`) | none | MISSING: a general commutation of tensor products with restricted products, independent of number fields. |
| `FiniteAdeleRing.baseChangeAlgEquiv`, `baseChangeContinuousAlgEquiv` and the instance `IsModuleTopology 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]` | none. `finiteAdeleNorm` (`Norm.lean:79`), `adeleNorm` (`:154`), `ideleNorm` (`:162`) and the proved `normCompatibility` (`NormCompatibilityProof.lean:11`) are field-norm results, owned by task `51d4331f` | MISSING. The Library's norm theorems are not base-change statements, and a base-change equivalence alone gives no norm theorem. |

### 5.3 Version and API problems at our pin

**Imperial.** Four patches suffice; Appendix A gives them exactly.

| | Location | Problem at our pin | Patch |
|---|---|---|---|
| (a) | `FLT/Mathlib/Topology/Algebra/Module/Quotient.lean:9` | module `Mathlib.Topology.Algebra.Module.Equiv.Basic` does not exist | import `Mathlib.Topology.Algebra.Module.Equiv`; the [Haar audit](imperial-haar-audit-2026-10-21.md) needed the same change |
| (b) | `FLT/Mathlib/Topology/Algebra/UniformRing.lean:34–35` | unknown constant `MonoidHom.coe_ofClass` in a `simp only` list (`644dad01`) | remove it from the list |
| (c) | same file, line 38 | `exact extensionHom_coe _ _ m` fails (`cd82450e`) | `exact mapRingHom_coe hf m`, using Mathlib's `UniformSpace.Completion.mapRingHom_coe` |
| (d) | `FLT/DedekindDomain/Completion/BaseChange.lean:577–579`, the `IsBiscalar` instance of line 575 | the `simp only` proof of `map_smul₂` no longer rewrites the right-action scalar multiplication (`34cc16be`); turning off `backward.isDefEq.respectTransparency` does not help (`13e7c29b`) | rewrite first with `rw [Algebra.smul_def s a, map_mul, Algebra.smul_def]`, then the reordered `simp only` and the existing `rfl` |

With these patches the closure builds (`8be90130`), even without Imperial's `maxSynthPendingDepth = 3`, and the 46 `respectTransparency` options elaborate under our Lean.

**Anthropic.** Diagnostic `1103b363` shows 9 errors in 4 modules, and the dependent modules were not built:

- `Def_DedekindDomain_AdicValuation_InlineSpecific`: rewrites with the patterns `- -?a` (line 101) and `?r • ?x` (line 353) fail, `inv_mabs_le` gives a type mismatch (line 111), and a rewrite pattern is not found (line 471);
- `Def_Mathlib_RingTheory_Localization_BaseChange` line 62 and `Def_Mathlib_RightActionInstances` lines 33, 44 and 73: "Invalid alternative name `zero`" in `TensorProduct` induction;
- `Def_Mathlib_Topology_Algebra_RestrictedProduct_Basic` line 277: `RestrictedProduct.singleAddMonoidHom` has already been declared, because Mathlib now has it;
- among the warnings are deprecations such as `Set.Countable.setOf_finite` and `continuous_finset_sum`.

At Imperial's two proof failures, the derivative has the older proofs. Its `UniformRing` file still uses `exact extensionHom_coe _ _ m`, with `MonoidHom.coe_coe` in place of `MonoidHom.coe_ofClass` in the `simp` list. Its `IsBiscalar` proof (`Def_DedekindDomain_Completion_BaseChange.lean:858`) is Imperial's original `simp only` proof. Its quotient file imports the umbrella `Mathlib`, so problem (a) does not arise.

The derivative keeps Imperial's declaration names and namespace, the same variable block (lines 390–393, textually identical to Imperial's lines 44–47), the same inputs (lines 447 and 459) and the same conclusions (lines 606, 611, 720 and 724). It uses older names: `restrictedProduct_tensorProduct_equiv_restrictedProduct_prod`, `restrictedProduct_prod_equiv`, `restrictedProduct_pi_equiv` and `SemialgHom.baseChange_of_algebraMap`. Its root file inlines `ContinuousSemialgHom` (lines 10–97), the restricted-product module API (lines 101–307, including `isModuleTopology` at line 285) and `Pi.FiberwiseSMul` and `RestrictedProduct.FiberwiseSMul` (lines 312 and 349). Its closure is smaller (21 modules), but our Lean 4.34.0 lies between its 4.33.1 and Imperial's 4.35.0-rc4, and only Imperial's closure builds here.

## 6. Verdict and smallest next units

**Verdict: adapt.** The evidence is in §4–§5. The Imperial construction passes every check made here: its patched closure builds at our pin, and its main declarations use only the three standard axioms. It also fits our objects: its map is the Library's `finiteAdeleInclusion` by `rfl` at default transparency, and the Library-built algebra satisfies its coherence class. It cannot be imported as it stands, for three reasons. It needs four patches. Its general API (`SemialgHom`, `ContinuousSemialgHom`, `IsBiscalar`, `FiberwiseSMul`, `TensorProduct.RightActions`) is absent from Mathlib. Its global local-algebra instance would duplicate the Library's at instance-reducible transparency. The Anthropic derivative is rejected as a port source: it fails at our pin and fixes neither proof failure.

Design decisions for any port:

- **Source:** use Imperial `923d4517` with patches (a)–(d), and keep its notices (§3).
- **Instances:** use one local algebra instance, the Library's scoped `FiniteExtension` instance, and one adelic algebra instance, `finiteAdeleInclusion.toAlgebra` (scoped; unit 1). Do not port Imperial's line 238 or its number-field instances.
- **Local field comparison:** reuse the Library's `finiteTensorMap` and `completedTensorComparison`. Port only the integral part of Imperial's local file.
- **Statement form (our recommendation):** state the global equivalence in the Library's tensor order, `FiniteAdeleRing (𝓞 K) K ⊗[K] L`, matching `finiteTensorMap`. Mathlib's standard left-factor algebra structure then supplies the `FiniteAdeleRing (𝓞 K) K`-linearity, and no `TensorProduct.RightActions` scope is needed. Port FLT-local API only where the proofs need it.

The smallest next units follow, in dependency order. Each would be a separate authorized task with published statement targets, normal validation and independent semantic review; this audit publishes none.

1. **Definition (Library, number fields).** A scoped instance `Algebra (FiniteAdeleRing (𝓞 K) K) (FiniteAdeleRing (𝓞 L) L) := finiteAdeleInclusion.toAlgebra` in `Langlands/Global/AdelicFunctoriality/`, with the coordinate lemma `(x • y) q = completionMap (q.under _) q (x (q.under _)) * y q`, which holds by `rfl` (`52fd0d30`). This lemma is the Library form of Imperial's `ComapFiberwiseSMul`. The unit belongs to task `51d4331f` or to a task coordinated with it.
2. **Definitions and proofs (general, no number fields).** `RestrictedProduct.lTensorEquivLeft`, for `Module.Flat` and `Module.FinitePresentation`, with its FLT-local helpers. The sources are `FLT/DedekindDomain/FiniteAdeleRing/{TensorPi, IsDirectLimitRestricted, TensorRestrictedProduct}.lean`, `FLT/Mathlib/Algebra/IsDirectLimit.lean` and the parts of `FLT/Mathlib/Topology/Algebra/RestrictedProduct/` that these use. The result suits a standalone general module.
3. **Statement, then proof: integral local comparison.** For each finite place `p`, transport the bijection of `finiteTensorMap p` to `𝓞 L ⊗[𝓞 K] p.adicCompletion K` and show that the image of `𝓞 L ⊗[𝓞 K] p.adicCompletionIntegers K` is `Π (q : FinitePlacesAbove L p), q.1.adicCompletionIntegers L`. This is the Library form of Imperial's `integerBaseChangeLinearEquiv_bijOn`. The proof sources are the integral parts of `Completion/BaseChange.lean`: lines 364–547 (`tensorAdicCompletionIntegersTo` through `range_baseChange_comp_tensorAdicCompletionTo_eq_pi`), the `IsBiscalar` instance of line 575 (patch (d)) with the definitions that follow it, and lines 810–870 (`integerBaseChangeLinearEquiv` and its `_bijOn`).
4. **Statement, then proof: global algebra equivalence.** Show that the `FiniteAdeleRing (𝓞 K) K`-algebra map `FiniteAdeleRing (𝓞 K) K ⊗[K] L → FiniteAdeleRing (𝓞 L) L`, `x ⊗ l ↦ finiteAdeleInclusion x * algebraMap L _ l`, is bijective, and package it as an algebra equivalence. The proof source is `FiniteAdeleRing/BaseChange.lean:129–275`, with units 2 and 3 in place of Imperial's local file.
5. **Statement, then proof: topology.** `IsModuleTopology (FiniteAdeleRing (𝓞 K) K) (FiniteAdeleRing (𝓞 L) L)`. Unit 4 then becomes a homeomorphism for the module topology on the tensor product, which the statement must name explicitly because Mathlib has none. The proof sources are `FiniteAdeleRing/BaseChange.lean:277–365`, `RestrictedProduct.isModuleTopology` (`FLT/Mathlib/Topology/Algebra/RestrictedProduct/Module.lean`) and `IsModuleTopology.continuousAlgEquivOfAlgEquiv` (`FLT/Mathlib/Topology/Algebra/Module/ModuleTopology.lean`).

Any norm statement, for example relating `Algebra.norm` along unit 4 to `finiteAdeleNorm`, belongs to task `51d4331f`. The base-change units prove none.

## Appendix A. Compatibility patches

Diffs against the Imperial snapshot at `923d4517`. Each patched file would need a modification notice in a port (§3).

```diff
--- FLT/Mathlib/Topology/Algebra/Module/Quotient.lean (line 9)
-public import Mathlib.Topology.Algebra.Module.Equiv.Basic
+public import Mathlib.Topology.Algebra.Module.Equiv

--- FLT/Mathlib/Topology/Algebra/UniformRing.lean (lines 34-35 and 38)
-    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
-      MonoidHom.coe_ofClass]
+    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe]
     rw [Algebra.smul_def, map_mul, Algebra.smul_def]
     congr
-    exact extensionHom_coe _ _ m
+    exact mapRingHom_coe hf m

--- FLT/DedekindDomain/Completion/BaseChange.lean (lines 577-579; line 580 `rfl` is kept)
-  map_smul₂ _ _ := by
-    simp only [tensorAdicCompletionIntegersTo_tmul, Algebra.smul_def,
-      TensorProduct.RightActions.algebraMap_eval, map_mul, map_one]
+  map_smul₂ s a := by
+    rw [Algebra.smul_def s a, map_mul, Algebra.smul_def]
+    simp only [TensorProduct.RightActions.algebraMap_eval, tensorAdicCompletionIntegersTo_tmul,
+      map_one]
     rfl
```

## Appendix B. Imperial closure: files, copyright and authors

Every file has the Apache-2.0 header. The years and holders below are from each file's "Copyright (c)" line.

| Module | Lines | Copyright | Authors |
|---|---|---|---|
| `FLT.DedekindDomain.AdicValuation` | 606 | 2025 Matthew Jasper | Matthew Jasper |
| `FLT.DedekindDomain.IntegralClosure` | 323 | 2025 Kevin Buzzard | Kevin Buzzard, Andrew Yang, Matthew Jasper |
| `FLT.DedekindDomain.Completion.BaseChange` | 870 | 2025 Kevin Buzzard | Kevin Buzzard, Andrew Yang, Matthew Jasper |
| `FLT.DedekindDomain.FiniteAdeleRing.TensorPi` | 275 | 2025 Madison Crim | Madison Crim |
| `FLT.DedekindDomain.FiniteAdeleRing.IsDirectLimitRestricted` | 107 | 2025 Madison Crim | Madison Crim |
| `FLT.DedekindDomain.FiniteAdeleRing.TensorRestrictedProduct` | 259 | 2025 Matthew Jasper | Matthew Jasper |
| `FLT.DedekindDomain.FiniteAdeleRing.BaseChange` | 367 | 2025 Kevin Buzzard | Kevin Buzzard, Matthew Jasper |
| `FLT.Mathlib.Algebra.Algebra.Hom` | 178 | 2025 Kevin Buzzard | Kevin Buzzard, Salvatore Mercuri |
| `FLT.Mathlib.Algebra.Algebra.Tower` | 147 | 2025 Salvatore Mercuri | Salvatore Mercuri, Kevin Buzzard |
| `FLT.Mathlib.Algebra.Algebra.Bilinear` | 155 | 2025 Kevin Buzzard | Kevin Buzzard, Salvatore Mercuri, Ruben Van de Velde |
| `FLT.Mathlib.Algebra.Algebra.Pi` | 168 | 2025 Kevin Buzzard | Kevin Buzzard, Salvatore Mercuri |
| `FLT.Mathlib.Algebra.Module.Submodule.Basic` | 28 | 2025 Yaël Dillies | Yaël Dillies, Kevin Buzzard, Matthew Jasper |
| `FLT.Mathlib.Algebra.IsDirectLimit` | 194 | 2025 Madison Crim | Madison Crim |
| `FLT.Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic` | 22 | 2025 Salvatore Mercuri | Salvatore Mercuri, Kevin Buzzard |
| `FLT.Mathlib.RingTheory.Valuation.ValuationSubring` | 47 | 2025 Ruben Van de Velde | Ruben Van de Velde, Kevin Buzzard, Salvatore Mercuri |
| `FLT.Mathlib.RingTheory.DedekindDomain.AdicValuation` | 59 | 2025 Kevin Buzzard | Kevin Buzzard, Salvatore Mercuri |
| `FLT.Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing` | 216 | 2025 Salvatore Mercuri | Salvatore Mercuri, Kevin Buzzard |
| `FLT.Mathlib.RingTheory.Localization.BaseChange` | 95 | 2025 Matthew Jasper | Matthew Jasper |
| `FLT.Mathlib.RingTheory.TensorProduct.Basis` | 96 | 2025 Matthew Jasper | Matthew Jasper |
| `FLT.Mathlib.RingTheory.RamificationInertia.Basic` | 46 | 2026 Kevin Buzzard | Kevin Buzzard |
| `FLT.Mathlib.Topology.Algebra.Module.ModuleTopology` | 540 | 2024 Kevin Buzzard | Kevin Buzzard, Pietro Monticone, Salvatore Mercuri, Matthew Jasper, Ruben Van de Velde, William Coram |
| `FLT.Mathlib.Topology.Algebra.Module.Quotient` | 56 | 2025 Salvatore Mercuri | Salvatore Mercuri, Kevin Buzzard, Pietro Monticone |
| `FLT.Mathlib.Topology.Algebra.UniformRing` | 53 | 2025 Kevin Buzzard | Kevin Buzzard, Salvatore Mercuri |
| `FLT.Mathlib.Topology.Algebra.RestrictedProduct.Basic` | 318 | 2025 Matthew Jasper | Matthew Jasper, Kevin Buzzard, Ruben Van de Velde |
| `FLT.Mathlib.Topology.Algebra.RestrictedProduct.Equiv` | 657 | 2025 Kevin Buzzard | Kevin Buzzard, Salvatore Mercuri |
| `FLT.Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace` | 739 | 2025 Matthew Jasper | Matthew Jasper, Kevin Buzzard, Bhavik Mehta, Ruben Van de Velde, Bryan Wang Peng Jun, Pietro Monticone |
| `FLT.Mathlib.Topology.Algebra.RestrictedProduct.Module` | 262 | 2025 Matthew Jasper | Matthew Jasper |
| `FLT.Mathlib.Topology.Algebra.RestrictedProduct.Algebra` | 33 | 2026 Andrew Yang | Andrew Yang |
| `FLT.Mathlib.Topology.Algebra.MulAction` | 27 | 2025 Matthew Jasper | Matthew Jasper, Kevin Buzzard |
| `FLT.Mathlib.Topology.Algebra.ContinuousMonoidHom` | 78 | 2025 Salvatore Mercuri | Salvatore Mercuri, Kevin Buzzard |
| `FLT.Mathlib.Topology.Algebra.Group.Units` | 22 | 2025 Kevin Buzzard | Kevin Buzzard, Ruben Van de Velde |
| `FLT.Mathlib.Topology.Algebra.Algebra.Hom` | 116 | 2026 Salvatore Mercuri | Salvatore Mercuri, Kevin Buzzard |
| `FLT.Mathlib.Topology.Bases` | 31 | 2025 Kevin Buzzard | Kevin Buzzard |
| `FLT.Mathlib.LinearAlgebra.Pi` | 79 | 2025 Salvatore Mercuri | Salvatore Mercuri, Kevin Buzzard |
| `FLT.Mathlib.Order.Filter.Cofinite` | 26 | 2025 Kevin Buzzard | Kevin Buzzard |
| `FLT.Hacks.RightActionInstances` | 248 | 2025 Kevin Buzzard | Kevin Buzzard, Pietro Monticone |
| `FLT.Deformations.ContinuousRepresentation.IsTopologicalModule` | 53 | 2025 Javier López-Contreras | Javier López-Contreras |

## Appendix C. Library comparison probes

These private probes import the patched closure and the Library. They are evidence for §2.6, not proposed Library code.

```lean
-- FLT/LibraryBridge.lean (diagnostic 264816ba): imports FLT.DedekindDomain.FiniteAdeleRing.BaseChange
-- and Langlands.Global.AdelicFunctoriality.Inclusion
open IsDedekindDomain NumberField
variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

example (x : FiniteAdeleRing (𝓞 K) K) (q : HeightOneSpectrum (𝓞 L)) :
    FiniteAdeleRing.mapRingHom (𝓞 K) K L (𝓞 L) x q =
      Langlands.Global.AdelicFunctoriality.finiteAdeleInclusion x q :=
  rfl

theorem probe_mapRingHom_eq_finiteAdeleInclusion :
    FiniteAdeleRing.mapRingHom (𝓞 K) K L (𝓞 L) =
      Langlands.Global.AdelicFunctoriality.finiteAdeleInclusion :=
  RingHom.ext fun _ => FiniteAdeleRing.ext L fun _ => rfl

section LibraryInstance
noncomputable local instance : Algebra (FiniteAdeleRing (𝓞 K) K) (FiniteAdeleRing (𝓞 L) L) :=
  (Langlands.Global.AdelicFunctoriality.finiteAdeleInclusion (K := K) (L := L)).toAlgebra

local instance : FiniteAdeleRing.ComapFiberwiseSMul (𝓞 K) K L (𝓞 L) where
  map_smul r x b σ := by obtain ⟨a, rfl⟩ := σ; rfl

open scoped TensorProduct TensorProduct.RightActions in
noncomputable example :
    L ⊗[K] FiniteAdeleRing (𝓞 K) K ≃A[L] FiniteAdeleRing (𝓞 L) L :=
  FiniteAdeleRing.baseChangeContinuousAlgEquiv (𝓞 K) K L (𝓞 L)

open scoped TensorProduct TensorProduct.RightActions in
example (l : L) (x : FiniteAdeleRing (𝓞 K) K) :
    FiniteAdeleRing.baseChangeAlgEquiv (𝓞 K) K L (𝓞 L) (l ⊗ₜ x) =
      algebraMap L (FiniteAdeleRing (𝓞 L) L) l *
        Langlands.Global.AdelicFunctoriality.finiteAdeleInclusion x :=
  SemialgHom.baseChange_of_algebraMap_tmul _ l x
end LibraryInstance
```

```lean
-- FLT/TransparencyBridge.lean (diagnostic 173c090c): imports FLT.DedekindDomain.FiniteAdeleRing.BaseChange,
-- Langlands.Global.AdelicFunctoriality.Extension and Langlands.Global.AdelicFunctoriality.Inclusion
open IsDedekindDomain HeightOneSpectrum NumberField
variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

theorem probe_localAlgebra_eq_default_not_reducible (p : HeightOneSpectrum (𝓞 K))
    (w : p.Extension (𝓞 L)) [w.1.asIdeal.LiesOver p.asIdeal] :
    (inferInstance : Algebra (p.adicCompletion K) (w.1.adicCompletion L)) =
      (Langlands.Global.AdelicFunctoriality.FiniteExtension.completionMap p w.1).toAlgebra := by
  fail_if_success with_reducible_and_instances rfl
  rfl

theorem probe_mapRingHom_eq_finiteAdeleInclusion_default_not_reducible :
    FiniteAdeleRing.mapRingHom (𝓞 K) K L (𝓞 L) =
      Langlands.Global.AdelicFunctoriality.finiteAdeleInclusion := by
  fail_if_success with_reducible_and_instances rfl
  rfl
```

Diagnostic `bca04899` checked the first equation of `TransparencyBridge` by a plain term-mode `rfl`, together with the pointwise equation `Extension.adicCompletionSemialgHom K L w x = FiniteExtension.completionMap p w.1 x := rfl`.

## Sources

- `external-lean-reuse-snapshots-2026-10-21`: pinned snapshots of ImperialCollegeLondon/FLT at `923d45174c500aa1d994ba973bac38ea39eacbf7` and anthropics/fermats-last-theorem at `6e837e75355538c7f80bab5b956861e86c4eacc2`, with their `tree.json`, `LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
- `anthropic-flt-6e837e75-basechange-closure-supplement`: the 14 Anthropic `Definitions/*.lean` files of the derivative's closure that the snapshot lacks, checked against `tree.json`.
- Library `55cf6172e313c02aa8f5978501d957bfa08de20d`, `Langlands/Global/AdelicFunctoriality/` (byte-identical at `2f8d1873`, `bb7700ac` and `dd9f9be5`), and Mathlib `5ed2965256430c3649e86755f9576b54eca72435` in environment `3b864ddf`.
- Related notes: [external Lean reuse survey](external-lean-survey-2026-10-21.md) and [Imperial FLT Haar scaling audit](imperial-haar-audit-2026-10-21.md).
