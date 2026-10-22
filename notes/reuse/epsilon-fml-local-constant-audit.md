# Ueda epsilon_FML local constants: normalization audit

Worker 216 wrote this audit for task `44d2f4d1` (revision 2). It compares Fukuhiro Ueda's `LanglandsFirstMainLemma.firstMainLemma` and its canonical `localConstant` with the project's rank-one epsilon expressions in `Langlands/LocalFactor/Abelian/Padic.lean` (imported by `Langlands/LocalFactor/PadicAbelian.lean`) and with `Langlands/LocalFactor/PadicAbelianStatement.lean`. It also fixes the dependency boundary to the second-main-lemma repository. This audit does not establish any external theorem, and it adds or changes no Lean target.

**Verdict: adapt.** Do not import or vendor the repository. Its `Δ` is Tate's Langlands-normalized root number written as a phase. For every Haar measure `μ`, the project's `epsilon T χ ψ μ s` equals `Δ(χ·|·|^{s-1/2}, ψ)` times an explicit positive real `r(χ, ψ, μ)`. The equality `langlandsConstantAtSelfDual = Δ` additionally needs two facts that the Library does not currently prove (§2.7). The proved First Main identity is a degree-zero statement, in which `r` cancels apart from the Gauss-sum modulus. Section 6 lists the smallest port units.

## 1. Pins, source closure and missing inputs

**Pins.**

- **Repository:** [fukubillueda-web/epsilon_FML](https://github.com/fukubillueda-web/epsilon_FML/tree/0b4159be50e1bd45ddff1de4280399576a3e2024) at commit `0b4159be50e1bd45ddff1de4280399576a3e2024`. The GitHub tags API on 2026-10-21 showed `v1.0.0` pointing at this commit. Tags can be moved, so cite the commit, not the tag.
- **Toolchain:** `lean-toolchain` is `leanprover/lean4:v4.32.2`. `lakefile.toml` requires Mathlib at `rev = "v4.32.2"`, a tag that `lake-manifest.json` resolves to `905b95818eb32af7874a58b427f50c1711a5e96c`. The lakefile also requires `checkdecls` at `3d425859e73fcfbef85b9638c2a91708ef4a22d4`.
- **Our target:** Lean 4.34.0 with Mathlib `5ed2965256430c3649e86755f9576b54eca72435` (environment `3b864ddf`).

**Sources read.**

- **Snapshot:** registered source `external-lean-reuse-snapshots-2026-10-21`, folder `fukubillueda-web--epsilon_FML/source` (147 files). All 147 files match the git blob SHA1s in the snapshot's `tree.json`.
- **Missing files:** the snapshot omits `CITATION.cff`, `.gitignore` and the companion manuscript `references/epsilon_FML.tex`. I fetched them, checked their blob SHA1s against `tree.json`, and registered them as `ueda-epsilon-fml-0b4159be-supplement` (fingerprint `732d2916391aea73a2b1688d8be48779ff51ac135b2250e135685ad3b24a0ac8`). The same folder holds the GitHub compare response `b91ad939...0b4159be` and the recursive tree of `b91ad939`.

**Later FML commit versus the SML pin.** epsilon_SML pins FML at `b91ad93900a5e6d9207a4e6166ac94bb3bbcf3ed`. The compare response shows that `0b4159be` is `b91ad939` plus one commit, which changes only `README.md`, `SOURCE_MAP.md` and `references/epsilon_FML.tex`. All 141 `.lean` files, `lakefile.toml`, `lake-manifest.json` and `lean-toolchain` have identical blob SHAs in both trees. SML's FML dependency is therefore the audited Lean source, byte for byte. The snapshot's warning that the two pins might differ is resolved for Lean files.

**Dependency closure** (computed from `import` lines):

| Root | Internal modules | Lines | External imports |
|---|---|---|---|
| `LanglandsFirstMainLemma.Main` (proof of the exported theorem) | 140 of 141 (all except the root `LanglandsFirstMainLemma.lean`) | 138,486 | 35 distinct: `import Mathlib` in `Prelude.lean` plus 34 named Mathlib modules |
| `Delta.LocalConstantRealization` + `Delta.FirstMainStatement` (definitions of `localConstant` and the identity) | 20 | 8,672 | `import Mathlib` plus 10 named Mathlib modules |
| `Delta.FirstMainStatement` alone | 10 | 3,673 | `import Mathlib` plus 3 named Mathlib modules (`Topology.Algebra.Module.FiniteDimension`, `Topology.Algebra.Module.Compact`, `RingTheory.Finiteness.Finsupp`, all imported by `LocalField.Extension`) |

The 10-module closure of `Delta.FirstMainStatement` is `Prelude`, `Basic.{CharacterTypes, CharacteristicConvention, Phase}`, `LocalField.{Valuation, Lattices, ResidueField, UnitFiltration, Extension}` and `Delta.FirstMainStatement` itself. It does **not** contain the conductor layer `Basic.CharacterConductors`/`Basic.CharacterConductorExistence`; §6 accounts for this.

The 20-module definition closure consists of:

- `Prelude`;
- `Basic.{CharacterTypes, CharacteristicConvention, Phase, CharacterConductors, CharacterConductorExistence, StandardCharacterBridge}`;
- `LocalField.{Valuation, Lattices, ResidueField, UnitFiltration, FiniteQuotients, Extension}`;
- `Delta.{FiniteDefinition, IntegralDefinition, IntegralFiniteBridge, Nonvanishing, ErrorTerm, FirstMainStatement, LocalConstantRealization}`.

The *statement* of `firstMainLemma` reaches beyond `FirstMainStatement`. Its `letI`s use `PrimeCyclicExtension.ofCyclicPrimeExtension` (`Ramification/PrimeCyclicExtension.lean`) and the theorem `primeCyclicNormCharacter_finite` (`Ramification/NormCharacters.lean:457`). Because `Finite` is a `Prop`, a port can take `[Finite (NormCharacter F K)]` as a hypothesis or prove it separately (§6).

**Inputs still missing:**

- no build log, CI workflow (the tree has no `.github`) or `leanchecker` output;
- no NOTICE file;
- no external build: the pinned toolchain differs from the approved environment, and an external build is not permitted here.

## 2. Selected declarations and their meaning

All FML declarations are in namespace `LanglandsFirstMainLemma`. File paths are relative to `source/LanglandsFirstMainLemma/`.

### 2.1 Character types and conductors

```lean
-- Basic/CharacterTypes.lean:21, :25
def ContinuousAddChar (A : Type*) [AddMonoid A] [TopologicalSpace A] :=
  {ψ : AddChar A ℂˣ // Continuous ψ}
abbrev ContinuousQuasiChar (F : Type*) [Monoid F] [TopologicalSpace F] :=
  ContinuousMonoidHom Fˣ ℂˣ

-- LocalField/Lattices.lean:74 (carrier); LocalField/UnitFiltration.lean:89
noncomputable def lattice (n : ℤ) : Submodule (ringOfIntegers F) F where
  carrier := {x | (n : WithTop ℤ) ≤ ord F x}  -- ...
noncomputable def unitFiltration : ℕ → Subgroup Fˣ
  | 0 => unitGroup F
  | n + 1 => positiveUnitFiltration F n          -- 1 + 𝔭^(n+1)

-- Basic/CharacterConductors.lean:30, :35, :94, :100, :394, :402
def AddCharTrivialOnLattice (ψ : ContinuousAddChar F) (r : ℤ) : Prop :=
  ∀ x : F, x ∈ lattice F r → ψ x = 1
def QuasiCharTrivialOnUnitFiltration (χ : ContinuousQuasiChar F) (m : ℕ) : Prop :=
  ∀ u : Fˣ, u ∈ unitFiltration F m → χ u = 1
structure IsAdditiveConductor (ψ : ContinuousAddChar F) (n : ℤ) : Prop where
  trivial : AddCharTrivialOnLattice F ψ (-n)
  minimal : ∀ r : ℤ, AddCharTrivialOnLattice F ψ r → -n ≤ r
structure IsMultiplicativeConductor (χ : ContinuousQuasiChar F) (m : ℕ) : Prop where
  trivial : QuasiCharTrivialOnUnitFiltration F χ m
  minimal : ∀ r : ℕ, QuasiCharTrivialOnUnitFiltration F χ r → m ≤ r
structure LocalAddCharData where
  character : ContinuousAddChar F
  conductor : ℤ
  isConductor : IsAdditiveConductor F character conductor
structure LocalQuasiCharData where
  character : ContinuousQuasiChar F
  conductor : ℕ
  isConductor : IsMultiplicativeConductor F character conductor
```

Here `ord F : AddValuation F (WithTop ℤ)` (`LocalField/Valuation.lean:89`) is the normalized additive valuation. It is built from the `ValuativeRel` valuation through `IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt`. The FML conductor `n(ψ)` is the largest `n` with `ψ` trivial on `𝔭^{-n}`. The FML `m(χ)` is the least `m` with `χ` trivial on `U^m`, where `U^0 = 𝒪ˣ`. These are Tate's `n(ψ)` and `a(χ)`.

`canonicalLocalQuasiCharData F χ` and `canonicalLocalAddCharData F ψ hψ` (`Basic/CharacterConductorExistence.lean:397`, `:442`) choose the exponents with `Classical.choose` from proved existence theorems. Uniqueness lemmas make the choice unobservable.

### 2.2 Finite and integral local constants

```lean
-- Delta/FiniteDefinition.lean:27, :88, :163, :1055
abbrev AdmissibleGamma (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F) :=
  {γ : Fˣ // ord F (γ : F) = (((χ.conductor : ℤ) + ψ.conductor : ℤ) : WithTop ℤ)}
def finiteGaussSummandRepresentative (χ ψ) (γ : AdmissibleGamma F χ ψ)
    (u : unitFiltration F 0) : ℂ :=
  (ψ.character (((u : Fˣ) : F) / ((γ : Fˣ) : F)) : ℂ) * (χ.character (u : Fˣ) : ℂ)⁻¹
def finiteGaussSum (χ ψ) (γ : AdmissibleGamma F χ ψ) : ℂ := by
  letI := unitFiltrationQuotientFintype F (Nat.zero_le χ.conductor)
  exact ∑ u, finiteGaussSummand χ ψ γ u          -- sum over U⁰/U^m
def deltaFinite (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F)
    (γ : AdmissibleGamma F χ ψ) : ℂ :=
  (χ.character (γ : Fˣ) : ℂ) * phase (finiteGaussSum χ ψ γ)

-- Basic/Phase.lean:13
noncomputable def phase (z : ℂ) : ℂ := if z = 0 then 1 else z / (‖z‖ : ℂ)

-- Delta/IntegralDefinition.lean:37, :194, :304, :381
abbrev IntegralAdmissibleGamma (chi psi) := {γ : Fˣ // ord F (γ : F) = ...}  -- same equation
noncomputable instance unitFiltrationZeroMeasurableSpace :
    MeasurableSpace (unitFiltration F 0) := borel (unitFiltration F 0)
def unitGaussIntegral (mu : Measure (unitFiltration F 0)) (chi psi gamma) : ℂ :=
  ∫ u, unitHaarIntegrand chi psi gamma u ∂mu  -- integrand ψ(u/γ)·χ(u)⁻¹
def deltaIntegral (mu : Measure (unitFiltration F 0)) [mu.IsHaarMeasure]
    (chi psi) (gamma : IntegralAdmissibleGamma F chi psi) : ℂ :=
  (chi.character (gamma : Fˣ) : ℂ) * phase (unitGaussIntegral mu chi psi gamma)
```

The following results are proved in the source:

- `finiteGaussSum_ne_zero` (`:998`) and `deltaFinite_gamma_independent` (`:1063`);
- `deltaIntegral_measure_independent` (`Delta/IntegralDefinition.lean:390`);
- `deltaIntegral_eq_deltaFinite` (`Delta/IntegralFiniteBridge.lean:280`);
- `delta_trivial_character` (`Delta/Elementary.lean:268`): `Δ(1, ψ) = 1`;
- `localAddChar_norm_eq_one` (`Delta/Elementary.lean:340`): `‖ψ x‖ = 1` for characters with conductor data.

The source proves the Gauss sum nonzero but has no theorem giving its modulus `|G| = q^{m/2}`. Its only Gauss-sum modulus result concerns finite fields.

### 2.3 The total function and the trivial additive character

```lean
-- Delta/FirstMainStatement.lean:80; Delta/LocalConstantRealization.lean:65, :73
abbrev LocalConstantFunction (E : Type*) [Field E] [TopologicalSpace E] :=
  ContinuousQuasiChar E → ContinuousAddChar E → ℂ
noncomputable def localConstantFunction : LocalConstantFunction F := by
  classical
  exact fun χ ψ => if hψ : ψ = 1 then 0 else canonicalDeltaFiniteValue F χ ψ hψ
@[simp] theorem localConstantFunction_apply_one (χ : ContinuousQuasiChar F) :
    localConstantFunction F χ 1 = 0
noncomputable abbrev localConstant : LocalConstantFunction F := localConstantFunction F  -- :140
```

Here `canonicalDeltaFiniteValue` is `private`. It evaluates `deltaFinite` on the canonical packages at a `Classical.choice` admissible `γ`.

**The value `0` at `ψ = 1` is only a totalization.** The source says so itself (file docstring and `:60`–`:64`). It is not a local constant, it is not a nonzero value, and no realization theorem covers it. Every theorem with mathematical content assumes `hψ : ψ ≠ 1`:

```lean
-- Delta/LocalConstantRealization.lean:149, :160, :144
theorem localConstant_eq_deltaFinite (χ : ContinuousQuasiChar F) (ψ : ContinuousAddChar F)
    (hψ : ψ ≠ 1)
    (γ : AdmissibleGamma F (canonicalLocalQuasiCharData F χ) (canonicalLocalAddCharData F ψ hψ)) :
    localConstant F χ ψ =
      deltaFinite (canonicalLocalQuasiCharData F χ) (canonicalLocalAddCharData F ψ hψ) γ
theorem localConstant_eq_deltaIntegral (μ : Measure (unitFiltration F 0)) [μ.IsHaarMeasure]
    (χ : ContinuousQuasiChar F) (ψ : ContinuousAddChar F) (hψ : ψ ≠ 1)
    (γ : IntegralAdmissibleGamma F (canonicalLocalQuasiCharData F χ)
      (canonicalLocalAddCharData F ψ hψ)) :
    localConstant F χ ψ =
      deltaIntegral μ (canonicalLocalQuasiCharData F χ) (canonicalLocalAddCharData F ψ hψ) γ
theorem localConstant_isDeltaFinite : IsDeltaFiniteLocalConstant (localConstant F)
-- Delta/ErrorTerm.lean:27
def IsDeltaFiniteLocalConstant {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] (Δ : LocalConstantFunction E) : Prop :=
  ∀ (χ : LocalQuasiCharData E) (ψ : LocalAddCharData E) (γ : AdmissibleGamma E χ ψ),
    Δ χ.character ψ.character = deltaFinite χ ψ γ
```

`IsDeltaFiniteLocalConstant` constrains `Δ` only at characters that carry exact-conductor data, and a trivial `ψ` has no exact additive conductor. In the First Main identity the additive arguments are `ψ_F ≠ 1` and `ψ_F ∘ Tr_{K/F}`.

The second is also nontrivial. Directly: `K/F` is Galois, hence separable, so its trace form is nondegenerate. The trace `Tr_{K/F} : K → F` is therefore a nonzero `F`-linear map to the one-dimensional `F`-space `F`, hence surjective. Any point where `ψ_F ≠ 1` thus lifts along the trace. That argument is mine, not a cited source theorem. In the source, each branch of `firstMainLemma_nonarchimedean` gives `ψ_F ∘ Tr` an exact conductor. The dispatcher splits on `ramificationIndex F K = 1` (`Dispatch.lean:44`):

- **Unramified.** `unramified_additiveConductor_compTrace` (`Ramification/UnramifiedCompatibility.lean:987`) needs only the field instances, `[ValuativeExtension F K]`, `[Module.Finite F K]` and `ramificationIndex F K = 1`. It states `IsAdditiveConductor K ψ.compTrace n ↔ IsAdditiveConductor F ψ n`. The private package `unramifiedAddCharData` (`Cases/Unramified.lean:52`) uses it to give `ψ_F ∘ Tr` the conductor `n(ψ_F)`. The dispatcher reaches it through `firstMain_unramified_dispatchReady` (`Dispatch.lean:52`; `Cases/Unramified.lean:1891`).
- **Ramified.** `additiveConductor_compTrace_cyclicPrime` (`Ramification/PullbackConductors.lean:169`) gives the conductor `[K:F]·n + ([K:F] − 1)(t + 1)`. It holds only under the section hypotheses included at `:159`–`:165`: `ht : PrimeCyclicExtension.IsLowerBreak F K t`, `hres : residueDegree F K = 1`, and an integral uniformizer `pi` of `K` with `hpi` and `hgen : Algebra.adjoin 𝒪_F {pi} = ⊤`. So it does not cover the unramified case. In the ramified branch the dispatcher builds `primeCyclicPreparation F K hunr` (`Dispatch.lean:55`; `Ramification/PrimeCyclicPreparation.lean:138`), which supplies these hypotheses:
  - `hres` comes from `totallyRamified_of_ramified` (`Ramification/PrimeDegreeDichotomy.lean:57`);
  - `t` and `ht` come from the canonical selector `lowerBreakIndex`/`lowerBreakIndex_isLowerBreak` (`Ramification/PrimeCyclicExtension.lean:316`, `:321`);
  - `pi`, `hpi` and `hgen` come from `monogenicUniformizer` (`LocalField/MonogenicUniformizer.lean:204`).

  The ramified case modules then apply the theorem to the prepared data, for example `Cases/TameQuadraticPreparation.lean:99` and `Cases/WildStablePreparation.lean:100`.

The zero branch therefore never occurs in the proved identity. **A project port must not transport `localConstant` at `ψ = 1`.** Our `UnitaryAdditiveCharacter` already includes `nontrivial`, which keeps that branch out of reach.

### 2.4 The First Main statement and theorem

```lean
-- Delta/FirstMainStatement.lean:32, :42, :56, :86, :104, :113, :121
def normQuasiChar (χ : ContinuousQuasiChar F) : ContinuousQuasiChar K :=
  χ.pullback (continuousNormUnits F K)               -- χ ∘ N_{K/F}
def tracePullbackAddChar (ψ : ContinuousAddChar F) : ContinuousAddChar K :=
  ψ.pullback (continuousTrace F K)                   -- ψ ∘ Tr_{K/F}
def NormCharacter := {μ : ContinuousQuasiChar F // normQuasiChar F K μ = 1}
def CyclicPrimeExtension (F K : Type*) [Field F] [Field K] [Algebra F K]
    [Module.Free F K] [Module.Finite F K] : Prop :=
  IsGalois F K ∧ IsCyclic Gal(K/F) ∧ (Module.finrank F K).Prime
def firstMainLeftSide (ΔF ΔK χF ψF) : ℂ := by
  letI := Fintype.ofFinite (NormCharacter F K)
  exact ΔK (normQuasiChar F K χF) (tracePullbackAddChar F K ψF) *
    ∏ μ : NormCharacter F K, ΔF μ.1 ψF
def firstMainRightSide (ΔF χF ψF) : ℂ := by
  letI := Fintype.ofFinite (NormCharacter F K)
  exact ∏ μ : NormCharacter F K, ΔF (μ.1 * χF) ψF
def FirstMainIdentity (ΔF ΔK χF ψF) : Prop :=
  firstMainLeftSide F K ΔF ΔK χF ψF = firstMainRightSide F K ΔF χF ψF

-- Main.lean:16
theorem firstMainLemma
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K] [Module.Free F K] [Module.Finite F K]
    (hcyclic : CyclicPrimeExtension F K) :
    letI : PrimeCyclicExtension F K := PrimeCyclicExtension.ofCyclicPrimeExtension F K hcyclic
    letI : Finite (NormCharacter F K) := primeCyclicNormCharacter_finite F K
    ∀ (chiF : ContinuousQuasiChar F) (psiF : ContinuousAddChar F),
      psiF ≠ 1 → FirstMainIdentity F K (localConstant F) (localConstant K) chiF psiF
```

`continuousTrace` and `continuousNormUnits` (`LocalField/Extension.lean:374`, `:392`) are continuous for the module topology. The global instance `localFieldExtensionIsModuleTopology : IsModuleTopology F K` (`:471`) supplies that topology from the `ValuativeExtension`.

The body of `firstMainLemma` applies `firstMainLemma_nonarchimedean` (`Dispatch.lean:24`). That theorem is stated for **any** `DeltaF`, `DeltaK` with `IsDeltaFiniteLocalConstant`, and for `LocalQuasiCharData`/`LocalAddCharData` packages. It splits into the unramified, tame quadratic, tame odd, wild quadratic and wild odd cases.

**Hypotheses and quantifiers:**

- `S(K/F)` is defined intrinsically as the characters of `Fˣ` trivial on norms. No reciprocity map occurs.
- `χ_F` ranges over **all** continuous quasi-characters, not only unitary ones.
- `ψ_F` ranges over continuous `ℂˣ`-valued additive characters with `ψ_F ≠ 1`.
- Galois-ness, cyclicity and prime degree are explicit hypotheses. No characteristic or unitarity hypothesis is made, so equal characteristic is covered.

### 2.5 Mathematical meaning

Let `m = a(χ)`, `n = n(ψ)`, `ord γ = m + n`, and `G = Σ_{u ∈ U⁰/U^m} ψ(u/γ) χ(u)⁻¹`. Then

```
Δ(χ, ψ) = χ(γ) · G / |G|.
```

This agrees with the manuscript's `eq:def-delta` (`references/epsilon_FML.tex` l.384) and with Tate, *Number theoretic background* (1979), (3.6.3) on printed p. 17:

```
ε_L(χ, ψ) = χ(c) ∫_{𝒪ˣ} χ⁻¹(u) ψ(u/c) du / |∫ ...|,   ord c = a(χ) + n(ψ).
```

Both sides use `ψ(u/c)` with a plus sign, so no `χ(-1)` correction is needed. Tate's (3.6.1) gives `ε_L(V, ψ) = ε_D(V ⊗ ω_{1/2}, ψ, dx_ψ)` with the self-dual measure `dx_ψ`.

The manuscript defines `ε(s, χ, ψ) := Δ(|·|^{s-1/2} χ, ψ) = q^{-(m+n)(s-1/2)} Δ(χ, ψ)` (l.107–120), and states `thm:first-main` at l.140.

### 2.6 Project definitions compared

From `Langlands/LocalFactor/Abelian/Padic.lean`, with `F : PadicField.{u} p` and `T : F.TopologicalData`:

- `MultiplicativeCharacter` is local notation for `HarmonicAnalysis.Quasicharacter F.Carrier`. That type is `abbrev ... := ContinuousMonoidHom Fˣ ℂˣ` (`HarmonicAnalysis/Basic.lean:31`), the **same type** as FML's `ContinuousQuasiChar` once both use `T.topology`.
- `AdditiveCharacter` is `HarmonicAnalysis.UnitaryAdditiveCharacter`, a structure extending `AddChar F Circle` with fields `continuous_toFun` and `nontrivial` (`:20`).
- `epsilonAt T π χ ψ μ a n s` (`:183`) has two branches:
  - for `a = 0`: `χ(π)^n · q^{n(1-s)} · μ(𝒪)`;
  - otherwise: the integral over the shell `ord x = -(n+a)` of `gaussIntegrand T χ ψ s x = χ⁻¹(x) · |x|^{-s} · ψ(x)`.

  This is Tate's fixed-measure `ε(χω_s, ψ, μ)`, with a plus-sign character.
- `epsilon T χ ψ μ s` (`:202`) is `epsilonAt` at `uniformizerUnit T` and the project's chosen conductors:
  - `T.multiplicativeConductor χ` (`HarmonicAnalysis/Conductor.lean:270`) is the least `n` with `χ` trivial on `T.principalUnits n`, using `Nat.find`;
  - `T.additiveConductor ψ` (`:150`) is the largest `n` with `ψ` trivial on `π^{-n}𝒪`, chosen from proved existence.
- `deligneConstant = epsilon · · · 0` and `centeredConstant = epsilon · · · (1/2)`. `deligneConstant_eq_abelianEpsilonExpression` (`:379`) is proved.
- `SelfDualHaar T ψ` (`:406`) is the subtype of `LocalHaar` satisfying `HarmonicAnalysis.IsSelfDual ψ μ`. `langlandsConstantAtSelfDual T χ ψ μ := centeredConstant T χ ψ μ.val.measure` (`:422`). `langlandsEpsilonAtSelfDual` (`:430`) evaluates `epsilon` at `s`, not at `s + 1/2`.

The conductors agree mathematically. FML's `lattice F (-n)` is `{ord ≥ -n}`, which equals `T.additiveLattice n = π^{-n}𝒪`. FML's `unitFiltration` matches `T.principalUnits` level by level: level 0 is the units, and level `k ≥ 1` is `1 + 𝔭^k`. Both normalize the valuation with the same map `(valuation).map valueGroupWithZeroIsoInt`; the project's `discreteValuation` is at `LocalField/Normalization/Definitions.lean:87`. No Lean lemma identifies the two exponents yet; that is units 2 and 3 in §6.

### 2.7 Exact relation to the project epsilon (derived here)

The following derivation is my own hand computation from the definitions above, checked against Tate (3.6.3). It is not a Lean result. Fix:

- `χ : Quasicharacter`;
- `ψ : UnitaryAdditiveCharacter`, with FML image `ψ' = Circle.toUnits ∘ ψ`;
- any additive Haar measure `μ`;
- `a = T.multiplicativeConductor χ`, `n = T.additiveConductor ψ`, `c` with `ord c = a + n`.

Substituting `x = u/c` in the shell integral gives, for every `s : ℂ`,

```
epsilon T χ ψ μ s = χ(c) · |c|^{s-1} · μ(U^a) · G,     G = finiteGaussSum at γ = c   (a ≥ 1)
epsilon T χ ψ μ s = χ(π)^n · q^{n(1-s)} · μ(𝒪),         G = 1                         (a = 0)
```

Using `μ(U^a) = q^{-a} μ(𝒪)` for `a ≥ 1`, both cases combine into

```
epsilon T χ ψ μ s = r · Δ(χ · ω_{s-1/2}, ψ'),     r = r(χ, ψ, μ) = q^{(n-a)/2} · μ(𝒪) · |G| > 0,
```

where `ω_t = |·|^t`. This is unramified, so it changes neither `a` nor `G`. In particular `centeredConstant T χ ψ μ = r · Δ(χ, ψ')`.

When `r = 1`:

- **Hence** `langlandsConstantAtSelfDual T χ ψ μ = Δ(χ, ψ')` exactly when `r = 1`. This holds if (i) `μ(𝒪) = q^{-n/2}` and (ii) `|G| = q^{a/2}`.
- **Condition (i) for a `SelfDualHaar`** is the second clause of `PadicFourierNormalizationStatement` (`LocalFactor/Harmonic/Statement.lean:113`). That statement is unproved. Its `dual` predicate, built from Mathlib's `Fourier.fourierIntegral χ⁻¹` on locally constant compactly supported functions, is also not syntactically `HarmonicAnalysis.IsSelfDual`, so a bridge lemma is needed as well.
- **Condition (ii)** is not in FML. It follows from the unproved unitarity clause of `PadicAbelianLocalAnalysisStatement`: for unitary `χ` and `μ(𝒪) = q^{-n/2}`, `‖ε(1/2)‖ = 1`. Apply it to the unitary part of `χ`, which has the same `G`. It is also the classical Gauss-sum modulus, which could be proved directly.
- **Degree-zero ratio form.** For any Haar `μ`, `epsilon T χ ψ μ (1/2) / epsilon T 1 ψ μ (1/2) = q^{-a/2} |G| · Δ(χ, ψ')`. Under (ii) alone this is `Δ(χ, ψ')`; no self-dual measure is needed.

**Additive-character sign:** FML `ψ(u/γ)`, Tate (3.6.3) and the project's `gaussIntegrand` all use `ψ` itself, not `ψ⁻¹`.

**Spectral twisting:**

- FML: Langlands' `ε(s) = Δ(χ|·|^{s-1/2})`.
- Project: Deligne's `epsilon(s) = ε_D(χω_s)`.
- The displayed formula relates the two for every `s`. Since `epsilonAt` with character `χω_{1/2}` at `s = 0` equals `epsilonAt` with `χ` at `s = 1/2` (same conductors), the Deligne-convention form `ε_D(χω_{1/2}, ψ, μ)` agrees with `centeredConstant`.

### 2.8 Trace pullback, reciprocity and Frobenius conventions

- **Formal content.** `Δ(1, ψ) = 1` and all `Δ` values are nonzero (`IsDeltaFiniteLocalConstant.apply_ne_zero`). The First Main identity is therefore
  `Δ_K(χ_K, ψ_K) / Δ_K(1_K, ψ_K) = ∏_{μ ∈ S} Δ_F(μχ, ψ) / ∏_{μ ∈ S} Δ_F(μ, ψ)`,
  with `χ_K = χ ∘ N` and `ψ_K = ψ ∘ Tr`.
- **Weil-side reading.** Local reciprocity identifies `S(K/F)` with the characters of `Gal(K/F)`, matches `χ ∘ N` with restriction to `W_K`, and gives `Ind(χ_K) = ⊕_{μ ∈ S} μχ`. Under this identification the identity is degree-zero inductivity for `x = [χ_K] − [1_K]`, twisted by `ω_{1/2}` (note `ω_{1/2,F} ∘ N = ω_{1/2,K}`). This is `NonabelianSystem.InductionRelation` (`LocalFactor/NonabelianSystem.lean:42`), whose arbitrary Haar measures cancel in degree zero, combined with `RankOneRelation` (`:51`), which uses Deligne's unshifted `abelianEpsilonExpression`.
- **Frobenius convention.** The project's convention (geometric Frobenius ↔ uniformizer, `ν = q⁻¹`) affects only which Weil character corresponds to a given `χ`. Both conventions have the same norm kernel and both are compatible with norm/restriction, so the FML identity is unchanged by the arithmetic/geometric choice. This step uses reciprocity, which neither FML nor this audit proves.

### 2.9 Universe and field/topology compatibility

- **Universes.** The FML definitions are universe-polymorphic (`Type*`). However, `firstMainLemma`, `firstMainLemma_nonarchimedean` and the case modules take `(F K : Type)`, universe 0 (261 such binders in the scan). The project's `PadicField.{u} p` has `Carrier : Type u`. Direct application therefore needs `u = 0`; otherwise a universe-lifting transport is required.
- **Instances.** `F.TopologicalData` packages `topology`, `valuativeRel`, `ValuativeExtension (Padic p)`, `IsModuleTopology (Padic p)` and `localField : IsNonarchimedeanLocalField` (`LocalField/Definitions.lean:65`). These are exactly the instances FML needs on each field, once installed with `letI`.
- **Extensions.** For `K/F`, FML also needs `[Algebra F K] [ValuativeExtension F K]` and a topology on `K` with `IsNonarchimedeanLocalField K`. Its global instance then supplies `IsModuleTopology F K`, which must agree with the project's topology on `K`. Both are the module topology over `Padic p`, but a transport lemma is required.
- **Characteristic.** The project's fields have characteristic 0. FML also covers equal characteristic, which is harmless.
- **Measures.** FML's Haar measure lives on `unitFiltration F 0` via a global *data* instance `MeasurableSpace := borel`. The project uses local `letI := borel F.Carrier` on the field. The two do not interact unless FML's instance is imported into the same scope.

## 3. Licenses, notices and attribution

- **License.** FML's `LICENSE` is the stock Apache License 2.0 text, SHA256 `c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4`, 201 lines, with the appendix placeholder `Copyright [yyyy] [name of copyright owner]` unfilled. epsilon_SML's `LICENSE` is byte-identical.
- **Notices and headers.** There is no NOTICE file. None of the 141 `.lean` files has a copyright or SPDX header.
- **Authorship.** The README and `CITATION.cff` (version 1.0.0, `license: Apache-2.0`) name the sole author, Fukuhiro Ueda, and ask users to cite the software.
- **Obligations for any port.** Keep the Apache-2.0 license text. Credit Ueda in the module docstring and the paired Markdown, citing the commit. State any modifications.

## 4. Kernel and axiom evidence

**Kernel evidence obtained: none.**

- I did not build FML and did not run `#print axioms` or `leanchecker` on any FML declaration. Its pins (Lean 4.32.2, Mathlib `905b9581`) differ from the approved environment, and external builds are not permitted.
- The `firstMainLemma` theorem, its finite/integral realizations and its nonvanishing results are therefore **not** established for this project.

**Textual checks (mine):** a scan of all 141 `.lean` files found:

- 0 hits for `sorry`, `admit`, `axiom` declarations, `native_decide`, `implemented_by`, `unsafe`, `@[extern]`, `sorryAx` and `ofReduceBool`;
- one `opaque`, which is in a doc comment (`Parameters/PhaseReduction/Odd/AssemblyInputs.lean:966`);
- `set_option maxHeartbeats` values up to 16,000,000, three uses of `backward.isDefEq.respectTransparency false`, and one `hygiene false` in a tactic macro.

The snapshot's `STATIC-SCAN.json` likewise lists no lexical hits for the 140-module Main closure. Textual scans cannot establish transitive axioms.

**Author reports:** the README gives build instructions ending in `lake env leanchecker --fresh LanglandsFirstMainLemma.Main`. This is an instruction; no output or CI record is published.

**Our probe (name level only):** the private draft `.private/drafts/fmlapi` ran 236 `#check`s of the Mathlib names used by the 20-module definition closure in our environment. The result was recorded as diagnostics `8c0ee64d-3d4b-4108-9d8d-010ee9b82559`, `6c101b46-3836-4ef5-82d8-8bd9d2b312bd` and `0aeb063e-3a1c-4a88-89ca-a1a33d49245c` (§5). This checks name resolution, not FML's proofs.

## 5. Current Mathlib/Library overlap and version/API problems

**Mathlib `5ed29652` already has:**

- `IsNonarchimedeanLocalField` (`NumberTheory/LocalField/Basic.lean:45`), `ValuativeRel`, `ValuativeExtension`, `IsModuleTopology`, `AddChar`, `ContinuousMonoidHom`, `Circle.toUnits` and Haar measure uniqueness;
- Gauss sums only over finite rings (`NumberTheory/GaussSum.lean`, Dirichlet and quadratic variants).

It has no local Gauss sums, local constants or epsilon factors.

**The Library already has:**

- the character type `Quasicharacter` (identical to FML's) and conductor constructions with existence and uniqueness (`HarmonicAnalysis/Conductor.lean`);
- the rank-one epsilon expressions, self-dual subtypes and statement targets of §2.6–2.7;
- the nonabelian system predicates `InductionRelation`/`RankOneRelation`.

The Library has no counterpart to FML's `finiteGaussSum`, `deltaFinite`, the norm-character group `NormCharacter`/`S(K/F)` of a field extension, or `CyclicPrimeExtension`. Name search found only the unrelated Weil-group `localNormCharacter`.

**Version/API findings from the probe:**

- Of 14 errors in `8c0ee64d`, 13 are false positives of the probe: module-path fragments such as `Topology.Algebra.Module.Compact` read as names, `Complex.Circle`, `Ideal.Norm.AbsNorm`, and FML's own `ContinuousAddChar.*` names.
- The 14th, `Subgroup.genLTOne_unique`, resolves in our Mathlib as `LinearOrderedCommGroup.Subgroup.genLTOne_unique` (`6c101b46`), so the open namespace must be checked during any port.
- Two deprecations remain: `Ideal.inertiaDeg'_eq_inertiaDeg` and `Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing`, used in `LocalField/Extension.lean` and `LocalField/Valuation.lean`.
- `0aeb063e` confirms that `set_option backward.isDefEq.respectTransparency false` is accepted by Lean 4.34, and that `IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt` and `Circle.toUnits` resolve.

No definite API break was found, but these are name checks only. Elaboration, `simp` set and heartbeat differences across two Lean minor versions remain untested.

**Porting hazards:**

- `Prelude.lean` imports all of Mathlib.
- Global instances in the closure include the data instance `unitFiltrationZeroMeasurableSpace` and the `Prop` instance `localFieldExtensionIsModuleTopology`.
- The private declarations `canonicalDeltaFiniteValue` and `normalizedMultiplicativeValuation` cannot be named from outside.
- Short generic names in the open namespace (`ord`, `lattice`, `trace`, `phase`, `unitFiltration`) would clash if opened alongside project names.
- Heartbeat limits are large.

## 6. Verdict and smallest next units

**Verdict: adapt.** FML is a careful, readable, Apache-licensed source whose `Δ` is exactly Tate's `ε_L` (§2.5), with the trivial-`ψ` value isolated. It remains unsuitable for import:

- it is pinned to Lean 4.32.2 and a different Mathlib;
- it has no kernel evidence here;
- it imports all of Mathlib and uses universe-0 theorems;
- the proof closure is 138k lines;
- its relation to our normalization is `r · Δ` rather than equality, until (i) and (ii) of §2.7 are proved.

A rejection is not warranted either: the definitions agree with ours up to the explicit positive factor, and `firstMainLemma_nonarchimedean` is interface-based (`IsDeltaFiniteLocalConstant`), which makes a staged port practical. Each unit below must be a separately authorized task with published statement targets, normal validation and independent semantic review. None alters an existing target.

All ports are at universe `u`, with targeted Mathlib imports in place of `Prelude`'s `import Mathlib`. Units 1–3 replace FML's existence layer with the Library's proved conductors.

1. **Definitions: valuation layer, conductor predicates and character transport.**
   - **Port** the 7-module closure of `Basic.CharacterConductors`: `Prelude`, `Basic.{Phase, CharacterTypes, CharacterConductors}` and `LocalField.{Valuation, Lattices, UnitFiltration}` (2,699 lines; its only external import is `Mathlib`).
   - **What this provides:** `ord` (`LocalField/Valuation.lean:89`), `lattice` (`LocalField/Lattices.lean:74`), `unitFiltration` (`LocalField/UnitFiltration.lean:89`), `phase`, `ContinuousAddChar`, and the predicates and packages of §2.1. These are `AddCharTrivialOnLattice`, `QuasiCharTrivialOnUnitFiltration`, `IsAdditiveConductor`, `IsMultiplicativeConductor`, `LocalAddCharData` and `LocalQuasiCharData` (`Basic/CharacterConductors.lean:30`, `:35`, `:94`, `:100`, `:394`, `:402`).
   - **Add the transport:** `UnitaryAdditiveCharacter → ContinuousAddChar` via `Circle.toUnits`, which is injective, so `nontrivial` gives `ψ' ≠ 1`. `Quasicharacter` needs no transport. A map back to `UnitaryAdditiveCharacter` would need a modulus-one lemma such as `localAddChar_norm_eq_one`, but no unit below uses one.
   - **Do not port `Basic.CharacterConductorExistence`.** Its existence theorems are `exists_isMultiplicativeConductor` (`:220`) and `exists_isAdditiveConductor` (`:269`). Its canonical packages are `canonicalLocalQuasiCharData` and `canonicalLocalAddCharData` (`:397`, `:442`). Porting them would also bring in `Basic.StandardCharacterBridge` and `LocalField.{ResidueField, Extension}` (an 11-module closure of 4,743 lines). The Library already proves the same existence and uniqueness, so units 2–3 use that instead.
2. **Statements: agreement with the Library's conductors.** Prerequisites: unit 1 and `Langlands/HarmonicAnalysis/Conductor.lean`. Take `F : PadicField.{u} p` and `T : F.TopologicalData`, with FML's instances installed from `T`. The statements are:
   - `(lattice F.Carrier (-n) : Set F.Carrier) = (T.additiveLattice n : Set F.Carrier)` for all `n : ℤ` (`Conductor.lean:50`);
   - `unitFiltration F.Carrier k = T.principalUnits k` for all `k : ℕ` (`:175`);
   - `IsAdditiveConductor F.Carrier ψ' n ↔ n = T.additiveConductor ψ` (`:150`);
   - `IsMultiplicativeConductor F.Carrier χ m ↔ m = T.multiplicativeConductor χ` (`:270`).
3. **Proofs, then canonical packages.** Prerequisite: unit 2.
   - **Lattice and filtration agreement.** Prove both from the fact that FML's `ord` and `T.discreteValuation` (`LocalField/Normalization/Definitions.lean:87`) use the same map `(valuation).map valueGroupWithZeroIsoInt`.
   - **Conductor agreement.** Then prove both conductor equivalences from `additiveConductor_spec`/`additiveTrivialAt_iff_le_conductor` (`Conductor.lean:153`, `:158`) and `multiplicativeConductor_spec`/`multiplicativeTrivialAt_iff_conductor_le` (`:274`, `:279`).
   - **Packages.** Only after these proofs, define `T.localQuasiCharData χ := ⟨χ, T.multiplicativeConductor χ, _⟩` and `T.localAddCharData ψ := ⟨ψ', T.additiveConductor ψ, _⟩`. Their `isConductor` fields are the proved equivalences. These packages replace FML's `canonicalLocal*Data`, and they add no choice beyond the Library's.
4. **Definitions: finite local constant.** Prerequisite: unit 3.
   - **Port** `Delta.FiniteDefinition` and `Delta.Nonvanishing`. Beyond unit 1, they add `LocalField.{ResidueField, FiniteQuotients}` and `Mathlib.RingTheory.Ideal.Norm.AbsNorm`, for an 11-module closure of 5,346 lines.
   - **What this provides:** `AdmissibleGamma` with `exists_admissible` (`:49`), `finiteGaussSum` and `deltaFinite`, together with the proof ports `finiteGaussSum_ne_zero` (`:998`), `deltaFinite_gamma_independent` (`:1063`) and `deltaFinite_ne_zero` (`Delta/Nonvanishing.lean:9`).
   - **Then define** the project-side `Δ(χ, ψ')` as `deltaFinite (T.localQuasiCharData χ) (T.localAddCharData ψ) γ`, at any admissible `γ`.
   - **Leave out** `deltaIntegral` and its global measurable-space instance unless they are needed.
5. **Statement (provable without unproved inputs).** Prerequisite: unit 4. For every Haar `μ` and every `s`, `epsilon T χ ψ μ s = r · Δ(χ·ω_{s-1/2}, ψ')` with `r = q^{(n-a)/2} μ(𝒪) |G| > 0`.
6. **Statements.** Prerequisite: unit 4.
   - the Gauss-sum modulus `|G| = q^{a/2}`;
   - consequently `langlandsConstantAtSelfDual T χ ψ μ = Δ(χ, ψ')` for every `μ : SelfDualHaar T ψ`, given a lemma that `IsSelfDual` implies `μ(𝒪) = q^{-n/2}`.

   These would discharge the parts of `PadicFourierNormalizationStatement`/`PadicAbelianLocalAnalysisStatement` used here only after those owners' targets are proved; this unit must not assume them.
7. **Statement: the First Main identity in project terms.** Prerequisite: unit 4.
   - **Port** the rest of the statement layer: `Basic.CharacteristicConvention`, `LocalField.Extension` (`continuousTrace`, `continuousNormUnits`, and the `IsModuleTopology` instance, which needs the transport lemma of §2.9) and `Delta.FirstMainStatement`, plus `Delta.ErrorTerm` for `IsDeltaFiniteLocalConstant`.
   - **State** the identity for `K/F` cyclic of prime degree inside the project's extension framework, with `[Finite (NormCharacter F K)]` as a separate proved instance.
   - **Then state** its equivalence, under reciprocity, with `InductionRelation` at `([χ_K] − [1_K]) · ω_{1/2}`.

   The proof port of the case analysis (≈130k lines) comes last, and is optional if a different route to the nonabelian system is chosen. That port needs both trace-conductor theorems of §2.3 and `primeCyclicPreparation`.

**Next boundary: epsilon_SML.** Only the boundary was read, at [`5b55d3f6e7c053f733afb1be523e532d212d94d0`](https://github.com/fukubillueda-web/epsilon_SML/tree/5b55d3f6e7c053f733afb1be523e532d212d94d0): 211 `.lean` files, 118,917 lines, Lean 4.32.2, Mathlib `905b9581`, FML pinned at `b91ad939` in both `lakefile.toml` and the manifest. Its exported `LanglandsSecondMainLemma.secondMainLemma` (`Main.lean:37`) has `(F K : Type)`, the same field instances as FML, and the following inputs and conclusion:

- **`PrimeSquareExtension F K ℓ`** (`Basic/SecondMainStatement.lean:47`): a `Prop` structure with `ℓ.Prime`, `IsGalois F K`, and `Nonempty (Gal(K/F) ≃* Multiplicative (ZMod ℓ) × Multiplicative (ZMod ℓ))`.
- **`PrimitiveCompatibleFamily F K extension`** (`:81`), which is data:
  - `topCharacter : ContinuousQuasiChar K`;
  - Galois invariance via `conjugateQuasiChar` (`χ^σ(x) = χ(σ⁻¹ x)`);
  - `not_normPullback`;
  - `inducingCharacter` on each degree-`ℓ` intermediate field `L`, with SML-defined restricted valuation and topology;
  - `compatible`: `θ_L ∘ N_{K/L} = Θ`.
- **`ψF ≠ 1`.**
- **Conclusion `SecondMainIdentity`** (`:169`): `inductionExpression` (`:128`), `= localConstant L θ_L (ψF ∘ Tr_{L/F}) · ∏_{ν : NormCharacter F L} localConstant F ν ψF`, is independent of `L`.

SML imports FML's `Main` and about 40 internal FML modules (`Ramification.*`, `Lamprecht.*`, `FiniteField.*`, `Parameters.*`, `Cases.*`). Its *statement* closure contains `Ramification.PrimeCyclicExtension` and `Ramification.NormCharacters.primeCyclicNormCharacter_finite`. An SML adaptation therefore depends on units 1–4 and 7 above, and on a port or reproof of the finiteness of `NormCharacter F L`. Its normalization questions reduce to those settled here, since it uses only FML's `localConstant` at nontrivial `ψ`. Auditing SML's proofs is a separate unit.

## Sources

- **Ueda, epsilon_FML** at `0b4159be`: snapshot `external-lean-reuse-snapshots-2026-10-21` (folder `fukubillueda-web--epsilon_FML`), plus supplement `ueda-epsilon-fml-0b4159be-supplement` (`CITATION.cff`, manuscript `references/epsilon_FML.tex`, GitHub compare/tree records).
- **Ueda, epsilon_SML** at `5b55d3f6`: same snapshot, folder `fukubillueda-web--epsilon_SML`.
- **J. Tate**, *Number theoretic background*, Proc. Sympos. Pure Math. 33 (1979), part 2, §3.6, (3.6.1) and (3.6.3): registered as `tate-1979-number-theoretic-background`.
- **Library** commit `0686b4fa`: `Langlands/LocalFactor/Abelian/Padic.lean`, `PadicAbelianStatement.lean`, `Harmonic/Statement.lean`, `NonabelianSystem.lean`, `HarmonicAnalysis/{Basic,Conductor}.lean`, `LocalField/Definitions.lean`.
