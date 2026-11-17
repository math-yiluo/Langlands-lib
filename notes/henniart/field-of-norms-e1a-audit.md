# Field-of-norms formalization: audit for the close-fields statement E1a

Author: Worker 5168 (Task 7341).

## Purpose

The close-fields statement E1a is the first half of input (I2) of the numerical route
to Henniart (1988), Théorème 1.2. In group form it says the following. Let `K` be a
p-adic field with absolute ramification index `e`, and let `X = k((t))` have the same
residue field. Then `G_K/G_K^e ≅ G_X/G_X^e` as filtered groups. The operator plan note
`operator-external-inputs-plan-2026-11-16` (Remark 4.1, `rem:fon`) derives E1a from
Wintenberger's field of norms. The note applies it to the Kummer tower
`L = ⋃ K(ϖ^{1/p^n})`. It names an external Lean formalization of the field of norms.

On 17 November 2026 the operator decided that this formalization is not imported in the
current instance, because the Lean environment takes no packages. The Library instead
states, in its own vocabulary, the one statement that crosses the boundary. It is a
named premise. E1a is then proved from that premise inside the Library.

This note records the audit of the external formalization:

- the checked commit and its pins;
- its root modules;
- the exact theorems the premise combines, with their hypotheses;
- what the formalization does not contain for this application;
- how its statements correspond to the Library premise.

Nothing in this note is an accepted Lean result.

## Checked version

| Item | Value |
| --- | --- |
| Repository | `https://github.com/YijunYuan/FontaineWintenberger` (author Yijun Yuan) |
| Commit | `e835d58871d8d564901c0f13b685034cd202659e`, committed 28 October 2026 |
| Licence | Apache License 2.0 (`LICENSE`) |
| Toolchain | `leanprover/lean4:v4.35.0` (`lean-toolchain`) |
| Mathlib | `1e75e9dd53d483fa01eff9ac7d4ea0472ce9d1fa` (`lake-manifest.json`) |
| Size | 192 Lean files (the root `FontaineWintenberger.lean` and 191 under `FontaineWintenberger/`), 50,734 lines |
| Module system | Every file is a `module` with `public import`s |

For comparison, the Library's environment is pinned to `leanprover/lean4:v4.34.0` and
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`. So the formalization cannot be built
against the Library's pin without a port, and it was not compiled for this audit.

A text scan of all 192 files found:

- no `sorry` and no `admit` tactic (the word "admit" occurs three times, all in docstrings);
- no `axiom` declaration.

This is a text scan only. The axioms of the cited theorems have not been checked with
`#print axioms`. That check needs a build on the formalization's own pin.

An import closure was also computed. It follows the `import` lines inside the
repository, starting from the files that contain the theorems below.

| Starting files | Files in closure | Lines |
| --- | --- | --- |
| `FieldOfNorms/Galois/AbsoluteGroup.lean`, `FieldOfNorms/Galois/Filtration.lean` | 147 | 42,512 |
| the same and `APF/Tower/Criterion.lean` | 154 | 43,431 |
| the whole library (root module) | 192 | 50,734 |

## Root modules

The root `FontaineWintenberger.lean` imports five subtrees: `APF`, `FieldOfNorms`,
`LocalField`, `Mathlib` and `Ramification`. Its docstring lists eight main items, all for a
complete discretely valued field `K` with perfect residue field
(`IsPerfectResidueLocalField K`) and a separable extension `L/K`:

1. arithmetically profinite extensions (Wintenberger 1.2.1);
2. the field of norms `FieldOfNorms K L` (2.1.1, 2.1.3);
3. Theorem 2.1.3: completeness, discrete valuation ring and the residue isomorphism;
4. Theorem 3.2.2 (ii) and Corollary 3.2.3: `FieldOfNorms.absoluteGaloisEquiv`;
5. Remark 3.2.4: the relative versions for any separable closure;
6. the elementary tower of §1.4.1;
7. Remark 1.4.2: the APF criterion for elementary towers;
8. Corollary 3.3.6: `RelFieldOfNorms.map_normUpperRamificationGroup`.

The field-of-norms statements assume that `L/K` is infinite and arithmetically
profinite (APF).

## Theorems used by the field-of-norms route, with hypotheses

All names are in the namespace `FontaineWintenberger`. Paths are relative to
`FontaineWintenberger/`. Line numbers refer to the checked commit.

Most of the statements share one set of hypotheses, called the common hypotheses below:

- `K` is a `NontriviallyNormedField` with `IsPerfectResidueLocalField K`. This class
  (`LocalField/Basic.lean`, line 73) extends `IsCompleteDiscreteValuedField K` and
  `PerfectField 𝓀[K]`, and requires the residue characteristic to be prime.
- `L` is a field with `[Algebra K L] [Algebra.IsSeparable K L]`.
- `L/K` is arithmetically profinite (`[IsAPF K L]`) and infinite
  (`[Fact (¬ Module.Finite K L)]`).

| Declaration | Location | Statement | Hypotheses |
| --- | --- | --- | --- |
| `IsAPF K L` | `APF/Defs.lean`, line 210 | Wintenberger 1.2.1: every `K`-embedding of `L` into `SeparableClosure K` has APF image | `K` a complete discretely valued `NontriviallyNormedField`, `L/K` separable |
| `apfPsi K L u` | `APF/Herbrand.lean`, line 78 | Herbrand function `ψ_{L/K}` (Wintenberger 1.2.1); the definition itself makes no APF assumption | the same |
| `FieldOfNorms.residueEquiv` | `FieldOfNorms/Structure/ResidueEmbedding.lean`, line 553 | Theorem 2.1.3: the residue field of `L` is that of `X_K(L)` | common hypotheses |
| `FieldOfNorms.laurentEquiv` | `FieldOfNorms/Structure/Laurent.lean`, line 93 | `LaurentSeries κL ≃+* FieldOfNorms K L` for a normalized uniformizer `u` of `X_K(L)`, where `κL` is the residue field of the integral closure of `𝒪[K]` in `L`; `laurentEquiv_valuation` (line 159) gives compatibility with valuations | common hypotheses and `hu : valuation u = exp (-1)` |
| `RelFieldOfNorms.absoluteGaloisEquiv` | `FieldOfNorms/Galois/AbsoluteGroup.lean`, line 176 | `(Ω ≃ₐ[L] Ω) ≃ₜ* (SeparableClosure X ≃ₐ[X] SeparableClosure X)` with `X = FieldOfNorms K L` | common hypotheses; `Ω` with `[IsSepClosure K Ω]` and a tower `K → L → Ω` (lines 154-160) |
| `FieldOfNorms.absoluteGaloisEquiv` | the same file, line 225 | Corollary 3.2.3, the case `Ω = SeparableClosure L` | common hypotheses |
| `upperRamificationGroupInfinite K Ω u` | `Ramification/Infinite/Basic.lean`, line 50 | the intersection, over finite Galois `E ⊂ Ω`, of the preimages of the upper groups of `E ≃ₐ[K] E` acting on `spectralIntegerRing K E` | `K` complete discretely valued, `Ω` a `K`-algebra |
| `RelFieldOfNorms.upperRamificationGroup K L Ω u` | `FieldOfNorms/Galois/UpperLimit.lean`, line 38 | the intersection, over finite Galois `N/L` inside `Ω`, of the preimages of the upper groups of the norm-field extension `X_K(N)/X_K(L)` | common hypotheses |
| `RelFieldOfNorms.normUpperRamificationGroup K L M u` | `FieldOfNorms/Galois/Filtration.lean`, line 42 | the image of the previous group under `RelFieldOfNorms.autEquiv` (`FieldOfNorms/Relative/Hom.lean`, line 402) | common hypotheses |
| `RelFieldOfNorms.map_normUpperRamificationGroup` | `FieldOfNorms/Galois/Filtration.lean`, line 112 | Corollary 3.3.6: for `-1 ≤ u`, the image of `normUpperRamificationGroup K L M (apfPsi K L u)` under `normGaloisEmbedding K L M` is `upperRamificationGroupInfinite K M u ⊓ (normGaloisEmbedding K L M).range` | common hypotheses; `M` a field with a tower `K → L → M`, `M/L` separable and `[IsGalois K M]` (lines 105-108) |
| `IsElementaryStep K E F hEF i` | `APF/Tower/Criterion.lean`, line 47 | the step `F/E` between finite subfields of `SeparableClosure K` is elementary of level `i` (`IsElementary`, `APF/Elementary/Basic.lean`, line 33), for the spectral norm on `E` | `K` a complete discretely valued `NontriviallyNormedField` (line 38) |
| `apfFiniteStage_iSup_eq_of_isElementaryStep` | the same file, line 163 | in an elementary tower with APF union, the stages are the fixed fields of the union's upper products between consecutive transformed levels | `K` as in the previous row and, in addition, `[PerfectField 𝓀[K]]` (the section variable at line 39, used through the base-change and ramification-index arguments); `E` monotone, levels `i` strictly increasing, every step elementary, `G_K^u ≤ G_{E 0}` for `u > 0` |
| `apfPhi_eq_sum_of_isElementaryStep` | the same file, line 214 | Remark 1.4.2: `φ_{E_n/K}(i_n) = i_0/e(E_0) + Σ_{k<n} (i_{k+1} - i_k)/e(E_{k+1})` | the same as the previous row, including `[PerfectField 𝓀[K]]` |
| `isAPF_iSup_iff_tendsto_of_elementary_tower` | the same file, line 241 | Remark 1.4.2: the union is APF iff `φ_{E_n/K}(i_n) → ∞` | `K` with `IsPerfectResidueLocalField` (line 236); `E` strictly monotone, `i` strictly increasing, every step elementary, the ramification index of `E 0` prime to the residue characteristic |

In the Library's setting the base `K` is a p-adic field. The Library takes `Ω` to be
`AlgebraicClosure F.Carrier`, which is a separable closure because the characteristic is
`0`. `RelFieldOfNorms.absoluteGaloisEquiv` accepts any `Ω` with `IsSepClosure K Ω`, so
the Library's closure can be used as it is. The base field must still be given that
library's `NontriviallyNormedField` and `IsPerfectResidueLocalField` structures. These
must then be compared with the structures the Library's p-adic layer uses.

## What the formalization does not contain for this application

1. **The Kummer step is not specialized, and not shown to be elementary.** Wintenberger's
   criterion (`isAPF_iSup_iff_tendsto_of_elementary_tower`) needs `IsElementaryStep` for
   `K_{n+1}/K_n`, `K_n = K(ϖ^{1/p^n})`, at level `p^{n+1} e/(p-1)`. The general theory of
   a step of prime degree is in the formalization, and it does not assume normality.
   `APF/Elementary/PrimeDegree.lean` has the section hypotheses: `K` a complete discretely
   valued `NontriviallyNormedField` with `[PerfectField 𝓀[K]]` (lines 338-339 and
   448-449), and `L` a field with `[Algebra K L] [FiniteDimensional K L]
   [Algebra.IsSeparable K L]` (lines 340-341 and 450-451). There is no `IsGalois`
   hypothesis. Each theorem below adds that `Module.finrank K L` is prime and that `L/K`
   is totally ramified (the ramification index of the spectral integer ring equals the
   degree).
   - `apfIndex_prime_degree_different_profile` (line 348) gives one break `b ≥ 0`.
     `apfIndex K L u` is `1` for `0 ≤ u ≤ b` and `[L:K]` for `u > b`, and the order of
     the different is `([L:K] - 1)(b + 1)`. The proof passes through a normal closure.
   - `apf_prime_degree_different_profile` (line 457) gives the same break together with
     the formulas for `apfPsi K L` and `apfPhi K L`.
   - `apfIndex_prime_degree_eq_different` (line 474) says that the break is
     `v(𝔇)/([L:K] - 1) - 1`, where `v(𝔇)` is the order of the different.

   Two things are missing for the Kummer tower.
   - The Kummer specialization. The formalization does not show that `K_{n+1}/K_n` is
     totally ramified of degree `p` with different of order `p^{n+1} e + p - 1`. That
     order follows from the Eisenstein polynomial `X^p - π_n`, and with the last theorem
     it gives the break `p^{n+1} e/(p-1)`.
   - The passage to `IsElementaryStep`. The theorems that conclude elementarity,
     `IsElementary.of_embedding` (`APF/Elementary/Basic.lean`, line 49),
     `isElementary_of_apfSubgroup_profile` (`APF/Tower/FiniteProfile.lean`, line 169) and
     `isElementaryStep_of_apfSubgroup_profile` (`APF/Tower/Criterion.lean`, line 115),
     take as input the profile of the upper products `G_E · G^u` (`apfSubgroup`), not the
     index profile above. I found no theorem that goes from the index profile to these
     products. `apfIndex_eq_one_of_apfSubgroup_eq_top` (`APF/Tower/Elementary.lean`,
     line 51) goes the other way. For a totally ramified step the conversion is short,
     but it has to be written.

   So the formalization does not state that the Kummer tower is arithmetically
   profinite. The plan note ("What remains to be done by us", item 1) describes the
   formalization's prime-degree results as results on Galois extensions. At the checked
   commit the three theorems above have no Galois hypothesis.
2. **No residue or Frobenius compatibility.** No statement relates `absoluteGaloisEquiv`
   to the projections onto the Galois groups of the residue fields. E1a in group form does
   not need it. The filtered isomorphism at index `0` carries inertia onto inertia, so
   it induces an isomorphism of the unramified quotients `G/G^0`. Continuous characters
   of these profinite quotients have finite image, so finite-order unramified twists
   correspond on the two sides. The Galois–Weil dictionary of Task 7426 then carries the
   count over to Weil groups.
3. **Its own ramification layer.** The filtrations of the theorems above are that
   library's (`upperRamificationGroupInfinite`, `RelFieldOfNorms.upperRamificationGroup`).
   Two bridges are needed before they can be used with the Library (plan note, same
   list, item 3):
   - from `upperRamificationGroupInfinite K Ω u` to the Library's
     `Langlands.Ramification.Padic.absoluteUpperRamificationGroup F u`;
   - from the norm-field filtration, transported along `absoluteGaloisEquiv` and
     `laurentEquiv`, to the absolute upper filtration of the Laurent-series field in the
     Library's general layer (Task 7403).
4. **The residue field.** `laurentEquiv` gives Laurent series over `κL`, the residue
   field of `L`. The Library premise uses `Langlands.Weil.Local.localResidueField F`. The
   Kummer tower is totally ramified, so the two are isomorphic, but the identification
   has to be written.

## The Library premise and its correspondence

The Library states the boundary in three statement tasks. All three are published as tasks
and not yet as Library modules (17 November 2026); their declaration names are fixed by
the task contracts.

- Task 7450 (`45f364a1-995f-476c-87de-0d9eb13b19f5`), module
  `Langlands.LocalFactor.Ramification.Herbrand.KummerTowerStatement`, namespace
  `Langlands.Ramification.Kummer`. It defines the tower (`IsKummerRootSystem`,
  `kummerStage`, `kummerTower`, `kummerBreak = p e/(p-1)`). It states the Kummer-step
  and tower lemmas on the Library's p-adic layer: the Herbrand function of the step and
  of every stage, the truncation lemma, and `G_{K_n} · G_F^u = G_F` and
  `G_L · G_F^u = G_F` for `u ≤ p e/(p-1)`.
- Task 7451 (`6a2c9e18-7b7e-46c4-8a33-0b892673c7da`), module
  `Langlands.LocalFactor.Ramification.KummerFieldOfNormsStatement`, the same namespace.
  It states the premise `KummerTowerFieldOfNormsStatement` and the implication
  `CloseFieldsGaloisFromKummerFieldOfNormsStatement` (premise → E1a).
- Task 7436 (`dd29c761-8c7b-46a7-a8d6-e918cf37c1fe`), module
  `Langlands.LocalFactor.Ramification.CloseFieldsStatement`, states E1a as
  `Langlands.Ramification.Local.CloseFieldsGaloisQuotientStatement`.

The premise says: for every p-adic field `F`, uniformizer `ϖ` and compatible system
`πs` of `p^n`-th roots of `ϖ`, there is `φ : G_L ≃ₜ* G_X`, `X = LaurentSeries k`, such
that `φ` maps `G_F^u ∩ G_L` onto `G_X^v` whenever `-1 ≤ u` and
`relativeHerbrandPsi (kummerStage F πs n) u = v` for all large `n`.

Its parts correspond to the formalization as follows.

| Premise | Formalization |
| --- | --- |
| `G_L = (kummerTower F πs).fixingSubgroup` | `Ω ≃ₐ[L] Ω` with `Ω = AlgebraicClosure F.Carrier` |
| `X = LaurentSeries (localResidueField F)` | `FieldOfNorms K L` through `laurentEquiv` and the residue identification (item 4 above) |
| `φ` | `RelFieldOfNorms.absoluteGaloisEquiv K L Ω`, transported along `laurentEquiv` |
| `v`, the eventual value of `ψ_{K_n/F}(u)` | `apfPsi K L u` |
| `φ(G_F^u ∩ G_L) = G_X^v` | `map_normUpperRamificationGroup` with `M = Ω`, after the two bridges |

The premise avoids `ψ_{L/F}` for infinite `L`. For `u ≥ 0` the derivative of
`ψ_{K_n/F}` at `w ≤ u` is `(G_F^0 : G_{K_n}^0 G_F^w)`. Arithmetic profiniteness makes
`G_L^0 G_F^u` open, so `G_{K_n}^0 G_F^w = G_L^0 G_F^w` for all `w ≤ u` once `n` is large.
Hence `ψ_{K_n/F}(u)` is eventually Wintenberger's `ψ_{L/F}(u)` (1.2.1). On `[-1, 0]`
both are the identity.

## Discharging the premise later

If a later instance can import the formalization, these steps discharge the premise:

1. Prove that `K_{n+1}/K_n` is elementary of level `p^{n+1} e/(p-1)` (in the numbering
   of `K_n`). Show that the step is totally ramified of degree `p` and that its different
   has order `p^{n+1} e + p - 1`. Then `apfIndex_prime_degree_eq_different` gives the
   one-break index profile at that level. Convert this profile into the upper-product
   profile and apply `IsElementary.of_embedding` (or
   `isElementaryStep_of_apfSubgroup_profile`). No Galois closure is needed for this.
   Then `isAPF_iSup_iff_tendsto_of_elementary_tower` with `E 0 = K` gives `IsAPF K L`,
   because the sum `apfPhi_eq_sum_of_isElementaryStep` is `p e/(p-1) + n e` and tends to
   infinity.
2. Show that `apfPsi K L u` is the eventual value of `relativeHerbrandPsi
   (kummerStage F πs n) u`, using the argument above.
3. Write the two filtration bridges and the residue identification.
4. Apply `RelFieldOfNorms.absoluteGaloisEquiv` and `map_normUpperRamificationGroup` with
   `M = Ω`.

The proof of E1a from the premise does not wait for these steps. It uses only Task 7450's
lemmas and group theory (plan note, Remark 4.1 (ii)).

## Sources

- Operator plan note `operator-external-inputs-plan-2026-11-16`, LaTeX source
  `external-inputs-plan.tex`. The formalization is described at lines 277 and 341-349,
  Remark 4.1 is at lines 586-609, and "What remains to be done by us" with the
  recommendation is at lines 613-632.
- J.-P. Wintenberger, *Le corps des normes de certaines extensions infinies de corps
  locaux; applications*, Ann. Sci. ÉNS (4) 16 (1983), registered as
  `wintenberger-1983-field-of-norms`. The printed page is the PDF page + 57. The results
  used are 1.2.1 (p. 62), 1.3.1 and 1.4.1-1.4.2 (pp. 64-65), Théorème 2.1.3 (p. 65),
  Théorème 3.2.2 and Corollaire 3.2.3 (p. 72), and Corollaire 3.3.6 (p. 77).
- J.-P. Serre, *Local Fields* (1979), registered as `serre-1979-local-fields`: II §4,
  Theorem 2 (Cohen's structure theorem, p. 33) and IV §3 (Herbrand functions).
