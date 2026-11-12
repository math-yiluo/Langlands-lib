# Group-side local Langlands statements: coverage, versions and obligations

Author: Worker 5, for task `a2a442fc-f72b-43ea-a3f3-bcfd61415ccc` (Task 5,
revision 1), written 9 November 2026 and rechecked on 10 November 2026
against Library commit `e449cde988d4e97ab280b8d4d11262887ccc26e0`.

This note maps every theorem family that Task 5 requires to the
proposition definitions that state it in the current Library. The families
are: smooth and admissible representations and finite length; induction,
compact induction and Jacquet functors (exactness, transitivity,
adjunction); the geometric lemma and cuspidal support; finite length and
irreducibility of cuspidal induction; exponent criteria for square
integrability and temperedness; segments and multisegments of `GL_n`;
special and tempered representations; Langlands quotients; the unitary
generic classification input; and their twist, contragredient and
central-character compatibilities.

For each family the note names the actual aggregate declarations and their
principal original source, and says whether a published theorem proves the
aggregate. The appendix gives the SHA256 of the Lean file of every
aggregate in the tables and of its paired Markdown at the pinned commit;
together with the commit, these identify the exact accepted versions.
Declarations mentioned only in passing are identified by the commit. The note also lists the
retained source gaps and the responsibilities that remain open.

Every declaration cited as a statement is a `def` whose type ends in
`Prop`. Publication of a statement accepts its formulation and its source
correspondence. It does not prove the proposition, and no statement here is
assumed true in order to state another.

Two earlier public notes already give component-level tables, and this note
does not repeat them:

- [GL_n classification coverage](../henniart/gln-classification-coverage.md)
  covers the twelve classification pairs (sections 4, 6 and 8 below);
- [Jacquet exponents and Langlands quotients](../jacquet/source-map.md)
  covers the Casselman and Silberger exponent and quotient families
  (sections 5 and 7).

The general reductive statements are mapped in the Renard notes, chiefly
[parabolic functors and tempered representations](../renard/parabolic-functors-tempered-progress.md)
and [supercuspidal induction and cuspidal support](../renard/supercuspidal-finite-length-progress.md).
Sections 1–3 below map the foundational and structural families in
detail; the earlier notes do not collect them in one place. The unreviewed
coverage draft of the previous executors of this task (shared draft of
Task 5, revision 1) was used for navigation only; every entry below was
rechecked against the Library files at the pinned commit.

## How the inventory was checked

- **Existence and elaborated types.** All 105 aggregates in the appendix
  were imported into one private probe module and printed with `#check` at
  the pinned commit, in the task's Lean environment
  `bb168ec3-1031-46d9-816b-5c2ed7bbe1a6` (Lean 4.34.0, Mathlib
  `5ed2965256430c3649e86755f9576b54eca72435`). Lean check
  `92e56db1-31b0-4931-a2df-1429adaee1fe` compiled with zero errors and zero
  warnings. Every printed type has codomain `Prop`; some aggregates take
  outer arguments such as a field `F` and its `TopologicalData`. Separate
  single-declaration inspections reported `statement_returns_prop: true` and
  only the standard axioms `propext`, `Classical.choice` and `Quot.sound` for
  `Induction.StructuralStatement`
  (`8cae538b-3552-4120-b26e-e432c203f787`), `AdmissibleShortExactStatement`,
  `AdmissibleSchurStatement`, `AdmissibleCofinalStatement`,
  `FiniteLengthAdmissibilityStatement`, the Howe statement,
  `SmoothAdmissibleDualityStatement`,
  `SmoothContragredientShortExactStatement` and
  `SmoothContragredientHomDualityStatement`. These inspections were made at
  the earlier commit `18a1f10aef8ea135d90e8474439a5e6d9c130008`. The
  inspection `a7d9d175-6699-4128-b378-07acf874334b` of
  `CuspidalSupport.BernsteinDecompositionStatements`, made at the earlier
  commit `c2558dd50b1b9c025d6182938ef25351b58d7e49`, reports the same. The
  files of all these declarations are byte-identical at the pin (same
  manifest hashes).
- **Proof status.** "Proved by `t`" means that the Library contains a
  published theorem `t` whose stated type is exactly the aggregate (applied
  only to its outer variables). This was found by scanning all theorem
  headers that end in the aggregate name and then reading each header.
  Conditional reductions, whose extra hypotheses are other statements, are
  reported as conditional. "Open" means that no such theorem exists at the
  pin. Some open aggregates have published proofs of individual clauses;
  these are named where they matter.
- **Sources.** Each paired Markdown records the source edition, its
  fingerprint and the exact pages read. Below, BZ77 is Bernstein–Zelevinsky,
  *Induced representations of reductive p-adic groups I* (1977); Ze80 is
  Zelevinsky's sequel (1980); Ca19 is Casselman, *Introduction to admissible
  representations of p-adic groups*, Chapters II and III (2019 revisions);
  Ca95 is Casselman's draft of 1 May 1995; S78 and S79 are Silberger's 1978
  article and 1979 book; Re26 is Renard, *Représentations des groupes
  réductifs p-adiques* (9 July 2026); Ta86 is Tadić (1986); H00 and H02 are
  Henniart (2000, 2002). BZ76 is Bernstein–Zelevinsky's 1976 survey of
  `GL(n,F)` in the English translation, Russian Math. Surveys 31:3
  (registered source `bernstein-zelevinsky-1976-representations-gln`; BZ77
  is `bernstein-zelevinsky-1977-induced-i`), cited by printed pages. W03 is
  Waldspurger's Plancherel article (2003); Ku94 is Kudla (1994); Ja77 is
  Jacquet (1977); JS83 is Jacquet–Shalika (1983); Ro82 is Rodier (1982);
  Au04 is Auel's 2004 memoir. The linked coverage notes and
  the paired Markdown give the full citations and registered source IDs.

## Conventions shared by the statements

- Coefficients are complex. Representation carriers are arbitrary complex
  vector spaces in their own universes, with no topology and no
  finite-dimensionality assumption. A smooth representation has open
  stabilizers. `IsAdmissible` includes smoothness and requires finitely
  generated fixed vectors for every open subgroup.
- The `GL_n` statements use the actual group `GeneralLinear n F.Carrier`
  over every finite extension `F : PadicField p` of `ℚ_p` and every
  compatible `T : F.TopologicalData`. The general reductive statements use
  rational points of an actual connected reductive group scheme over a
  nonarchimedean local field, of any characteristic.
- Parabolic induction is from the standard **upper** block parabolic, uses
  right translation, and has covariance `f(pg) = δ_P(p)^(1/2) σ(p) f(g)`.
  The normalized Jacquet module twists the actual unipotent coinvariants by
  `δ_P^(-1/2)`. The modulus is the explicit block-determinant product
  `δ_B(m) = ∏_(i<j) |det m_i|^(n_j) / |det m_j|^(n_i)` of
  `Langlands.Group.GL.BlockModulus`, and in the general constructions it is
  the actual Haar modulus of `Langlands.Group.HaarModulus` (BZ77 §1.7
  convention).
- Casselman's duality pairs the upper Jacquet module of a representation
  with the **opposite** Jacquet module of its smooth dual. This is distinct
  from same-parabolic duality of induced representations.
- For a segment `Δ = [ρ, ν^(m-1)ρ]`, the increasing product
  `ρ × νρ × ⋯ × ν^(m-1)ρ` has Zelevinsky's `Z(Δ)` as unique irreducible
  subrepresentation and the special representation as unique irreducible
  quotient. Ze80 §3.1 (submodule) and §9.1 (quotient) distinguish the two,
  and the statements keep them apart.
- Equal real exponents are grouped into tempered blocks
  (`SquareIntegrableEqualExponentGrouping`) before Silberger's regular
  positive chamber is used (`GLRegularLanglandsQuotientStatement` requires
  strictly decreasing exponents).
- Square integrability and temperedness are analytic predicates on smooth
  matrix coefficients modulo the centre. Unitarizability is the existence of
  an invariant positive Hermitian form. Genericity uses actual nonzero
  Whittaker functionals. None of these predicates is defined through a
  classification.
- No statement asserts irreducibility of tempered induction for a general
  reductive group. `GLTemperedInductionStatement` (from S79 Lemma 4.5.15)
  asserts only complete reducibility and temperedness. Irreducibility is
  stated only for `GL_n`, in `TemperedBlockInduction` and
  `SquareIntegrableBlockInduction`.

## 1. Smooth and admissible representations, duality and finite length

| Aggregate (module under `Langlands.Representation.`) | Content | Principal source | Proof |
| --- | --- | --- | --- |
| `Langlands.AdmissibleShortExactStatement` (`Smooth.Admissibility.ExactStatement`) | In a short exact sequence with smooth middle term, the middle term is admissible iff both ends are. Assumes compact-open cofinality. | Ca19 II, Cor. II.1.4 with Prop. II.1.3, p.4 | `admissibleShortExact` |
| `Langlands.AdmissibleSubrepresentationStatement` (`Smooth.Admissibility.EmbeddingStatement`) | The source of an injective intertwiner into an admissible representation is admissible (Noetherian coefficients). | Ca19 II, Cor. II.1.4, derived | `admissibleSubrepresentation` |
| `Langlands.AdmissibleCofinalStatement` (`Smooth.Admissibility.CofinalStatement`) | Admissibility may be tested on any cofinal family of open subgroups. | Ca19 II §1, p.2, derived | `admissibleCofinal` |
| `Langlands.AdmissibleSchurStatement` (`Smooth.Schur.Statement`) | For irreducible admissible representations: scalar endomorphisms, Hom spaces of dimension one or zero, and a locally constant central character. | Ca19 II, Props. II.1.6 and II.2.1, pp.4–5; the missing irreducibility and admissibility hypotheses of II.1.6 are restored | `admissibleSchur` |
| `Langlands.Representation.CompactSchurAveragingStatement` (`CompactSchurAveragingStatement`) | Schur averaging over a compact group for a finite-dimensional irreducible continuous representation. | internal | `compactSchurAveraging` |
| `Langlands.SmoothDualCompactFixedDualityStatement` (`Smooth.Contragredient.CompactDualityStatement`) | Restriction from `K`-fixed smooth functionals to the dual of the `K`-fixed vectors is bijective. | Ca19 II, Prop. II.3.1, p.6 | `smoothDualCompactFixedDuality` |
| `Langlands.SmoothAdmissibleDualityStatement` (`Smooth.Contragredient.AdmissibleDualityStatement`) | Smooth functionals separate vectors; the contragredient of an admissible representation is admissible; its smooth bidual map is bijective. | Ca19 II, Prop. II.3.1 and Lemma II.3.2, p.6 | `smoothAdmissibleDuality` |
| `Langlands.SmoothContragredientShortExactStatement` (`Smooth.Contragredient.ExactStatement`) | The smooth contragredient reverses short exact sequences. | Ca19 II, Cor. II.3.3, p.6 | `smoothContragredientShortExact` |
| `Langlands.SmoothContragredientHomDualityStatement` (`Smooth.Contragredient.HomDualityStatement`) | `Hom(ρ, σ) ≃ Hom(σ∨, ρ∨)` by contragredient pullback, for smooth `ρ` and admissible `σ`. | Ca19 II, Prop. II.3.4, p.7 | `smoothContragredientHomDuality` |
| `Langlands.SmoothInvariantPairingDualityStatement` (`Smooth.Contragredient.InvariantPairingStatement`) | A nondegenerate invariant pairing between a smooth `σ` and an admissible `ρ` makes `σ` equivalent to the smooth dual of `ρ`, by the map that the pairing defines. | internal | `smoothInvariantPairingDuality` |
| `Langlands.SmoothContragredientLawsStatement` (`Smooth.Contragredient.LawsStatement`) | Smoothness, action, evaluation, functoriality and bidual naturality of the smooth contragredient. | internal | `smoothContragredientLaws` |
| `Langlands.SmoothContragredientFiniteLengthStatement` (`Smooth.Contragredient.FiniteLengthStatement`) | The contragredient of an admissible finite-length representation has finite length. | derived | `smoothContragredientFiniteLength` |
| `Langlands.GelfandKazhdanContragredientStatement` (`Smooth.Contragredient.GelfandKazhdanStatement`) | For irreducible admissible `ρ` of `GL_(n+1)(F)`, `g ↦ ρ(ᵗg⁻¹)` is equivalent to the smooth contragredient. | BZ76 Theorem 7.3 | `gelfandKazhdanContragredient` |
| `Langlands.JordanHolderMultiplicityIndependenceStatement` (`Filtration.MultiplicityStatement`) | Jordan–Hölder multiplicities do not depend on the composition series. | S78 §1, p.97; BZ77 §1.2, p.443, derived | `jordanHolderMultiplicityIndependence` |
| `Langlands.CentralExponentPrerequisitesStatement` (`Exponents.CentralStatement`) | Generalized central-character decomposition, twists and contragredients. | Ca95 pp.18–22, Props. 2.1.3 and 2.1.9 | open; its decomposition clause is proved by `centralCharacterDecomposition` |
| `Langlands.FiniteLengthAdmissibilityStatement` (`Smooth.Admissibility.FiniteLengthStatement`) | Finite-length smooth representations of `GL_n(F)` and of its block Levis are admissible. | derived from published theorems | `finiteLengthAdmissibility` |
| `Langlands.GLAdmissibleFiniteLengthStatement` (`Classification.FiniteLengthStatement`) | Finitely generated admissible representations of `GL_n(F)` have finite length. | S79 Thm. 5.4.1.6, pp.291–292 | `glAdmissibleFiniteLength` |
| `Langlands.SmoothRep.RationalPointsFinitelyGeneratedAdmissibleFiniteLengthStatement` (`Smooth.Admissibility.HoweStatement`) | The same implication for rational points of every connected reductive group. | Re26 VI.6.3, p.178 | open |
| `Langlands.GLFixedCentralCharacterSplittingStatement` (`Classification.FixedCentralSplittingStatement`) | With a fixed central character, an admissible representation with compactly supported coefficients modulo the centre splits off from surjections and injections. | Ca95 Thm. 5.3.1 and §5.4, pp.48–51 | open |

Ca19 and Ca95 work over Noetherian or rational coefficient rings and with
countability hypotheses on the group. The statements specialize the
coefficients to `ℂ`, except the cofinality and embedding statements, which
keep a Noetherian commutative ring. They replace the ambient hypotheses by
the explicit compact-open cofinality condition that the arguments use. The
existing averaging, cofinality and smooth-duality targets above are reused
by name; this task adds no duplicate of them.

## 2. Induction, compact induction and Jacquet functors

### 2.1 Arbitrary l-groups and closed subgroups

| Aggregate | Content | Principal source | Proof |
| --- | --- | --- | --- |
| `Langlands.Induction.StructuralStatement` (`Induction.StructuralStatement`) | Seven clauses for unnormalized smooth and compact induction from a closed subgroup `H` of an l-group: Frobenius reciprocity (`SmoothFrobeniusClause`); exactness of both inductions (`InductionExactnessClause`); bijectivity of compact-to-smooth induction and admissibility when `H\G` is compact (`CompactQuotientClause`); character twists (`InductionTwistClause`); central action (`InductionCentralActionClause`); transitivity through a closed `P ⊇ H` (`InductionTransitivityClause`); compact induction left adjoint to restriction for open `H` (`OpenSubgroupAdjunctionClause`). | BZ77 §§1.1, 1.8, 1.9(a)–(c), (e), (f), pp.442–445, specialized to `U = 1`; the open-subgroup adjunction and the central action are derived | open; `CompactQuotientClause` is proved by `compactQuotientClause_holds` and `InductionTwistClause` by `inductionTwist` |
| `Langlands.Induction.CompactInductionTransitivityStatement` (`Induction.CompactTransitivityStatement`) | Natural transitivity of compact induction through closed subgroups. | BZ77 §1.9(c) with `U = V = 1` | `compactInductionTransitivity` |
| `Langlands.SmoothCoinvariantExactnessStatement` (`Jacquet.ExactStatement`) | Coinvariant relations are detected on one compact open subgroup, and coinvariants are exact, when every finite subset lies in a compact open subgroup. | Ca19 III, §3 (III.3.1, III.3.3–3.4) | `smoothCoinvariantExactness` |
| `Langlands.Jacquet.Localization.CharacterLocalizationExactnessStatement` (`Jacquet.LocalizationExactnessStatement`) | When `U` is a limit of compact subgroups (`IsLimitOfCompactSubgroups`): θ-relations are detected in one compact subgroup, and θ-localization is exact, for a locally constant character `θ` of `U` and a subgroup normalizing `U` and fixing `θ`. | BZ77 §§1.8(b), 1.9(a), pp.444–445 | `characterLocalizationExactness` |
| `Langlands.Jacquet.CharacterReciprocityStatement` (`Jacquet.ReciprocityStatement`) | `Hom_G(ρ, Ind_P^G(χσ)) ≃ Hom_P(χ⁻¹ρ_N, σ)` for closed `P`, `N ⊴ P`, and a smooth character `χ` of `P` trivial on `N`, with the evaluation formula. | BZ77 §1.9(b) with `θ = 1` and a supplied character | `characterReciprocity` |
| `Langlands.Jacquet.CoinvariantAlgebraStatement` (`Jacquet.AlgebraStatement`) | Coinvariants in stages, scalar twists and central action, for actual normal-subgroup coinvariants. | BZ77 §1.8(b), §1.9(c), (f), derived algebra | open; `CoinvariantTowerStatement` is proved by `coinvariantTower` |

These statements keep BZ77's exact topological hypotheses: an l-group is
Hausdorff with a basis of compact open subgroups, the inducing subgroups are
closed, and only localization requires `U` to be a limit of compact
subgroups.

The smooth dual of compact induction (BZ77 §1.9(d)) is stated in the
Library only for parabolic subgroups (§§2.2–2.3), in normalized form. The
modular factors work as follows.

- For a closed subgroup `H` and unnormalized induction, BZ76 Prop. 2.25(c)
  (p.23) gives `(ind(G,H,ρ))∨ ≅ Ind(G,H,(Δ_G/Δ_H)·ρ∨)`.
- This factor `Δ_G/Δ_P` is not trivial for a parabolic `H = P = M ⋉ U` of
  a reductive group. There `Δ_G = 1`, but `Δ_P` is not trivial: for
  `G = GL_2(F)` and its upper Borel subgroup, conjugation by `diag(ϖ,1)`
  scales `U` by `|ϖ|`, so `mod_U(diag(ϖ,1)) = |ϖ| ≠ 1`.
- BZ77 §1.9(d) (p.445) assumes `Δ_U = 1` and states the normalized version
  `(Δ_G · i_{U,θ}(ρ))∨ ≅ I_{U,θ⁻¹}((Δ_M·ρ)∨)`. BZ77 takes this from BZ76 and
  says on the same page that the `mod_U^(1/2)` factors must be checked to be
  compatible.
- The half-modulus absorbs the factor. BZ77's compact induction
  `i_{U,θ}(ρ)` is BZ76's `ind(G,P,·)` of the `P`-representation
  `θ·mod_U^(1/2)·ρ` (covariance §1.8(a)). Its dual is
  `θ⁻¹·mod_U^(-1/2)·ρ∨`. On `M`, multiplicativity of modules over the
  normal subgroup `U` gives `Δ_G/Δ_P = (Δ_G/Δ_M)·mod_U`. Multiplying,
  BZ76's formula induces `θ⁻¹·mod_U^(1/2)·(Δ_G/Δ_M)·ρ∨`, which is BZ77's
  §1.9(d) after the twist rule §1.9(f).
- Only `Δ_G/Δ_M` remains, and it is trivial when `G` and `M` are unimodular.
  The rational points of a connected reductive group and of its Levi
  subgroups are unimodular.

So, with the positive half-modulus convention above, the Library's
same-parabolic duality statements (`NaturalNormalizedInductionDualityStatement`,
`RationalNaturalInductionDualityStatement`) carry no modular factor.

For §1.9(g), preservation of colimits is stated for general reductive
parabolics (`LeviParabolicFunctorsPreserveLimitsStatement`, §2.3, proved by
`leviParabolicFunctorsPreserveLimits`). It is also proved for the `θ = 1`
semidirect induction (`InductionColimits`). The commutation with
external tensor products in §1.9(g), which BZ77 says can be verified
directly, has no separate statement; the classification pairs that need it
record it as a proof step.

### 2.2 Actual block parabolics of `GL_n`

The groups are `G = GL_n(F)`, `P = B.parabolic F.Carrier`,
`M = B.Levi F.Carrier` and the radical `N = B.unipotentRadical F.Carrier`,
for every ordered block shape `B`. Normalized induction is
`T.normalizedParabolicInduced B` and the normalized Jacquet module is
`T.normalizedJacquet B`. A block refinement `S` gives the inner parabolic
of `M` and the refined functors.

| Aggregate (namespace `Langlands.Parabolic` unless shown) | Content | Principal source | Proof |
| --- | --- | --- | --- |
| `AdmissibilityStatement` | Admissible representations of `P` are trivial on `N`; inflation from `M` preserves and reflects admissibility; unnormalized induction and Jacquet modules preserve admissibility. | Ca19 III §§1–3, III.5.6; BZ77 §2.3(e) | open; `LeviInflationAdmissibilityClause` is proved by `leviInflationAdmissibility` |
| `ExactnessReciprocityStatement` | Unnormalized Frobenius reciprocity with formula `f ↦ ([v] ↦ f(v)(1))`, and exactness of Jacquet modules and of induction. | BZ77 §2.3(a)–(b); Ca19 III | open; the induction clause is proved by `inductionExactness` |
| `GeometricPrerequisitesStatement` | `P\G` is compact; `N` is an increasing union of compact open subgroups, so every finite subset lies in one. | BZ77 §2.3 proof; Ca19 III | open; proved clauses `parabolicQuotientCompact` and `unipotentFiniteContainment` |
| `NormalizedInductionStatement` | Normalized induction preserves admissibility and short exact sequences, is compatible with the same-parabolic smooth contragredient, and preserves unitarizability of admissible input. | Ca19 III.1–1.2; BZ77 §§1.8–1.9, 2.3 | open; admissibility and exactness are proved by `normalizedInductionAdmissibility` and `normalizedInductionExactness` |
| `NormalizedJacquetStatement` | The normalized Jacquet module is smooth, preserves admissibility, is exact, and satisfies normalized Frobenius reciprocity. | BZ77 §§1.8–1.9, 2.3; Ca19 III.3, III.5.6 | open; admissibility and exactness are proved by `normalizedJacquetAdmissibility` and `normalizedJacquetExactness` |
| `NaturalNormalizedFirstAdjointnessStatement` | The Frobenius equivalences form natural families, standard and refined. | Ca19 III, Prop. III.3.5 | open |
| `NormalizedRefinementTransitivityStatement` | `i_M^G ∘ i_L^M ≅ i_L^G` and `r_L^M ∘ r_M^G ≅ r_L^G` as natural isomorphisms for block refinements, with prescribed formulas. | BZ77 §2.3(c) via §1.9(c) | open; both clauses are proved by `normalizedRefinementInductionTransitivity` and `normalizedRefinementJacquetTransitivity` |
| `NaturalNormalizedInductionDualityStatement` | Natural same-parabolic duality `(i_P σ)∨ ≅ i_P(σ∨)`, standard and refined. | Ca19 III, Prop. III.1.1; BZ77 §2.3(d) via §1.9(d) | `naturalNormalizedInductionDuality` |
| `OppositeDualityStatement` | Casselman's canonical pairing between the upper Jacquet module and the opposite Jacquet module of the smooth dual, with its asymptotic characterization, and the induced equivalence. | Ca19 III §§4–6, Thm. III.6.2 and Cor. III.6.3 | open |
| `NaturalNormalizedJacquetDualityStatement` | Natural equivalence `r_P(π∨) ≅ (r_P̄ π)∨` for admissible `π`. | Ca19 III, Thm. III.6.2 | `naturalNormalizedJacquetDuality` |
| `NormalizedSecondAdjointnessStatement` | `Hom(i_P σ, π) ≃ Hom(σ, r_P̄ π)` for admissible inputs, standard and refined. | Ca19 III, Cor. III.6.3 | `normalizedSecondAdjointness` |
| `NormalizedParabolicFiniteLengthStatement` | Normalized induction and Jacquet modules preserve finite length. | derived from published finite-length and admissibility theorems | `normalizedParabolicFiniteLength` |
| `NormalizedOppositeJacquetAdmissibilityStatement` | Opposite (standard, refined, composed) normalized Jacquet modules preserve admissibility. | Ca19 III | `normalizedOppositeJacquetAdmissibility` |
| `NormalizedJacquetFiniteGenerationStatement` | Normalized Jacquet modules preserve finite generation. | Ca95 Thm. 3.3.1, p.35 | `normalizedJacquetFiniteGeneration` |
| `NormalizedCompatibilityStatement` | Every character of `GL_n(F)` is trivial on `N`; normalized induction and Jacquet modules commute with ambient character twists; both preserve a prescribed scalar central character. | BZ77 §§1.8–1.9(f), 2.1–2.3 | open; the induction central clause is proved by `normalizedInductionCentralClause` |
| `Langlands.GLNormalizedInductionUnitarityStatement` (`Induction.UnitaryStatement`) | Normalized parabolic and product induction preserve unitarizability. | Ca95 §3.1; Ku94 §1.1 | `glNormalizedInductionUnitarity` |
| `Langlands.GLNormalizedInductionUnitaryCentralCharacterStatement` (`Parabolic.NormalizedInductionUnitaryCentralCharacterStatement`) | A unitary central character of the inducing representation gives the induced unitary central character through the centre restriction. | internal | `glNormalizedInductionUnitaryCentralCharacter` |

### 2.3 General connected reductive groups and the `GL_n` specialization

For an arbitrary rational parabolic `P = MN` of a connected reductive group,
with the normalized represented-parabolic functors `i_P^G` and `r_P^G`, the
Library states (namespace `Langlands.Aubert.General.RepresentedParabolic`,
modules `Exponents.*`):

| Aggregate | Content | Re26 source | Proof |
| --- | --- | --- | --- |
| `LeviFrobeniusReciprocityStatement` | Frobenius reciprocity with the evaluation formula. | VI.1.2, p.136 | `leviFrobeniusReciprocity` |
| `LeviParabolicFunctorsExactStatement` | Both functors are exact. | VI.1.2, p.136 | `leviParabolicFunctorsExact` |
| `LeviParabolicFunctorsPreserveLimitsStatement` | `i` preserves limits and colimits and `r` preserves colimits. | VI.1.2 | `leviParabolicFunctorsPreserveLimits` |
| `LeviParabolicTransitivityStatement` | Natural transitivity of both functors. | VI.1.4, pp.136–137 | `leviParabolicTransitivity` |
| `LeviSecondAdjointnessStatement` | Second adjointness `i_P^G ⊣ r_P̄^G`. | VI.9.6, (VI.9.6.1) | conditional only (`leviSecondAdjointness_of_structure`) |
| `LeviJacquetContragredientStatement` | Natural isomorphism `r_P̄^G(π∨) ≅ (r_P^G π)∨`. | VI.9.6, (VI.9.6.2) | conditional only (`leviJacquetContragredient_of_structure`) |
| `LeviUnnormalizedParabolicStatements` | For the unnormalized functors `Ind_P^G` and `j_N`: Frobenius reciprocity `j_N ⊣ Ind_P^G`, exactness of both, `j_N` preserves colimits, and `Ind_P^G` preserves limits and colimits. | VI.1.1, Theorem, Corollary and Remark, pp.134–135 | open |
| `ArbitraryParabolicQuotientCompactStatement` | `P(k)\G(k)` is compact for every rational parabolic. | V.5.1, Corollary, p.123 (compactness part) | `arbitraryParabolicQuotientCompact` |
| `ArbitraryParabolicJacquetAdmissibilityStatement` | The normalized Jacquet module of an admissible representation is admissible. | VI.6.1, Corollary, pp.176–177 | `arbitraryParabolicJacquetAdmissibility` |
| `ArbitraryParabolicExponentStatement` | Characteristic-space decomposition of `r_P^G π` and finiteness of its exponents; the case `P = G`; exponents of induced representations restrict from Levi exponents. | VII.1.1, pp.220–221 | `arbitraryParabolicExponent` |

On the actual rational-point group `RationalPoint k G.X` of a connected
reductive group, with its standard parabolics given by a maximal split
torus, a generic cocharacter and a subset of simple roots (namespace
`Langlands.Aubert.General.RationalPointFamily`), two further statements
follow Ca19 rather than Re26:

| Aggregate | Content | Ca19 source | Proof |
| --- | --- | --- | --- |
| `RationalNaturalInductionDualityStatement` | Natural same-parabolic duality `(i_P σ)∨ ≅ i_P(σ∨)` for admissible `σ`. | Prop. III.1.1, p.2 | `rationalNaturalInductionDuality` |
| `RationalNaturalJacquetDualityStatement` | Natural opposite-Jacquet duality `r_P(π∨) ≅ (r_P̄ π)∨` for admissible `π`. | Thm. III.6.2 and Cor. III.6.3, pp.7–8 | `rationalNaturalJacquetDuality` |

Section 3 gives the general geometric lemma and cuspidal support. Further
general reductive units of the Renard whole-book task
(`f5d1f399-a1f8-4ab5-a981-90b92abd4857`), such as
`CuspidalSupport.BernsteinCentralIdempotentStatements` (Re26 VI.7.4) and
`Compact.CompactBlockDecompositionStatements` (Re26 IV.1.6–IV.1.7), are not
needed by the families of this note; their paired Markdown documents them.

These general statements and the `GL_n` statements of §2.2 are separate
published pairs; neither is derived from the other. The `GL_n` pairs state
the general reductive results of BZ77 §2.3 and Ca19 III for the standard
upper block parabolics of `GL_n(F)` with the explicit block modulus, and
their paired Markdown explains that specialization.

For an arbitrary semidirect decomposition `P = M ⋉ U` of subgroups of a
locally compact nonarchimedean group, with trivial character `θ`, the
published `Langlands.Representation.Aubert.General.Parabolic` constructs the
actual Haar-normalized functors `normalizedInductionFunctor` and
`normalizedJacquetFunctor` (BZ77 §1.8 with `θ = 1`, valid as BZ's `I_{U,1}`
when `U` is unimodular, which follows from `IsLimitOfCompactSubgroups`).
Published constructions with proofs in the same directory supply their
first adjointness (`Aubert.General.FirstAdjointness.equiv`), induction and
Jacquet functors in stages (`InductionStages`, `JacquetStages`, under
explicit modulus hypotheses), limits and colimits (`InductionLimits`,
`InductionColimits`), and the support filtration of `r_Q ∘ i_P` with
Mackey-orbit graded pieces (`ParabolicSupportFiltration`, BZ77 §§5.1–5.4).
These are constructions and theorems, not new statements.

## 3. Geometric lemma, cuspidal support and quasicuspidal structure

| Aggregate | Content | Principal source | Proof |
| --- | --- | --- | --- |
| `Langlands.Geometric.PadicGeometricLemmaTheorem` (`Geometric.GeometricLemmaStatement`) | For block shapes `B`, `C` of `GL_n`, the functor `r_C ∘ i_B` has a natural filtration whose graded pieces are the actual Jacquet–Weyl transport–induction functors, indexed by minimal permutations. | BZ77 §2.12 | `padicGeometricLemma` |
| `Langlands.Geometric.PadicProductLeviGeometricLemmaTheorem` (`Geometric.ProductLeviGeometricLemmaStatement`) | The same inside a product Levi, for refined functors. | BZ77 §2.12 | `padicProductLeviGeometricLemma` |
| `Langlands.Geometric.PadicGeometricWeylTheorems` (`Geometric.WeylStatement`) | Minimal permutations parametrize `W_C \ S_n / W_B` and `P_B \ GL_n(F) / P_C`; both intersection triples are standard. | BZ77 §§2.6–2.7, Lemma 2.11, §§6.3–6.4 | open |
| `Langlands.Geometric.ClosedSubgroupMackeyTheorems` (`Geometric.ClosedSubgroupStatement`) | For closed subgroups of an l-group with finite double cosets, an ordered orbit cover exists, and the natural support filtration has the orbit pieces as graded quotients. | BZ77 §§5.1–5.2 with `U = V = 1` | open |
| `Langlands.Aubert.General.RepresentedParabolic.RepresentedGeometricLemmaStatement` (`Geometric.RepresentedGeometricLemmaStatement`) | The geometric lemma for arbitrary rational parabolics of a connected reductive group. | Re26 VI.5.1, pp.161–162 | conditional only (`representedGeometricLemma_of_geometry_and_supportGraded`) |
| `Langlands.CuspidalSupport.PadicLeviQuasicuspidalStructureTheorems` (`CuspidalSupport.QuasicuspidalStructureStatement`) | On product Levis: the subquotient observation and parts (a)–(c) of BZ77 §2.4 (subquotients, decomposition, cuspidal constituents and contragredients of quasicuspidal representations). | BZ77 §2.4 | open |
| `Langlands.CuspidalSupport.PadicProperRefinedInductionTheorem` (`CuspidalSupport.ProperInductionStatement`) | Proper normalized induction has no nonzero quasicuspidal subquotient. | BZ77 §2.4(d) | `padicProperRefinedInduction` |
| `Langlands.CuspidalSupport.PadicCuspidalityComparisonTheorems` (`CuspidalSupport.CuspidalityComparisonStatement`) | Standard Jacquet vanishing agrees with the all-conjugates supercuspidality predicate. | BZ77 §2.4 | `padicCuspidalityComparisonTheorems` |
| `Langlands.CuspidalSupport.PadicQuasicuspidalJacquetTheorems` (`CuspidalSupport.JacquetInductionStatement`) | Jacquet modules of quasicuspidal induction: conjugating cosets, vanishing for non-associated Levis, and a filtration with one Weyl-transported piece per minimal permutation. | BZ77 Cor. 2.13 | open |
| `Langlands.GLSupercuspidalSupportStatement` (`Classification.SupercuspidalSupportStatement`) | Every irreducible representation of `GL_n(F)` embeds in a product of supercuspidals, and its supercuspidal support multiset is unique. | Ze80 Prop. 1.10, via BZ77 §§2.5, 2.7, 2.9(a) | open |
| `Langlands.Aubert.General.RepresentedParabolic.LeviCuspidalSupportAssociationStatement` and `LeviCuspidalSupportSurjectiveStatement` (`Exponents.*`) | For general reductive groups: cuspidal data occurring in Jacquet modules of one irreducible representation are associated (Lemma), and a partial form of the Proposition (surjection onto a given supercuspidal and finiteness of representatives). | Re26 VI.7.1, p.180 | open |
| `Langlands.Aubert.General.RepresentedParabolic.LeviCuspidalEmbeddingStatement` (`Exponents.LeviCuspidalEmbeddingStatement`) | For general reductive groups: every irreducible smooth representation embeds in a representation induced from a supercuspidal representation of the Levi of some rational parabolic. | Re26 VI.2.1, Corollary, p.139 | `leviCuspidalEmbedding` |
| `Langlands.CuspidalSupport.BernsteinDecompositionStatements` (`CuspidalSupport.BernsteinDecompositionStatements`) | For general reductive groups: the Bernstein decomposition of every smooth representation over the inertial classes, the splitting lemma, and abelianness of each block. | Re26 VI.7.2, pp.181–184 | open |

The `U = V = 1` Mackey statement and the `GL_n` statement do not cover
BZ77 §5.2 with general unipotent subgroups and characters. No statement
in this note depends on that general form; it is recorded as a retained
extension in §11.

## 4. Cuspidal induction: finite length and irreducibility

| Aggregate (namespace `Langlands.Classification` unless shown) | Content | Principal source | Proof |
| --- | --- | --- | --- |
| `Langlands.CuspidalSupport.PadicCuspidalInductionTheorems` (`CuspidalSupport.NormalizedCuspidalInductionStatement`) | Cuspidal embedding of irreducibles; finite length with the bound `B.length!` for irreducible cuspidal data; association iff nonzero Hom iff matching Jordan–Hölder factors iff a common subquotient; Hom dimension bound. | BZ77 Thms. 2.5, 2.8, 2.9, §2.13(c) | open |
| `Langlands.Aubert.General.RationalPointFamily.RationalSupercuspidalInductionFiniteLengthStatement` (`Aubert.General.RationalSupercuspidalInductionFiniteLengthStatement`) | For general reductive groups: normalized induction of an irreducible supercuspidal representation of a standard Levi has finite length. The bound and the association equivalences of the source are not part of this statement. | Re26 Thm. VI.5.4, pp.173–174 | open; split into two inputs by the published `RationalSupercuspidalInductionInputsStatement` module |
| `PadicNormalizedProductFiniteLengthTheorems` (`Classification.NormalizedProductFiniteLengthStatement`) | Products of arbitrary irreducible factors, and of admissible finite-length factors, have finite length. | H02 §2.5; Ca95 Cor. 6.3.8 | open |
| `PadicSupercuspidalProductIrreducibilityTheorems` (`Classification.SupercuspidalProductStatement`) | A product of supercuspidals is irreducible iff no pair satisfies `ρ_j ≅ νρ_i`. | BZ77 Thm. 4.2 and Remark 4.2(2); Ze80 Thm. 4.2 | open |

## 5. Exponents, square integrability and temperedness

All `GL_n`. The [Jacquet source map](../jacquet/source-map.md) gives the
chamber conventions, the block form of the exponent conditions and the
component declarations.

| Aggregate (namespace `Langlands`) | Content | Principal source | Proof |
| --- | --- | --- | --- |
| `GLSquareIntegrableExponentCriterionStatement` | Square integrability iff unitary central character and strict exponent bounds on the negative chamber. | Ca95 Thm. 4.4.6; W03 Prop. III.1.1 | `glSquareIntegrableExponentCriterion` |
| `GLTemperedExponentCriterionStatement` | Temperedness iff weak exponent bounds on the closed negative chamber. | S78 p.98; S79 Lemma 4.5.3; W03 Prop. III.2.2 | `glTemperedExponentCriterion` |
| `GLSquareIntegrabilityPrerequisitesStatement` | Haar-measure independence, unitary twist and contragredient invariance, and the one-coefficient criterion. | Ca95 §2.5, Prop. 2.5.3 | open |
| `GLTemperedInductionPrerequisitesStatement` | Irreducible tempered representations are unitarizable; tempered induction is completely reducible and tempered. | S79 Cor. 4.5.13, Lemma 4.5.15 | open |
| `GLDiscreteSeriesJacquetPrerequisitesStatement` and `GLTemperedDiscreteSeriesPrerequisitesStatement` | Discrete series of Levis are tempered; Jacquet quotients and discrete-series support of tempered representations. | S79 Thms. 4.5.10, 4.5.18, Cor. 4.5.11 | open |
| `GLCuspidalJacquetMultiplicityPrerequisitesStatement` and `GLDiscreteSeriesJacquetMultiplicityStatement` | Exact Jacquet lengths and constituent multiplicities for cuspidal and square-integrable induction. | S79 Thm. 5.4.1.1, §5.4.4 | cuspidal case proved by `glCuspidalJacquetMultiplicityPrerequisites`; discrete-series case open |
| `GLDualJacquetExponentPrerequisitesStatement` and `GLWeaklyCriticalTemperedRefinementStatement` | Full-dual exponents, class comparisons and weakly critical support refinement. | S79 §2.4, §3.2, Cor. 4.5.11–4.5.12 | open |
| `Classification.PadicTemperedSmoothDualityStatement` | An admissible representation is tempered iff its smooth contragredient is. | derived | `padicTemperedSmoothDuality` |
| `Classification.PadicSegmentSquareIntegrabilityTheorems` | Special representations are essentially square integrable, and these exhaust the essentially square-integrable classes. | Ze80 §9.3; H02 §2.6; Au04 Thm. 6.1 | open |

## 6. Segments, multisegments, special and tempered representations, unitary generic input

All `GL_n`, namespace `Langlands.Classification`. Component tables are in
the [classification coverage note](../henniart/gln-classification-coverage.md).

| Aggregate | Family | Principal source | Proof |
| --- | --- | --- | --- |
| `PadicSegmentConstituentTheorems` | Socle `Z(Δ)` of the increasing product and its special head; uniqueness; distinctness for length at least two; rank-one character. | Ze80 §§2.2, 2.10, 3.1–3.2, 9.1–9.2 | open |
| `PadicSegmentSquareIntegrabilityTheorems` | Special and square-integrable representations (see §5). | Ze80 §9.3 | open |
| `PadicSegmentGenericTheorems` | Irreducibility and genericity of segment products, exhaustion and uniqueness of generic representations. | Ze80 Thms. 4.2, 9.7, §9.10 | open |
| `PadicMultisegmentClassificationTheorems` | Socle and head classification by multisegments; square-integrable Langlands heads. | Ze80 Thm. 6.1, §6.5; Ro82 §4.3 Thm. 3; H02 §2.8 | open |
| `PadicTemperedBlockTheorems` | Products of square-integrable blocks are irreducible, unitarizable, tempered and generic; tempered exhaustion and uniqueness; equal-exponent grouping. | Ja77 Cor. 3.3; JS83 §1.2; Ku94 §2.2, Prop. 2.2.1 | open |
| `PadicUnitaryGenericTheorems` | Construction, exhaustion and parameter uniqueness of generic unitarizable representations. | Ta86 Thm. D with the generic specialization; H00 App. A.2 | open |

## 7. Langlands quotients

| Aggregate (namespace `Langlands`) | Content | Principal source | Proof |
| --- | --- | --- | --- |
| `GLRegularLanglandsQuotientStatement` | Unique-head existence, uniqueness of ordered inducing data, and exhaustion, for tempered blocks with strictly decreasing real exponents. | S78 Thm. 4.1(1)–(3), p.99 | open |
| `Classification.SquareIntegrableLanglandsHeadExistence`, `…QuotientUniqueness`, `…Exhaustion`, `…Classification` (components of `PadicMultisegmentClassificationTheorems`) | The same for essentially square-integrable blocks with weakly decreasing exponents. | H02 §2.8 | open |
| `Classification.SquareIntegrableEqualExponentGrouping` (component of `PadicTemperedBlockTheorems`) | Grouping of equal exponents into tempered blocks. | Ku94 §2.2 | open |
| `RootWeightConeDecompositionStatement`, `GLParabolicRootWeightConeStatement` | Root/weight cone decomposition and its block-parabolic form. | S78 Lemma 7.1; Langlands Lemma 4.4 | parabolic form proved by `glParabolicRootWeightCone` |
| `GLRelativeGenericParameterStatement`, `GLRelativeGenericComparisonStatement`, `GLRelativeRegularComparisonStatement` | Multiplicity comparison, generic then regular parameters. | S78 Prop. 5.1, Lemmas 5.2–5.6 | comparisons proved by `glRelativeGenericComparison` and `glRelativeRegularComparison` |
| `GLRelativeRecoveryStatement`, `GLRelativeCosocleMultiplicityStatement`, `GLRegularLanglandsTensorRecoveryStatement`, `GLSemistandardLanglandsConjugacyStatement` | Recovery of inducing data and semistandard conjugacy. | S78 Props. 5.7–5.9, 6.1, Cor. 6.2 | recovery proved by `glRelativeRecovery`, cosocle multiplicity by `relativeCosocleMultiplicity`, tensor recovery by `glRegularLanglandsTensorRecovery`; semistandard conjugacy open |
| `GLMaximalConeJacquetQuotientStatement` | Maximal-cone Jacquet quotient used for exhaustion, with the published dominance correction. | S78 Prop. 7.2 | `glMaximalConeJacquetQuotient` |

## 8. Twist, contragredient and central-character compatibilities

| Construction | Twist | Contragredient | Central character |
| --- | --- | --- | --- |
| Smooth/admissible representations | `CentralCharacterTwistStatement` (in `CentralExponentPrerequisitesStatement`) | §1 duality statements; `CentralCharacterContragredientStatement` | `AdmissibleSchurStatement` |
| Subgroup induction (l-groups) | `InductionTwistClause` | — (the Library states BZ77 §1.9(d) only for parabolics; see §2.1) | `InductionCentralActionClause` |
| Coinvariants / localization | `CoinvariantTwistStatement` | — | `CoinvariantCentralActionStatement` |
| `GL_n` parabolic induction and Jacquet modules | `NormalizedInductionTwistClause`, `NormalizedJacquetTwistClause` | `NormalizedInductionDualityClause`, `NaturalNormalizedInductionDualityStatement`, `OppositeDualityStatement`, `NaturalNormalizedJacquetDualityStatement` | `NormalizedInductionCentralClause`, `NormalizedJacquetCentralClause`, `GLNormalizedInductionUnitaryCentralCharacterStatement` |
| General reductive parabolics | — | `LeviJacquetContragredientStatement`; on standard parabolics of the rational-point group, `RationalNaturalInductionDualityStatement` and `RationalNaturalJacquetDualityStatement` (both proved) | — |
| Supercuspidal representations | determinant twists in `Classification.SupercuspidalTwist` (construction) | `GeneralLinear.SupercuspidalContragredientStatement` (proved by `supercuspidalContragredient`) | — |
| Square-integrable and tempered representations | `GLSquareIntegrabilityPrerequisitesStatement` (unitary twists) | `GLSquareIntegrabilityPrerequisitesStatement`; `PadicTemperedSmoothDualityStatement` | a unitary scalar central character is part of both analytic predicates; `SegmentSpecialSquareIntegrabilityCriterion` |
| Segments | `SegmentConstituentRealTwistCompatibility`, `SegmentConstituentCharacterTwistCompatibility` | `SegmentConstituentContragredientCompatibility` | `SegmentConstituentCentralCharacter` |
| Multisegments and Langlands heads | `MultisegmentConstituentRealTwistCompatibility`, `MultisegmentConstituentCharacterTwistCompatibility` | `MultisegmentConstituentContragredientCompatibility`, `SquareIntegrableLanglandsHeadContragredientCompatibility` | `MultisegmentConstituentCentralCharacter` |
| Unitary inducing data | `TwistedProductCharacterTwistClause`, `UnitaryBlockCharacterTwistClause` | `UnitaryAdmissibleHermitianClause`, `RealTwistOrdinaryDualClause`, `TwistedProductOrdinaryDualClause` | `TwistedProductCentralCharacterClause`, `ScalarCharacterTwistDualClause` |

The segment, multisegment and unitary clauses are components of
`PadicSegmentConstituentCompatibilityTheorems`,
`PadicMultisegmentConstituentCompatibilityTheorems` and
`AllPadicUnitaryGenericCompatibilityStatement`. The segment duality formula
follows Ze80 Props. 3.3 and 9.4, which correct the missing dual on `ρ` in
H02 §2.6. A dash means that no separate statement exists for that
combination at this pin; none is needed by the classification families.

## 9. General reductive theorems and their `GL_n` specialization

- BZ77 §2 states its parabolic results for any connected reductive group.
  The Library states them for `GL_n` with the explicit block modulus
  (§§2.2, 3, 4). The general reductive versions of the same functor
  properties are separate statements (§2.3).
- Ca19 and Ca95 are general. Their duality, Jacquet admissibility and
  exponent criteria are specialized to `GL_n` in the pairs of §§2.2 and 5.
  Each pair records the conversion of chambers and normalizations.
- S78 Thm. 4.1 and S79 are general. Their `GL_n` specializations (§§5, 7)
  replace the Levi tempered data by `GL_n` block data and convert `-iλ` to
  decreasing `|det|` exponents for upper parabolics, as explained in the
  [Silberger note](../henniart/silberger.md) and the Jacquet source map.
- Ze80, Ta86 and H02 concern `GL_n` only, so no specialization is involved.

## 10. Retained source gaps

These gaps are recorded in the paired Markdown and in the linked notes.
None of them is a hypothesis of a statement.

- Ze80 §9.3 omits the converse proof that every essentially
  square-integrable representation is special. The statement follows the
  printed assertion. Au04 gives a later written route through Aubert
  duality and Casselman's criterion, whose upstream inputs are not audited
  here. See [classification sources](../henniart/gln-classification-sources.md).
- Ze80 Prop. 1.11 (reducibility of `ρ × νρ`) is a sketch, and BZ77 defers
  the necessity part of its irreducibility criterion to a sequel.
- BZ77 Thm. 2.5 is proved elsewhere. BZ77 refers §1.9(b)–(d) to BZ76
  Ch. I and leaves the compatibility of the `mod_U^(1/2)` factors to the
  reader (p.445). §2.1 above gives the modular factors of §1.9(d).
- Ja77 contains no tempered exhaustion; Ro82 Prop. 12 and Ku94
  Prop. 2.2.1 state it without a complete proof in the retained sources.
- S78 Lemma 5.3 does not hold in its unrestricted wording; see the
  [scope boundary](../jacquet/silberger-lemma53-scope.md). The analytic
  steps of the exponent criteria rest on W03's account of Harish-Chandra's
  results.
- Ta86 Theorem D's generic specialization needs the derivative argument
  that excludes Speh sizes greater than one, not irreducibility alone.

## 11. Responsibilities and remaining obligations

- **Proofs.** Every aggregate marked "open" or "conditional only" above is a
  separate proof obligation. A proof task names its target by the full Lean
  declaration name; search the task pool by that name. Published clause
  proofs do not prove the aggregate.
- **Nontrivial characters `θ` in BZ77 §§1.8–1.9 and general §5.2.** The
  Library has the `θ = 1` semidirect constructions (§2.3) and the `U = V = 1`
  and parabolic geometric lemmas (§3), but no normalized induction or
  localization for a closed triple with a nontrivial character of `U`.
  Task 149 (`82bfcc29-81a6-4092-9b9c-f089d2abfb76`, revision 1, a definition
  task with Worker 149 as executor and no accepted artifact at the pin)
  owns that construction. Unreviewed
  statement drafts for BZ77 §1.9(a)–(b) in this generality are in the shared
  draft of Task 5 (`drafts/a2a442fc-f72b-43ea-a3f3-bcfd61415ccc/`); they
  import the unpublished constructor and are not Library dependencies. No
  family required by Task 5 depends on this extension: Whittaker-type
  characters belong to the representation-factor branch, and the parabolic
  theory uses `θ = 1`.
- **Adjacent branches.** Whittaker uniqueness, Rankin–Selberg factors and the
  local converse theorem belong to the representation-factor statement
  branch ([local factors](../local-factors/coverage.md)). The final
  correspondence statements belong to the assembly branch
  ([LLC specification](../henniart/llc-specification-coverage.md)).

## Appendix: exact versions at `e449cde988d4e97ab280b8d4d11262887ccc26e0`

Modules are under `Langlands.Representation.`; the aggregate is the declaration
that the probe check `92e56db1-31b0-4931-a2df-1429adaee1fe` printed with
codomain `Prop`. The hashes are the SHA256 of the Lean file and of its paired
Markdown in the Library manifest of this commit.

| Module | Aggregate | Lean SHA256 | Markdown SHA256 |
| --- | --- | --- | --- |
| `Smooth.Admissibility.ExactStatement` | `Langlands.AdmissibleShortExactStatement` | `3e0e7e7d92c7da8a00137a2ad51d23ab6550955102538def39c087b243bb1479` | `450aa6d5498149c1c77e2a579311a61b3a715ae768ecd90385a0eb651ead65c8` |
| `Smooth.Schur.Statement` | `Langlands.AdmissibleSchurStatement` | `1eb7a1761466b6eab72cb9b17fbb186562ecd2dc0bbcecbaa012da1094cb3d34` | `082059663ed9d61b60e018ee0475b9836aeef93d171d756cb593eb10e2970b7c` |
| `Smooth.Admissibility.CofinalStatement` | `Langlands.AdmissibleCofinalStatement` | `df36b24b8e9972dbaa6d810baa13fcb796fbc81465367c8de92a08ca4449a433` | `7cd745762089838e4cbc5d4e6a96718a7bc7632de6b74c2499e84e59af9911e1` |
| `Smooth.Admissibility.EmbeddingStatement` | `Langlands.AdmissibleSubrepresentationStatement` | `8521d3f4c64187dcd24fb55dfd4de9bbe30210eb65df8fd68728bce3ccc7b2d9` | `58845f9496da31d552f760c3ae59db5fc288e143108b9f451e496b8d1ca05e50` |
| `Smooth.Admissibility.FiniteLengthStatement` | `Langlands.FiniteLengthAdmissibilityStatement` | `82735dd13676b49a523566ed0446e38643471480d23fca886cc8b88ef000d19b` | `843d0cf807fc581f725f79153efdda98e6bfdd264f621cecf83e792b811e1a0a` |
| `Smooth.Admissibility.HoweStatement` | `Langlands.SmoothRep.RationalPointsFinitelyGeneratedAdmissibleFiniteLengthStatement` | `1bf01593802a33b8317f9af457a7d27d2b5f78ca0648e5a17200ddfb70f03ae8` | `c1009a1db09d6026417820e1884cb51c8580b75071a4628ff1a303f599fc68b4` |
| `CompactSchurAveragingStatement` | `Langlands.Representation.CompactSchurAveragingStatement` | `d918afd3b952c88543d37f2ffc5c038a0ea708912a122ff2fe4e912afc5c7b1c` | `23e520210680f80bd75931997ecab12e1d542a7257434de0434d629683c2392e` |
| `Smooth.Contragredient.AdmissibleDualityStatement` | `Langlands.SmoothAdmissibleDualityStatement` | `a3b9788828170bc1ef481d64332c945c3827876bcf3d12f7c9af7278b1378e09` | `bfb5809f5bfd36bd7b873b7b41932d0777f9f54e70369011b88800d9b15dfc26` |
| `Smooth.Contragredient.CompactDualityStatement` | `Langlands.SmoothDualCompactFixedDualityStatement` | `aecf6195a2703a560242c597cce8c8de908a3be30ef3a12992956cffc7b3550d` | `27b6ba05c0923755f12cb6ed6508cc9fd0f4c1112bf6cdcd1a715a06f70c2abb` |
| `Smooth.Contragredient.ExactStatement` | `Langlands.SmoothContragredientShortExactStatement` | `4608b911207b38b224ec62e444e38a78144a52e923ebb0e63d84051aff559435` | `cda561e6ebc0dae91eafb6f1eaa100e89da8091f9d515eb67227beb662223a58` |
| `Smooth.Contragredient.HomDualityStatement` | `Langlands.SmoothContragredientHomDualityStatement` | `12d47df8361ce30416737f793c462de023e4590117b95013c49d1848ef66c4da` | `507caaf8aa9a4d786864120edaf3bd716b51286c05c2730192103d4736a77c4c` |
| `Smooth.Contragredient.FiniteLengthStatement` | `Langlands.SmoothContragredientFiniteLengthStatement` | `90243ecd74226eb787e7ba9d530805ff8c62c3590b758a1bf1096a26cf46a37c` | `a14e1a71a0a55ef1cdccd2494578867d5b116445035068c45d71f73235a945dd` |
| `Smooth.Contragredient.InvariantPairingStatement` | `Langlands.SmoothInvariantPairingDualityStatement` | `79e580019100d21a88ac3e5b2ce0c170e6139b34195e8072bd7f1d75ec5b524b` | `be187d696a8bb67ca988e720ab72893d86cb17a3b5b83f827de00faadb0f6414` |
| `Smooth.Contragredient.LawsStatement` | `Langlands.SmoothContragredientLawsStatement` | `7de3e69140e0c23094b408621626db56a75e68234d88e1dba74deab77696f24a` | `71ae34dcd1a19591e0b1ddf209b262b6405d9737577dc69065a4c7aaac02e4f7` |
| `Smooth.Contragredient.GelfandKazhdanStatement` | `Langlands.GelfandKazhdanContragredientStatement` | `1acddaf0533cbf03d7a8cf6dffd5cfe8998424315e36134a7125d89653df7078` | `d95a498616c01041d4f6727ea52c5e1243bcd4045d9fec8b7e610bf7a8b0487d` |
| `Filtration.MultiplicityStatement` | `Langlands.JordanHolderMultiplicityIndependenceStatement` | `eee2596c0e71d7a3750a625677c9e6ee5b435a1ff32d4924f755b774406c4ec2` | `183f2aa047781ceb727bd0832b78265c6e486e12c3ead7f3613e9c6ba5af7eeb` |
| `Exponents.CentralStatement` | `Langlands.CentralExponentPrerequisitesStatement` | `0413a5d72f6a0d729592d4767b067204ed19147f6c3902c7de7ef8c65b6ed7f3` | `210d43a153c93233a962c4e6c48b6028ac84a7432ee522ad2c180c8e1262971c` |
| `Classification.FiniteLengthStatement` | `Langlands.GLAdmissibleFiniteLengthStatement` | `b35baf903670b558bbc5fbae97d4f8350c21f72553bc844bd7c858fcb64ee46d` | `dc554c0a5dc5352804716353022e8a971cf345ef51bb8c0591dd063d7a27b1fb` |
| `Classification.FixedCentralSplittingStatement` | `Langlands.GLFixedCentralCharacterSplittingStatement` | `48ace7be0156943408440f4e6f1adcd7af9399169ae86c5810b144b672c2b40a` | `a2cf58df4e20d46f09b56bd2d370da64557b6d9d9910b349455e966dd60d2299` |
| `Induction.StructuralStatement` | `Langlands.Induction.StructuralStatement` | `2379edca85c168570183f0ad2673670fbbcb16efbe4bb817ccc60893feb56185` | `eacfe34e82aab124462d814d283f6fab550ba007ec2eb83d1a1e231f5212b9fa` |
| `Induction.CompactTransitivityStatement` | `Langlands.Induction.CompactInductionTransitivityStatement` | `5f3d0e9591da3e0399df594b07ef4a269411f797ecce8e7355a77c7451dadca7` | `b433a5f7c6c07a6f71f373f7cc0539efcf1bda87edbd14463872f99a365d38bb` |
| `Induction.UnitaryStatement` | `Langlands.GLNormalizedInductionUnitarityStatement` | `af0bb472c57e9399f0554a1217d79459724f334854ad2c46330cb74275643ec4` | `c0d63ebc54631077ddc54d850cc34898e45cfae877cd1d9994682749859b92d2` |
| `Jacquet.ExactStatement` | `Langlands.SmoothCoinvariantExactnessStatement` | `40b1f46115fb5901f25d178b36a4d3dcc27a2aca9e1bf6be0f6e263238fa229f` | `90a8cfe32f709cd355ae1d6d6d737860d639611450762a72318fc3f6c0b900ed` |
| `Jacquet.AlgebraStatement` | `Langlands.Jacquet.CoinvariantAlgebraStatement` | `08710cdb6b70ccea63cca7b8ac42d3a4a7067a203859b618ce5e637093cca1cc` | `bae932f731ebe39be292ce296c230b68856bba6feb921f5aa8bd07d45f9e2c74` |
| `Jacquet.ReciprocityStatement` | `Langlands.Jacquet.CharacterReciprocityStatement` | `445906e981e46a3b46d2c5beec4bc68a0ef5a70c240a48e3ecea18de65d8dc0e` | `0d358084254d0aed456e9f41aa87d891d4f90789584f33ffa49fc077edc183b5` |
| `Jacquet.LocalizationExactnessStatement` | `Langlands.Jacquet.Localization.CharacterLocalizationExactnessStatement` | `a9522d236a6d2a3a3bdc53eb844ac00eb1fd885c1afb0f98f61fa4815673e9cc` | `f6613fe26b384516f9d4c3bd0f680af536968d4035067ffd10d664537fca52a3` |
| `Parabolic.AdmissibilityStatement` | `Langlands.Parabolic.AdmissibilityStatement` | `423f1a8a24ea8ec81088c251b7126c5f3a66ff848ddc9d64ddc12906d324c5d0` | `2a055286698a6165bdf902bfb0d502468dd64acd6afcfa6e96191cc4fda16ff2` |
| `Parabolic.ExactnessReciprocityStatement` | `Langlands.Parabolic.ExactnessReciprocityStatement` | `a4c8f132092cb78b23f940c76266bf706658d4e5e36a902c501c37a2369b9a44` | `270b94212d3cb3ffa724f93ea2a178da81d9b204f3a07412d9c51cbaa35dcb87` |
| `Parabolic.GeometricPrerequisitesStatement` | `Langlands.Parabolic.GeometricPrerequisitesStatement` | `842bdfec134e48e533c86e8ab58cd0a4630d617bfa1b2453fc2b401d9614bc76` | `4043a06afbbc476c63eea833f08c6cf5cd4325eaada6f362d718e0b2b4499641` |
| `Parabolic.NormalizedInductionStatement` | `Langlands.Parabolic.NormalizedInductionStatement` | `15c31e074841a316baf63908f17f7c0417f32f1a9918443b09ec5a4db10b78b8` | `e7d5dab09b8550a3e54ceb4852ba287e385db2b6c7d9cbeae4fa8940fa42a2ad` |
| `Parabolic.NormalizedJacquetStatement` | `Langlands.Parabolic.NormalizedJacquetStatement` | `543a1bc79063bc9ef3ad9d03e587d3491240105cec8170ba1596f297c0ff16c6` | `ac1f4c78b6182fc0b2564440c80d8acca373ed1632e748bf3eb460f13421eb41` |
| `Parabolic.NormalizedCompatibilityStatement` | `Langlands.Parabolic.NormalizedCompatibilityStatement` | `31896f590b2f394f7237e2296927410ded686ad3a2cc224d106095d0dc888f88` | `f839c9c1cc2dc5672e3b17e81905daa992313b5b46f4bdb2c8471c2e500265e5` |
| `Parabolic.OppositeDualityStatement` | `Langlands.Parabolic.OppositeDualityStatement` | `9b27288eb06958a37695c5d6cc90e41a8f88870d26e3c0e6ada87bc399410648` | `6fdd316b7f58e34331332b8ef25be2b0a691db993433c6ca973c9531d762ef75` |
| `Parabolic.RefinementTransitivityStatement` | `Langlands.Parabolic.NormalizedRefinementTransitivityStatement` | `a957a83451ece178d65dfb36aea16cc1a152ec641acecf447fd5eb2d7a0b1c94` | `506b14035be02e030e8637206e8aba3da7affd40b98d905ef0e3e6b1ce31cf95` |
| `Parabolic.NaturalFirstAdjointnessStatement` | `Langlands.Parabolic.NaturalNormalizedFirstAdjointnessStatement` | `8799052dcd437d39c5422bc191af3c73062a98d75f17dc6cace98e8dc4f82069` | `938dda4b0c6d858707cbf3890166a68e3c2cd0e00d48bcf36a48d35d58be862f` |
| `Parabolic.SecondAdjointnessStatement` | `Langlands.Parabolic.NormalizedSecondAdjointnessStatement` | `59208242514b93b66452af980212698ec06d46e293b95159a789baf6260b29d5` | `706f343cdc2b487790cfcd4c81ac3a8670b8ac541cb1bbd43d435739a312bd3a` |
| `Parabolic.NaturalInductionDualityStatement` | `Langlands.Parabolic.NaturalNormalizedInductionDualityStatement` | `e49fbdf7a6181f714b0b9c1b1f32961786a511f065812185982907c1d97c9182` | `1809cdf8b273a3e8dada77de4dd72efdd2271d633b2a8ce3b1d2ceb53628d937` |
| `Parabolic.NaturalJacquetDualityStatement` | `Langlands.Parabolic.NaturalNormalizedJacquetDualityStatement` | `7590db0ed8006906356828b0e79163e5244cf0591d5d7c4aa2e44309cf4c6f1a` | `759a81d02bb708dbd3b2315f19dae800ad10a1b6419c792efbc315c9d8eb705b` |
| `Parabolic.FiniteLengthFunctorStatement` | `Langlands.Parabolic.NormalizedParabolicFiniteLengthStatement` | `645443e03222ed9a1b41bd780770dfa51ecc8e3efd710bcf1ba4ef81de676eaa` | `60ce9be731f0771ffe22a2bdc6abcd40deda92f61a9ffb3b52d37e2f867f0de4` |
| `Parabolic.OppositeJacquetAdmissibilityStatement` | `Langlands.Parabolic.NormalizedOppositeJacquetAdmissibilityStatement` | `37f90dfe9ea02c77f1801b1687eea842c8cacccff0715aa523e493f90e7f1fba` | `f6997f3dc7608f463c5825f32e9bc926aa3292d36fbe230cd380713af6025aad` |
| `Parabolic.JacquetFiniteGenerationStatement` | `Langlands.Parabolic.NormalizedJacquetFiniteGenerationStatement` | `38357596916530bddcb902e1e0e282a083f1d9d9fddae0a2496a82b7da59aee8` | `ba87b8a2a13757c47a0863dd9e8821bc50964c388c3abe0beb378dec483d69d9` |
| `Parabolic.NormalizedInductionUnitaryCentralCharacterStatement` | `Langlands.GLNormalizedInductionUnitaryCentralCharacterStatement` | `1417d35442e88336ae5f3adad422ce84f0664de9d7bff9fb0c84719d7ee741c1` | `b0ad409ee84bff9a043f8a0f15ac2c79eecfcb1798dfcb196361d678c22d45c6` |
| `Exponents.LeviFrobeniusReciprocityStatement` | `Langlands.Aubert.General.RepresentedParabolic.LeviFrobeniusReciprocityStatement` | `8c9914a250fa5ba27d2341a581050fe39b866da8b4d825f307b918e76cfd87b9` | `45850121f22fc60b1a63eecd3711b346187885c6be0e6c042de2bf5d3a7c16f9` |
| `Exponents.LeviParabolicFunctorsExactStatement` | `Langlands.Aubert.General.RepresentedParabolic.LeviParabolicFunctorsExactStatement` | `1ea1d50819771b3a4af897943659ce5ebb27e1ebb54ea6deff63faf9bdb3b30f` | `c073453160d52f7191553efc2a88a72500eb0e47715915b3438a77d40c76b1a3` |
| `Exponents.LeviParabolicFunctorsPreserveLimitsStatement` | `Langlands.Aubert.General.RepresentedParabolic.LeviParabolicFunctorsPreserveLimitsStatement` | `2c40c116aa76b8fae950da80cca4a812206d7173a750e4cb18aecec71a73c763` | `90a676dad89f61aae974e6253613d185333c36ed8af43389b860caa198d52d22` |
| `Exponents.LeviParabolicTransitivityStatement` | `Langlands.Aubert.General.RepresentedParabolic.LeviParabolicTransitivityStatement` | `f108e172638cb2286ac10cf43f01d5003f7a6cc0aa51151eed35f2fef8edbfa4` | `19c205cda7c833635fe4ed7336f26cac6b3e7963a2aa5fc63baff734ac228502` |
| `Exponents.LeviSecondAdjointnessStatement` | `Langlands.Aubert.General.RepresentedParabolic.LeviSecondAdjointnessStatement` | `0498c7c9dd69072fc87724e0708243b9e5f2343bab7a7c968d58e012553ac3e9` | `ede0d9494ed92efcbe45f30609ac16b68f3da5e3ca4a29ea8f3818d856f131f8` |
| `Exponents.LeviJacquetContragredientStatement` | `Langlands.Aubert.General.RepresentedParabolic.LeviJacquetContragredientStatement` | `260896492b8b9824cecb8215959f922b34b1c91cf892bbd67960036834810412` | `533802d597da145a679e8d7b900349e20c62e5722380682edb780ee71ced53e5` |
| `Geometric.RepresentedGeometricLemmaStatement` | `Langlands.Aubert.General.RepresentedParabolic.RepresentedGeometricLemmaStatement` | `c251c0e867a12d090af539d6bcd03e2fe85af750bd6c2083e057b20c83c03865` | `58ec4ed175668d7f03b9a87dab948ea41aef299f23b445431787e616ced69f9c` |
| `Exponents.LeviCuspidalSupportAssociationStatement` | `Langlands.Aubert.General.RepresentedParabolic.LeviCuspidalSupportAssociationStatement` | `b2703ddefc1d5425e4f2c41fe5f3f67a1a4c9d7f9b1a346994f5a43119fa8c07` | `d2bdb50a5c2f8c49aa1059592e724d2af62825c4e3e10f5e9f5d827298419072` |
| `Exponents.LeviCuspidalSupportSurjectiveStatement` | `Langlands.Aubert.General.RepresentedParabolic.LeviCuspidalSupportSurjectiveStatement` | `d08c217cd218924e9e0dfba73734ba81f051b14c18a798499b923a100f7bfb54` | `6988bf781697eaebc9a3dd35d28943a80a873f88046ae5a9c21c52d7b419a2ba` |
| `Exponents.LeviInductionNormalizedTemperedStatement` | `Langlands.Aubert.General.RepresentedParabolic.LeviInductionNormalizedTemperedStatement` | `9ecfd230e306c15b7af75ef50743c98d072b73c83d53435286c917e778f3d38a` | `7f7992c560ca889010a48cec49375b00396f2d74d098992991ea1ab4dc96a494` |
| `Geometric.GeometricLemmaStatement` | `Langlands.Geometric.PadicGeometricLemmaTheorem` | `2f7942617b88947db2150b7ffacefd6b34267340d872995f29aeab8b79b5d58a` | `bacedb9cc0dbbb40b34b948d82af91117d7413c822c27f0a5d11c03320591eb9` |
| `Geometric.WeylStatement` | `Langlands.Geometric.PadicGeometricWeylTheorems` | `45d7e698c59e2b04a100dabbc296abcf8bb7c49bd84b669fbe3dec2e8d298389` | `79b776c818b8c27e5285e5cfc2a24dea5ae2fcf1cdd3355ab20fab18cc8366ef` |
| `Geometric.ClosedSubgroupStatement` | `Langlands.Geometric.ClosedSubgroupMackeyTheorems` | `146d56e0f5bb0465da7ee6ce9daab93684703c5a9fc8fa3d3d450de3e118c60f` | `3f024633abff72ffd7e01fecb254718357c31d17d4dd6255ff9c1d0df8f96b79` |
| `Geometric.ProductLeviGeometricLemmaStatement` | `Langlands.Geometric.PadicProductLeviGeometricLemmaTheorem` | `13efaa95fa97ea7a52e507fd35716e872af5fa23bc7c643d728ee6f2f5486a8e` | `52c502e58e399345c5d8ec525ac3b9d73ee27f0b5a67cffeaa8e91e3b7560426` |
| `CuspidalSupport.QuasicuspidalStructureStatement` | `Langlands.CuspidalSupport.PadicLeviQuasicuspidalStructureTheorems` | `7c7841d6081f80008ffe05b16bcb85d3e04e2526f0030d6350e57bf228940975` | `38bffee32a7794d86442f634d051161821f3ac34945f0b9e397adf95b36b013f` |
| `CuspidalSupport.NormalizedCuspidalInductionStatement` | `Langlands.CuspidalSupport.PadicCuspidalInductionTheorems` | `e702e01039359e8e328f3e113b642d2b3f7795bb555425414fddcd958a007a1e` | `9bf3bc29a9c5effa0ae07a501731a457a28fe24090d78a6257d1ad5c04a36269` |
| `CuspidalSupport.ProperInductionStatement` | `Langlands.CuspidalSupport.PadicProperRefinedInductionTheorem` | `388467044929d0af465abdec5acaea2d6ff7362369966f45150910dbbc4d9691` | `1ea3f9a8c759d0237a80e5fe83ad7e35de2e1df4a3eebbf6f2e3379478f739c2` |
| `CuspidalSupport.CuspidalityComparisonStatement` | `Langlands.CuspidalSupport.PadicCuspidalityComparisonTheorems` | `6eebcb9f841fcccdfafae53d677c5381f5d96724b5412f132913dddf3e2e2a24` | `cc5b60bbf12e42fba30589ab3d6c8f11ce2115be46397a385d3a2c73a43a7324` |
| `CuspidalSupport.JacquetInductionStatement` | `Langlands.CuspidalSupport.PadicQuasicuspidalJacquetTheorems` | `50b1bb4130a051c6220b65b4528302db3dfd49443e35349637c70145ce05ca7f` | `c81abe8cd83d1e27899a073c32a6015c1637b289211fd67b7049f70c9241d7e3` |
| `Classification.SupercuspidalSupportStatement` | `Langlands.GLSupercuspidalSupportStatement` | `74d4b6414bf6aa146f1b5d5936d388a6e552c2f8f8341f2da66615d3ec19364f` | `4612c57588b712324930b08abbcbc7e4df7d6913cae6718aa7de1f2c7a41b041` |
| `Classification.SupercuspidalContragredientStatement` | `Langlands.GeneralLinear.SupercuspidalContragredientStatement` | `d56c904f48439794e34a4029152063a94a19a2bfa908f15102eeb023e7971177` | `3904bee0caf97f7b1b558369b985149ed3378d57fb362b99837ca966c0b6de2b` |
| `Classification.NormalizedProductFiniteLengthStatement` | `Langlands.Classification.PadicNormalizedProductFiniteLengthTheorems` | `ad77de724ec74c75a6fd349b61119f6fa106adef2bf204f28d26c87c70ccf6b5` | `e428d95b452fadae47625d55cdd3b3ce89fc44292547de8f57c3631e982830d5` |
| `Classification.SupercuspidalProductStatement` | `Langlands.Classification.PadicSupercuspidalProductIrreducibilityTheorems` | `5c6916b78b80e072c35d6b86be0c818f05d63f63e01c7043fc3c798d33903f89` | `14b7e18a61a8f9916cddc6e86c72e4d244dd1dfa5e6ddb2932c814a05a00b517` |
| `Classification.SquareIntegrableExponentStatement` | `Langlands.GLSquareIntegrableExponentCriterionStatement` | `6602a2c0ae2d6421015a513765a4a56595d2f9cfc0e74f67aa59e63543c4f5f1` | `5f74093879bff8abf531c08df9179abd2fcd5e13e307ae78aa401e2b21e7e676` |
| `Classification.TemperedExponentStatement` | `Langlands.GLTemperedExponentCriterionStatement` | `57a85ef43394437121b6d3564a15cc1cc248c1164bea7f2e87b18380dced5068` | `cb43455b3685a74c38d6f4958be503e9c78c7c74340bf548e68667ff57ffe26e` |
| `Classification.SquareIntegrabilityStatement` | `Langlands.GLSquareIntegrabilityPrerequisitesStatement` | `e4416e6ccdc0adcb6972a59c8a7b1bcc10f7f9f3409265fb53a4d4ac503c9c1f` | `e5b653cd2582b6c699c58b901cc13e855fa99937c7059c78faabdb13bb2ea5c8` |
| `Classification.TemperedInductionStatement` | `Langlands.GLTemperedInductionPrerequisitesStatement` | `119272506a480330549a4c10c12a3cc25cc10830488c852094d7705bc989db90` | `0dc2c3c5f4eda5e797389e7d39ee4a15e052a08d805a581bcc7b33faff1ee9ea` |
| `Classification.TemperedSmoothDualityStatement` | `Langlands.Classification.PadicTemperedSmoothDualityStatement` | `190bf2056b742d24060b94b91dd2a1baf8577eb7ad5579e200aa8efaa291704a` | `5b8169e2d5e400690e112465d6b363f59bc3d7dacf332ee8e20bb730ead9947e` |
| `Classification.DiscreteSeriesJacquetStatement` | `Langlands.GLDiscreteSeriesJacquetPrerequisitesStatement` | `5b09a7d89f3fb1c93586d80094913bef3ebc3502896de8cb2614cddc9fb2ac86` | `e1aeb9625fddffe06f9b2f7a768daa2d3e539ca85eb04897c4615d3e9516d98a` |
| `Classification.TemperedSupportStatement` | `Langlands.GLTemperedDiscreteSeriesPrerequisitesStatement` | `b9bd252df661d89a93ddfbb154391e7370978a8d8e89ff03f272bf84820519b4` | `32047c7876072f552c9979e10fd8bcd8ad4224d1b32c2b7305081ac53424fdf0` |
| `Classification.CuspidalJacquetMultiplicityStatement` | `Langlands.GLCuspidalJacquetMultiplicityPrerequisitesStatement` | `0adb72d788d2ac848e510f8a6e016f2a888cdf95e65f023d60f67c248421ff1e` | `b5395e1f4a3143c89fb8ab794b7c2ae12a0832aa28b98074edb6fb1f00a4f6d0` |
| `Classification.DiscreteSeriesMultiplicityStatement` | `Langlands.GLDiscreteSeriesJacquetMultiplicityStatement` | `60e8e0deaec7c0be768c66b482bcc9417be96c981028de5077034c9d75f681b7` | `bda2f20f6d8ac5ed5a65ceac334271340c82ccf226de5c23f82572ce71ddc438` |
| `Exponents.DualJacquetStatement` | `Langlands.GLDualJacquetExponentPrerequisitesStatement` | `d9de43e187719840878aec110a196b099434c617383876f5a7db8034a41877f5` | `9d2de723ea280bca05f7ea4a87aaeac93ba8ad18aec60db24075b40519d9afb5` |
| `Exponents.WeakCriticalStatement` | `Langlands.GLWeaklyCriticalTemperedRefinementStatement` | `71180583b9177dd63c716bade4939944470d1af37b58bf7ff48d8b4015d54f9c` | `f826267bee36b5602cf4bb9597828e70f12dff80dda16e5bd84d739190cb8867` |
| `Classification.SegmentConstituentStatement` | `Langlands.Classification.PadicSegmentConstituentTheorems` | `7639f8816b3e05d00203be1a25093811a5b7d6b0b02026ade3484aa2b08c4ff3` | `cfed4fcab0337dc2870c97272b78fb18ab80759fe8efc71a83ec3bc5c2400aa3` |
| `Classification.SegmentConstituentCompatibilityStatement` | `Langlands.Classification.PadicSegmentConstituentCompatibilityTheorems` | `0efd1b50ee4894259c2fa698529ec2976494ab9d825cdd2a71b49390873b0338` | `62d19df82ed6ef5ff3e917182ae1fd361b408c1f6e4ef8af9493d9ba10a0faf7` |
| `Classification.SegmentSquareIntegrabilityStatement` | `Langlands.Classification.PadicSegmentSquareIntegrabilityTheorems` | `3d68550aa37302e968b484f4f621ae13f6f6d1533b3f8a4b139b97a0937b9d8d` | `97abbdd2e12b7716a7ac0b5fff85107ab9e46545def33ae513676d82ba494a46` |
| `Classification.TemperedBlockStatement` | `Langlands.Classification.PadicTemperedBlockTheorems` | `4ee2708e0b993d1354692206ef105448e0f72572d3bf47e8b76b7ddee781c8a4` | `ec9c746a6e2ac6ed878494c95942969aa6954c4999ead9b32ee0e162a68868bb` |
| `Classification.SegmentGenericStatement` | `Langlands.Classification.PadicSegmentGenericTheorems` | `c0080526923e45537eda625445405c47dc60b9558858aaad204c5c4dc88b5ab6` | `7e70cafedb92951167a7bca9e0cdeccc9db389024749d991df30acb95604b234` |
| `Classification.UnitaryGenericStatement` | `Langlands.Classification.PadicUnitaryGenericTheorems` | `df7dee49bd0e7d135bd0a14887d2c4615713c6bd9623933e473b2f54439cae43` | `f9ccd75675b3bc8ca19900d5fd7cf5a0a7d0e157bc9418a8d8669ad28862bfc6` |
| `Classification.MultisegmentClassificationStatement` | `Langlands.Classification.PadicMultisegmentClassificationTheorems` | `639faca64a0ed605c85b3b4629f85dcbc5da336c4a13219c854f88a9a7c7b182` | `1691e3c85c5024496e9c4621c11468423a88880450057eb7d68677b1c5d9fe5e` |
| `Classification.MultisegmentConstituentCompatibilityStatement` | `Langlands.Classification.PadicMultisegmentConstituentCompatibilityTheorems` | `2136dadf198f0c97f7656577d50d72f4b767db27382acc1b5c0e36188a5e58d8` | `a1d7be37450301f02b0ec332c9924d89c53bc3d9b1c30ca021df1e0f4497d7bb` |
| `Classification.UnitaryGenericCompatibilityStatement` | `Langlands.Classification.AllPadicUnitaryGenericCompatibilityStatement` | `743b1379e5142b26f1e867aba13b12371a2ffcc2437d3ed994a8aa6b2b531063` | `77aa1a23f065e4bf98e0d6d529a01e407f5aaf5b702c4e7b19b33d5f20aaf758` |
| `Classification.RootWeightConeStatement` | `Langlands.RootWeightConeDecompositionStatement` | `f84f4469f0469a70af06fb496c1e18d0e188228a65d38f1b101178e49db70383` | `f179363455c445779f76178d2982533623bc5d4a189148b402a2932febec42ed` |
| `Classification.ParabolicConeStatement` | `Langlands.GLParabolicRootWeightConeStatement` | `736ede21c1c33afa56f3aa067aac4c80049c5dd61be0452fcaf50e90fc3f5815` | `3f4e8755df5ca796bcb8e2b70ec859dd49b7adbb6a6406345a20dce281ee9fd3` |
| `Classification.RelativeGenericityStatement` | `Langlands.GLRelativeGenericParameterStatement` | `ec66e13bd324f131144f3101310355d42f48f988df87ad4396a47e5bf5ef3702` | `c4879f3c9d6333cc1e51f1964d11bca6072c452ae801361f41143e0bea2f8a09` |
| `Classification.RelativeJacquetMultiplicityStatement` | `Langlands.GLRelativeGenericComparisonStatement` | `6785998cba4954984bf5f15ceac15f88c0ad00f3c6891f4fd3f5405655ba866d` | `9cca876b170dd424ba180773adc291708d7cb923472de1c3d42911e4361adf72` |
| `Classification.RelativeRegularComparisonStatement` | `Langlands.GLRelativeRegularComparisonStatement` | `3d138ec42287c2fd5c28edafd1e243d4e8e355c5d7ca8a9dcd39379fa083c440` | `0b4c6187e55cd0e332ec256e7b29b3304a9a92d96e19b56503acd784119965f7` |
| `Classification.RelativeRecoveryStatement` | `Langlands.GLRelativeRecoveryStatement` | `e1e0bf0971eb7c6ac137a0643bffb5afdd349e0bc61fa7db2672fde2ef425a80` | `57b7de8faa9a1399baf9efdb678a0190f20200949164ecd6a8110ea2b1080574` |
| `Classification.RelativeCosocleMultiplicityStatement` | `Langlands.GLRelativeCosocleMultiplicityStatement` | `df537bcdcd0cd0ad55357c2eaa3a87adaa593e60ae94b37dd415f27b34916c08` | `26e54723cba3b73b5056108ecfcd7fffc26f61e87b4d9017ec220da60a44c7a3` |
| `Classification.SemistandardLanglandsStatement` | `Langlands.GLSemistandardLanglandsConjugacyStatement` | `15536b747f44470be0da67417f56bff988d73bfdb736e309ec0ecd0404354dbc` | `c0323c927f0b46a7a3c5e5f21cfd27e96f6d00ec663f26f408521f0307c848b9` |
| `Classification.MaximalConeStatement` | `Langlands.GLMaximalConeJacquetQuotientStatement` | `ed0e3da7ae9187ed3e78fda7778c82fbfb88875e478f83dfcfd1600a66b48928` | `9224576b5230418d5034aa1159ffa7db0b9ecdf9bf3dcd3daa2859098472cf83` |
| `Classification.RegularLanglandsTensorRecoveryStatement` | `Langlands.GLRegularLanglandsTensorRecoveryStatement` | `9a175b44b91a770d8ae34a258ff82c5c2beead885bb3cd9742d0ff440a2103e3` | `5e6e955259610a3307845107d7f2d3dce8252758bfd55448c523050d6fdf23a1` |
| `Classification.RegularLanglandsStatement` | `Langlands.GLRegularLanglandsQuotientStatement` | `ce6da19d4d611e50551e31edd5404f4d83d14d90a645d6d00b5cb26d26d7e352` | `c45725c3faf41a59d39c5d0b7197849226c8104d277287f0150dfe1f1b685f62` |
| `Exponents.LeviUnnormalizedParabolicStatements` | `Langlands.Aubert.General.RepresentedParabolic.LeviUnnormalizedParabolicStatements` | `2024561d4542dd3b2541267339a2216cf20f0485c8bcda6f18afadf676b27b0e` | `b216cad7d737f117e1061cd9ac82e497ac874719413d8840c32bb3099277f41d` |
| `Exponents.ArbitraryParabolicQuotientCompactStatement` | `Langlands.Aubert.General.RepresentedParabolic.ArbitraryParabolicQuotientCompactStatement` | `41ef8c9ba889b5cc01c15f82339ddee01726c1362a531dd5c6cf47653c5d931d` | `1d60bf3ab31681a2077f2ca20816eced1e72617a653a01114e9ad299d7133c84` |
| `Exponents.ArbitraryParabolicJacquetAdmissibilityStatement` | `Langlands.Aubert.General.RepresentedParabolic.ArbitraryParabolicJacquetAdmissibilityStatement` | `d6439f89b0a75bd9a5b9d3d3432c4e2bbdb8a6f6302c1b48a1941b3a6180d3d0` | `ef22a1dd61de6e38018087fdb097534ea96bc73dca943c003a41d9ca25ef97a2` |
| `Aubert.General.RationalInductionDualityStatement` | `Langlands.Aubert.General.RationalPointFamily.RationalNaturalInductionDualityStatement` | `da8be0fcc17104367e518a34ae8bc0accb6ac31e85c799b5242159b594b6b6a2` | `ff035e6b2716f6be9adf3a0ba02e1f588d60c04bec2e54d7af398420979ae595` |
| `Aubert.General.RationalJacquetDualityStatement` | `Langlands.Aubert.General.RationalPointFamily.RationalNaturalJacquetDualityStatement` | `9ee5979bc10dc770872aea6149e922a62ae923b5a5c359483c15576a0deb27e6` | `720578a315157f1f26a8125e374670efa1585943486d7c9476522dc1e920b052` |
| `Exponents.ArbitraryParabolicExponentStatement` | `Langlands.Aubert.General.RepresentedParabolic.ArbitraryParabolicExponentStatement` | `e4f3e09a282be814652bbb667bb263f3cd72554d543fc6ec04637c4cebd9e18a` | `5dbe03a119396032ac75b980c26302a61310ebe323a5ac9e6bfb3699a5201240` |
| `Exponents.LeviCuspidalEmbeddingStatement` | `Langlands.Aubert.General.RepresentedParabolic.LeviCuspidalEmbeddingStatement` | `6972ce3c52ae6a5fa3aa2989d4a981ef1bc8e88de5fc276a0ee5e600c08503f6` | `030cac2afe053bba35f051b2b84aa251130d486261f87c44f1e6f7b27f192410` |
| `Aubert.General.RationalSupercuspidalInductionFiniteLengthStatement` | `Langlands.Aubert.General.RationalPointFamily.RationalSupercuspidalInductionFiniteLengthStatement` | `6c1333737f23a47246eab8dacd979904b4118b814fb8b7ef1b053e7bd9276e89` | `591b597783a8e8863311670cd281069248f5fb66077d98a7a3eb70e109c449a6` |
| `CuspidalSupport.BernsteinDecompositionStatements` | `Langlands.CuspidalSupport.BernsteinDecompositionStatements` | `cbd7fd1f5cbb1cf2f21094da95c3cec3732a66555f2531f211f06c235c8c7c66` | `1acf9bb3a64801f90e7db23388b2e7cee97d1a504d986223b1f1bdcd01b491ca` |
