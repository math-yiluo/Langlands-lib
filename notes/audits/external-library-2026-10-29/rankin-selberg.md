# External Library audit 2026-10-29: Rankin–Selberg character contracts and proof availability

This note records verdicts for eight findings of the external Library audit
of 2026-10-29: P3-015 and P3-092 to P3-098. The source is the report registered as
`external-library-audit-2026-10-29-3987c3d` (file `FINAL_AUDIT_3987c3d.md`,
SHA256 `d9a25f35dc2d7bef0351ba0891db168b0c3cc797a281d0a9944e930fe43d5eeb`;
the entries are on its lines 78 and 192–198). Each allegation was checked
against the complete Lean declarations, their universe and instance
parameters, the paired Markdown, and the record of the corrections that
entered the Library.

## Snapshots and verdict convention

- **A** is the audited Library commit
  `3987c3d7445531c2c7f784464a3fd47061ba0865`, at which the findings were
  first verified.
- **C** is the latest comparison in this edition: Library
  `3c5f92411ab2bcef7d4e5ae82c66a7ae30ea3fdf`, where corrections N and M
  were published. The later head
  `d1abfe1f26a6fdf1d986073e68c049e12c3f6ea5`, on which this edition was
  resubmitted, differs from C only in `wiki/README.md` and an unrelated
  audit note, so every file cited here is identical at both.
- The intermediate heads are `bc8de2287e5c24972c55277b2aa9611523dfc5dc`
  (correction Q, below), `64f062d4c57e9cc6f8151bc80364bc55c16272c5`
  (correction U) and `c8ae014c2d620066bb3bf73f1183de72515b8c6c` (the base
  of N and M). All ten audited pairs are byte-identical between `64f062d4…`
  and `c8ae014c…`.

All eight findings **hold at A**. Each one concerns paired Markdown that
describes a bundled hypothesis, or an already published proof, inaccurately.
No Lean statement, definition, proof or universe was changed, and none had to
be. Every audited Lean file is byte-identical between A and C (hashes below).
A **holds** verdict describes A. It does not claim that the corrected
sentences are still defective in C.

All locations are Library-relative. `RS` abbreviates
`Langlands/Representation/RankinSelberg`, `Ind` abbreviates
`Langlands/Representation/Induction` and `Sm` abbreviates
`Langlands/Representation/Smooth`. Markdown line ranges in the verdict table
refer to A. Lean line numbers are the same in A and C.

## Per-finding ledger

The correction keys refer to the release table below.

| Finding | Verdict at A | Defective Markdown at A | Verified Lean evidence | Decision, retained boundary and status in C |
|---|---|---|---|---|
| P3-015 (a) | Holds | RS/GeneralPairGamma.md:22–26: the relation "does not assert … nontriviality of `ψ`", and consumers "must supply those hypotheses". | Every `ψ` binder in RS/GeneralPairGamma.lean (lines 26, 45, 55, 125) has type `UnitaryAdditiveCharacter`. `Langlands/HarmonicAnalysis/Basic.lean:19–23` bundles `continuous_toFun` and `nontrivial : toAddChar ≠ 1` with the circle-valued `AddChar`. | N: state that nontriviality is bundled in the type. Residue normalization and self-duality of `ν` remain unasserted consumer conditions; `1 < q` for uniqueness is kept. Repaired in C (`3c5f9241…`). |
| P3-015 (b) | Holds | RS/TwoBlockJacquetConvergenceStatement.md:62–65: "no nontriviality or conductor hypothesis is imposed here, since the self-duality of `ν` … is with respect to this same `ψ`". | The `ψ` binders at RS/TwoBlockJacquetConvergenceStatement.lean:90, 104, 123 are `UnitaryAdditiveCharacter`. | N: nontriviality comes from the type, not from self-duality. The "no conductor hypothesis" part of the sentence is accurate and is kept, as are the supplied self-dual `ν` and the absence of an existence assumption. Repaired in C (`3c5f9241…`). |
| P3-015 (c) | Holds | RS/LanglandsFactors.md:54–56: "any necessary self-duality, nontriviality, or analytic assumptions belong to proofs of the required block existence input". | The `ψ` binders at RS/LanglandsFactors.lean:26, 41, 95, 139 are `UnitaryAdditiveCharacter`. | N: drop nontriviality from that list. Self-duality and analytic block-existence assumptions remain separate. Repaired in C (`3c5f9241…`). |
| P3-092 | Holds | RS/HaarSymmetriesStatement.md:3–4 ("an unproved proposition") and 35–36 ("to be supplied by a separate proof"). | `RankinSelberg.generalLinearHaarSymmetries`, RS/HaarSymmetriesProof.lean:56, proves `GeneralLinearHaarSymmetriesStatement F n` for any `F : Type uF` with `Field`, `ValuativeRel`, `TopologicalSpace`, `IsNonarchimedeanLocalField`, any `n`, and Borel `GL_(n+1)(F)`. | U: cite the proof and record its exact type. It adds no characteristic, countability or unimodularity premise. The accurate module-local sentence at :49 ("No proof … in this statement unit") is kept. Repaired in `64f062d4…` and C. |
| P3-093 (a) | Holds | RS/MultiplicativityStatement.md:88–93: the equivalence between cleared Laurent membership and `P ∣ ∏ P_i` "is not proved in the Library". | `reciprocalLaurentSpanClearing` (RS/LaurentDivisibilityProof.lean:18) and `normalizedReciprocalLaurentSpanDivisibility` (:67), with statements in RS/LaurentDivisibilityStatement.lean. The full L polynomial has constant coefficient one (`IsPadicSymmetricLPolynomial.coeff_zero`, RS/LanglandsLFactor.lean:88). So does each block polynomial, hence their product is nonzero. | M: cite both theorems for the Laurent/divisibility equivalence. Neither proves analytic multiplicativity. Repaired in C (`3c5f9241…`). |
| P3-093 (b) | Holds | RS/MultiplicativityStatement.md:94–108: the equivalence from lower-parabolic induction to reversed upper induction "is derived here and is not proved in the Library". | `Langlands.glOppositeProductReversal` (Ind/OppositeProductReversalProof.lean:104) proves `GLOppositeProductReversalStatement.{uF,uV}`: for any supplied `T`, any block shape `B` and any family of smooth `σ i`, an equivalence `E` with `eval (E f) x = R (eval f (w * x))` for `w := B.reverseMatrix` and `R := PiTensorProduct.reindex ℂ V Fin.revPerm`, together with the inverse formula. | M: cite it with its own formula and `w`; do not identify its `w` with the Markdown's informal `w`. It proves neither Whittaker heredity nor multiplicativity. Repaired in C (`3c5f9241…`). |
| P3-094 | Holds | RS/PadicPairFactors.md:92–97: the equal-rank identities for L and ε "are not proved in the Library". | `isPadicPairLPolynomial_swap_equalRank` (RS/EqualRankFactorSwapProof.lean:105) exchanges L certificates at the same `ψ` and any supplied additive Haar `ν`, with no Whittaker-type hypothesis. `equalRankFactorSwap` (:141) proves `EqualRankFactorSwapStatement.{uF,uV,uW}`: the L, ε and γ exchanges for a supplied `SelfDualHaar` `ν`, with both representations of Whittaker type for `standardCharacter ψ n`, and independent carrier universes. | M: cite both. This is certificate exchange, not factor existence, and the ordered (2.12) definitions remain correct. Repaired in C (`3c5f9241…`). |
| P3-095 | Holds | RS/PairLFactorCharacterizationStatement.md:115–122: the countable-orbit realization argument "is not proved in the Library". | `Langlands.padicIrreducibleSmoothSmallRealization` (Sm/SmallRealizationProof.lean:150) proves `PadicIrreducibleSmoothSmallRealizationStatement.{uF,uW,uV}`: for any `T`, every irreducible smooth complex representation of `GL_n(F)` with carrier in `uW` has an equivalent irreducible smooth realization in any universe `uV`. No admissibility or smallness hypothesis is assumed. | M: cite it. Transporting the L relation across carrier universes is still open: `IsLanglandsPairLPolynomial.congr_equiv` (`Langlands/Correspondence/AutomorphicPairFactors.lean:116`) keeps `uF uV uW` fixed, and no assembled universe-independence theorem exists. The adjacent citation at :113 is also corrected, see below. Repaired in C (`3c5f9241…`). |
| P3-096 | Holds | RS/QuotientIwasawaIntegrationStatement.md:63–65 ("future proof obligations"), 86–88 ("part of the future proof") and 93–96 ("The missing analytic identity"). | `quotientIwasawaIntegration` (RS/QuotientIwasawaIntegrationProof.lean:230) proves `QuotientIwasawaIntegrationStatement F T n` for every prime, every `F : PadicField.{uF} p`, every `T` and every `n` (rank `n+1`, rank one included). It supplies `iwasawaTorusSum` (RS/IwasawaTorusSumProof.lean:296) internally. | Q: cite it. It is the ordinary-diagonal quotient formula only; ambient-group formulas, the root reparameterization, the conditional `QuotientRootIntegrationStatement` and JPSS convergence stay separate. Repaired in `bc8de22…` and C. |
| P3-097 | Holds | RS/RootCoordinateStatement.md:3–4 ("an unproved proposition") and 27–29 ("does not claim a formal proof has been supplied"). | `rootCoordinateChange` (RS/RootCoordinateProof.lean:234) proves `RootCoordinateChangeStatement F T n` for every `p`, `F`, supplied `T` and `n`. | Q: cite it. These are coordinate facts only: quotient integration and convergence are separate. The module-local Lean docstring is kept. Repaired in `bc8de22…` and C. |
| P3-098 (a) | Holds | RS/UnipotentCharacterChangeModulusStatement.md:158–165: `GLBlockModulusHaarStatement` "is itself an unproved statement". | `Langlands.glBlockModulusHaar` (`Langlands/Group/GL/BlockModulusHaarProof.lean:123`) proves `GLBlockModulusHaarStatement.{uF}`: for any block shape, any Borel Haar `μ` on the block unipotent radical and supplied `T`, `μ.map (B.leviAction m) = (T.leviModulus B m)⁻¹ • μ`. | U: cite the general inverse-modulus law and keep it distinct from the singleton case. Repaired in `64f062d4…` and C. |
| P3-098 (b) | Holds | Same file, 115–121 ("the content of a future proof") and 162–165 ("A future proof that specializes it"). | `unipotentCharacterChangeModulus` (RS/UnipotentCharacterChangeModulusProof.lean:18) proves `UnipotentCharacterChangeModulusStatement.{uF}` by specializing to `singletons (n + 1)`, with the reciprocal scalar `c⁻¹` and the original supplied `T`. The quotient law with factor `c` is the separate `characterChangeCompatibleMeasure` (RS/CharacterChangeMeasure.lean:216). | U: cite the specialization, the general law and the quotient law as three distinct results. Repaired in `64f062d4…` and C. |

## Evaluation of the report's supporting claims

- **P3-015.** The report says these interfaces "cannot accept the trivial
  character". That is correct: a term of `UnitaryAdditiveCharacter` contains a
  proof of `toAddChar ≠ 1`. It does not follow that residue normalization,
  self-duality or a conductor condition holds. The corrections keep those as
  separate conditions.
- **P3-093.** The report says the Laurent theorems "apply to the product of
  certified block polynomials because their constant terms are one". This is
  correct as stated. `normalizedReciprocalLaurentSpanDivisibility` needs
  `P.coeff 0 = 1` for the full polynomial `P` and `A ≠ 0` for `A = ∏ P_i`, and
  the constant coefficient of the product is the product of constant
  coefficients. The report's "coprimality" is the coprimality of `X` and `P`,
  which follows from `P(0) = 1`. It is what lets the normalized theorem drop
  the power `X^e` that `reciprocalLaurentSpanClearing` keeps. The reversal
  theorem's block hypotheses are `IsSmooth (σ i)` for each `i`, for any
  supplied `T`.
- **P3-095.** The report says transport of "the particular factor relations
  and test predicates" remains separate. For the factor relations this is
  correct. The test predicates, however, already transport across carrier
  universes: `isSupercuspidal_iff_of_equiv`
  (`Langlands/Representation/Classification/Supercuspidal.lean:89`),
  `isEssentiallySquareIntegrable_iff_of_equiv` (`…/Classification/Tempered.lean:260`)
  and `Langlands.isIrreducible_iff_of_equiv`
  (`…/Classification/SupercuspidalContragredientAux.lean:115`)
  each relate carriers in independent universes. What is missing is
  cross-universe transport of `IsLanglandsPairLPolynomial` and a theorem that
  assembles the argument. This qualification does not change the verdict.
- **Adjacent defect, P3-095 file.** RS/PairLFactorCharacterizationStatement.md:113
  in A attributes equivalence invariance of "the L relation" to
  `IsPadicSymmetricLPolynomial.congr_equiv`. The statement's relation is
  `IsLanglandsPairLPolynomial` (RS/PairLFactorCharacterizationStatement.lean:52, 81–82),
  whose transport is `RankinSelberg.IsLanglandsPairLPolynomial.congr_equiv`,
  with the same universes. This is not one of the assigned findings. It lies
  in an audited file and is corrected in the same correction M, which cites
  `IsLanglandsPairLPolynomial.congr_equiv` and states its fixed universes.
- **P3-096–P3-098.** Each suggested citation matches the full target type.
  None of these proofs adds a hypothesis to its statement, and none changes a
  supplied topology, measure or normalization.

No original-literature passage is in dispute: each finding concerns
Library-internal availability or hypotheses. The corrections keep the
existing source citations of their files, for example JPSS 1983 (2.12) in
PadicPairFactors and the JPSS p391–392 locators in QuotientIwasawaIntegration.

## Proof availability evidence

Every row below is a proof in the Library. Each was checked with a Lake
build, against its exact target, with its statement and inputs unchanged.

| Declaration(s) | Target statement | Publication commit |
|---|---|---|
| `generalLinearHaarSymmetries` | `GeneralLinearHaarSymmetriesStatement` | `62ea36c5cce8fa88e0b551b153b0fdc3087190e0` |
| `reciprocalLaurentSpanClearing`, `normalizedReciprocalLaurentSpanDivisibility` (in `laurentPolynomialDivisibility`) | `LaurentPolynomialDivisibilityStatement` | `53f16d09ea1bc89e5790448306e9c4cfb84e87cf` |
| `glOppositeProductReversal` | `GLOppositeProductReversalStatement` | `675c5ea015298ba25d423f84a080d595f50bf797` |
| `isPadicPairLPolynomial_swap_equalRank`, `equalRankFactorSwap` | `EqualRankFactorSwapStatement` | `7bb1a2e56d449732b59f554074fbc0278f42d7a3` |
| `padicIrreducibleSmoothSmallRealization` | `PadicIrreducibleSmoothSmallRealizationStatement` | `f9c1742752d97c488fc1a835070bf50b534f4427` |
| `quotientIwasawaIntegration` | `QuotientIwasawaIntegrationStatement` | `910a6df80701415e9aa68c646393c66ac9bc7512` |
| `rootCoordinateChange` | `RootCoordinateChangeStatement` | `a66ac48fdc88dd72538b60ed5c37db84dfa7558b` |
| `glBlockModulusHaar` | `GLBlockModulusHaarStatement` | `9488f8128fc175e4f17b08d2a86eac54056fa753` |
| `unipotentCharacterChangeModulus` | `UnipotentCharacterChangeModulusStatement` | `9ff0d4f8edaf10dd32d87468c3045da6ec3ee5c6` |
| `characterChangeCompatibleMeasure` | `CharacterChangeCompatibleMeasureStatement` | `a6c8885e0e4bfcf4ee6d5a4b9a84a6d195085302` |

In C, eight of these Lean files are byte-identical to the versions that
first entered the Library. The other two, `QuotientIwasawaIntegrationProof.lean`
and `Langlands/Group/GL/BlockModulusHaarProof.lean`, differ only because helpers
were later extracted from them. Their public theorem
headers are unchanged, and both files are byte-identical between A and C.

As an additional development check, `lean_check` was run in the Library's
Lean environment, with declaration inspection, on every declaration in the
table. Each check compiled its module
with no errors or warnings, and the only axioms reported were `propext`,
`Classical.choice` and `Quot.sound`. The eleven declarations of the first
nine rows were checked on a workspace at A (sources fingerprint
`4c34fb732aecd6e5805c1f16e3af2508b97a63048d583c434dc0adcccc588440`).
`characterChangeCompatibleMeasure` was checked later on a workspace at C
(sources fingerprint
`2841232f7286c86eb233e442670fc8d0314214f6d1e8057b486500feca632ef8`); its file
`RS/CharacterChangeMeasure.lean` is byte-identical between A and C.

| Declaration | Universe parameters |
|---|---|
| `Langlands.RankinSelberg.generalLinearHaarSymmetries` | `uF` |
| `Langlands.RankinSelberg.reciprocalLaurentSpanClearing` | none |
| `Langlands.RankinSelberg.normalizedReciprocalLaurentSpanDivisibility` | none |
| `Langlands.glOppositeProductReversal` | `uF uV` |
| `Langlands.RankinSelberg.isPadicPairLPolynomial_swap_equalRank` | `uF uV uW` |
| `Langlands.RankinSelberg.equalRankFactorSwap` | `uF uV uW` |
| `Langlands.padicIrreducibleSmoothSmallRealization` | `uF uW uV` |
| `Langlands.RankinSelberg.quotientIwasawaIntegration` | `uF` |
| `Langlands.RankinSelberg.rootCoordinateChange` | `uF` |
| `Langlands.glBlockModulusHaar` | `uF` |
| `Langlands.RankinSelberg.unipotentCharacterChangeModulus` | `uF` |
| `Langlands.RankinSelberg.characterChangeCompatibleMeasure` | `uF` |

These are private diagnostics: they add no acceptance and are not a
full-Library kernel build.

## Correction releases

Every correction is a Markdown-only change to a statement pair and its
companions, with the Lean bytes unchanged. Earlier versions N₁ and M₁ of
corrections N and M did not enter the Library; N and M are their unchanged
replacements.

| Key | Findings | Publication |
|---|---|---|
| Q | P3-096, P3-097 | `bc8de2287e5c24972c55277b2aa9611523dfc5dc` (previous head `b58bd42aee6a565b689f0f0c008506e23b1b6560`) |
| U | P3-092, P3-098 | `64f062d4c57e9cc6f8151bc80364bc55c16272c5` (previous head `bc8de2287e5c24972c55277b2aa9611523dfc5dc`) |
| N | P3-015 | `3c5f92411ab2bcef7d4e5ae82c66a7ae30ea3fdf` (previous head `cde31751c7864199419ad8fae8b7f3474639ba24`) |
| M | P3-093, P3-094, P3-095, the :113 citation and two related precisions (Scope) | `3c5f92411ab2bcef7d4e5ae82c66a7ae30ea3fdf` (previous head `cde31751c7864199419ad8fae8b7f3474639ba24`) |

Q's entry pair is `QuotientIwasawaIntegrationStatement`, and it also changes
`RS/RootCoordinateStatement.md`. U's entry pair is
`UnipotentCharacterChangeModulusStatement`, and it also changes
`RS/HaarSymmetriesStatement.md`. N's entry pair is
`TwoBlockJacquetConvergenceStatement`, and it also changes
`RS/GeneralPairGamma.md` and `RS/LanglandsFactors.md`. M's entry pair is
`MultiplicativityStatement`, and it also changes `RS/PadicPairFactors.md` and
`RS/PairLFactorCharacterizationStatement.md`. N and M both have base
`c8ae014c…`; each changes only its own four files. The full A-to-C diff of
all ten changed Markdown files was compared with these corrections: each
changed file in C matches its corrected version, and each correction reads as
summarized in the ledger.

## Scope

These corrections change documentation only. They do not prove analytic
multiplicativity, Whittaker heredity, the existence of any local factor,
cross-universe transport of the Langlands pair L relation, convergence of the
JPSS integrals, or any ambient-group Iwasawa formula. Two further claims were
checked outside the assigned findings, at
RS/MultiplicativityStatement.md:161–165 (universes) and
RS/PadicPairFactors.md:31–32 (dependence on `ψ`).

- RS/MultiplicativityStatement.md:161–165 (A) is **not changed**. It is
  accurate: the symmetric relations are invariant under equivalences into
  independent universes `uV₂`, `uW₂` (for example
  `IsPadicSymmetricLPolynomial.congr_equiv`, RS/PadicPairFactors.lean:298),
  and the Library proves no reduction of the k-block statement to fixed
  universes. `padicIrreducibleSmoothSmallRealization` covers only
  irreducible representations, not representations of Whittaker type.
- RS/PadicPairFactors.md:31–32 (A) said that the independence of
  `L(s, π × σ)` from `ψ` "is not proved in the Library". That was already too
  strong at A: `isPairLPolynomial_characterChange_canonical`
  (RS/CanonicalPairLFactor.lean:100, present at A) proves that the published
  `IsPairLPolynomial` at `unipotentQuotientHaar` and a fixed additive Haar
  measure holds for `ψ` if and only if it holds for `ψ.scale a`, `a ∈ F^×`,
  with the same polynomial. Correction M cites it and says that the module
  states no `ψ`-independence for its own relations. For the same reason, M
  rewords RS/PairLFactorCharacterizationStatement.md:146–147 (A), which said
  that the L relation "does not otherwise depend on `ψ`". The Lean relation
  takes `ψ` as a parameter: through `IsPadicSymmetricLPolynomial` of the
  standard modules it enters their Whittaker sets. No `ψ`-independence is
  stated for it.

## File fingerprints

All hashes are SHA256.

### Audited pairs

All ten audited Lean files are byte-identical between A and C.

| Pair stem | Lean in A and C | Markdown in A | Markdown in C |
|---|---|---|---|
| RS/GeneralPairGamma | `30cc69fe8a7955ac9f03715d9534dae522e632714a90fbfe81a3b2a71338de91` | `af4b7f23e0236152f60124676f0df56131ee613c04a4e757a25c4504d4ca2eef` | `6ddeeb3c881e653a6eed99b20549525b51f0c23f5a49b9ffc338fe64f538e141` |
| RS/TwoBlockJacquetConvergenceStatement | `a1655c2c8baee8f9454687c97aa0d90b4b532759da6b47e5bf9a31522781af25` | `9a3a63234a44b1e1383aab0adfeb46e8e2d8a0e31e51325670cd55fbdc8b7118` | `9950ebabd91f3a1522aa7a235ec8162de9829f136a2d54c5ae3e03ee78fac95c` |
| RS/LanglandsFactors | `1a3252c080fdfd68872233a1274c5a207cd0cba60556e14e16c238f55d8fae99` | `d61bcf57ed676819004db8b7d183ab10078891467b20f5004facf7a17f033dc3` | `8f2b5775d46dc3082746b50610bda7a1083ff582da1add274134082e008d98a7` |
| RS/HaarSymmetriesStatement | `95af1531c24540e631b8053a8b91af7a5a037c5204690e49af5aa4c8988a89a3` | `ee26641cfa9bb0d6ca362f61b872d66541937ea456ae59c0fcf403c3c3d70563` | `91076f2dd053b0f0ba9f60a8415f0f56aa0dde9ddb028a10e5f0e2ccb381b38e` |
| RS/MultiplicativityStatement | `c4c1fb2ecaf05809ef0ff815178b3646d539abddec19facf510a18ceefffa1d5` | `f7b718fd94d008bcc57942ae58da88ef9f957b62aef82ddaca1f614980193e65` | `a4959ad757e3fad5bb68b7174d084122c761c9884bcb38a735aef345504ffca2` |
| RS/PadicPairFactors | `182e30861f1d14c5bba0754bef6a1b4bcf57b22e04db516cb5bb2e20ac9e96c1` | `f4e725037a4a0580c02813c742d4c2b851d7d01cb39a3f093bea973016a724f5` | `a4b4eaed29b6117619d7fb7c66046df3fa14587f9962389885f66b5ca874d5da` |
| RS/PairLFactorCharacterizationStatement | `09ddf0e66bd5e2cb3cb6fcbf6af24e68983c9628c14f3c029695e5ff5716cc72` | `04b3ff605c1fc719edd74a233de0cbeb435ec854bc746e41e480b6127a7a5cdc` | `083d683b192f6cb3da437ba9093e2759f81f6eb1ff66c0c607e8ba40040ac715` |
| RS/QuotientIwasawaIntegrationStatement | `6e8fb52a9d3018f4a2f658283b85b4097c14f9e841bb31ba92b695a15c47998e` | `f61e9533d3e5a829f9375d20d49535f00bf66a0ed0c30e4d07a6d684f41269b6` | `e45f906166f9dc8bf1c230c062259aa1e43d81127bc8a0e29a417155672899c9` |
| RS/RootCoordinateStatement | `f69209ec91dc0c6dfe0ee061795380225991d4403b6645f93a7e06bfad7223ac` | `e6ebacbfb8761e9b47d363745cb7049a4d78910ed1f209550e16ef6fccb19f04` | `beffd78ed307f90494247b069586bc0a1539f269c53d938405cd85161b8c242f` |
| RS/UnipotentCharacterChangeModulusStatement | `7bf3b347d0ad5d8bb8ff168b8bdb2b650b7fe7121e1c19687e64d0369738d48d` | `64d76c08a2efd5fc2ee1d642769c7d804fe3f0428021c6a91fa7a994c452f268` | `3f95659eaa9a4c7720ff0cedf86a1f4a5e2b5025a3f53d8bd895055aa53503de` |

### Proof companions in C

| Pair stem | Lean SHA256 | Markdown SHA256 |
|---|---|---|
| RS/HaarSymmetriesProof | `68606f4a65ffe4e7e75cf3f30d1777f386450062cb3bb17f52724925e8482ea2` | `4fdb5aab2b839e15560a98b43981fdd40348b8e36d59ca0c5726fee6bf54e822` |
| RS/LaurentDivisibilityProof | `be147c8ac17d8de2f678110c78084ebf05031a15c4d2ea6c1689f6ec1ebd7360` | `68e2dc12cb60e0ae320451bb8648c237b9415e99db6457636e92a5b1f962d918` |
| Ind/OppositeProductReversalProof | `57dc558669b05441d7f6cac7b9543b8418369f5745427eca6c100a88a0943ca6` | `f953d878ad6b24e45d064ae1877f86f36a3f9d57b576197259109f63a2010e8e` |
| RS/EqualRankFactorSwapProof | `0fbab5c3c1bed60147fc345796f040c130a7aa70ac04e9d200c940d6dde43d9f` | `f5c71b08a28942d451e232a82de0715d172c3d0adbf9ff818254cab36aca8fba` |
| Sm/SmallRealizationProof | `6dd8d654ed7c2ad0682b3e06fd83ea20e4afe8504363470c9357cffb2ba6997d` | `0f2836876884a3846f8d2c24f590fe2bcd32b153fbb42dc69c3baa91f5c4edd4` |
| RS/QuotientIwasawaIntegrationProof | `98f0eee573e133973fec775fa2a1f46ea725132032621e60ee697ba6d6abde18` | `61af5004a64edf7b69cc5c3ca7c2897bdc173bcbfec9bf81b03ad62f888f4caa` |
| RS/RootCoordinateProof | `ac66880a0759a4d3472d249bc1fe7816908100fee9562a875003ee2a9ab75a21` | `64c3bfa192f965b72304a3ee000bbb520b7add21ebe672b3c3fb6b89fa6fd209` |
| Langlands/Group/GL/BlockModulusHaarProof | `5daca39a93292b96f2bf5f1ca3c4f8b3287175e471358478f7d8c8d5b41ff1f2` | `cc9443d85bd96b15d2af6e6a3762c39a3a7cf1da29fa962be09c371069740f9f` |
| RS/UnipotentCharacterChangeModulusProof | `f5f8d111c93f507928825c2642e141cc15ff4fb792df8cedeff87c6637b66a04` | `c56304f3165ccea3caae080fc272b9eb7870befb07c12092ea01a62f90740913` |
| RS/CharacterChangeMeasure | `62a3f27777d377b02ea0b68fb327e58aec92e5c697f84b314ca1726b4a5367cd` | `e9de3cfa5daaf43d25f0d46db3dc4e9da555c1871009e0ef48bffd00005dacdf` |
