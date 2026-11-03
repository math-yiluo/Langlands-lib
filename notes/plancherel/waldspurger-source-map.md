# Waldspurger 2003 Plancherel formula: source map

Author: Worker 249, task `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927` (revision 1).
Lean coverage below was checked against Library commit
`538f554630aa4cd24a084e698b1768d7143ba586`.

This note maps every numbered item of Waldspurger's article to its page, its
content, the items of the article it uses, and the external sources it cites.
It classifies each item for the task's structural ledger and lists the
Library declarations that currently formalize part of it. It proves nothing.
A proposition definition listed here is a statement, not a proof. Where no
declaration is listed, the item is open.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333,
DOI 10.1017/S1474748003000082. Source ID `waldspurger-2003-plancherel`,
SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`,
file `Waldspurger--La formule de Plancherel pour les groupes p-adiques
d'apres Harish-Chandra--2003.pdf` in the central library.

Page numbers are printed numbers; the PDF page is the printed page minus 234.
All eight chapters were read in full.

## Classes

The task's completion condition 1 separates four kinds of input. Each item
below gets one or more of these labels.

- **Data**: a definition or a fixed choice (groups, measures, spaces, maps).
- **Struct**: a fact about the reductive group, its subgroups, decompositions
  or measures. Such a fact may be kept as an explicit hypothesis only if it is
  external at the Renard Chapter V boundary. That decision belongs to the
  task's structural ledger, not to this note.
- **Book**: a statement the article proves. It must be proved in Lean or
  imported from a published proof. The elementary facts of I.2, which the
  article states without proof or citation, are also labeled Book.
- **Ext**: a representation-theoretic or analytic theorem that the article
  cites from another source without proof. It is not structural input. It
  must be proved, or imported from a published proof.

## External sources cited

The bibliography is on p.333 (PDF p.99). The article cites outside results at
these places:

| Citation | Where | Used for |
|---|---|---|
| [BZ, 2.12] Bernstein–Zelevinsky | I.3, p.244 | the geometric-lemma filtration of `(I_P^G V)_{P'}` |
| [C, Prop. 4.2.3, Thm 4.2.4] Casselman | Thm I.4.1, p.245 | the canonical pairing on Jacquet modules |
| [C, Thm 4.3.3] | Prop. I.4.3, p.245 | coefficients equal Jacquet coefficients on cones `P_{m,t}` |
| [BD, 2.5, 3.1] Bernstein–Deligne | I.5, p.245 | the Jacquet module and the induced representation of an admissible `B`-family are admissible `B`-families |
| [BD, Prop. 3.5.2] | I.5, p.247 | `j_P` maps `V^H` onto `V_P^{H∩M}` (B-family version of I.4.1) |
| [H, Thm 4.6; Ex. 8 p.115] Humphreys | II.2 (6), p.254 | orbit map of `Ū` is an isomorphism onto a closed image (purely inseparable in characteristic p) |
| [C, Thm 4.4.6] | Prop. III.1.1, p.263 | square integrability via exponents |
| [C, Prop. 5.2.4] | III.1 (2), (3), p.265 | Schur orthogonality and the formal degree `d(π)` |
| [B, §4.6, Prop. 9] Bourbaki EVT | III.6, p.271 | the inductive-limit topology on `C(G)` is locally convex and complete |
| [S, Thm IV.1] Sauvageot | IV.3, p.285 | generic irreducibility of `I_P^G π'`; for square-integrable `π` the article derives it from IV.2.2 instead |

The introduction (pp.235–238) also cites Harish-Chandra [HC1], [HC2] and
Silberger [Si] as background; the proofs do not use them.

## Notation and source corrections

- `γ(G|M)` and `c(G|M) = γ(G|M)^{-1} ∏_{α ∈ Σ_red(P)} γ(M_α|M)` are defined in
  I.1, p.241. On p.305 (VI.3, definition of `κ̃`) the constant is printed as
  `C(G|M)^{-2}`, with a capital C. Everywhere else, including VII.2.4 and
  VIII.1 (2), (3) on p.320, it is `c(G|M)^{-2}`. The capital is a misprint for
  the same constant `c(G|M)`.
- p.325 (proof of Prop. VIII.3.1) cites "Lemme VII.2.1" for `f_1^{(P̄)} = 0`.
  The cuspidality lemma is VIII.2.1; VII.2.1 is a proposition about `(f_ψ)^`.
- p.330 (proof of Prop. VIII.4.1) cites "Corollaire III.3.2". There is no such
  corollary (III.3.2 is a lemma about weak constant terms). The convergence
  used is Cor. VIII.3.2.

## Main targets

| Target | Page | Statement |
|---|---|---|
| Thm VII.2.5 | p.320 | `κ` is an isometry of `C^∞(Θ)_inv` onto its image in `C(G)`, and `ψ_{κ(ψ)}[O,P] = ψ[O,P]` |
| Rem. VII.2.4 | p.320 | the formulas for `κ` and the Hermitian product over association classes `Θ/ass`, with `\|Stab(O,M)\|^{-1}` |
| Thm VIII.1.1 | p.320 | `κ` is surjective; equivalently (1) finitely many `ψ_f[O,P] ≠ 0` and (2) `f = Σ c^{-2} γ^{-1} \|W^M\|\|W^G\|^{-1}\|P(M)\|^{-1} f_{ψ_f[O,P]}` |
| VIII.1 (3) | p.320 | pointwise inversion `f(g) = Σ_{Θ/ass} c(G\|M)^{-2} γ(G\|M)^{-1} \|Stab(O,M)\|^{-1} ∫_O μ(ω) d(ω) θ^G_ω(λ(g) f̌) dω` |
| Thm VIII.1.2 | p.321 | for every compact open `H`, `Θ^H_G` is finite |

The coefficient of `f_{ψ[O,P]}` in `κ̃` (VI.3, p.305) and in VIII.1 (2) is
`c(G|M)^{-2} γ(G|M)^{-1} |W^M| |W^G|^{-1} |P(M)|^{-1}`.

## Chapter I. Notation and Jacquet modules (pp.238–250)

| Item | Page | Content | Uses | Class | Lean coverage |
|---|---|---|---|---|---|
| I.1 | 238–242 | `F`, `G`, `A_0`, `M_0`, `P_0`, `Rat(G)`, `a_G`, `H_M`, roots `Σ`, `W`, special `K`; left Haar measures with `mes(H ∩ K) = 1`, the functional `∫_{H\G}` on `δ_H`-covariant functions and the integration formulas (2) (p.240); `G = P K`, Iwahori factorization, `γ(P)` depends only on `M` (proof on p.241), `c(G\|M)`, Cartan decomposition (4), `mes(KmK) ≍ δ_0(m)^{-1}` (5), the norm `‖·‖` via `τ : G → GL_n` with `τ(K) ⊆ GL_n(O)`, `σ = log‖·‖`, (6) `1 + σ(m) ≍ 1 + \|H_0(m)\|` | — | Data, Struct; `γ(P)` independence and (5) are Book | see below |
| I.2 | 242–243 | finite-dimensional `ρ(A_M)`-stable spaces `V ⊂ C^∞(A_M)`: expansion `f(a) = Σ_{χ ∈ X} χ(a) P_{χ,f}(H_M(a))` with `deg P_{χ,f} ≤ d`; for minimal `X`, polynomial growth on `A_M` ⇔ `Re χ = 0` for all `χ ∈ X`; if `∏_{χ ∈ Y} (ρ(a) − χ(a))^D` kills `V`, then `X ⊂ Y` and `d ≤ D − 1`; the same for `A_M`-finite `f` | I.1 | Book (stated without proof or citation) | none |
| I.3 | 243–244 | Jacquet functor, normalized induction `I_P^G`, filtration `F_w` of `(I_P^G V)_{P'}` | [BZ] | Data, Ext | GL_n only (see Library coverage) |
| Thm I.4.1 | 245 | Casselman pairing `⟨·,·⟩_P` on `V_P × V̌_{P̄}` | [C] | Ext | GL_n statements only |
| Cor. I.4.2 | 245 | `V̌_{P̄}` is the contragredient of `V_P` | I.4.1 | Book | none |
| Prop. I.4.3 | 245 | coefficients equal Jacquet coefficients on `M_0^+` cones | [C] | Ext | none |
| Cor. I.4.4 | 245 | polynomial growth: `\|⟨π(g)v, v̌⟩\| ≤ c‖g‖^d` | I.1 (4), I.4.3 | Book | none |
| I.5 | 245–248 | `B`-families (`B` finitely generated commutative Noetherian), contragredient, Jacquet modules, induction, exponents, rationality; analogue of I.4.1 | I.4.1, [BD, 2.5, 3.1], [BD, 3.5.2] | Data, Book, Ext | none |
| Lemme I.6.1, Prop. I.6.2 | 249–250 | `C_lisse(G)`, `ρ`, `λ`; `A_ρ = A_λ = A(G)`; constant term `f_P` of `A(G)` and `f_P^{Ind}` | I.4 | Data, Book | none |

## Chapter II. `Ξ`, `σ` and estimates (pp.250–263)

| Item | Page | Content | Uses | Class | Lean coverage |
|---|---|---|---|---|---|
| II.1 | 250–251 | `Ξ(g) = ⟨π(g)e, e⟩ = ∫_K δ_0(m_0(kg))^{1/2} dk` | I.1, I.3 | Data | `xi` (generic, see below) |
| Lemme II.1.1 | 251 | `Ξ` bi-`K`-invariant; `C_1 δ_0^{1/2} ≤ Ξ ≤ C_2 δ_0^{1/2}(1+σ)^d` on `M̄_0^+` | I.1, I.3, I.4.3 | Book | bi-invariance only: `xi_mul_mul` |
| Lemme II.1.2 | 251 | translation bound `Ξ(g_1 g g_2) ≤ C Ξ(g)(1+σ(g))^d` | I.1 (4), I.4.3, II.1.1 | Book | `xi_uniformTranslationBound` (generic, with `d = 0`; proof via II.1.3, not the article's) |
| Lemme II.1.3 | 252 | `∫_K Ξ(g_1 k g_2) dk = Ξ(g_1) Ξ(g_2)` | II.1 | Book | `integral_xi_mul_mul` (generic) |
| Lemme II.1.4 | 252 | `Ξ(g^{-1}) = Ξ(g)` | II.1 (`π ≅ π̌`) | Book | `xi_inv` (generic; `G` unimodular and `δ` the modular character of `P` as hypotheses, see below) |
| Lemme II.1.5 | 252 | `∫_G Ξ^2 (1+σ)^{-d} < ∞` for some `d` | I.1 (4)–(6), II.1.1 | Book | `CartanSquareBound.squareIntegrableWeight` (generic; the Cartan, measure, norm and II.1.1 bounds as hypotheses, see below) |
| Lemme II.1.6 | 252 | `Ξ(g) = ∫_K δ_P(m_P(kg))^{1/2} Ξ^M(m_P(kg)) dk` | II.1 | Book | `LeviData.xi_eq_integral` (generic; direct Fubini proof, not the article's induction in stages) |
| II.2 | 253–254 | algebraic representation `τ_P` with properties (1)–(5); (6) `1 + σ(ū) ≍ 1 + log‖τ_P(ū)e_1‖` | [H] | Struct, Book | none |
| Lemmes II.3.1–II.3.5 | 254–259 | estimates for `δ_P(m_P(ū))`, `σ` on `Ū` | II.2, I.1 | Book | none |
| Lemmes II.4.1–II.4.4, Prop. II.4.5 | 259–263 | integrals over `Ū`; constant term of functions bounded by `Ξ(1+σ)^{-d'}` | II.1, II.3 | Book | none (II.4.5 is the explicit hypothesis `ConstantTermEstimate` of `ConstantTerm`) |

## Chapter III. Tempered representations and `C(G)` (pp.263–276)

| Item | Page | Content | Uses | Class | Lean coverage |
|---|---|---|---|---|---|
| III.1 | 263 | square integrable modulo `A_G` | I.1 | Data | `IsSquareIntegrableModCentralSubgroup` |
| Prop. III.1.1 | 263 | square integrability via exponents | [C] | Ext | GL_n only |
| Cor. III.1.2 | 263–264 | coefficients bounded by `c Ξ(1+σ)^{-r}` on `G^1`, for every `r` | I.1 (4), I.4.3, II.1.1, III.1.1 | Book | GL_n only |
| Lemme III.1.3 | 264 | an admissible square-integrable representation is unitary and semisimple | II.1.5, III.1.2 | Book | none |
| III.1 (2), (3) | 265 | Schur orthogonality, formal degree `d(π) > 0` | [C], III.1.2, II.1.5 | Ext | none |
| Lemme III.2.1, Prop. III.2.2, Lemme III.2.3 | 265–267 | tempered representations; criteria via exponents; induction | I.2, I.3, I.4.1, I.6.1, II.1.1, II.1.2, III.1.2 | Book | GL_n only |
| Lemmes III.3.1–III.3.3 | 267–268 | weak constant terms `π^w_P` | I.3, III.1.1, III.2.2 | Book | GL_n only (III.3.1) |
| Prop. III.4.1 | 269 | an irreducible tempered representation embeds in some `I_P^G ω`, `ω ∈ E_2(M)` | III.3.2, III.3.3 | Book | none |
| Lemme III.5.1 | 269–270 | weak constant term `f^w_P` of `f ∈ A^w(G)` | III.3 | Book | none |
| III.6 | 271–272 | `C(G)`, seminorms `ν_r`, levels `C_H`, inductive-limit topology, (1), completeness, `C_c^∞(G)` dense, `G × G` acts continuously, constant term `f^{(P)}` via II.4.5 | I.6, II.1, II.1.2, II.4.5, [B] | Data, Book | generic: `C(G)`, `ν_r`, `C_H`, topology, (1), density, `G × G` continuity, completeness (`Space.completeSpace`, for a cofinal sequence of compact open subgroups), `f^{(P)}` and `C(G) → C(M)` (`constantTerm`, with II.4.5 as a hypothesis), `f^{(P),Ind}` and the diagram (`constantTermInd`, pointwise; see below) |
| Lemme III.6.1 | 271 | for `f_1, f_2 ∈ C(G)`: `∫_G f_1(h) f_2(h^{-1}g) dh` converges absolutely, `f_1 * f_2 ∈ C(G)`, and `(f_1, f_2) ↦ f_1 * f_2` is separately continuous | II.1.3–II.1.5 | Book | `Convolution` (generic; II.1.3–II.1.5 as hypotheses) |
| III.7, Prop. III.7.1, Cor. III.7.2, III.7.3 | 273–276 | `π(f)`, `θ_π(f)` continuous on `C(G)`; `E_2(G)`; orbits `O` of `Im X(G)`; polynomials on `O`; `W(G\|M)`; regular `ω`: `(I_P^G ω)^w_{P'}` semisimple | III.1.2, III.3.2, III.3.3, III.6.1 | Data, Book | orbits: `DiscreteSeriesClass`, `discreteSeriesOrbit` |

## Chapter IV. Intertwining operators (pp.276–287)

| Item | Page | Content | Uses | Class | Lean coverage |
|---|---|---|---|---|---|
| IV.1 | 276–278 | compact picture, rational families via `B`-families, `J_{P'\|P}(π)` by integrals over `U ∩ U' \ U'` | I.5 | Data | none |
| Thm IV.1.1 | 278 | convergence in a cone and rationality of `J_{P'\|P}(π ⊗ χ)` | II.3.4, II.4.2, I.4.4, I.3 | Book | none |
| IV.1 (10)–(14) | 283–284 | uniform convergence, nonvanishing, adjoint, composition, transitivity | IV.1.1 | Book | none |
| Cor. IV.1.2 | 284 | pole order at 0; for square integrable `π`, `J` regular unless `P̄` conjugate to `P` | IV.1.1 | Book | none |
| Prop. IV.2.1 | 284 | tempered: convergence for `⟨Re χ, α^∨⟩ > 0` | II.4.3 | Book | none |
| Prop. IV.2.2 | 284 | `ω` square integrable and `G`-regular: `I_P^G ω` irreducible, `J` regular and invertible | III.7.3, IV.1 | Book | none |
| IV.3 (1)–(6) | 285–287 | `j(π)`: `J_{P\|P̄} J_{P̄\|P} = j(π)`, independence of `P`, symmetries, product formula, `j ≠ 0` for square integrable | IV.1, IV.2.2, [S] (avoided for square integrable `π`) | Book | none |

## Chapter V. Weak constant terms of induced coefficients (pp.287–295)

| Item | Page | Content | Uses | Class | Lean coverage |
|---|---|---|---|---|---|
| V.1 | 287–289 | `L(ω,P)`, `E_P^G`, `W(M'\|G\|M)`, `c_{P'\|P}(s,ω)` | III.7, IV | Data | none |
| Prop. V.1.1 | 289 | weak constant terms of `E_P^G ψ` | III.3.3, III.4.1, IV.2.2, III.5.1, IV.1, IV.3 | Book | none |
| V.2, Lemme V.2.1 | 292 | `μ(ω) = j(ω)^{-1} ∏ γ(M_α\|M)^2`: rational, regular, `≥ 0`, product formula, Weyl invariant | IV.3 | Data, Book | none |
| Lemme V.2.2, Cor. V.2.3 | 293–294 | norm identity for `c_{P'\|P}(s,ω)`; regularity of `μ^G μ^{M'}(sω)^{-1} c` | V.1.1, V.2.1 | Book | none |
| V.3, Lemmes V.3.1, V.3.2 | 295 | normalized `°c_{P'\|P}(s,ω)`: regular, unitary, `E_{P'}^G(°c ψ) = E_P^G ψ`, cocycle | V.2 | Data, Book | none |

## Chapter VI. Wave packets (pp.295–313)

| Item | Page | Content | Uses | Class | Lean coverage |
|---|---|---|---|---|---|
| VI.1 | 295–296 | identifications of `L(ω,P)` along an orbit; `C^∞(O,P) = [C^∞(Im X(M)) ⊗ L_K(ω,P)]^{Stab}` | V.1 | Data | none |
| Lemmes VI.2.1–VI.2.3 | 296–301 | smoothness in `ω`; `\|E_P^G ψ_ω(g)\| ≤ C Ξ(g)`; exponential decay of the `+` part on `D_{M'}(δ)` | I.5, I.4.3, III.1.2, II.1.6, II.1.1, III.2.2 | Book | none |
| VI.3 | 301–302 | topology on `C^∞(O,P)`; measure on `O`; wave packet `f_ψ(g) = ∫_O μ(ω) (E_P^G ψ_ω)(g) dω` | VI.1 | Data | none |
| Prop. VI.3.1 | 302 | `f_ψ ∈ C(G)`, `ψ ↦ f_ψ` continuous | I.1 (4), I.4.3, I.5, VI.2, V.1.1, V.2.3, II.1.1 | Book | none |
| VI.3 | 305–306 | `Θ`, `C^∞(Θ)`, `κ̃`; invariant subspace `C^∞(Θ)_inv`; `κ`; projector | V.3 | Data | none |
| Lemme VI.3.2 | 306 | `κ̃` factors through the projector | V.3.1 | Book | none |
| Prop. VI.4.1 | 306–313 | constant terms `f_ψ^{(P'),Ind}`: zero for smaller non-conjugate Levis; explicit for `M' = M` | VI.2, V.1.1, V.2.3, III.1.2, II.3.4, II.4.3, IV.2.1 | Book | none |

## Chapter VII. Fourier transform and isometry (pp.313–320)

| Item | Page | Content | Uses | Class | Lean coverage |
|---|---|---|---|---|---|
| VII.1 | 313–314 | `f̂(ω,P) = d(ω) π(f̌)` in `L(ω,P)`; `θ^G_ω`; `(f_1,f_2)_X = ∫ conj(f_1) f_2` | III.7 | Data | `f̌` and `(f_1,f_2)_G` on `C(G)`: `L2` (generic) |
| Lemme VII.1.1 | 314 | equivariance; `(E_P^G ψ, f)_G = (ψ, f̂(ω,P))`; `E_P^G(f̂(ω,P))(g) = d(ω) θ^G_ω(λ(g) f̌)` | III.7 | Book | none |
| Lemme VII.1.2 | 315 | `f̂(ω,P) = f̂^{(P),Ind}(ω)`, where `f̂^{(P),Ind}(ω)(g_1,g_2) = [f^{(P),Ind}(g_1,g_2)]^(ω,M)` is the Fourier transform of VII.1 for `M`, applied pointwise to the induced constant term `f^{(P),Ind} : G × G → C(M)` of III.6 | III.6, VI.2.2, II.1.5, VII.1.1 | Book | none |
| Prop. VII.1.3 | 316 | `ψ_f[O,P] ∈ C^∞(O,P)`, continuous in `f` | VII.1.2, III.6, III.1.2, II.1.5 | Book | none |
| Lemme VII.1.4 | 317 | `ψ_f` is `°c`-invariant | VII.1.1, V.3.1 | Book | none |
| Prop. VII.2.1 | 317 | `(f_ψ)^(ω',P)` in terms of `ψ` | VI.4.1, VII.1.2, III.1 (2), (3) | Book | none |
| Prop. VII.2.2, Cor. VII.2.3 | 318–319 | orthogonality of wave packets for non-conjugate Levis; inner-product formula | VI.2.2, VII.1, VI.4.1, VII.2.1 | Book | none |
| VII.2 | 319 | Hermitian product on `C^∞(Θ)_inv`, positive definite, `G × G`-invariant | VII.2.2 | Data, Book | none |
| Rem. VII.2.4, Thm VII.2.5 | 320 | main targets above | VII.2.1–VII.2.3, VII.1.4 | Book | none |

## Chapter VIII. Plancherel formula (pp.320–332)

| Item | Page | Content | Uses | Class | Lean coverage |
|---|---|---|---|---|---|
| Thm VIII.1.1, VIII.1 (1)–(3) | 320 | main targets above | VII.1.1, VII.2.4, VIII.2–VIII.5 | Book | none |
| Thm VIII.1.2, Rem. VIII.1.3 | 321 | finiteness of `Θ^H_G`; finiteness of `Θ^H` by induction on semisimple rank | VIII.4.1, VIII.4.2 (proof in VIII.5) | Book | none |
| VIII.2, Lemme VIII.2.1 | 321–322 | `°f = f − κ(ψ)`; `°C(G)` = cuspidal Schwartz functions | VII.1.2, VII.2.5, III.6, VIII.1 (2) for Levis | Data, Book | none |
| Rem. VIII.2.2, Lemme VIII.2.3 | 322–323 | symmetries of `°`; `f_1 * f_2 = f_1 * °f_2` for cuspidal `f_1` | VII.2, VIII.2.1 | Book | none |
| Prop. VIII.3.1 | 323–326 | decay of `∫_G f_1(a g a^{-1}) f_2(g) dg` on `A_0^+` | II.3, II.4, II.1, VIII.2.1 | Book | none |
| Cor. VIII.3.2 | 326 | absolute convergence over `A_G\G` | VIII.3.1, I.1 (4), (5) | Book | none |
| VIII.4, Prop. VIII.4.1 | 327–330 | `p_χ`, `°C_H`; `p_χ(°C_H)` finite-dimensional | VIII.2, VIII.3.2 | Data, Book | none |
| Thm VIII.4.2 | 330 | `p_χ(°C(G)) = A_2(G)_χ` | III.1 (2), VII.2.5, VIII.2.2, VIII.2.3, VIII.4.1 | Book | none |
| VIII.5 | 331–332 | proofs of VIII.1.2 and VIII.1.1 | VII.2.5, VIII.1.3, VIII.4.1, VIII.4.2 | Book | none |

## Library coverage

The declarations below formalize parts of the article in the Library at commit
`538f5546`. The list covers the modules of this task's two executors and other
modules found by searching the Library for the article and for the reductive
data of I.1; it is not the declaration-level reuse audit of condition 7. None
proves a theorem of Chapters IV–VIII. Most work over explicit abstract data.
The modules `RationalCharacterValuation`, `LocalFieldUnits`,
`RationalImageCharacters`, `RationalImageRealPart`,
`RationalCharacterTopology`, `RationalNormKernelTopology` and `PointTopology`
are specializations to the actual rational points of a group scheme over an
actual nonarchimedean local field. The Library has the rational-point topology
on `G(F)` and the existence of a compact open subgroup of `G(F)`
(`Langlands.BruhatTits.rationalPoint_exists_compactOpenSubgroup`). It has
predicates for maximal split tori and minimal parabolic subgroups
(`IsMaximalSplitTorus`, `IsMinimalParabolicSubgroup`), Prop-valued product
predicates for a given subgroup `K` of the rational points
(`Langlands/BruhatTits/Iwasawa/PointProducts`), and the finite index of the
restriction of rational characters to a split component
(`IsSplitComponent.finiteIndex_range_characterRestrict`, Worker 1001: the
finite-index half of I.1's `Rat(G) ⊗ Q ≅ Rat(A_G) ⊗ Q`; the module
`CharacterRestrictionInjective` derives injectivity from the Prop
`CentralSplitTorusCharacterStatement`, taken as a hypothesis). It does not yet
construct the special maximal compact subgroup `K` of I.1, and it does not
prove `G = P K`, the Cartan decomposition (4), or the finite rank and full
rank of the lattice of `H_G`. For the roots and Weyl group of I.1 it has
`relativeRoots`, `relativeWeylGroup` and `relativeWeylAction` (module
`Langlands/GroupScheme/Rational/RelativeRoots`), the normalizer and centralizer
subgroup functors of `Langlands/GroupScheme/Rational/TorusNormalizer`, and the
Prop target `RelativeWeylCoxeterStatement` (statement only). Representative data for the Cartan decomposition
(`RenardUniformizerSection`, `RenardRepresentativeData`, Worker 454) and the
Prop targets `RenardLatticeComparisonStatement` and
`RenardDominantComparisonStatement` are in
`Langlands/Representation/Plancherel/`; those targets are statements only.

### General groups

Namespace `Langlands.Plancherel`, module directory
`Langlands/Representation/Plancherel/` (Worker 200 unless stated):

- `UnramifiedCharacters`: `commonNormKernel`, `unramifiedCharacters`,
  `unitaryUnramifiedCharacters` for a supplied family of positive norm
  characters (I.1, `X(G)` and `Im X(G)`).
- `UnramifiedLogarithm`: `normLog`, `normLogarithm` (I.1, the map `H_G`
  for supplied characters).
- `UnramifiedValuation`: `characterValuation`, `characterValuationImage`,
  `normKernelValuationQuotientEquiv`: integer evaluation of a supplied family
  of characters, its actual image, and the comparison of the quotient by the
  common norm kernel with that image (I.1, `H_G` and its image; Renard V.2.3).
- `RationalCharacterValuation`: `rationalNormCharacters`,
  `rationalCharacterValuation`, `rationalCommonNormKernel`,
  `rationalNormLogarithm`, `rationalCharacterValuationImage` on
  `GroupScheme.rationalPoints G` for the actual rational characters (I.1).
- `RationalImageCharacters`, `RationalImageRealPart`: characters and unitary
  characters of the actual valuation image (with the discrete topology);
  `rationalImageUnramifiedEquiv`, their identification with the unramified
  characters, assuming continuity of the valuation projection; and the real
  and unitary parts of such characters (I.1, `X(G)`, `Im X(G)` and `Re`).
- `RationalCharacterTopology`: `rationalNormContinuousCharacter`,
  `rationalOrderContinuousCharacter`, `isClosed_rationalCommonNormKernel`,
  `compactSubgroup_le_rationalCommonNormKernel` (the actual rational norm
  characters are locally constant for the rational-point topology; their common
  kernel is closed and contains every compact subgroup). Openness of the kernel
  and the comparisons with the valuation image (`...Conditional`) assume
  `NonarchimedeanGroup` and `WeaklyLocallyCompactSpace` for the rational-point
  topology.
- `RationalNormKernelTopology`: `isOpen_rationalCommonNormKernel`,
  `rationalCommonNormOpenSubgroup`, `rationalNormKernelQuotientDiscrete`,
  `rationalNormKernelQuotientContinuousEquiv`,
  `continuous_rationalValuationImageProjection`,
  `rationalCanonicalImageUnramifiedEquiv` (the same conclusions without those
  two premises, for an affine group scheme locally of finite type: the common
  norm kernel is open, the quotient by it is discrete and homeomorphic to the
  valuation image, and the characters of that image are the unramified
  characters; I.1, `H_G` and `X(G)`). Continuity of the last equivalence for
  the compact-open topologies is not claimed.
- `RationalUnramifiedCharacterTopology`:
  `rationalCanonicalImageUnramifiedContinuousEquiv`,
  `rationalCanonicalUnitaryImageUnramifiedContinuousEquiv`,
  `compactSpace_rationalUnitaryUnramifiedCharacters` (the identification of
  the unramified characters with the characters of the valuation image is a
  homeomorphism for the compact-open topologies, and the unitary unramified
  characters form a compact group; I.1, `X(G)` and `Im X(G)`).
- `LocalFieldUnits`: `fieldNormUnits`, `fieldOrderUnits` (the normalized
  absolute value and order on `F^×`).
- `FieldUnitsTopologyStatement` with its proof `fieldUnitsTopology` in
  `FieldUnitsTopologyProof` (Worker 1218): continuity and local constancy of
  these maps.
- `NormKernelTopologyStatement`: `CommonNormKernelTopologyStatement` (the
  common kernel of continuous positive characters of a nonarchimedean, weakly
  locally compact group is open and closed and contains every compact subgroup
  and the commutator subgroup). Proof `commonNormKernelTopology` in
  `NormKernelTopologyProof` (Worker 55).
- `CentralSubgroupCoefficients`: `centralQuotientProjection`,
  `IsSquareIntegrableModCentralSubgroup` (III.1, square integrable modulo a
  prescribed central subgroup). `CentralSubgroupComparisonStatement` compares
  square integrability modulo a closed central subgroup `A` with compact
  quotient in the center with square integrability modulo the center; the proof
  `centralSubgroupSquareIntegrabilityComparison` is in
  `CentralSubgroupComparisonProof` (Worker 117).
- `DiscreteSeriesOrbits`: `IsDiscreteSeriesClass`, `DiscreteSeriesClass`,
  `unramifiedTwistStabilizer`, `discreteSeriesOrbit`,
  `discreteSeriesStabilizer`, `discreteSeriesOrbitEquiv` (III.1, III.7:
  `E_2(G)` and its `Im X(G)`-orbits).

Namespace `Langlands.GroupScheme`, module
`Langlands/GroupScheme/Rational/PointTopology` (Worker 200):
`rationalPointsAffineHomeomorph` (the published rational-point topology agrees
with the evaluation topology on affine points) and
`rationalCharacterContinuousEval`, evaluation of an actual rational character
as a continuous homomorphism on rational points with that topology (I.1,
p.239).

Namespace `Langlands.HarishChandraSchwartz` (Worker 249), module directory
`Langlands/HarmonicAnalysis/HarishChandraSchwartz/`:

- `Basic`: `IsBiInvariant`, `weight`, `nu`, `levelSubmodule`,
  `schwartzSubmodule`, `Level`, `Space` with its inductive-limit topology
  `Space.topologicalSpace`, `Space.t2Space`, `Space.continuous_toFunLinear`
  (III.6 for arbitrary weights `Ξ`, `σ`; III.6 (1)).
- `Height`: `glNorm`, `height` (`σ = log‖τ(·)‖` for a supplied
  `τ : G →* GL_n(F)`), `height_mul_le`, `one_add_height_le`,
  `isCompact_height_le` (I.1, the norm and `σ`).
- `Spherical`: `IsIwasawaPair`, `iwasawaWeight`, `xi`, `xi_mul_mul`,
  `continuous_xi`, `integral_xi_mul_mul` (II.1 and Lemma II.1.3 from a
  supplied factorization `G = P K` and a positive character of `P`).
  Its Markdown records II.1.1, II.1.2, II.1.4, II.1.5 and the comparison of
  the integral formula with the matrix coefficient `⟨π(g)e, e⟩` as open
  proof obligations.
- `TestFunctions`: `ofSchwartzBruhat`, `denseRange_ofSchwartzBruhat` (the
  inclusion `C_c^∞(G) → C(G)` and its density, III.6, under explicit
  hypotheses on the weights).
- `Translations`: `Space.translate`, `Space.continuous_translate` (the
  continuous action of `G × G` on `C(G)`, III.6, with II.1.2 as an explicit
  hypothesis).
- `SphericalInverse`: `compactAverage`, `inducedPairing` (the functional of I.1
  and the pairing of I.3 on `I_P^G 1`, written as averages over `K`; their
  agreement with Waldspurger's quotient integrals is not proved), and `xi_inv`
  (Lemma II.1.4) when `G` is unimodular and `δ` is the modular character of a
  closed `P`. Both are explicit hypotheses.
- `Convolution`: `ConvolutionWeights`, `convolution` (an alias of
  `Hecke.convolutionIntegral`), `Space.convolution`,
  `Space.continuous_convolution_left`, `Space.continuous_convolution_right`
  (Lemma III.6.1: absolute convergence, closure of `C(G)` and separate
  continuity, with II.1.3, II.1.4 and II.1.5 as fields of `ConvolutionWeights`).
- `L2`: `check` (`f̌`), `pairing` (`(f_1, f_2)_G` of VII.1), `Space.check`,
  `Space.toL2`, `Space.inner_toL2` (VII.1, and the derived inclusion
  `C(G) ⊆ L^2(G)`).
- `SquareIntegrability`: `SquareIntegrableWeight` (the conclusion of Lemma
  II.1.5, `∫_G Ξ^2 (1+σ)^{-d} < ∞` for some `d`), `CartanSquareBound` and
  `CartanSquareBound.squareIntegrableWeight` (its proof from bounds that
  collect I.1 (4), the upper bound of I.1 (5), the lower bound of I.1 (6) and
  the upper bound of Lemma II.1.1, for countably many abstract cells covering
  `G` with an injective map `H` into a discrete subgroup of a
  finite-dimensional real normed space). Those bounds are hypotheses; they are
  not proved for an actual reductive group.
- `SphericalLevi`: `leviComponent`, `LeviData`, `LeviData.xi_eq_integral`
  (Lemma II.1.6 for `xi` and the function `Ξ^M` built in the same way on `M`,
  from a supplied Levi projection `P → M` and characters `δ_P`, `δ_0^M` with
  `δ_0 = δ_0^M δ_P` as hypotheses).
- `SphericalTranslation`: `UniformTranslationBound`,
  `xi_uniformTranslationBound` (Lemma II.1.2 for `xi` with `d = 0`),
  `xi_translationWeights`, `xi_convolutionWeights` (the hypotheses of
  `Translations` and `Convolution` for `xi`, the last one with Lemma II.1.5 as
  a hypothesis).
- `ConstantTerm`: `constantTerm` (`f^{(P)}` of III.6), `ConstantTermEstimate`
  (the estimate of Proposition II.4.5 for `P̄`, as a hypothesis),
  `ConstantTermData`, `Space.constantTerm` (the continuous linear map
  `C(G) → C(M)`).
- `ConstantTermInd`: `constantTermInd` (`f^{(P),Ind}` of III.6), its
  `G × G`-equivariance and transformation law, `IsConjModulus`,
  `isConjModulus_restrictCharacter` (the bridge to the Library's Haar modulus
  `HaarModulus.restrictCharacter`), `TransitivityData` and
  `TransitivityData.constantTermInd_constantTermInd` (the diagram of III.6,
  proved pointwise; the induced space `I_{P×P}^{G×G} C(M)` is not constructed).
- `Completeness`: `Space.completeSpace`, `Space.completeSpace_of_firstCountable`
  (`C(G)` is complete, III.6 via [B], when `G` has a sequence of compact open
  subgroups such that every compact open subgroup contains one of them; the
  second form takes `G` nonarchimedean, weakly locally compact and first
  countable).

Other generic modules: `Langlands.GroupScheme.Rational.Characters` (rational
characters, I.1); `Langlands/Representation/Exponents/CentralEigencharacterExtensionStatement`
(statement only, I.3).

### `GL_n`-specific work

These modules cite the article but are stated for `GL_n` over a `p`-adic or
nonarchimedean local field. They are not general-group adapters. A
specialization of the general targets to `GL_n` may reuse them.

- `Langlands/Group/GL/Cartan*`: Cartan cells and the count `mes(KmK)` (I.1 (4), (5)).
- `Langlands/Representation/Classification/`: `SquareIntegrableExponent*`,
  `ProductLeviSquareIntegrable*` (III.1, III.1.1, III.1.2);
  `TemperedExponentStatement`, `TemperedInduction*`, `TemperedSupportStatement`,
  `ProductLeviTempered*`, `InductionWeakJacquetBounds*`, `MaximalCone*`
  (III.2.2, III.2.3); `TemperedOppositeJacquetScalarLayer*` (III.3.1);
  `TemperedDiscreteSeriesIsotypic*`, `DiscreteSeriesJacquetStatement`.
- `Langlands/Representation/Exponents/`: `CoefficientExtractionStatement`,
  `JacquetEigenvector*` (I.3, I.4.1), `StrictCartanCoefficientBound*`
  (I.4.3, III.1.1, III.1.2), `TemperedDualJacquetExponentBound*` (III.2.2),
  `OppositeJacquetSubquotientInheritanceStatement` (III.3.1),
  `ExtractedCoefficientL2ObstructionStatement` (III.1).

This list records which modules cite which items. It is not the
declaration-level reuse audit of condition 7, which remains open.

## Dependency chains to the main targets

- **VII.2.5** needs VII.2.1–VII.2.3 and VII.1.4. These need VI.4.1, VII.1.2,
  III.1 (2), (3) and V.3.1. VI.4.1 needs VI.2, V.1.1, V.2.3, III.1.2, II.3.4,
  II.4.3 and IV.2.1. V needs IV.1–IV.3, III.3–III.5 and III.7. The
  wave-packet side needs VI.3.1 (Schwartz membership).
- **VIII.1.2** needs VIII.4.1 and VIII.4.2. These need VIII.2, VIII.3 (with
  II.1, II.3, II.4, I.1 (4), (5)), VII.2.5 and Schur orthogonality III.1 (2).
- **VIII.1.1** needs VIII.1.2 for all Levi subgroups (Rem. VIII.1.3),
  VIII.2.1 and VIII.4.2.
- **VIII.1 (3)** follows from VIII.1 (2) with VII.1.1 (iii) and VII.2.4.

The external inputs on these chains are [BZ] (I.3), [C] (I.4.1, I.4.3,
III.1.1, III.1 (2), (3)), [BD] (I.5), [H] (II.2) and [B] (III.6). Sauvageot
[S] is not needed for square-integrable `π`.
