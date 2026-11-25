# Henniart's numerical correspondence: a Route A program plan

This note, written on 15 November 2026, was checked against Library commit
`72480b70c88adff84a438bd7029d64ee3977469c`; what it says the Library contains is
said of that commit.

This note is a planning document. It proves nothing, and it does not decide
whether Route A is followed.
It refines Route A of the
[route study for the orbit counts](numerical-count-route-study.md), which is
cited below as "the route study". The route study compares the routes; this
note breaks Route A into a dependency-ordered program. For each step it gives a
size estimate, what the step shares with the Harris branch and with the existing
Library, and the literature still needed.

Page numbers are printed pages unless marked "PDF". For Henniart 1988 ("H88"),
printed page = PDF page + 495. For Arthur–Clozel 1989 ("AC"), printed page =
PDF page − 14. For the BDKV volume, which contains [DKV] and [De2], printed
page = PDF page − 4. Bibliography keys in brackets are those of H88.

## 1. Where the surjectivity proof stands

- The published `Langlands.Henniart.numericalOrbitReduction` proves
  `Langlands.Henniart.NumericalOrbitReductionStatement`: it derives
  `NumericalSurjectivityStatement` from two premises, each quantified over all
  primes `p` and all `K : PadicField p`. They are the orbit counts
  `NumericalOrbitCountStatement` and `Numerical.conductor K π ≠ ⊤` for every
  supercuspidal class `π`.
- The published `Langlands.Henniart.supercuspidalOrbitStratumFiniteness`
  (module `Correspondence/HenniartOrbitStratumFinitenessProof`) proves that
  every `Numerical.supercuspidalOrbitStratum K k a` is finite. This is lemma U1
  of the route study.
- The published `Langlands.Conductor.supercuspidalPadicConductorExponent`
  (module
  `Representation/Conductor/SupercuspidalPadicConductorExponentProof`) proves
  the JPSS conductor theorem for supercuspidal representations over p-adic
  fields.
- A development check outside the Library composes these. It proves the second
  premise,
  `Numerical.conductor K π ≠ ⊤`, and that `NumericalOrbitCountStatement`
  implies `NumericalSurjectivityStatement` at arbitrary universes `uK`, `uW`,
  `uV`. It compiles at commit `72480b70` with 0 errors and 0 warnings and uses
  only the standard axioms.

So the only open premise of `NumericalSurjectivityStatement` is
`NumericalOrbitCountStatement`; a search by name in the present Library finds
no proof of either. Route A
does not compute the counts. It constructs, in every rank, a numerical
injection that is also surjective. That is, the map is injective, preserves
conductors and commutes with unramified twists, as in
`Numerical.IsNumericalInjection`. Lemma U2 of the route study then gives the
counts: Weil-side finiteness transfers through the bijection from U1, and the
strata have equal `Set.ncard`. The published reduction then gives the target.
This is Henniart's own logical shape. In H88 §1.9 (p. 502) and §6.8 (pp. 520–522)
he shows that a constructed injection is surjective, then passes to an
arbitrary injection "par les raisonnements de comptage".

## 2. Conventions

Route A here means the proof of H88 Théorème 1.2 for fields of characteristic 0,
§§2–7. It excludes §8, which proves Théorème 1.2 in characteristic `p` and is
not needed for the p-adic target.

Size classes. They are estimates, calibrated on Lean module counts at commit
`72480b70`. One pair is a statement module and its proof module, of about the size of
U1 (`HenniartOrbitStratumFinitenessProof.lean`, 290 lines).

- **S**: one to three such pairs.
- **M**: about 10–40 modules. For comparison, `LocalFactor/Ramification` has
  35 Lean modules.
- **L**: about 100–300 modules. For comparison, `Representation/Conductor` (the
  JPSS conductor development) has 127 and `ClassFieldTheory/Local` has 319.
- **XL**: of the order of 1000 modules, or a new foundational area that the
  Library does not have. For comparison, `Representation/RankinSelberg` has 1086
  and `Representation/Classification` has 791.

"Harris branch" means the chain behind premise 1 (candidate existence) of the
published three-premise entry, as recorded in
[the LLC proof-route note](llc-proof-route.md). That chain runs through
`Henniart.candidateExistenceReduction`, Harris 1998 Prop. 4.8
(`Global.Harris.Proposition48ReductionStatement` with its fourteen inputs), and
the cohomological branch of Harris 1999, Thm 5.9 (see
[the Galois-family coverage note](galois-family-coverage.md)). "H4"
means the discharge stage of the global program in
[the global program coverage note](../automorphic/global-program-coverage.md)
(Arthur–Clozel III.3.1, III.4.2, III.5.1, III.6.2), which that note keeps as
sourced hypotheses until trace-formula work proves them.

## 3. The steps in dependency order

Notation as in H88: `𝒢_K(n)` is the set of irreducible `n`-dimensional Weil
classes, `𝒜_K(n)` the set of supercuspidal classes of `GL_n(K)`, `s(·)` the Swan
exponent, and `e_K` the absolute ramification index. `C_K(n, j)` is the number of
unramified-twist orbits of the representations counted in Théorème 1.3. The
steps are listed in the order of their prerequisite proofs: every step depends
only on steps listed before it. In particular, Théorème 1.9 (R10) comes before
the descent R11 that uses it, although H88 presents the descent first (§6.8)
and proves Théorème 1.9 afterwards (§7).

| Step | H88 location | Content | Depends on | Size |
| --- | --- | --- | --- | --- |
| R1 | §§4–5 (implicit) | Local fields of characteristic `p`, their Weil groups, irreducible Weil classes, Swan exponents and unramified twists | — | L |
| R2 | §§2.1–2.4, 3.1–3.4 (pp. 503–509) | Elementary Weil-side counting in any characteristic: twist stabilizers (Prop. 2.2), finiteness (Prop. 2.3), Koch's conjecture ⇔ Théorème 1.3 (§2.4), `n = 1`, `j = 0`, the reduction to `n = p^r` over tame totally ramified extensions (§3.1), Prop. 3.3 and Cor. 1.4 | R1 for characteristic `p` | M (L with Prop. 3.3) |
| R3 | §4 (pp. 509–512) | Théorème 1.3 in characteristic `p`, by Laumon's local Fourier transform | R1, R2 | XL |
| R4 | §5.1 (p. 512) | Close local fields: `C_K(n, j) = (q_K − 1) q_K^j` for p-adic `K` and `j < n e_K`, and the same for unramified `E/K` | R1, R3 | L |
| R5 | §§2.5–2.6 (pp. 504–505) | Jacquet–Langlands in characteristic 0 with conductor preservation; Zelevinsky's `St_d(ρ)` and its conductor; the `D^×` conductor `a(σ) = i + n − 1` | — | XL (JL), M (rest) |
| R6 | §2.7, first paragraph (p. 506) | Koch's count of `𝒜_D(j, ϖ_K)` ([Ko3]) | — | M–L |
| R7 | §2.8 (pp. 506–507), §5.1 Proposition (p. 512), §5.2 (p. 513) | Counting comparison: with the Weil counts for unramified `E` of degree dividing `n`, every numerical injection `𝒢⁰_K(n) → 𝒜⁰_K(n)` reaches every supercuspidal `π` with `s(π) < n e_K`. §5.2 extends the maps to all classes and defines the slope `λ(π)` | R2 (Koch's §7), R4, R5, R6 | M |
| R8 | §§6.1–6.6 (pp. 513–519) | Arthur–Clozel local cyclic base change `Ch_{L/K}` and the properties (1)–(8) of §6.1. Also its image and fibres (§§6.2–6.4), `G`-cuspidal classes, the central character in case II (§6.5, global) and transitivity (Prop. 6.6, global) | — | XL |
| R9 | §6.7 (pp. 519–520) | Slopes under base change, and a finite subextension `E` of a `Z_p`-extension making all slopes `< e_E` (Corollary) | R8 | M |
| R10 | §6.9 (p. 522) and §7 (pp. 522–542) | Théorème 1.9: compatible injections `φ_L(d)`, `φ_M(d)` for every cyclic `M/L` of prime degree, with `Ch_{M/L} ∘ φ_L(d) = φ_M(d) ∘ Res_{M/L}` | R8 and global inputs (section 4) | XL |
| R11 | §§1.9 and 6.8 (pp. 501–502, 520–522) | Théorème 1.9 ⇒ Théorème 1.2 in characteristic 0: descent along a cyclic `p`-power tower, with the counting step | R7, R8, R9, R10 | M |
| R12 | — | Lean assembly: U2, then `numericalOrbitReduction` with the conductor check of section 1 | R11 | S |

Basis of the estimates:

- R1 is L because the Library's p-adic Weil layer (`Weil/`, 103 modules)
  would need a characteristic-`p` counterpart.
- R3 is XL because its ℓ-adic sheaf theory is absent.
- R4 is L: Deligne's paper is about 40 pages and needs R1.
- R5 (JL) and R8 are XL because their proofs are global and need the simple or
  twisted trace formula, which the Library does not have (H4 keeps them as
  hypotheses).
- R6 is M–L: Koch's computation is 23 pages of explicit arithmetic.
- R10 is XL because it needs the global inputs of section 4 in addition to R8.
- The remaining steps are local arguments of a few pages each over objects that
  the Library has or that R1–R11 supply.

### R1. Characteristic-`p` local fields

R3 and R4 need Weil groups, irreducible Weil classes and Swan exponents for
local fields of characteristic `p`. The Library's numerical objects
(`Numerical.IsNumericalInjection`, `weilOrbitStratum`, …) and the local Weil
group `Weil.Local.localWeilGroup` are stated for `PadicField` only. R4 also
compares a p-adic field with a characteristic-`p` field of the same residue
field. Some Library modules are stated for every nonarchimedean local field
(`IsNonarchimedeanLocalField`, for example the JL statements and parts of
`AllField/`), but I found no Weil group of a local field of characteristic `p`.
The ported Anthropic FLT ramification definitions
(`IsLocalRing.lowerRamificationGroup`, `herbrandPhi`, `herbrandPsi` and
`upperRamificationGroup`, module
`AnthropicFLT/Definitions/Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup`)
concern a group acting on a local ring and do not depend on the characteristic.

### R2. Elementary Weil-side counting

This is H88 §§2.1–2.4 and 3.1–3.4, and [Ko2] §§5–8.

- [Ko2] (Koch 1984, now present and registered as
  `koch-1984-numerical-langlands-remarks`) contains the inputs that H88 takes
  from it. Satz 1 (§5) is finiteness, used in H88 Prop. 2.3. Satz 2 (§6) is
  independence of the uniformizer. Satz 3 (§7) is the Möbius computation used
  in H88 §2.8. Satz 4 (§8) is the reduction to `n = p^r`, used in H88 §3.1.
  Satz 5 (§9, `n = p`) is not used by H88 (H88 §3.1, Remarque 2, p. 508).
- Satz 1 needs Koch's Lemma 2. Its proof uses Koch 1977, *Classification of
  the primitive representations of the Galois group of local fields*, Invent.
  Math. 40, Theorem 2.1 and §7. That paper is missing (section 5).
- Over p-adic fields Satz 1 can be avoided. Once R10 supplies a numerical
  injection, the Weil-side strata inject into the supercuspidal strata, which
  are finite by U1. I did not check whether the characteristic-`p` count (R3)
  needs Satz 1.
- Prop. 3.3 (pp. 508–509) uses [He4] §4 (present, registered as
  `henniart-1984-epsilon-mod-roots`) and "[He2, lemma 2]" (missing). §3.4 uses
  [He1] §3 (present).
- Library inputs: local reciprocity, proved as
  `LocalClassField.commonClosureReciprocityExistence`. Upper breaks of
  irreducible Weil representations, proved as
  `Ramification.HerbrandBridge.weilIrreducibleUpperBreak`. The induction formula
  for conductors is stated as
  `Ramification.Padic.FiniteGaloisConductorInductionStatement`, but not proved.
  [Ko2] (7) is Serre's Swan-conductor formula for induced representations.

### R3. Théorème 1.3 in characteristic `p` (Laumon)

H88 §4.3 (p. 510) uses Laumon's local Fourier transform `F^(0,∞')`. It cites
"[Lm], 2.4.2.3", "[Lm], Thm. 2.4.3e", and "[Lm] 2.5.2 et 3.6.3". The published
edition in the central library (registered as `laumon-1987-fourier-weil`) has no
item (e): its Théorème 2.4.3 is organized as (i)–(iii), each with items a)–d).
The facts H88 uses are on printed p. 163 (PDF 34) of that edition. Définition
2.4.2.3 defines the transform. Théorème 2.4.3 (i) b gives rank `r + s`, preserved
Swan conductor `s`, and slopes in `[0, 1[`. Théorème 2.4.3 (i) c says that the
transform is an equivalence onto the representations of slope `< 1`. I did not
check H88's locators 2.5.2 and 3.6.3 (twist compatibility) against this edition.
H88 §4.2 compares ℓ-adic and complex representations
with finite image. Laumon's construction rests on ℓ-adic sheaves on curves,
vanishing cycles and the global Fourier transform. The Library has the
étale-cohomology foundations of the cohomological branch (see
[the Harris cohomology coverage note](harris-cohomology-coverage.md)). A search
of its Lean sources found no perverse sheaves, no ℓ-adic Fourier transform and
no vanishing cycles. This is the most remote step: it shares
nothing with the Harris branch or with H4. I did not audit Laumon's own
references.

### R4. Close local fields

Let `K` be p-adic with `e = e_K`, and `K'` of characteristic `p` with the same
residue field. H88 §5.1 (p. 512) chooses an isomorphism
`K^×/U_K^e ≅ K'^×/U_K'^e` "préservant la ramification". By [De2] (Deligne 1984,
BDKV pp. 119–157; registered as `bdkv-1984-representations-local-field`), this
determines, up to inner automorphisms, an isomorphism `G_K/G_K^e ≅ G_K'/G_K'^e`
carrying `G_K^λ/G_K^e` to `G_K'^λ/G_K'^e` for every real `λ ≤ e`. It gives a
twist-compatible bijection between the classes of Swan exponent `j < n e` on
the two sides. Together with R3 for `K'`, this gives `C_K(n, j) = (q_K − 1) q_K^j`
for `j < n e`, and the analogous formula for unramified `E/K` of degree
`d | n`. Deligne's paper works with truncated discrete valuation rings and with
categories of extensions of bounded ramification (introduction, printed
pp. 121–122, and 3.5). Of the Library's ramification theory, the bridge to Weil
representations (`LocalFactor/Ramification/Herbrand`) is stated for p-adic
fields; the ported ramification groups of R1 are not. Kazhdan's
GL-side close fields ([Ka2], with [Ho2]) enter only H88 §2.7 for fields of
characteristic `p`. Route A does not need them.

### R5. Jacquet–Langlands with conductors, and discrete series

H88 §2.6 needs the JL bijection in characteristic 0 with three properties: it
preserves ε-factors up to sign, hence conductors; it preserves central
characters; and it commutes with twists.

- The Library states the bijection, central-character compatibility and twist
  compatibility as `JacquetLanglands.JacquetLanglandsCharZeroStatement` (module
  `JacquetLanglands/Statements`). It is unproved and has no ε- or
  conductor-preservation clause. Route A needs a statement with that clause.
- [DKV] lists the equality of L-factors and of ε-factors up to sign among the
  properties of the bijection (introduction, item d, printed pp. 34–35, PDF
  38–39). It says that the ε-case is proved with the global results (B.I.j).
  The whole proof is global: DKV §A.1 (printed p. 41) says that certain local
  results can only be proved with the trace formula. So [DKV] alone covers
  characteristic 0, and Rogawski 1983 ([Ro]) is not needed for this step.
- Zelevinsky's parametrization `St_d(ρ)` of discrete series is proved in the
  Library as `Classification.segmentEssentialSquareIntegrableClassification`.
  I found no statement of the conductor formula `a(St_d(ρ))` of H88 §2.5
  (p. 505).
- The `D^×` side uses `a(σ) = i + n − 1` [GJ] (p. 505), where `i ≥ 0` is the
  least integer with `σ` trivial on `1 + P_D^i` (see R6). The Library has
  Godement–Jacquet theory for `GL_n` (`Representation/GodementJacquet`) but, as
  far as I found, nothing for `D^×`. The Library has the topology of `D^×`
  (`JacquetLanglands/DivisionUnits`).

Bushnell–Henniart 2007 (now present, registered as
`bushnell-henniart-2007-counting-discrete-series`) is a short modern account of
this GL-side comparison. Its Theorem 1 (p. 133) counts discrete series of
`GL_n(F)` with `ω(ϖ) = 1` and a `K_{j+1}`-fixed vector. The proof (§§2–4) uses
three ingredients: JL with `L`- and ε-factors preserved (Lemma 2, p. 134); the
`D^×` conductor in terms of level (Lemma 3, p. 135, from Bushnell–Fröhlich
LNM 987); and Koch's count (Lemma 1, p. 134). §§5–6 compare the conductor with
the normalized level on the GL side through Bushnell–Kutzko types. H88 counts
by conductor rather than by level, so Route A needs BH 2007 §§2–4 only as a
cross-check. That cross-check covers only Swan cutoffs divisible by `n`, because
BH 2007's level `j` corresponds to H88's Swan cutoff `nj` (see R6). BH 2007
contains no Weil-side count, so the Weil-side gap that
section 3.2 of the route study records for Route B remains.

### R6. Koch's count of `D^×` representations

H88 §2.5 (p. 505) writes `a(σ) = i + n − 1` for `σ` in `𝒜(D)`, where `i ≥ 0`
is the least integer with `σ` trivial on `1 + P_D^i`, and `s(σ) = sup(0, a(σ) − n)`.
So `s(σ) ≤ j` exactly when `σ` is trivial on `U_D^{j+1} = 1 + P_D^{j+1}`. Hence
`𝒜_D(j, ϖ_K)` is the set of irreducible representations of the finite group
`D^×/⟨ϖ_K, U_D^{j+1}⟩`, for every integer `j ≥ 0`.

`|𝒜_D(j, ϖ_K)|` is computed in Koch 1981 ([Ko3], present, registered as
`koch-1981-eisenstein-polynomial-sequences`). The "Anzahlsatz" (p. 229) counts
the irreducible representations `ρ` of `D^×/(1 + P_D^{j+1})` with `ρ(ϖ_K) = 1`
for every `j`, which is exactly this set. It is proved in §11, pp. 250–251. The
proof is explicit arithmetic in the division algebra, through Eisenstein
polynomial sequences, over 23 pages. This step is purely local and finite.

BH 2007 uses a different level parameter, and the two must be kept apart. Its
`A(D, j)` (§2, p. 134) consists of the representations with `ω(ϖ) = 1` that are
trivial on `U_D^{nj+1}`. By its Lemma 3 (p. 135), this means `f(π, ψ) ≤ nj` for
an additive character `ψ` of level one, that is, Swan exponent at most `nj`. So
BH 2007's `A(D, j)` is H88's `𝒜_D(nj, ϖ_K)`, and BH 2007 Lemma 1 (p. 134),
which counts the conjugacy classes of `D^×/⟨ϖ, U_D^{nj+1}⟩`, is Koch's count at
the cutoffs `nj` only. R6 and R7 need every Swan cutoff `j`, so they need Koch's
general count.

### R7. The counting comparison and the first surjectivity result

H88 §2.8 (p. 507) starts from injections `φ_d` for `d | n` and the formula
`C_E(d, [j/d]) = (q_K^d − 1) q_K^{d[j/d]}` for every unramified `E/K` of degree
`d | n`. From these, "il découle des calculs de [Ko2] et [Ko3]" that
`|𝒢²_K(n, j, ϖ_K)| = |𝒜_D(j, ϖ_K)|`, hence `= |𝒜²_K(n, j, ϖ_K)|` by §2.6.
So the injection of `𝒢²_K(n, j, ϖ_K)` into `𝒜²_K(n, j, ϖ_K)` built from the
`φ_d` through `St_d` is bijective, and so is each `φ_d`. H88 §5.1 applies this
with R4 to obtain the Proposition on p. 512: every numerical injection
`𝒢⁰_K(n) → 𝒜⁰_K(n)` reaches every supercuspidal `π` with `s(π) < n e_K`. H88 §5.2
extends the maps to all classes by the standard construction of [Ze] §10 and
[Rd]. For that extension the Library already has the multisegment and Langlands
classification used by
`Correspondence.fullCorrespondenceStatement_of_supercuspidalCorrespondence`. The
Lean counting step has a published template in
`Henniart.FiniteOrbitCountingStatement` (module
`Correspondence/FiniteAuxiliaryProof`) and `numericalOrbitReduction`.

### R8. Local base change

H88 §6.1 lists eight properties of `Ch_{L/K}`. It cites AC Ch. 1, Thm 6.2
(p. 51), Props. 6.8 and 6.9, Lemma 2.8, §6.3 and Lemma 6.10. H88 cites the 1986
preprint of AC. The numbers I checked (Thm 6.2, Props. 6.8 and 6.9, Lemma 6.10)
name the corresponding results of the 1989 book.

- The existence of the local lift is global. AC prove Thm 6.2 in the discrete
  case (§6.3, pp. 54–55) with the global Theorem III.3.1 and a cuspidal
  globalization obtained from the Deligne–Kazhdan simple trace formula
  (Lemma 6.5).
- H88 §6.4 (pp. 515–516) deliberately avoids AC Ch. 1, Prop. 6.6, whose proof
  uses the Chapter III results resting on the global trace formula, and argues
  instead with the pair `L`-functions of [JPS2]. The Library has the local
  Rankin–Selberg theory of [JPS2] (`Representation/RankinSelberg`).
- §6.5, case II, and Prop. 6.6 (transitivity) are proved globally. They use AC
  III, Lemma 6.4, and the proof of Thm 6.2.

### R9. Slopes under base change

H88 §6.7 bounds the slope after base change by `ψ_{M/K}(λ)`. Its Corollary
(p. 520) produces, inside a fixed `Z_p`-extension `K̃/K` with finite residue
extension, a finite `E` making all slopes `< e_E`. The only outside input is
the sentence "`K̃/K` est arithmétiquement profinie [Wi 1.2.1] donc
`Gal(K̃/K)^{λ+1}` est ouvert dans `Gal(K̃/K)`", for the fixed real `λ > 0` of
the Corollary.

In Wintenberger 1983 (registered as `wintenberger-1983-field-of-norms`), §1.2.1
(printed p. 62, PDF 5) only gives definitions: an extension `L/K` is APF if
`G_K^u G_L` is open in `G_K` for every `u ≥ −1`, and strictly APF under a
further limit condition. The assertion about `Z_p`-extensions is in §1.2.2
(same page): every Galois extension with finite residue extension whose Galois
group is a p-adic Lie group is strictly APF; in characteristic 0 this is Sen's
theorem.
H88 uses only the weaker APF property. The assertion R9 needs is therefore:

> (APF for `K̃/K`) For every real `u ≥ 0`, the upper ramification subgroup
> `Gal(K̃/K)^u` is open in `Gal(K̃/K)`. Equivalently, there is a finite
> subextension `E_0` of `K̃/K` with `Gal(E/E_0) ⊆ Gal(E/K)^u` for every finite
> subextension `E ⊇ E_0` of `K̃/K`.

H88 uses it at `u = λ + 1`.

Since `K̃/K` is abelian, this follows from local class field theory with upper
numbering, so it should be proved rather than assumed. The reciprocity map
sends `U_K^n` onto a dense subgroup of the upper group `G^n` of an abelian
extension (Serre, *Local Fields*, Ch. XV, §2, Theorem 2, printed p. 228, PDF
233; registered as `serre-1979-local-fields`). For finite abelian extensions
of p-adic fields the Library proves this as
`Langlands.LocalClassField.finiteUpperReciprocityTheorems` (module
`ClassFieldTheory/Local/UpperReciprocityProof`). My sketch of the deduction,
not checked in Lean, runs as follows. Let `n = ⌈u⌉`, so that
`Gal(E/K)^n ⊆ Gal(E/K)^u`. For a finite subextension `E` of `K̃/K`, the index of
`Gal(E/K)^n` in `Gal(E/K)` is at most `f · [U_K : U_K^n]`, where `f` is the
residue degree of `K̃/K`: the inertia group `Gal(E/K)^0` has index at most `f`,
and it is the image of `U_K`, while `Gal(E/K)^n` is the image of `U_K^n`. This
bound does not depend on `E`. Let `p^b` be the largest power of `p` that is at
most the bound, and let `E_0` be the subextension of degree `p^b` over `K`.
Since `Gal(E/K)` is a cyclic `p`-group, its subgroup `Gal(E/K)^n` then contains
`Gal(E/E_0)` whenever `E ⊇ E_0`. The ported Herbrand functions
`herbrandPhi` and `herbrandPsi` (R1) and the Herbrand bridge of
`LocalFactor/Ramification/Herbrand` are relevant to the slope bound itself.

### R10. Théorème 1.9 (H88 §7)

This step is about 20 pages of H88. Its parts and inputs are as follows.

- **Theorems A and B (§§7.2–7.6, pp. 523–526).** They give maps `ψ°(E)` on
  successions of cyclic inductions (condition (SIC), p. 523). The maps are built
  by induction on the imprimitivity index through cyclic base change (R8,
  case II of §6.5). Well-definedness is proved globally (§7.4, p. 525). The
  local Galois extension is realized at one place of a global Galois
  extension. H88 then cites "[AC], Ch. III" for the strong Artin conjecture for
  the global representation, which gives a cuspidal automorphic
  representation, and local–global compatibility of base change identifies its
  local component. Pair `L`- and ε-factors are then compared at every place
  (§7.5). The argument uses the global functional equation and the stability
  of the factors under highly ramified twists, citing [He3], [He6] and
  "[AC I], 6.10".
- **The strong Artin input.** AC III §7 is titled "The strong Artin conjecture
  for nilpotent groups" (p. 220), but its Theorem 7.1, for nilpotent Galois
  groups, does not cover (SIC). H88 §7.1 notes only that a nilpotent `P(σ)`
  implies (SIC), and (SIC) does not imply nilpotence: the two-dimensional
  irreducible representation of `S_3` is induced from a character of the
  cyclic subgroup of order 3. The result that fits is AC III, Proposition 7.2
  (p. 220). Let `E/F` be a solvable Galois extension of number fields with
  group `Γ`. Let `r` be an irreducible representation of `Γ` whose character
  lies in the `Z`-span of the characters `Ind_{Γ_0}^{Γ} χ`, where `Γ_0` has a
  subnormal series `Γ_0 ◁ Γ_1 ◁ … ◁ Γ_n = Γ` with cyclic factors and `χ` is a
  character of `Γ_0`. Then `r` is automorphic and cuspidal. Its proof (p. 221)
  applies cyclic automorphic induction (AC III, Theorem 6.2) repeatedly along
  the series and then a theorem of Jacquet–Shalika. My check, not in H88: a
  finite-image `σ` satisfying (SIC) along `E = E_0 ⊂ … ⊂ E_r` factors through
  a finite Galois group that is solvable, and it is induced from a character
  of a subgroup with such a series. Indeed, if `N` is the Galois closure of
  `E_r/E`, then `σ(W_N)` is abelian and `Gal(N/E)` is solvable. So
  Proposition 7.2 applies. Alternatively, the repeated cyclic automorphic
  induction in its proof applies directly, since `σ` is itself an iterated
  cyclic induction.
- **Clifford lemma (§7.7, p. 526).** It cites [CR] §11 A, [DH] §2 and [He2]
  §5.7 together.
- **The remaining cases (§§7.8–7.25, pp. 527–542).** Essentially ramified
  representations (§§7.8–7.11) are handled by tame cyclic descent with uniqueness
  from the central character. They are followed by compatibility with
  prime-degree base change (§§7.12–7.14) and the general case with choices
  (§§7.15–7.25).

### R11. From Théorème 1.9 to Théorème 1.2

H88 §6.8 (pp. 520–522) runs an induction on `[E : M]` down a cyclic tower
`K ⊂ M ⊂ E`, where `E` comes from R9. At `E`, R7 applies. At each step it uses
R8 and the compatible injections of Théorème 1.9 (R10), and then the counting
argument. The Lean form of the output should be the existence of a bijective
numerical injection in every rank over every p-adic field, which is stronger
than the stated `NumericalInjectionExistenceStatement`.

### R12. Lean assembly

R11 gives a bijective numerical injection in every rank. Then U2 of the route
study gives `NumericalOrbitCountStatement`, and the private composite of
section 1 gives `NumericalSurjectivityStatement`. U2 was skipped on 13 November
2026 because nothing supplied its hypothesis. In Route A it becomes the final
small step.

## 4. What the steps share with the Harris branch and the Library

| Step | Shared with the Harris branch or H4 | Existing Library objects (commit `72480b70`) |
| --- | --- | --- |
| R1, R3, R4 | Nothing | No characteristic-`p` Weil groups, no ℓ-adic Fourier transform, no perverse sheaves or vanishing cycles, no close fields. Characteristic-free ramification groups and Herbrand functions (ported from Anthropic FLT). |
| R2 | Nothing specific | `commonClosureReciprocityExistence` (proved), `weilIrreducibleUpperBreak` (proved), `finiteInertiaConductorRefinement` (proved), `FiniteGaloisConductorInductionStatement` (stated). The Deligne–Henniart local-constant modules in `LocalFactor/` may serve [He4] §4. |
| R5 | Local JL: Harris 1999 §5 uses the local correspondence in its transfer `JL(π_f)`, stated as the relation `JacquetLanglands.IsHarrisJacquetLanglandsTransfer` with no existence theorem. A proof of the local JL theorem would serve both. Route A also needs the ε/conductor clause, which the Harris branch does not use. The proof in [DKV] is global (simple trace formula). | `JacquetLanglandsCharZeroStatement` (stated, unproved, no ε clause); `segmentEssentialSquareIntegrableClassification` (proved); `Representation/GodementJacquet` for `GL_n` |
| R6 | Nothing | Nothing |
| R7 | Nothing | `numericalOrbitReduction`, `supercuspidalOrbitStratumFiniteness`, `FiniteOrbitCountingStatement` (all proved); the classification behind `fullCorrespondenceStatement_of_supercuspidalCorrespondence` |
| R8 | **Strong overlap.** The weak cyclic transfer statements of AC Ch. III are stated in `Automorphic/Unramified/CyclicTransferStatement` and `IsobaricCyclicTransferStatement`. These include `CyclicRegularInductionStatement` (AC III, Lemma 6.4 with Thm 6.2), `CyclicStableDescentStatement` (Lemma III.6.3) and `CyclicRegularOrbitLiftStatement`. They are inputs 11–13 of `Proposition48ReductionStatement`. H88 §6.5 case II uses the same Lemma III.6.4 and Thm III.6.2. Local base change itself (AC Ch. 1, §6; III.5.1) has no Library object. Harris 1999 Thm 5.9 needs base change with supercuspidal-place control (cohomological branch), and H4 lists III.5.1. One local base-change development would serve Route A, H4 and the cohomological branch. | Weak transfer definitions and statements (unproved); local Rankin–Selberg factors of [JPS2] (`Representation/RankinSelberg`) for H88 §6.4 |
| R9 | Nothing | `LocalClassField.finiteUpperReciprocityTheorems` (proved; finite abelian upper-numbering reciprocity, for the APF input); the ported characteristic-free Herbrand functions and ramification groups; the p-adic Herbrand bridge `LocalFactor/Ramification/Herbrand` |
| R10 | **Strong overlap with Henniart 2000's global machinery**, which the Harris branch feeds. The overlapping inputs are: the global Rankin–Selberg functional equation for cuspidal pairs (`Global.CuspidalPairGlobalFunctionalEquationStatement`); stability of pair factors under highly ramified twists (`RelativeWeilGroup.stableTwistPairGammaMatchStatement`, proved); globalization of local Galois data (the Library states Henniart 2000's globalization as `Global.RelativeGaloisGlobalization`, which the unproved `HenniartGlobalizationStatement` derives from Harris 1998 Prop. 4.8; H88 §7.4 needs less, namely a global Galois extension realizing a given local one at one place with the full Galois group as decomposition group); and the AC Ch. III weak transfers above. The strong Artin input that H88 §7.4 needs, AC III Prop. 7.2 (solvable Galois groups, characters spanned by inductions along subnormal cyclic series), is not stated in the Library. | The global inputs just listed; `Weil.Local` for induced and restricted Weil representations |
| R11 | Nothing | Same as R7 |
| R12 | Nothing | U1, `numericalOrbitReduction`, `supercuspidalPadicConductorExponent` (proved) |

In short, Route A shares with the Harris branch and H4 exactly its two global
steps, R8 and R10, and the local JL theorem of R5. Its Weil-side steps R1–R4
share nothing and contain the most remote item, R3.

## 5. Literature

Present in the central library and registered by this note's author on
15 November 2026, besides the sources registered for the route study:

- `koch-1984-numerical-langlands-remarks` ([Ko2], German version);
- `bushnell-henniart-2007-counting-discrete-series`;
- `laumon-1987-fourier-weil` ([Lm]);
- `bdkv-1984-representations-local-field` ([DKV] and [De2]);
- `wintenberger-1983-field-of-norms` ([Wi]);
- `henniart-1984-epsilon-mod-roots` ([He4]).

Also present: AC (`arthur-clozel-1989-base-change`), Serre's *Local Fields*
(`serre-1979-local-fields`, for R9), [Ko3]
(`koch-1981-eisenstein-polynomial-sequences`), [He3] (`henniart-1984-gl3`),
[He6] (`henniart-1986-cyclic`), [DH] (`deligne-henniart-1981-variation`),
[He1], [Ze], [Rd], [GJ], [JPS1], [JPS2], and [Ka2] and [Ho2] (used only in
H88 §2.7, so not needed).

Missing and needed by Route A:

- [He2], Henniart 1982 (Astérisque 94): Lemma 2 for Prop. 3.3 (R2), and §5.7,
  cited in §7.7 (R10) together with [DH] §2, which is present.
- Koch 1977, Invent. Math. 40, 195–216: needed only for [Ko2] Satz 1 (R2).
  Over p-adic fields it can be bypassed as explained in R2. For characteristic
  `p` this is unchecked.
- [CR], Curtis–Reiner, §11 A (Clifford theory and the vanishing of a Schur
  multiplier), cited in §§7.7 and 7.20. This is textbook material; any standard
  account would serve.

Missing and not needed by Route A:

- [Ro], Rogawski 1983: [DKV] covers characteristic 0, including ε-factors
  (R5).
- Badulescu 2000, Manuscripta Math. 101: BH 2007 cites it for Lemma 2. In
  characteristic 0, [DKV] suffices.
- [Ko1] (only [Ko2] §9 and H88 §3.1, Remarque 2), [KZ] and [Zi] (see the route
  study, §6).
- Bushnell 1987 and 1991, and Bushnell–Fröhlich 1983 and 1985: used only in
  BH 2007's level comparisons, which Route A does not need.

I did not audit the references of the four large sources (Laumon 1987, AC 1989,
[DKV], [De2]).

This updates the route study in three places:

- [Ko2] is now present.
- [Ko2] Satz 1 depends on Koch 1977, which is missing.
- BH 2007 is a GL-side count through JL, not a Weil-side source, so the
  route study's conclusion on Route B stands.

## 6. A possible order of work

This is a suggestion, not a plan of record.

1. **Statements only.** State the deep inputs as named propositions:
   - the Weil-side count for small Swan exponent over p-adic fields (the
     display in H88 §5.1, p. 512), replacing R1, R3 and R4;
   - JL in characteristic 0 with ε-factors up to sign, extending
     `JacquetLanglandsCharZeroStatement` (R5);
   - local cyclic base change with the properties of H88 §6.1, the case II
     central character and transitivity (R8);
   - and Théorème 1.9 (R10).

   R9 needs no deep premise. Its one outside input, the APF property of
   `K̃/K` stated in R9, should be derived from
   `LocalClassField.finiteUpperReciprocityTheorems`. If it is stated as a
   premise instead, it is the displayed assertion of R9, not Wintenberger's
   §1.2.1, which only contains definitions.
2. **A conditional assembly.** Prove that these propositions imply
   `NumericalSurjectivityStatement`. This covers R2 (only Koch's §7), R5 (the
   `St_d` and `D^×` conductor computations), R6, R7, R9, R11
   and R12. It is local and of size L. It needs no missing source: [Ko2] and
   [Ko3] are present. This mirrors the Library's treatment of Henniart 2000 through the
   published three-premise entry. It would isolate the deep inputs and show
   exactly which of them the surjectivity proof needs.
3. **Discharge.** Discharge the deep inputs together with the Harris branch and
   H4, where they overlap:
   - local base change with the AC Ch. III statements (inputs 11–13 of
     `Proposition48ReductionStatement`) and with H4;
   - local JL with the Harris 1999 transfer;
   - Théorème 1.9 after local base change, with AC III Prop. 7.2 (the strong
     Artin conjecture for characters spanned by inductions along subnormal
     cyclic series of a solvable group; see R10), the global Rankin–Selberg
     functional equation for cuspidal pairs and the globalization inputs.

   The Weil-side count (Laumon and close fields) is independent of everything
   else, shares nothing with the other branches, and is the most remote item.

Route A thus has four XL items on its critical path: R3, R5 (JL), R8 and R10.
Three of them are global and shared with the Harris branch or H4. One, R3, is
specific to Route A.
