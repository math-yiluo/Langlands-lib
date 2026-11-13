# Henniart's numerical correspondence: route study for the orbit counts

Author: Worker 5733, for Task 5584 (`35ad7726-c0bc-499a-ba29-69e4bc6e3c2a`).
Written on 13 November 2026 at the operator's request (message
`6f6938abca3056869e24510367034c8d`) and checked against Library commit
`4b619cdd61c537ff5ee2587fda415e0adb66e5ef`. Revised the same day after
review `0bef28ce-570f-4e2f-ab6f-475fb7bd8ae7`: the source requirements for
[Zi], [He2] and [KZ] were corrected, and section 2.4 now lists the missing
sources each goal needs.

This note compares the source routes to the published proposition
`Langlands.Henniart.NumericalOrbitCountStatement`. For each route it lists the
Library prerequisites, with exact source locations, and names every missing
source. It proves nothing, and no Lean code in it has been accepted.

Page numbers are printed pages unless marked "PDF". Source files are in
`/home/taskhub/central-library/` under the file names given in section 6.

## 1. The target and where the counts enter

Task 5584 must prove `Langlands.Henniart.NumericalSurjectivityStatement`
(module `Correspondence/HenniartNumericalStatement`): for a p-adic field `K`,
every `Numerical.IsNumericalInjection` (injective, preserving conductors,
compatible with unramified twists) from irreducible `(k+1)`-dimensional Weil
classes to supercuspidal classes of `GL_(k+1)(K)` is surjective. This is the
second assertion of Henniart 1988, Théorème 1.2, p. 498 (PDF 3).

The intended proof goes through the published reduction
`NumericalOrbitReductionStatement`: the orbit counts and finite supercuspidal
conductors imply surjectivity. Its proof task is Task 5891
(`e69d09d4-6da8-4810-886b-664574e533f8`, ready). A compiled draft exists
(Task 5584 shared draft, revision 1, `numericalOrbitReduction`). It is a
pigeonhole argument on orbit strata that uses Mathlib's
`Set.surj_on_of_inj_on_of_ncard_le` together with the published orbit criteria
`VirtualRepresentation.Weil.unramifiedOrbitClass_eq_iff` and
`VirtualRepresentation.PadicSupercuspidal.unramifiedOrbitClass_eq_iff`. The
reduction has two hypotheses:

- `NumericalOrbitCountStatement`: for every `p`, `K`, `k` and `a`, both
  `Numerical.weilOrbitStratum K k a` and
  `Numerical.supercuspidalOrbitStratum K k a` are finite, and they have the same
  `Set.ncard`. These are unramified-twist orbits of fixed rank `k + 1` that
  contain a class of Artin conductor `a`, respectively of conductor
  `firstFixedLevel = a`. This note studies this hypothesis.
- Finiteness of `Numerical.conductor K π` for every supercuspidal `π`. This
  note does not study it. Under the operator's decision of 13 November 2026,
  conductor questions stay with Task 5585
  (`5da7d945-39ed-4dcb-ace6-030fa18e4f24`) and Task 5032
  (`7b8711bf-90dc-40ae-923e-5bfecc3550b6`, the JPSS conductor theorem).

The Lean count statement does not take the form of Henniart's counts.
Henniart's Théorème 1.3 (p. 498) is a Weil-side formula,
`C_K(n, j) = (q_K − 1) q_K^j`. Here `C_K(n, j)` sums the numbers of
unramified-twist orbits of representations of dimension `d | n` with irreducible
restriction to inertia and Swan exponent `k`, where `kn ≤ dj`. Henniart's
GL-side counting compares sets with fixed central character on a uniformizer
(§§2.6–2.8, pp. 505–507). Section 5 of this note discusses how those sets
translate into the Lean orbit strata.

## 2. Route A: Henniart 1988, §§2–7, for p-adic `K`

### 2.1 Logical order

The plan is in §1.10, p. 502. For a field of characteristic 0 the steps are:

1. Prove Théorème 1.3 in characteristic `p` (§4).
2. Transfer it to small Swan conductor in characteristic 0 by close local
   fields (§5).
3. Prove Théorème 1.2 in characteristic 0 from Théorème 1.9 by Arthur–Clozel
   base change (§6).
4. Prove Théorème 1.9 (§7).

Section 2.8 (pp. 506–507) links the two theorems in both directions, and the
two directions use different sources:

- Forward, Théorème 1.3 ⇒ Théorème 1.2 (first paragraph of p. 507). Assume
  `C_E(d, [j/d]) = (q_K^d − 1) q_K^(d[j/d])` for every unramified `E` of degree
  `d | n`. Then "il découle des calculs de [Ko 2] et [Ko 3]" that the Weil-side
  set `𝒢²_K(n, j, ϖ_K)` and the `D^×`-side set `𝒜_D(j, ϖ_K)` have the same
  size. By §§2.6–2.7 this is also the size of the GL-side set
  `𝒜²_K(n, j, ϖ_K)`, so the injection built from the `φ_d` is bijective. Route
  A uses this direction (steps A4 and A5).
- Reverse, Théorème 1.2 ⇒ Théorème 1.3 (Remarque, p. 507). If every `φ_d`,
  `d | n`, is a bijection, one gets a twist-compatible bijection between
  `𝒢²_K(n, j, ϖ_K)` and `𝒜_D(j, ϖ_K)`. "Par 2.3 et 2.4 de [KZ]" this gives the
  explicit formula `C_K(n, j) = (q_K − 1) q_K^j`. This is how Théorème 1.3 in
  characteristic 0 comes last (§6.8, last paragraph, p. 521).

The reverse direction is not part of the proof of the target. It recovers
Henniart's explicit Weil-side formula only.

Route A therefore proves the target directly, without the Lean counts. The
counts are still a natural intermediate. In §6.8 (pp. 520–521) Henniart shows
that the injection he constructs reaches every class of bounded slope. He then
passes to an arbitrary injection ("Par les arguments de comptage du paragraphe
4, il découle alors que l'hypothèse de récurrence est vraie pour L"), which is
the counting step that `NumericalOrbitReductionStatement` formalizes. A
similar remark ends §1.9, p. 502. In Lean terms:
a conductor-preserving, twist-compatible bijection in every rank gives the
orbit counts (unit U2, section 7), and Task 5891 then gives the target.

### 2.2 Steps, sources and prerequisites

| Step | Henniart 1988 | Sources it uses | Library |
| --- | --- | --- | --- |
| A1. Reduction to `n = p^r` over tame, totally ramified extensions; `n = 1` by local class field theory; `j = 0` | §3.1, p. 507; §3.2, p. 508 | [Ko2] (missing) for the reduction. The finiteness of `C_K(n, j)` (Prop. 2.3, p. 504) also uses [Ko2] Satz 1. Local class field theory. | Local reciprocity proved: `LocalClassField.commonClosureReciprocityExistence` (`ClassFieldTheory/Local/CommonClosureExistenceProof`). Koch's reduction: nothing. |
| A2. Prop. 3.3 (Swan exponent divisible by the dimension) and Cor. 1.4 | §3.3, pp. 508–509; §3.4, p. 509 | Henniart's own proof of Prop. 3.3 uses [He4] §4 (Henniart 1984, present) and "on raisonne alors exactement comme dans [He2, lemma 2]" (p. 509; Henniart 1982, missing). §3.4 uses [He1] §3 (Henniart 1980, present). The proposition is "pour l'essentiel due à E.-W. Zink ([Zi], 2.3.5)", but Henniart gives "une preuve différente", so [Zi] is not needed. | Nothing |
| A3. Théorème 1.3 in characteristic `p` | §4.3, pp. 510–511 (Prop. 4.3, p. 511); §4.4, p. 511 | Laumon's local Fourier transform `F^(0,∞')`: [Lm] 2.4.2.3, Thm 2.4.3(e), 2.5.2, 3.6.3; comparison of complex and ℓ-adic representations (§4.2) | Nothing. No ℓ-adic local Fourier transform. The numerical statements are stated over `PadicField` only, while this step needs local fields of characteristic `p` and their Weil groups. |
| A4. GL-side count | §2.5, pp. 504–505; §2.6, p. 505; §2.8, pp. 506–507 | Zelevinsky's `St_d(ρ)` [Ze]; Jacquet–Langlands [DKV] (and [Ro], missing) in characteristic 0, which preserves ε-factors and hence conductors; `a(σ) = j + n − 1` for `D^×` [GJ]; Koch's count of `D^×` representations [Ko3] = Koch 1981 ("Anzahlsatz", stated p. 229, proved §11, pp. 250–251); the computations of [Ko2] and [Ko3] in the forward direction of §2.8 (p. 507). [KZ] is not used here: it enters only the reverse direction (section 2.1). | JL: `JacquetLanglands.JacquetLanglandsCharZeroStatement` (`JacquetLanglands/Statements`), unproved, with no ε- or conductor-preservation clause. Zelevinsky: the segment and discrete-series statements listed in [GL_n classification coverage](gln-classification-coverage.md). `D^×` levels and Koch's count: nothing. |
| A5. Close local fields; surjectivity for Swan exponent `< n e_K` | §5.1, p. 512 (Proposition); §5.2, p. 513 (extension to all classes and slopes, [Ze] §10, [Rd]) | Deligne [De2] (in BDKV 1984, pp. 119–157): `G_K/G_K^e ≅ G_K'/G_K'^e`, compatible with ramification; A3 for `K'`; the §2.8 argument (A4) | Nothing for close fields. Upper breaks: `Ramification.HerbrandBridge.weilIrreducibleUpperBreak` (`LocalFactor/Ramification/Herbrand/WeilBreakProof`, proved), which gives the single break of an irreducible representation behind the slope `λ(σ) = s(σ)/n` of §2.1, p. 503. |
| A6. Local cyclic base change and its properties | §6.1–6.6, pp. 513–519 | [AC] I.6.2, 6.4, 6.8, 6.9, Lemma 2.8, 6.3 (as listed in §6.1); pair L-factors [JPS2] (§6.4); central character in case II by a global argument, [AC] III Lemma 6.4 and the proof of Thm 6.2 (§6.5, p. 518); compatibility with parabolic induction and transitivity, Prop. 6.6 (pp. 518–519, global) | No local base change object. See the Arthur–Clozel III.5.1 row of [global statement coverage](global-statement-coverage.md): "Not started; local base change has no Library object". The global weak transfers `Automorphic.Unramified.CyclicTransferStatement` and `IsobaricCyclicTransferStatement` are stated but unproved. |
| A7. Slopes under base change; `Z_p`-extension | §6.7, pp. 519–520 (Prop. and Cor.) | Wintenberger [Wi] 1.2.1 (APF extensions) | Nothing |
| A8. Théorème 1.9 ⇒ Théorème 1.2 in characteristic 0 | §6.8, pp. 520–521 | A5–A7; descent along a cyclic `p`-power tower; the counting step | Counting step: Task 5891 (draft) and the generic `Henniart.FiniteOrbitCountingStatement` (proved in `Correspondence/FiniteAuxiliaryProof`) |
| A9. Théorème 1.9 (compatible injections `φ_L`, `φ_M`) | §6.9, p. 522 (sketch); §7, pp. 522–542 | Successive cyclic inductions (Thm A, §7.2; Thm B); strong Artin conjecture for solvable extensions [AC] III (§7.4); pair L- and ε-factors by global functional equations (§7.5); general case §§7.7–7.25. The Clifford-theory step of §7.7 (p. 526) cites [CR] §11 A, [DH] §2 and [He2] §5.7 together; [DH] (Deligne–Henniart 1981) is present. | Nothing |

### 2.3 Assessment

Of the sources I read, Route A is the only complete chain that does not go
through a full local Langlands correspondence. It needs four large developments with no
Library object:

- Laumon's ℓ-adic local Fourier transform over function fields;
- Deligne's close local fields;
- Arthur–Clozel local base change, including its global trace-formula proof;
- Henniart's construction in §7, which is itself global.

It also needs the Jacquet–Langlands correspondence in characteristic 0 with
conductor preservation ([DKV] is present; [Ro], cited with it, is missing).
Two further missing papers are used in the proof of Théorème 1.2 itself:

- [Ko2]: the reduction to `n = p^r` (A1), the finiteness Prop. 2.3, and the
  computations in the forward direction of §2.8 (A4);
- [He2], Lemma 2: an argument that the proof of Prop. 3.3 (A2) cites without
  repeating it.

[Zi] is not needed: H88 attributes Prop. 3.3 to Zink but proves it differently.
[KZ] is not needed for Théorème 1.2 either. It is used only for the reverse
direction, which recovers the explicit formula of Théorème 1.3 (section 2.4).

### 2.4 Which sources each goal needs

| Goal | Missing sources it needs |
| --- | --- |
| Théorème 1.2 for p-adic `K` by Route A (the target) | [Ko2] and [He2] (Lemma 2); possibly [Ro], which H88 cites with the present [DKV]. The main cited sources of the four developments above (Laumon 1987, BDKV 1984, Arthur–Clozel 1989, H88 §7) are present; I did not audit their own references. |
| Lean orbit counts, given a bijective numerical injection in every rank (units U1 and U2, section 7) | None. U1 uses only Library results. U2 uses the bijection, U1, and the fact that each irreducible Weil class has exactly one Artin conductor (Library status unchecked). |
| Henniart's explicit Weil-side formula, Théorème 1.3, in characteristic 0 (not needed for the target) | [KZ] 2.3 and 2.4, applied to Théorème 1.2 in every rank `d` dividing `n` (§2.8 Remarque, p. 507) |

## 3. Route B: explicit counts on both sides

The idea is to compute both sides of `NumericalOrbitCountStatement`
independently of any injection.

### 3.1 GL side

B1, through Bushnell–Kutzko types (Bushnell–Kutzko 1993):

- (6.2.1), p. 202: if an irreducible supercuspidal representation contains a
  simple type, the `𝔬_E`-order attached to the type is maximal.
- (6.2.2), p. 203: when that order is maximal, every irreducible
  representation containing the type is supercuspidal and equals
  `c-Ind(Λ : E^×J, G)` for a unique extension `Λ`.
- (6.2.3), p. 204: the equivalent conditions for maximality. The
  representations containing the type form one unramified-twist orbit.
- (6.2.4) and (6.2.5), pp. 204–205: a supercuspidal representation contains
  only one simple type up to conjugacy. The unramified twists fixing `π` are
  those of order dividing `N/e(E|F)`.
- (8.4.1), p. 297: exhaustion, that is, every irreducible supercuspidal
  representation contains a simple type. It is unique up to conjugacy, and
  `π` is induced from an extension of it. Part (iii) treats the types of
  the form (5.5.10)(b), trivial on `U^1` of a principal order.
- (8.4.2) and (8.4.3), p. 298.

The 1993 book has no conductor formula. The formula
`f(σ, ψ) = n(1 + c(ψ) + m/e)` (with `n = 1` unramified excepted) is quoted in
Bushnell–Henniart–Kutzko 1998 (JAMS 11), (6.1.2), §6.1, p. 721 (PDF 19). It is
cited there from Bushnell 1987, which is missing.

To compare that formula with the Lean `Numerical.conductor`
(`firstFixedLevel`), two further inputs are needed:

- JPSS 1981, Théorème 5.1: `Conductor.ConductorExponentStatement`, owned by
  Task 5032. Supercuspidal genericity is proved:
  `Whittaker.SupercuspidalKirillovProof.exists_functional`.
- The comparison of Godement–Jacquet factors with the JPSS factors.

The remaining step counts conjugacy classes of maximal simple types of a given
level, using the combinatorics of simple strata and simple characters. I know
of no explicit count in the central library. Bushnell–Henniart, "Counting the
discrete series for GL(n)" (Bull. LMS, 2007) is the expected reference, but it
is missing and its content is unverified here. The Library has no simple
strata, simple characters or types.

B2, through the Jacquet–Langlands correspondence: this is step A4 of Route A
(H88 §2.6). Its prerequisites are listed in section 2.2.

### 3.2 Weil side

The Weil side needs `C_K(n, j) = (q_K − 1) q_K^j` (Théorème 1.3) and its
translation to the Lean strata (section 5). The available sources are:

| Case | Source | Status |
| --- | --- | --- |
| `n = 1` | local class field theory (H88 §3.1, p. 507) | Library reciprocity proved |
| `j = 0` | H88 §3.2, p. 508 (tame representations) | elementary; not in the Library |
| `n` prime to `p` | [Ko2] reduction plus `n = 1` (§3.1); also Howe 1977 [Ho1] and Moy 1986 [Mo] with JL (§3.1, Remarque 1, pp. 507–508) | [Ko2] missing |
| `n = p` | Koch [Ko1], [Ko2] (§3.1, Remarque 2, p. 508) | both missing |
| characteristic `p`, all `n` | Laumon (A3) | no Library object |
| p-adic `K`, Swan `j < n e_K` | close fields from characteristic `p` (A5) | no Library object |
| p-adic `K`, Swan `j ≥ n e_K` | only from Théorème 1.2 in every rank, through the reverse direction of §2.8 ([KZ] 2.3 and 2.4; §6.8), or from a full correspondence | **no source independent of a correspondence located** |

I looked for an independent source in the central library and in the
bibliographies of H88, Bushnell–Henniart–Kutzko 1998, Harris–Taylor 2001 and
Scholze 2013, and found none. Without one, Route B cannot be completed: its
Weil side needs Route A's steps A6–A9, or Route C. Route B can replace at most
the GL-side counting in A4 (B1 instead of B2).

## 4. Route C: from a full local Langlands correspondence

A bijection that preserves conductors and is compatible with twists, in every
rank, gives the orbit counts (unit U2, section 7). The available proofs of
such a bijection are these:

- Henniart 2000, and the Library's chain
  `Henniart.Extension.supercuspidalCorrespondenceHenniartSevenInputs`
  (`Correspondence/HenniartCorrespondenceSevenInputs`). Both take
  `NumericalSurjectivityStatement` as an input, so they are circular for this
  purpose.
- Harris–Taylor 2001. Corollary VII.2.16 (p. 250, PDF 258) uses H88
  Théorème 1.2, so this is also circular.
- Scholze 2013 "completely by-passes the numerical Local Langlands
  Correspondence of Henniart" (abstract and introduction; `LocalLanglands.tex`,
  lines 100–104 and 212–218, in the source folder). The proof still works
  with the Jacquet–Langlands correspondence and base change (lines 212–215)
  and with nearby cycles on Shimura varieties.

If the Library proved the correspondence by such a route, the correspondence
would not need Task 5584's target. Route C is therefore not a program for this
task. It only records that the counts follow from any independent proof of the
correspondence.

## 5. From Henniart's counts to the Lean orbit strata

Route A does not need this translation (unit U2 suffices). Route B does. It
needs:

- twist stabilizers. On the Weil side, H88 Prop. 2.2, pp. 503–504 ([Ko1],
  p. 266): `χσ = σ` for unramified `χ` of order `d` exactly when `σ` is induced
  from the unramified extension of degree `d`. On the GL side, BK (6.2.5).
- the split of an irreducible `σ` as an induction, from an unramified
  extension, of a representation with irreducible inertia restriction. Henniart
  §2.8 (p. 507) does this with `C_E(d, [j/d])` for unramified `E` of degree
  `d | n`.
- for B2 only, inclusion–exclusion over `d | n` between essentially
  square-integrable and supercuspidal classes (§2.5, Zelevinsky).
- the normalization `ω(ϖ_K) = 1` against orbits. An unramified twist by `z`
  multiplies `ω(ϖ_K)` by `z^n`, so an orbit with stabilizer of order `t` meets
  this condition in `n/t` classes.

In H88 the passage from the explicit formula to equal sizes of the
`ω(ϖ_K) = 1` sets (the forward direction of §2.8) refers to [Ko2] and [Ko3].
This is the computation Route B needs; [Ko3] is present and [Ko2] is missing.
The opposite passage, back to the explicit formula, refers to [KZ] (missing),
which Route B does not need. Two remarks bear on the unresolved Swan-zero summation range recorded in
[local construction coverage](local-construction-coverage.md), §3:

- §2.4, p. 504, describes the summation as over "les entiers naturels" `k`
  with `kn ≤ dj`.
- §3.2, p. 508, computes `C_K(n, 0) = q_K − 1` from tame characters, which
  needs `k = 0` to be included.

## 6. Sources

Present in the central library (file names):

- Henniart 1988, `Henniart--La conjecture de Langlands locale numerique pour
  GL(n)--1988.pdf`, registered `henniart-1988-numerical`. Printed page `p` is
  PDF page `p − 495`.
- Bushnell–Kutzko 1993, `Bushnell-Kutzko--The admissible dual of GL(N) via
  compact open subgroups (book)--1993.pdf`. Printed page = PDF page − 12. Not
  registered.
- Bushnell–Henniart–Kutzko 1998 (JAMS), registered
  `bhk-1998-explicit-conductor`.
- Koch 1981 ([Ko3]), registered `koch-1981-eisenstein-polynomial-sequences`.
  Printed page = PDF page + 228.
- Arthur–Clozel 1989 ([AC]), registered `arthur-clozel-1989-base-change`.
- Bernstein–Deligne–Kazhdan–Vignéras 1984. This contains [DKV], pp. 33–117,
  and [De2], pp. 119–157. Not registered.
- Laumon 1987 ([Lm]) and Kazhdan 1986, close fields ([Ka2]). Not registered.
- Wintenberger 1983 ([Wi]), Zelevinsky 1980 (registered
  `zelevinsky-1980-induced-ii`), Rodier 1982 (registered `rodier-1982-gln`),
  Godement–Jacquet 1972, JPSS 1981 (registered `jpss-1981-conductor`) and JPSS
  1983 ([JPS2]).
- Howe 1977 ([Ho1]), Howe–Moy 1985 ([Ho2]), Moy 1986 ([Mo]), Kutzko 1980
  ([Ku]), and Henniart 1980 ([He1], registered
  `henniart-1980-weil-representations`), 1983 on GL(3) ([He3]), 1984 ([He4],
  `Henniart--Galois epsilon-factors modulo roots of unity--1984.pdf`, not
  registered) and 1986 ([He6]).
- Deligne–Henniart 1981 ([DH]), registered
  `deligne-henniart-1981-variation`.
- Harris–Taylor 2001 (registered
  `harris-taylor-2001-geometry-cohomology-simple-shimura`) and Scholze 2013
  (folder `Scholze--The Local Langlands Correspondence for GL_n over p-adic
  fields--2013`).

Missing, with H88's bibliography keys. Each entry says whether the proof of
Théorème 1.2 by Route A needs it.

- [Ko1] Koch, Invent. Math. 62 (1980), 243–268. Not needed: H88 §3.1,
  Remarque 2, p. 508, says the case `n = p` from [Ko1] will not be used.
- [Ko2] Koch, "Bemerkungen zur numerischen lokalen Langlands-Vermutung",
  Proc. Steklov Inst. 163 (1984), 129–136. Needed (A1, A4). The operator
  declined request `e6ae248a5a155ec3906cd2ff39478631` for its Satz 1.
- [He2] Henniart, "La conjecture de Langlands locale pour GL(n)", Journées
  arithmétiques de Metz 1981, Astérisque 94 (1982), 67–85. Lemma 2 is needed
  for the proof of Prop. 3.3 (A2, p. 509). Its §5.7 is also cited in §7.7, but
  there beside [DH] §2, which is present.
- [KZ] Koch–Zink, "… II", same volume as [Ko2], 137–140. Not needed for
  Théorème 1.2 or for U1 and U2. Needed only to recover the explicit formula
  of Théorème 1.3 from Théorème 1.2 (§2.8 Remarque, p. 507).
- [Zi] Zink, AdW preprint (1980). Not needed: H88 §3.3, p. 508, attributes
  Prop. 3.3 to it but gives a different proof.
- [Ro] Rogawski, Duke Math. J. 50 (1983). Cited together with [DKV] (present)
  for the Jacquet–Langlands correspondence in characteristic 0 (A4). I did not
  check whether [DKV] alone suffices.
- [KuM] Kutzko–Moy, Ann. of Math. 121 (1985), and [He5]. Not needed: cited
  only in §3.1, Remarque 2, p. 508, for earlier bijections in rank `p`.
- Bushnell 1987, "Hereditary orders, Gauss sums and supercuspidal
  representations of GL_N", J. reine angew. Math. 375/376. Route B only
  (section 3.1).
- Bushnell–Henniart 2007, "Counting the discrete series for GL(n)". Route B
  only. The citation is not verified here.

## 7. Near-term units and recommendation

Two units are useful on every route, and I expect both to be elementary.
Neither has been started in Lean.

- U1, GL-side orbit-stratum finiteness: `(supercuspidalOrbitStratum K k a).Finite`.
  1. Twist each orbit to a representative with `ω(ϖ_K) = 1`. Unramified
     twists do not change the conductor, because `det` maps the level
     subgroups into `𝔬_K^×`.
  2. The scalars in `1 + 𝔭^a` lie in the level-`a` subgroup, so a class of
     conductor `a` has central character trivial on them. Only finitely many
     central characters remain.
  3. Apply the proved
     `Henniart.CompactOpenFiniteness.centralLevelStratum_finite`
     (`Correspondence/PadicSupercuspidalFinitenessProof`).
- U2, from a bijection to the counts: if every rank has a bijective
  `IsNumericalInjection`, then `NumericalOrbitCountStatement` holds. Weil-side
  finiteness transfers through the bijection from U1. The proof also needs
  every irreducible Weil class to have exactly one Artin conductor in the sense
  of `Numerical.HasArtinConductor`. I have not checked whether the Library
  provides this.

Recommendation: let Task 5891 proceed, and publish U1 and U2 as focused
statement and proof units. Together with Task 5891 and the conductor
hypothesis, they reduce the target to the existence of one bijective numerical
injection in every rank. This is Henniart's own logical shape (§1.9, p. 502;
§6.8). U1 and U2 need no missing source (section 2.4). The explicit
Weil-side count for p-adic fields with large Swan conductor has no source
independent of a correspondence, so I do not recommend a Route B program. The
only self-contained route is Route A. It needs Arthur–Clozel local base change,
Henniart §7, close local fields, Laumon's local Fourier transform and the
Jacquet–Langlands correspondence, none of which the Library has. Of the missing
papers it needs [Ko2] and [He2] (Lemma 2), and possibly [Ro]; it does not need
[KZ] or [Zi]. Starting Route A is a decision about those foundations, not about
counting. This note is a planning document: it supplies no accepted proof, and
it does not complete Task 5584.
