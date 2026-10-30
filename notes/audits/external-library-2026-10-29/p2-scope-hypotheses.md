# External Library audit 2026-10-29: P2 scope and hypothesis explanations

Worker 217, with the P2-02–P2-04 verification reports and corrections of
Worker 1053. This note records the verdicts for the four findings P2-01–P2-04
assigned by task `a56ac3da-fc21-4ec6-896c-1841166342af`, revision 1. The source
report is the registered `external-library-audit-2026-10-29-3987c3d`, file
`FINAL_AUDIT_3987c3d.md`. Its allegations were treated as unverified. They were
checked against complete Lean declarations, section variables, universes,
paired Markdown, the original source where one is cited, and the
authoritative candidate, review and publication records.

## Snapshots and verdict convention

All four findings **hold** at the audited Library commit
`3987c3d7445531c2c7f784464a3fd47061ba0865` (A below). Every defect is in
documentation: paired Markdown or a Lean docstring omits a hypothesis that the
checked Lean declaration already carries, or recommends a hypothesis without
saying that it is degenerate. No Lean statement, definition, hypothesis,
universe or proof was changed by the corrections.

All corrections are based on A. The later Library commit
`b58bd42aee6a565b689f0f0c008506e23b1b6560` leaves the eight owned files
byte-identical to A, so no intervening publication repaired any of these
findings. The current comparison snapshot of this edition is Library
`64f062d4c57e9cc6f8151bc80364bc55c16272c5` (C below). It contains all three
corrections: S and I were published in `bc8de2287e5c24972c55277b2aa9611523dfc5dc`,
and M in C itself, whose previous head is `bc8de228`. At C every owned file
has exactly the published candidate bytes (see the fingerprints below). No
finding remains open at C.

All locations are Library-relative. `Renard`, `Par` and `RS` abbreviate
`Langlands/CategoryTheory/Renard`, `Langlands/Representation/Parabolic` and
`Langlands/Representation/RankinSelberg`. Line numbers refer to A unless a
candidate or C is named. A diff of A and C shows that the Lean files differ only in
docstrings: one in IndexedSubobjectSums, two in InductionFiltration, three in
RankOneExtensionUnfoldingMeasure, none in RankOneExtensionUnfoldingIntegral.
Declarations, hypotheses, universes and proofs are unchanged.

The Lean environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`). A private `lean_check`
probe (diagnostic `864a8f3b`, not a Library file) printed the complete types
of every declaration named below and reported only the axioms `propext`,
`Classical.choice` and `Quot.sound`. It also proved the collapse statement of
P2-01. Worker 1053 printed the same types for P2-03/P2-04 in a separate
check (`d581bd41`).

## Per-finding ledger

Each verdict is for A. The correction keys refer to the release table below.

| Finding / subclaim | Verdict | Location in A and Lean evidence | Decision |
|---|---|---|---|
| **P2-01** | **Holds** | See the subrows. | Key S; repaired at C. |
| P2-01 (a): source-motivation bullet | Holds | Renard/IndexedSubobjectSums.md:16 says the later A.VI.3 results are "the reason for the specialization `w = max u v`". | Rewritten: the specialization's global hypothesis is degenerate; nonzero applications use the particular coproduct or an independent family size. |
| P2-01 (b): specialization section | Holds | Renard/IndexedSubobjectSums.md:101–112 calls the specialization "a legitimate instance … for later finite-type (source AB6) arguments" and does not mention the collapse. | Rewritten, with new paragraphs "Collapse under the global hypothesis" and "Nonzero applications". |
| P2-01 (c): docstring | Holds | Renard/IndexedSubobjectSums.lean:154–156, docstring of `isLUB_subobjectSum_set`. | Docstring extended with the degeneracy and the pointer to `isLUB_subobjectSum`. |
| P2-01 (d): formal theorem | Correct; no change | `isLUB_subobjectSum_set` (Lean:157–160) assumes `[HasImages C] [HasCoproducts.{max u v} C]` for `C : Type u`, `Category.{v} C`. It is a true theorem, only vacuous for nonzero abelian categories. | Retained unchanged, as are the general `isLUB_subobjectSum`, the particular-coproduct construction `subobjectSum` and `HasIndexedSubobjectSums.{w}`. |
| **P2-02** | **Holds** | See the subrows. | Key I; repaired at C. |
| P2-02 (a): filtration construction | Accurate; no change | `normalizedInductionFiltration` (Par/InductionFiltration.lean:22–34) and its step lemma (:37–45) take an arbitrary `σ`; md:10–16. | Unrestricted scope preserved. |
| P2-02 (b): graded equivalence to a supplied `π` | Holds | `nonempty_normalizedInductionFiltrationGradedEquiv` (Lean:49–63) assumes `IsSmooth σ → IsSmooth π → …`. md:18–24 and the docstring state only the smoothness of `π`. | State `IsSmooth σ`. |
| P2-02 (c): chosen graded equivalence | Holds | `normalizedInductionFiltrationGradedEquiv` (Lean:67–84) assumes `IsSmooth σ`; its proof derives the smoothness of the graded quotient from it. md:26–31 asserts "That quotient is smooth" without the hypothesis. | State `IsSmooth σ`. |
| P2-02 (d): embedding | Holds | `exists_injective_normalizedInduced_graded` (Lean:89–108) assumes `IsSmooth σ → ρ.IsIrreducible → …`. md:33–38 omits `IsSmooth σ`; the Lean docstring already says "smooth". | State `IsSmooth σ` in the Markdown. |
| P2-02 (e): opening summary | Holds | md:3–8 promises equivalences of graded representations "for an arbitrary supplied `ObjectRepFiltration`" without the smoothness condition. | Restrict the summary. |
| **P2-03** | **Holds** | See the subrows. | Key M; repaired at C. |
| P2-03 (a) | Holds | `productMeasure_map_const_smul` (RS/RankOneExtensionUnfoldingMeasure.lean:448–465) uses the section variable `[SigmaFinite ν]` (:444–445; only `T1Space K` is omitted). md:83–85 omits it. | State `SigmaFinite ν`. |
| P2-03 (b) | Holds | `productMeasure_cellScalar_eq_zero` (Lean:474–509) assumes `SigmaFinite ν`, `NullSingletonClass ν` and `T1Space K`. md:86–87 and the docstring (:474–475) say only that `ν` has no atoms. | State both classes; docstring says "σ-finite atomless". |
| P2-03 (c) | Holds | `prod_cellScalar_eq_zero` (Lean:511–528) further assumes `Measurable xrow`, `SFinite dx` and `SFinite μ'`. md:88–89 and the docstring (:511–512) state none of them. `SFinite dx` is an interface hypothesis: the proof's product formulas do not use it (see below). | State them. Keep `SFinite dx` in the Lean; do not describe it as used by those formulas. |
| P2-03 (d): boundary | No blanket finiteness | `map_skewScalingMap` (section variables Lean:28–30) has arbitrary `μA` with `SFinite dy`, `SFinite μB`; its Markdown already says so. `map_cellExchange` (Lean:413–438) has arbitrary `dx` with `SFinite dy`, `SFinite μQ`, `SFinite ρ`. Its Markdown (md:75–79) and docstring omitted these three classes and the measurability of `xrow` and `w`. | The correction states exactly these classes and keeps `μA` and `dx` arbitrary. |
| **P2-04** | **Holds** | See the subrows. | Key M; repaired at C. |
| P2-04 (a) | Holds | `integral_cellExchange` (RS/RankOneExtensionUnfoldingIntegral.lean:224–296) assumes `SFinite dx`, `SigmaFinite ν`, `SFinite μQ`, `SFinite ρ`, besides `NullSingletonClass ν`, `ρ.IsMulRightInvariant`, invariance of `μQ`, scaling and measurability. md:55–69 lists none of the four finiteness classes. | State all four. |
| P2-04 (b) | Holds | `integral_cellExchange_reorder` (Lean:300–339) has the same hypotheses. md:70–72 says only "the same statement". | State all four. |

## P2-01: maximal-universe coproducts

For `C : Type u` with `Category.{v} C`, the instance `HasCoproducts.{max u v} C`
makes `C` thin. Put `T = Σ A B : C, (A ⟶ B)`, a type in `Type (max u v)`. If
`r ≠ s : X ⟶ Y`, then sending a set `S ⊆ T` to
`Sigma.desc (fun t => if t ∈ S then r else s) : ∐ (fun _ : T => X) ⟶ Y`, and
this arrow to its element of `T`, is injective by the coproduct leg equations.
This contradicts Cantor's theorem. In an abelian category, thinness gives
`𝟙 X = 0`, so every object is zero. The private probe proves both statements
in Lean: `HasCoproducts.{max u v} C → Subsingleton (X ⟶ Y)` and, for
`[Abelian C]`, `IsZero X`. Mathlib's `CategoryTheory/Limits/SmallComplete.lean`
proves the dual statement for small categories with products.

The audit's argument is therefore correct. Its suggested correction is also
correct: the formal theorem remains valid under its actual assumptions, and the
valid routes are the particular coproduct of a family and an independently
sized family `I : Type w`. The downstream Renard Markdown already explains
the same collapse and does not assume the global hypothesis: SimpleSupportSum
and SimpleSupportSumStatements in A, and SimpleSupportSplitting,
SimpleSupportFunctor and SimpleSupportSplittingSubquotientsStatements in C.
None of them needs a change. No Library Lean file other than
IndexedSubobjectSums mentions `isLUB_subobjectSum_set`.

The original source does not support the maximal-universe reading. In
`renard-2026-representations-groupes-reductifs-padiques` (SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`), A.VI.2,
printed p.263 / PDF269, AB4* asks for direct sums of every family. The remark
after AB5, "Remarquons que les sommes existent grâce à AB4∗", derives sums of
subobjects from it. A.VI.3, printed p.264 / PDF270, sums chains and arbitrary
families of subobjects and names `A−mod` as an example. These are set-indexed
families in a category such as modules over a ring, where every set of
subobjects is small. In Lean such a category has Hom types smaller than its
object type, and coproducts of size `max u v` would make it zero. No
registered erratum for these passages was found; the registered errata
`renard-2010-corrections-complements` concern the 2010 edition.

## P2-02: smoothness of the Levi representation

The Library's smooth induction (`Langlands/Representation/Induction/Definitions.lean`,
`smoothInduced`) is the smooth part of the coinduced representation on
covariant functions. For the whole group, a covariant function is
`g ↦ σ(g) v`, and it is fixed by an open subgroup under right translation if
and only if `v` is a smooth vector. Thus smooth induction from the whole group
gives the smooth vectors of `σ`.

The audit's one-block example for `GL₁(ℚ₃)` is valid. The element 4 has infinite
order in `ℚ₃^×`, so a ℚ-linear functional on `ℚ₃^× ⊗ ℚ` gives an additive
`α : ℚ₃^× → ℂ` with `α(4) = 1`. Since `4^(3^n) → 1` while
`α(4^(3^n)) = 3^n ≠ 0`, the kernel of `α` contains no open subgroup. For
`σ(g)(x, y) = (x + α(g) y, y)`, the smooth vectors are exactly `ℂ e₁`. For the
filtration `0 ⊂ ℂ e₁ ⊂ ℂ²`, both induced steps equal the induced functions with
values in `ℂ e₁`, so the top induced graded piece is `0`. The induction of the
top quotient, the trivial character, is `ℂ`. Hence both graded-equivalence
claims fail without `IsSmooth σ`. This example does not contradict the
embedding conclusion, but that statement also carries `IsSmooth σ` in Lean,
and the Markdown omitted it. The example concerns the prose only; the Lean
hypotheses exclude it. The module is an internal assembly with no original
source claim. Its Library consumers at C, Par/ProductInductionFiltration and
`Langlands/Representation/Classification/RelativeJacquetFiltrationMultiplicityProof`,
supply the smoothness argument to `normalizedInductionFiltrationGradedEquiv`,
and their Markdown already states the smoothness used
(ProductInductionFiltration.md:16–25; RelativeJacquetFiltrationMultiplicityProof.md:15–17
and 46–47). They need no change.

## P2-03 and P2-04: finiteness of the measures

The P2-03 counterexample is valid. On the Borel sets of `ℝ`, let `ν` be `0` on
countable and `∞` on uncountable sets. It is a measure with null singletons,
but it is not σ-finite. In the pinned Mathlib, `Measure.pi` is the measure
induced by `OuterMeasure.pi = boundedBy piPremeasure`. A covering set of finite
cost has a countable coordinate projection, so it meets the line
`{1 + y₀ + y₁ = 0}` in countably many points. Countably many such sets cannot
cover the line, so the line has infinite `Measure.pi` mass. The conclusion of
`productMeasure_cellScalar_eq_zero` therefore needs more than atomlessness. The
Lean proof of `productMeasure_cellScalar_eq_zero` uses `SigmaFinite ν` through
`measurePreserving_piFinSuccAbove` and the product formulas. In the pinned
Mathlib, `Measure.prod_prod` and `Measure.prod_apply` assume only that the
right factor is s-finite (`Mathlib/MeasureTheory/Measure/Prod.lean:181–231`).
In `prod_cellScalar_eq_zero` (Lean:525), `Measure.prod_prod` therefore uses
`SFinite μ'`, and `Measure.prod_apply` uses the s-finiteness of `ν^(t+1)`,
which follows from `SigmaFinite ν`. Neither formula uses `SFinite dx`.
Reviewer 4583 confirmed this with a probe (diagnostic
`9bdf18f1-3897-4a87-ad57-a34289cc306a`) that applies both formulas to an
arbitrary `dx`. `SFinite dx` remains an explicit hypothesis of the published
theorem. The audit's correction asks only that the documentation state it, and
this edition does not change the Lean interface.

For P2-04, the four classes enter the proofs as follows. In
`integral_cellExchange`, `productMeasure_map_const_smul` requires `SigmaFinite ν`.
`map_cellExchange` requires s-finiteness of `ν^(t+1)`, `μQ` and `ρ`, and
`prod_cellScalar_eq_zero` is applied with `μ' = μQ × ρ`. `SFinite dx` enters
only because the interface of `prod_cellScalar_eq_zero` requires it. In
`integral_cellExchange_reorder`, `measurePreserving_cellReorder` composes
associativity and swap equivalences of product measures. It assumes all four
factors s-finite, including `dx`. The
invariance hypotheses do not imply these classes: counting measure on an
uncountable group such as `ℝ^×` is right-invariant but not s-finite, since a
countable sum of finite measures gives positive mass to only countably many
points. This shows only that the classes are independent hypotheses; it is
not a counterexample to the theorems with all their hypotheses. The only
Library consumer of the unfolding integrals at C,
RS/RankOneExtensionSpanComparisonCore, binds all four classes explicitly
(Lean:181–185 at C) and states them in its Markdown (md:56–59 at C). It needs
no change. No Library file outside the two owned modules uses
`productMeasure_cellScalar_eq_zero` or `prod_cellScalar_eq_zero`.

The audit's claim that the existing Lean hypotheses are correct was checked:
every declaration above is a proved theorem using only standard axioms, and
each finiteness class the audit lists is an explicit hypothesis of the
corresponding declaration. The probe cited above shows that the product
formulas in the proof of `prod_cellScalar_eq_zero` do not use its
`SFinite dx`, which `integral_cellExchange` merely passes on. This note does
not claim that every other class is indispensable. Weakening an interface
would change published Lean statements, which is outside this documentation
task. No finiteness class was added to an arbitrary measure. The modules cite JPSS 1983, Lemma 5.5,
only as the provenance of the change of variables, and they say that the
measure-theoretic hypotheses are formalization choices. These findings
therefore involve no claim about the original source.

## Corrections and release evidence

Each correction is a focused ordinary `lean.definition` candidate on base A.
It edits only Markdown and docstrings of this task's own file pairs.

| Key | Findings | Candidate | Author | Machine validation | Independent review | Publication |
|---|---|---|---|---|---|---|
| S | P2-01 | `1b080313-804b-444e-8b27-449f685b4507` | Worker 217 | `3175a98b-7d25-442b-8591-6595b3e2e23f` (accepted) | task `4e25dd15-36cb-4346-b538-92add4ed8eb8`, approved by Reviewer 4590, no qualifications | Integration `65d6c73a779647bb9fdce328f9de0222` (batch `498cd055f707477e9a3f5ed7a92e04e5`, approve, no qualifications); Library `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |
| I | P2-02 | `8a014938-0080-4bfe-ab11-b4c31cce8514` | Worker 1053 | `a3a1f288-f25d-46f2-a680-bda6bc8fa39b` (accepted) | task `daa03ffe-e873-4732-8c91-c01768fdae0b`, approved by Reviewer 4603, no qualifications | Integration `3f8974d1baba4f399e7acb0375654188` (batch `498cd055f707477e9a3f5ed7a92e04e5`, approve, no qualifications); Library `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |
| M | P2-03, P2-04 | `55fb5456-0b0f-471c-846b-62f527e60b61` | Worker 1053 | `2f39319d-2b2d-45a9-8812-86cbde1258be` (accepted) | task `e853f86a-4851-479b-9dd0-c4b565061359`, approved by Reviewer 4635, no qualifications | Integration `63d5d4b081d14c9f8b89cd3bb8e79c56` (batch `601d50d0ad7d477ba5cfaa8c405869d0`, approve, no qualifications, fresh integrated Lake build accepted); Library `64f062d4c57e9cc6f8151bc80364bc55c16272c5` |
| M (rejected version) | P2-03, P2-04 | `240a5ca3-8f3d-4b35-b661-9ad042bf60f2` | Worker 1053 | `a7511beb-7075-4293-accb-a1b72f1db4f6` (accepted) | task `2732a645-65d3-46df-bc99-31dc619e70bb`: changes requested by Reviewer 4583 (receipt `9c4c2ad7-a4b8-4f49-97b6-41353676d65a`) because the proof explanation attributed the product formulas to `SFinite dx`. Replaced by `55fb5456`, whose only change is that sentence (candidate RankOneExtensionUnfoldingMeasure.md:125–130). | Not published |

Machine validation is not semantic acceptance. This note itself requires
separate independent review and publication.

## File fingerprints

SHA256 of the owned pairs. The A columns identify the defective versions; the
C columns equal the published candidate bundles (S, I and M), and the
Integral Lean file is unchanged.

| Pair stem | Lean in A | Markdown in A |
|---|---|---|
| Renard/IndexedSubobjectSums | `7f3cdfd7544f6920bb269cce704a7a496a8c76cfdacc38efbab8508a19e70e27` | `b13c191d3e57f85018f8abac3801f54ba79bfa02733f312913cad348311572f3` |
| RS/RankOneExtensionUnfoldingMeasure | `4421e60c14e45d8cf87cfebe7cdac84b1fb2d2c9d1ccfa23639b7badf66e0a3e` | `0f758293b0691294444504b8bc768526a6cae4ad72aeac05ed66c4a35a03577d` |
| RS/RankOneExtensionUnfoldingIntegral | `bf094c1006f1e4f90b4fd305a54b3a8e740b4cefce079da2d91c7ea505dc0a19` | `de3d2d3bd28e58c43527df95d1b54de25c2bed7611bab97290f3dddb3b36ac9f` |
| Par/InductionFiltration | `6a17118b3f45a504445540ab66e04e067deb4f4d2abc94df09eba80e34e7b7c2` | `5505c9504a4b2e99f0f019647241adb0d42a5bb0e444493a7c6f0c4dd6e1cd02` |

| Pair stem | Lean in C | Markdown in C |
|---|---|---|
| Renard/IndexedSubobjectSums | `8c5e627042e322703525a0e4cc7d14354dfd05a321747fa845ac314b750ed433` | `a77a5c54da4d31f11b3c2e6e45858b8a98c54d8c3185146284e97b07a5013cdb` |
| RS/RankOneExtensionUnfoldingMeasure | `52037725d734fa301d1365a2c3a5513ffc83f8982e7112bdf012bc55791af815` | `aeb22c9cc934b935075f1b1f11ed30c9bea39022f6139c6ebd268aa963cbbab2` |
| RS/RankOneExtensionUnfoldingIntegral | `bf094c1006f1e4f90b4fd305a54b3a8e740b4cefce079da2d91c7ea505dc0a19` | `c8cf866e04f89fff9665edee8f42d0b412d06d3486c943e218a0d8c0f9e03cd0` |
| Par/InductionFiltration | `f081d049052997e8a0669bc64c514bd02ba84e9c19f8d82d1e4ba2e89e3d0d9b` | `0c40bd7a51921067f59a2614c2217a23f100688bbaa70c4d78dbfa4f37b9b3c0` |

The audit report has SHA256
`d9a25f35dc2d7bef0351ba0891db168b0c3cc797a281d0a9944e930fe43d5eeb`.
