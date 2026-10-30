# External Library audit 2026-10-29: class field theory, cohomology and global arithmetic

Worker 1056, with the verification reports and corrections of Worker 1061.
This note records the verdicts for the 19 findings P3-004–P3-011, P3-020–P3-022,
P3-050–P3-056 and P3-058 assigned by task
`1b73f1f7-c0da-4aa1-82d0-0365caf45751`, revision 2. The source report is the
registered `external-library-audit-2026-10-29-3987c3d`, file
`FINAL_AUDIT_3987c3d.md` (rows 67–74, 88–90, 135–141 and 143). Its allegations
were treated as unverified. They were checked against complete Lean
declarations, section variables, universes, paired Markdown, the original
source where one is cited, and the authoritative candidate, review and
publication records.

## Snapshots and verdict convention

All 19 findings **hold** at the audited Library commit
`3987c3d7445531c2c7f784464a3fd47061ba0865` (A below). Every defect is in
documentation. Paired Markdown or a Lean docstring either calls a published,
proved theorem unproved or open, states a scope that differs from the Lean
typeclasses, credits an exported theorem with more than its type says, or uses
a false example. No Lean statement, definition, hypothesis, universe or proof
was changed by the corrections. The Lean edits are docstring-only, in five
files: ArchimedeanLocalHerbrand, LocalUnitPowers,
SmoothGodementComparison/Invariants, SmoothGodementComparison/Transformation
and SupercuspidalRestriction/Statement.

All locations are Library-relative. `CF`, `CFT`, `Coh`, `Sh` and `GA`
abbreviate `Langlands/ClassField`, `Langlands/ClassFieldTheory`,
`Langlands/Cohomology`, `Langlands/Sheaf` and `Langlands/Global/Arithmetic`.
Line numbers refer to A unless C is named.

The 21 owned file pairs (see the fingerprints below) were followed through
the Library history. `b58bd42aee6a565b689f0f0c008506e23b1b6560` leaves them
byte-identical to A. The corrections changed them in
`bc8de2287e5c24972c55277b2aa9611523dfc5dc` (keys H, Q, C1, C2, G),
`64f062d4c57e9cc6f8151bc80364bc55c16272c5` (A1),
`6a6c913c7339c50634dd74722034032e7a167d97` (U, R, F1, F2, T1),
`cde31751c7864199419ad8fae8b7f3474639ba24` (T2, A2) and
`3c5f92411ab2bcef7d4e5ae82c66a7ae30ea3fdf` (S, V, W, K). The intermediate
heads `047f3489`, `c8ae014c`, `f35c1c21` and `9330fa8d` leave them
byte-identical to `6a6c913c`. The publication receipts give `9330fa8d` as the
previous head of `cde31751`, and `cde31751` as the previous head of `3c5f9241`.
Among the owned pairs, these two commits change only the files of the six keys
published in them. So no other publication repaired or reintroduced any finding. The comparison
snapshot is Library `3c5f92411ab2bcef7d4e5ae82c66a7ae30ea3fdf` (C below). At
C all 19 findings are repaired, and every owned pair is byte-identical to the
files of each published candidate that contains it. The later head
`d1abfe1f26a6fdf1d986073e68c049e12c3f6ea5` only adds another audit note and
changes `wiki/README.md`, so every Lean file and every owned pair there is
byte-identical to C.

### Corrections inside this task (revision 2)

The corrections were made inside this task. Revision 1 of the task asked that
corrections spanning independent reviewable units first be split into focused
child tasks. Revision 2 replaced only that sentence (operator decision
`faf0e51e963f5679b2a0265c153b78df`, relayed by Worker 0). Under revision 2
the executors may make corrections inside this task, as focused candidates
that are each validated, independently reviewed and published. A child task
is required only for a change of a Lean statement or proof target, or for an
edit outside the assigned pairs. Neither occurred, so no child task was
created.

The 11 corrections published before the revision change keep their actual
receipts, which bind them to task revision 1. The other six candidates had been
approved in review under revision 1 but were not yet published when the
revision changed. The revision change superseded them and invalidated their
reviews. Each was resubmitted against revision 2 as one replacement candidate,
with the same files as the superseded candidate, reviewed again and published.
Both the superseded and the replacement receipts are listed in the release
table.

### Lean evidence

The Lean environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`). The statements,
hypotheses and universes of the proved declarations cited in this note were
read from their complete declarations in the Library source, at the lines
given in the ledger. Private `lean_check` probes, which are not Library files,
added the following machine checks.

- Diagnostic `1bf9ea6d-fc53-4ad2-8539-2cdf6198f5be` ran before C. It printed
  the axiom dependencies of 22 proved declarations and reported only
  `propext`, `Classical.choice` and `Quot.sound` for each:
  `finiteQuotientComparisonIsIso`, `restrictionComparisonLaws`,
  `continuousCorestrictionLaws`, `smoothGodementZeroCSoft`,
  `acyclicResolutionComparisonStatement`,
  `resolutionComparisonIndependenceStatement`,
  `resolutionComparisonNaturalityStatement`, `resolutionLiftStatement`,
  `PadicField.TopologicalData.generalLinearSigmaCompactSpace`,
  `globalInvariantStatement`, `globalFundamentalClassStatement`,
  `ideleClassGaloisDescent`, `cyclicIdeleClassHerbrandQuotient`,
  `tateCupIsomorphism`, `pGroupTateVanishing`, `sylowTateVanishing`,
  `tateComparison`, `ordinaryTateCupLaws`, `classFormationTateIsomorphisms`,
  `primeTotallyRamifiedBreak`, `primeBreakUnramifiedBaseChange` and
  `cyclicNonsplitPrimeStatement`. It printed the types of only four
  declarations: `finiteQuotientComparisonIsIso`,
  `generalLinearSigmaCompactSpace` and the P3-006 exports
  `exists_pow_eq_one_add_sq_mul` and `infiniteUnitPowers_two_finiteIndex`.
- Diagnostic `9fd5107b-8bf5-4ab0-9636-8317c3a4a7a1` ran at C with
  `pp.universes true` and reported no errors or warnings. For each of the same
  22 declarations and the two P3-006 exports, it printed the type (`#check`)
  and the axiom dependencies (`#print axioms`). Every axiom list is again
  `propext`, `Classical.choice` and `Quot.sound`. For 20 of the 22
  declarations, the printed type is the named statement with its universe
  parameters, for example `tateCupIsomorphism.{u_1} : TateCupIsomorphism.{u_1}`
  and `acyclicResolutionComparisonStatement.{u_1, u_2, u_3, u_4} :
  AcyclicResolutionComparisonStatement.{u_1, u_2, u_3, u_4}`. The types of
  `smoothGodementZeroCSoft`, `generalLinearSigmaCompactSpace` and the two
  P3-006 exports are printed with their full binder lists.
- Diagnostic `575fe032-3d5f-47c9-8b16-25022fe839af` (for P3-004) imports only
  Mathlib. It proves `FiniteDimensional F E` for `F E : Type` under
  `[Field F] [Field E] [NumberField E] [Algebra F E]`, with no errors and three
  style warnings. The Library variables (CF/Global/ArchimedeanLocalHerbrand.lean:95)
  have `F E : Type u`; the argument does not depend on the universe.
- Diagnostic `f6ea4eed-10dc-4399-9ca6-9ef75777ebe9` (for P3-053) reported no
  errors or warnings. It elaborates `acyclicResolutionComparisonStatement` at
  `AcyclicResolutionComparisonStatement.{u + 1, u, u + 1, u}` (the hypothesis
  of `comparisonIso`, Coh/SmoothGodementComparison/Transformation.lean:128 at C) and
  `AcyclicResolutionComparisonStatement.{u + 1, u, u', v'}` (the hypothesis of
  `sheafComparisonIso`, Invariants.lean:136 at C), and `resolutionLiftStatement`
  at `ResolutionLiftStatement.{u + 1, u}`.

An axiom list shows only that a declaration is proved without `sorryAx` or an
added axiom. A printed type that is only a statement name does not show what
the statement says. The content, hypotheses and scope of each cited statement
come from reading its Lean source. Worker 1061 checked their corrected
modules by compilation only. Their counterexamples were checked by hand, not in Lean.

## Per-finding ledger

Each verdict is for A. The correction keys refer to the release table below.

| Finding / subclaim | Verdict | Location in A and Lean evidence | Decision |
|---|---|---|---|
| **P3-004** | **Holds** | CF/Global/ArchimedeanLocalHerbrand.md:13–15 says that under `[Field F] [Field E] [NumberField E] [Algebra F E]` (Lean:95) "`E/F` need not be Galois or finite". The field map makes `F` a subfield of `E` containing `ℚ`, and a finite `ℚ`-spanning set of `E` spans over `F`. A private probe (diagnostic `575fe032`, for `F E : Type`) proves `FiniteDimensional F E`. | Key H; repaired at C (md:13–18): finite degree is implied, so no separate hypothesis is needed. |
| **P3-005** | **Holds** | See the subrows. | Key H; repaired at C. |
| P3-005 (a): Markdown | Holds | md:85–86 writes `Subquotient φ ψ = ker φ ⧸ range ψ` for arbitrary `φ`, `ψ`. The definition (Coh/HerbrandQuotient.lean:28–30) is `ker φ ⧸ (range ψ).submoduleOf (ker φ)`, the quotient by `ker φ ∩ range ψ`. | Rewritten (md:88–90 at C). |
| P3-005 (b): docstring | Holds | Docstring of `subsingleton_subquotient_of_forall` (Lean:24) has the same formula. | Docstring corrected (Lean:24–25 at C); the theorem is unchanged. |
| **P3-006** | **Holds** | CF/Global/LocalUnitPowers.md:83–92 says that `exists_pow_eq_one_add_sq_mul` (Lean:169) "is this statement" of Milne I.1.7 and that `infiniteUnitPowers_two_finiteIndex` (Lean:300) has the "content" of I.1.6. The exports give only `∃ y, y ^ d = 1 + d ^ 2 * t` and `FiniteIndex`; they give neither `u ∈ 1 + 𝔪` nor that the squares are the positive reals. The docstring (Lean:299) says "index at most two". | Key U; repaired at C (md:87–99, Lean:299–300): the exports are stated as consequences. |
| **P3-007** | **Holds** | CFT/Local/ResidueNormalization.md:5–6 states the scope "complete nonarchimedean normed field with finite residue field". The section variable (Lean:23) is `[NontriviallyNormedField K]`. A finite field with the trivial norm satisfies the prose but not the typeclass. | Key R; repaired at C (md:6–10): "nontrivially normed" added. |
| **P3-008** | **Holds** | See the subrows. | Key C1; repaired at C. |
| P3-008 (a): profiniteness | Holds | Coh/Continuous/FiniteQuotientSystem.md:54–57 says that profiniteness and the continuous discrete action are needed for the intended comparison. `FiniteQuotientComparisonIsIso` (FiniteQuotientComparisonStatement.lean:10) quantifies over compact, locally compact topological groups, with no Hausdorff or total-disconnectedness hypothesis, and is proved by `finiteQuotientComparisonIsIso` (FiniteQuotientComparisonProof.lean:514). For the circle group, the only open subgroup is the whole group, and continuous cochains with values in a discrete module are constant, so the audit's example is consistent with the theorem. | Rewritten (md:56–74 at C): the comparison is proved under the Lean hypotheses; Serre's profinite setting (*Local Fields* X.3) is a special case. |
| P3-008 (b): status | Holds | md:58–60 and 83–85 call the comparison and the transfer laws separate obligations. `restrictionComparisonLaws` (RestrictionComparisonProof.lean:78) and `continuousCorestrictionLaws` (CorestrictionLawsProof.lean:14) are proved. | Status updated (md:51–52, 98–99 at C). |
| **P3-009** | **Holds** | Coh/DivisibleSystem/InvariantTransition.md:57–60 says that for `j = some i` "all the maps are identities". In the proof of `extendXMapIso_inv_comp_comp` (Lean:48–56) only the extension comparisons are identities (up to `F₂.map_id`); the arbitrary component `α.inv.app (K.X i)` remains on both sides. With identity functors on `ℤ`-modules and `α` the negation automorphism, both composites are `-id`. | Key C2; repaired at C (md:59–63). |
| **P3-010** | **Holds** | Coh/EquivariantGodement/Statement.md:229–230 calls `H^1(ℤ, R) = R` nonzero, while `R` is an arbitrary `CommRing` (Lean:27). This fails for the zero ring. | Key G; repaired at C (md:229–232): a nonzero ring such as `ℤ`. The propositions are unchanged. |
| **P3-011** | **Holds** | Coh/HerbrandQuotient.md:87–89 says that every cardinality statement comes with explicit `Finite` hypotheses or conclusions. `card_eq_card_ker_mul_card_range` (Coh/HerbrandQuotient.lean:78), `card_hexagon` (:95), `CompatibleExact.card_subquotients` (:284), `card_subquotient_mul_card_range` (:340) and `CompatibleExact.card_subquotients_rat` (:384) are `Nat.card` identities with no finiteness hypothesis; they also hold, with value `0`, for infinite types. | Key Q; repaired at C (md:87–100): the five identities are named, and the assurance is restricted to `HasSubquotientRatio`, `HasHerbrandQuotient` and the other statements with explicit finiteness. The theorems are unchanged. |
| **P3-020** | **Holds** | Coh/CompactSoft/Statement.md:174–176 says that the description of sections in Step 0 "is not constructed in Lean". `coordinateIso`, `read` and `read_map` (Sh/Equivariant/CoinducedFamilies/Coordinates.lean:140, 146, 164) describe the sections of coinduction as families over the pairs `(g, y)` with `g • y ∈ U`. The proof of `smoothGodementZeroCSoft` (Coh/CompactSoft/SmoothZeroProof.lean:24) goes through this description. | Key G; repaired at C (md:175–189). The statement module itself still proves nothing; `CSoftAcyclicityStatement` (Lean:44) remains unproved. |
| **P3-021** | **Holds** | Coh/SmoothCompactComparison/Statement.md:319–320 says that no `c`-softness predicate for equivariant sheaves is published. `IsCSoft` (Sh/CompactSoft.lean:217) is defined for ordinary module sheaves and is applied to the underlying sheaf of the smooth zero sheaf in `SmoothGodementZeroCSoftStatement` (Coh/CompactSoft/Statement.lean:51), which is proved. That sheaf is the smooth coinduction of the ordinary Godement zero sheaf; the `D⁰` of this module is the smooth coreflection of the equivariant zero functor, a different object. | Key G; repaired at C (md:320–331): cites `IsCSoft` for the underlying sheaf and does not identify that object with `D⁰`, whose softness is not stated. |
| **P3-022** | **Holds** | See the subrows. | Key S; repaired at C. |
| P3-022 (a): σ-compactness | Holds | The docstring of `glSupercuspidalRestriction_of_compactModCenter` (Coh/SupercuspidalRestriction/Statement.lean:116–119) says that total disconnectedness and σ-compactness of `GL_n(F)` "are not proved in the Library". `PadicField.TopologicalData.generalLinearSigmaCompactSpace` (Langlands/Group/GL/CountabilityProof.lean:13) proves `SigmaCompactSpace` for `T.generalLinearTopology n`, the canonical topology. | Docstring (Lean:118–122 at C) and Markdown (md:83–97, 248–253 at C) cite it. The instance arguments are kept. |
| P3-022 (b): total disconnectedness | Holds; proofs are private | The only proofs are two `private` theorems `generalLinearTotallyDisconnected` (Langlands/Representation/CuspidalSupport/LeviAdmissibleFactorizationProof.lean:29, Langlands/Representation/Tensor/FactorMatchingProof.lean:324), which other modules cannot use. No public theorem exists at A or C. md:81–83 ("Instance search finds neither") is accurate for instance search. | The docstring at C says that total disconnectedness is proved only by private theorems and that both properties remain instance arguments because instance search does not find them. |
| **P3-050** | **Holds** | See the subrows. | Keys F1, F2; repaired at C. |
| P3-050 (a): fundamental class | Holds | CF/Global/FundamentalClassStatement.md:92 says "Global invariants are not formalized" and md:155–156 calls global invariant maps later work and the proof a separate task. `GlobalInvariantStatement` (CF/Global/InvariantStatement.lean:119) with its invariant-map interface is published and proved by `globalInvariantStatement` (InvariantProof.lean:20); `globalFundamentalClassStatement` (FundamentalClassProof.lean:35) proves this module's statement. | Key F1 (md:92–101, 163–168 at C). The targets keep their hypotheses (relative class formation and arithmetic normalization). |
| P3-050 (b): idele tower | Holds | CF/Global/IdeleArchimedeanTower.md:51 says "`GlobalInvariantStatement` remains open". | Key F2 (md:51–54 at C). |
| **P3-051** | **Holds** | CFT/Local/ClassFormationCupLawsStatement.md:46–48 says that a proof of `TateCupIsomorphism` "can be applied to it once that proof exists"; md:80–81 calls Tate's theorem a separate proof task. `tateCupIsomorphism : TateCupIsomorphism.{u}` (Coh/Tate/TateTheoremProof.lean:191) and `classFormationTateIsomorphisms` (CFT/Local/ClassFormationTateIsomorphismsProof.lean:95) are proved. | Key T1; repaired at C (md:47–51, 83–85). The conditional interface is kept. |
| **P3-052** | **Holds** | CFT/Local/PrimeBreakUnramifiedBaseChangeStatement.md:58–61 says `PrimeTotallyRamifiedBreak` "is not yet proved". `primeTotallyRamifiedBreak : PrimeTotallyRamifiedBreak.{u, v}` (CFT/Local/PrimeRamificationBreakProof.lean:13) proves it. This module's own statement is proved separately by `primeBreakUnramifiedBaseChange` (PrimeBreakUnramifiedBaseChangeProof.lean:17). | Key T2; repaired at C (md:58–70): cites `primeTotallyRamifiedBreak` as the proof and `primeBreakUnramifiedBaseChange` as the separate proof of this module's statement. |
| **P3-053** | **Holds** | See the subrows. | Key A1; repaired at C. |
| P3-053 (a): comparison | Holds | Coh/AcyclicResolution/Comparison.md:119–131 calls `AcyclicResolutionComparisonStatement` unproved and plans a proof task; md:176–191 says the same of the independence and naturality statements. `acyclicResolutionComparisonStatement` (Coh/AcyclicResolution/ComparisonProof.lean:247), `resolutionComparisonIndependenceStatement` (IndependenceProof.lean:22) and `resolutionComparisonNaturalityStatement` (NaturalityProof.lean:21) are proved. | Rewritten (md:126–131, 177–190, 197–199 at C). The explicit hypotheses of `comparisonNatIso` are kept. |
| P3-053 (b): invariants | Holds | Docstring at Coh/SmoothGodementComparison/Invariants.lean:15–18 and md:66, 157–160 call the comparison statement unproved. | Docstring (Lean:17–19 at C) and Markdown (md:66–69, 160–163 at C) corrected. |
| P3-053 (c): transformation | Holds | Transformation.md:76–82 says both hypotheses of `comparisonIso` are "published statements without proofs"; the docstring (Lean:24–27) says "unproved published statements". The first is proved; the second, `SmoothGodementCompactDerivedAcyclicStatement`, remains unproved. | Docstring (Lean:24–28 at C) and Markdown (md:81–85, 104–107 at C) distinguish the two. |
| **P3-054** | **Holds** | Coh/SmoothGodementComparison/Statement.md:129–133 calls `ResolutionLiftStatement` and `CokernelResolutionStatement` "Both … unproved statements". `resolutionLiftStatement : ResolutionLiftStatement.{u, v}` (Coh/AcyclicResolution/LiftProof.lean:23) is proved; `CokernelResolutionStatement` (Sh/Godement/ExactnessStatement.lean:62) remains unproved. | Key A2; repaired at C (md:133–139): `ResolutionLiftStatement` is cited as proved, and the application still rests on the unproved `CokernelResolutionStatement`. |
| **P3-055** | **Holds** | Coh/Tate/CohomologicalTrivialityStatement.md:3–6 calls its three propositions ingredients "that the Library does not yet contain". `pGroupTateVanishing` (PGroupTateVanishingProof.lean:482), `sylowTateVanishing` (SylowTateVanishingProof.lean:18) and `tateComparison` (TateComparisonProof.lean:154) are proved, and `tateCupIsomorphism` uses `tateComparison`. | Key V; repaired at C. The module cites the three proofs (md:4–14 at C) and states at md:83–86 that `tateCupIsomorphism` uses the proved `tateComparison`. |
| **P3-056** | **Holds** | Coh/Tate/CupProof.md:32–33 says "The separate comparison with ordinary cochain cup products remains open". `ordinaryTateCupLaws : OrdinaryTateCupLaws.{u}` (Coh/Tate/OrdinaryTateCupProof.lean:170), with the lemma `ordinaryToTate_cup` (:158), proves it for an arbitrary commutative ring, finite group, pairing and natural degrees. In degree zero the map to Tate cohomology is a surjection, not an isomorphism. | Key W; repaired at C (md:32–40). |
| **P3-058** | **Holds** | GA/KummerSecondInequality.md:7 says the module proves its target "from three unproved Library statements". `cyclicNonsplitPrimeStatement` (GA/CyclicNonsplitPrimeProof.lean:20), `ideleClassGaloisDescent` (CF/Global/IdeleClassGaloisDescentProof.lean:122) and `cyclicIdeleClassHerbrandQuotient` (CF/Global/CyclicIdeleClassHerbrandAssembly.lean:98) prove them at independent universes, and `Langlands/Global/AdelicFunctoriality/IdeleClassPrimeDegreeSecondInequalityProof.lean:18–25` supplies them to this module's theorem. | Key K; repaired at C (md:7–18). The three explicit hypotheses are kept. |

## Scope and example findings

P3-004, P3-005, P3-006, P3-007, P3-010 and P3-011 concern prose that does not
match the Lean typeclasses, definitions or exported types.

**P3-011.** Coh/HerbrandQuotient.md:87–89 says that every cardinality
statement comes with explicit `Finite` hypotheses or conclusions. This is
false for `card_eq_card_ker_mul_card_range` (Lean:78), `card_hexagon` (:95),
`CompatibleExact.card_subquotients` (:284), `card_subquotient_mul_card_range`
(:340) and `CompatibleExact.card_subquotients_rat` (:384). These are `Nat.card` identities that
also hold, with value `0`, for infinite types, as md:110–111 itself notes. Key Q
restricts the assurance to `HasSubquotientRatio`, `HasHerbrandQuotient` and
the final cohomological statements (md:87–100 at C). The theorems are
unchanged.

**P3-006** cites J. S. Milne, *Class Field Theory*, version 4.03, Chapter I,
1.6–1.7, printed p.22 (PDF p.31). Worker 1061 read this passage. No erratum
was checked. Milne obtains `u ∈ 1 + 𝔪` with `u^m = a` and states that the
squares of `ℝ^×` are the positive reals. The Lean exports are consequences of
these statements, not the statements themselves.

**P3-007** is a typeclass-scope finding. The canonical `p`-adic
specialization of the module is nontrivially normed and is unaffected.

## Status of interfaces and proved theorems

The other 13 findings concern what the Library proves elsewhere. P3-008 (a)
asks for more hypotheses than the proved comparison has, and P3-009 claims that
a component is an identity although it is arbitrary. P3-008 (b), P3-020,
P3-021, P3-022, P3-050, P3-051, P3-052, P3-053, P3-054, P3-055, P3-056 and
P3-058 call a published, proved theorem or a published construction
unproved, open or absent. Every correction cites the proved declaration by
its exact Lean name and keeps the explicit hypotheses of the module's own
declarations, since a proof elsewhere does not remove a hypothesis from a
published statement. No correction claims a new theorem.

The corrections also keep the statements that are still unproved at C as
hypotheses in the prose: `CokernelResolutionStatement`,
`SmoothGodementCompactDerivedAcyclicStatement`, `CSoftAcyclicityStatement` and
`AcyclicResolutionEquivarianceStatement`. A search of C found no public
theorem that `GL_n(F)` is totally disconnected; the two proofs are `private`.

For P3-008 the original source is Serre, *Local Fields*, X.3, printed p.154
(PDF p.160), where the group is a compact totally disconnected Galois group.
The Lean theorem is more general. Its hypotheses are compactness and local
compactness only.

**Out of scope.** `notes/henniart/harris-cohomology-coverage.md:102–103` (at C)
says that total disconnectedness of `GL_n(F)` "is not proved in the Library".
Only private proofs exist, as in P3-022 (b). The note is not an assigned pair.
Reviewer 4702 pointed it out during the revision-1 review of key S, and it is recorded
here for a later editorial task.

## Corrections and release evidence

Each correction is a focused ordinary `lean.definition` or `lean.statement`
candidate whose entry pair is the corrected pair. It edits only Markdown and
docstrings of this task's own file pairs. The review and publication of every
published correction recorded no qualifications, and every publication
recorded an accepted fresh integrated Lake build.

| Key | Findings | Candidate | Author | Machine validation | Independent review | Publication |
|---|---|---|---|---|---|---|
| H | P3-004, P3-005 | `caa2cd36-5f03-49ba-ad40-684499e348db` (rev. 1) | Worker 1061 | `a4756def-8ca9-4d52-b32d-bb0cbb8afd96` (accepted) | task `8747d3ed-b785-4a06-b177-4e2b7d53d3a7`, approved by Reviewer 4584 | Integration `211a9c65b5b74b8b82d2fc23ea55af4e` (batch `498cd055f707477e9a3f5ed7a92e04e5`); Library `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |
| Q | P3-011 | `38c5698c-a1eb-44ea-9ceb-0dc95a3a1126` (rev. 1) | Worker 1061 | `0dbdc633-b4fe-4595-ba88-5918cd1a00b7` (accepted) | task `b8f118e7-b624-493e-bdb8-620dd9487aa7`, approved by Reviewer 4601 | Integration `e5ccd2e1bd6742dca94d2fb1315a5338` (batch `498cd055f707477e9a3f5ed7a92e04e5`); Library `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |
| C1 | P3-008 | `d626bcc2-5835-4a80-91cd-e21d024873f8` (rev. 1) | Worker 1056 | `b59f1f2b-3688-4b76-a5ee-a2fb24d69fab` (accepted) | task `0dc4e56a-b30b-47e6-bad1-46cbe75e6b75`, approved by Reviewer 4597 | Integration `1fc5f1d2e564467eba6e1d972058c4ec` (batch `498cd055f707477e9a3f5ed7a92e04e5`); Library `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |
| C2 | P3-009 | `64ecc1f7-3a59-4c8e-b166-b2dc730ab652` (rev. 1) | Worker 1056 | `9530dc7b-7b6e-42f4-ba40-a98a16fd1cf9` (accepted) | task `6a73092b-3588-4c09-a01b-6ea00f6bfab4`, approved by Reviewer 4599 | Integration `87dc9ad3573943bfa39ec36c0c11a0f6` (batch `498cd055f707477e9a3f5ed7a92e04e5`); Library `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |
| G | P3-010, P3-020, P3-021 | `2f1a6ae5-8f1c-488f-bbd4-cbf01de18f1a` (rev. 1) | Worker 1056 | `0c4f8903-6b13-431b-9f9c-a62724cbc48f` (accepted) | task `19dbf92e-23fb-4ca8-a286-11c73300b7a4`, approved by Reviewer 4620 | Integration `b4fa028c20fe474f856b4f57f367f311` (batch `498cd055f707477e9a3f5ed7a92e04e5`); Library `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |
| A1 | P3-053 | `08ded917-42cf-41b8-81d1-cb72c7bc4075` (rev. 1) | Worker 1056 | `c5d67407-1ece-405f-9b01-2a8f4d3086ba` (accepted) | task `2a981217-b047-44ce-ba8b-724e9e324b89`, approved by Reviewer 4662 | Integration `79c5bababd434990b72b392c3e91de39` (batch `601d50d0ad7d477ba5cfaa8c405869d0`); Library `64f062d4c57e9cc6f8151bc80364bc55c16272c5` |
| U | P3-006 | `2aef5c7d-6385-402a-b74f-f354ead2dfcd` (rev. 1) | Worker 1061 | `55c48abc-0cea-4e03-b5af-b7ceebad0796` (accepted) | task `c6e5c250-3988-4c4d-9b88-fbd479260398`, approved by Reviewer 4670 | Integration `67d7871d65414f27869a8075cf7ab3cb` (batch `289cd90d6d7147ce8016ea239c85dce3`); Library `6a6c913c7339c50634dd74722034032e7a167d97` |
| R | P3-007 | `adb0a264-39e0-45f2-a028-e73ac455c76b` (rev. 1) | Worker 1061 | `2f66e861-0f7d-491f-8495-0711a31b3184` (accepted) | task `817a95d1-6e04-4c09-9077-1ac20471d17e`, approved by Reviewer 4672 | Integration `a1c923e88d254881907b69bc1f74194f` (batch `289cd90d6d7147ce8016ea239c85dce3`); Library `6a6c913c7339c50634dd74722034032e7a167d97` |
| F1 | P3-050 (a) | `5f30abe5-7a2e-4014-a1eb-e54fa9a05e36` (rev. 1) | Worker 1061 | `6524d6c6-eeb4-48e3-9241-d92692bb17a1` (accepted) | task `d1e28cdc-e99e-41c0-a718-82f2cbd04a08`, approved by Reviewer 4673 | Integration `2530ffcde72643aaae38c847e33c3ef0` (batch `289cd90d6d7147ce8016ea239c85dce3`); Library `6a6c913c7339c50634dd74722034032e7a167d97` |
| F2 | P3-050 (b) | `155f1d4a-9c67-47a0-b507-69e1e735a1b0` (rev. 1) | Worker 1061 | `b9edfc1c-4a48-4cf0-8438-6e3c63263e84` (accepted) | task `fb463bfe-8cac-427b-aef9-c7d0ca68b7c9`, approved by Reviewer 4674 | Integration `571e84cc4bf54940acac0ee82bf309fe` (batch `289cd90d6d7147ce8016ea239c85dce3`); Library `6a6c913c7339c50634dd74722034032e7a167d97` |
| T1 | P3-051 | `22d6e99f-5e4a-4acc-9fe1-2798a572f2d4` (rev. 1) | Worker 1061 | `cb6f46be-e8a2-4d31-9fa4-71f4f7e8b843` (accepted) | task `bf303723-fe3a-4e68-a7d7-a7ca91e349e4`, approved by Reviewer 4676 | Integration `76bf6372b0b94059b17c484eec26a29a` (batch `289cd90d6d7147ce8016ea239c85dce3`); Library `6a6c913c7339c50634dd74722034032e7a167d97` |
| T2 (superseded) | P3-052 | `ff029319-8cd0-4705-9d72-1866301a6db9` (rev. 1) | Worker 1061 | `093d205c-30ba-4e65-ae0d-a81a2a547a1d` (accepted) | task `b6a628f7-2936-43aa-ae94-7f7693657f9b`, approved by Reviewer 4683; review invalidated by the revision change | Not published |
| T2 | P3-052 | `ac993aaa-82db-4d69-bfc4-5e83aff4939e` (rev. 2) | Worker 1061 | `790f0909-57da-41c2-97d4-a5fb4a35f13d` (accepted) | task `985cdb21-6551-4faa-9653-006bf1a602ae`, approved by Reviewer 4742 | Integration `0c894c205a5f49b7988b9bce49e349ad` (batch `18c3545d35894e979aa9890314e49d25`); Library `cde31751c7864199419ad8fae8b7f3474639ba24` |
| V (superseded) | P3-055 | `cc489da6-2cfa-4642-b06b-d27a0d974848` (rev. 1) | Worker 1061 | `f24f33dd-b35d-44c7-a833-d150b78abb2d` (accepted) | task `1b2f28d0-cfe8-4100-93c3-7d5b9cda90a6`, approved by Reviewer 4686; review invalidated by the revision change | Not published |
| V | P3-055 | `487a7a22-8ecf-41f2-8627-bcec972025e9` (rev. 2) | Worker 1061 | `89ea7d8b-2884-409b-bb85-bd9eda13be04` (accepted) | task `5ff8846c-b408-41f5-89c3-5b55f66c3d78`, approved by Reviewer 4745 | Integration `d05fb34240344094978c28cdf29d37a3` (batch `8e63a9d684c34de2ab37ceba21c8d400`); Library `3c5f92411ab2bcef7d4e5ae82c66a7ae30ea3fdf` |
| W (superseded) | P3-056 | `3c2a1328-1c3c-41bd-b9e8-c9027bbcbae4` (rev. 1) | Worker 1061 | `c4451a67-924e-4763-888d-a3ed911221c7` (accepted) | task `04c3e223-1d96-4518-bf54-edd7a6fc5fba`, approved by Reviewer 4700; review invalidated by the revision change | Not published |
| W | P3-056 | `77c25dbe-2d52-4d6f-903a-4369260871b7` (rev. 2) | Worker 1061 | `3ca549ad-b3c3-4e54-9268-461354d6a62e` (accepted) | task `2a303e81-ae6d-4fc3-8601-ed6729d9a2ff`, approved by Reviewer 4748 | Integration `3b10686c667640cb84941c98a0e1405e` (batch `8e63a9d684c34de2ab37ceba21c8d400`); Library `3c5f92411ab2bcef7d4e5ae82c66a7ae30ea3fdf` |
| K (superseded) | P3-058 | `9101da0c-60b1-47c1-a91d-88066db1d8ca` (rev. 1) | Worker 1061 | `c4064440-935c-451c-8baf-f19c9db55461` (accepted) | task `e042ca38-eaa7-4709-9a1e-230a1024e1a9`, approved by Reviewer 4706; review invalidated by the revision change | Not published |
| K | P3-058 | `2eb98dd7-079a-4093-bb50-a5c5ba5684e7` (rev. 2) | Worker 1061 | `ddeea18f-bbe8-45b6-8b67-f66e8bf2f5ba` (accepted) | task `b51234d2-67e9-45ca-ab95-6fbfe73cfa0a`, approved by Reviewer 4749 | Integration `256efd3085d647f1a076750275ff82a3` (batch `8e63a9d684c34de2ab37ceba21c8d400`); Library `3c5f92411ab2bcef7d4e5ae82c66a7ae30ea3fdf` |
| A2 (superseded) | P3-054 | `aa388ad6-e852-4b2d-9f39-e6bdd353db96` (rev. 1) | Worker 1056 | `39cee6ba-bbc3-4bff-b493-645bbe34db45` (accepted) | task `4f1fda0b-eff9-4b1e-801f-e656d9fc4704`, approved by Reviewer 4699; review invalidated by the revision change | Not published |
| A2 | P3-054 | `7af37353-b51d-418f-ab6e-72a1d7058d04` (rev. 2) | Worker 1056 | `cf233d96-dc5a-45cf-b172-509511b1c858` (accepted) | task `cc923bb8-968d-435e-8352-85daac7dc528`, approved by Reviewer 4738 | Integration `37feca68a7f44f3eb9b6bb6ac67ba410` (batch `18c3545d35894e979aa9890314e49d25`); Library `cde31751c7864199419ad8fae8b7f3474639ba24` |
| S (superseded) | P3-022 | `8f1be1dc-022d-4f85-ba70-a58cabf9cc3d` (rev. 1) | Worker 1056 | `82d05e10-ed4a-4bfb-959e-7881155223b2` (accepted) | task `c353fe38-6c05-4963-951d-08c84ddf9790`, approved by Reviewer 4702; review invalidated by the revision change | Not published |
| S | P3-022 | `7670349d-71d7-4fb5-8be7-2c960b97267a` (rev. 2) | Worker 1056 | `d68e2784-b23d-4bf3-934b-48d73fd78231` (accepted) | task `0560a0bc-aae9-45a1-afed-33ccf3740ade`, approved by Reviewer 4743 | Integration `acb580e68e094c73bd9c60e609be3f97` (batch `8e63a9d684c34de2ab37ceba21c8d400`); Library `3c5f92411ab2bcef7d4e5ae82c66a7ae30ea3fdf` |

No correction candidate was rejected or withdrawn. "rev. 1" and "rev. 2" are
the task revisions to which the candidate is bound. Each revision-2
replacement has the same files as the candidate it replaces and names it in
its introduction. Machine validation is not semantic acceptance. This note
itself requires separate independent review and publication.

### Sources read in review

The reviewers recorded these original-source checks in the publication or
review receipts. H: Milne VII.2, printed pp.203, 205–206 (PDF pp.212,
214–215). Q: Artin–Tate, printed pp.5–6 and 11 (PDF pp.14–15, 20). U: Milne
I.1.6–1.7, printed p.22 (PDF p.31), and Artin–Tate VI.1, printed p.20 (PDF
p.29). R: Serre, *Local Fields*, I.7 pp.20–22, XIII.2 pp.190–191 and XIII.4
pp.196–198, Henniart 1.1 p.439, and the 2019 Serre corrections (the p.191
erratum concerns Proposition 4(a) and is not relevant). C1: Serre X.3 p.154
(PDF p.160) and VII.5 pp.115–116. F1: Artin–Tate preliminaries, VI.1,
VII.3–4 and XIV.3, and Tate 1979. T1: Serre XI.2–3 pp.167–169 and IX.8
pp.148–149, with the corrections. For the six revision-2 keys the published
review is listed first. T2: Serre V.3 p.83 (PDF p.90) and V.4 pp.87–88 (PDF
pp.94–95), with the 2019 corrections (PDF pp.2–3), in both reviews. V: Serre
IX, Theorem 4 and Corollary, printed p.140, through Theorems 13–14, printed
pp.148–149 (PDF pp.146–155), with the corrections (revision 1: Serre IX
§§2–8, with the corrections). W: Serre VIII.3, printed pp.130–132 (PDF
pp.136–138), especially Proposition 5 on p.131, with the corrections
(revision 1: Serre VIII.3, Proposition 5, with the corrections). K:
Artin–Tate VI.3, printed pp.24–27 (PDF pp.33–36), and its appended errata (PDF
p.202), in both reviews. A2: Cartan–Eilenberg V, Proposition 1.1a, printed
p.78 (PDF p.100), and V.3, printed pp.82–83 (PDF pp.104–105); Harris 1999,
section 2, printed pp.304–305 (PDF pp.6–7); and, for unchanged context,
Berkovich 1.5, pp.10–12, and Grothendieck 1957, 2.4, printed p.148 (PDF
p.30). S: Bernstein–Zelevinsky 1976, printed pp.34–36 (3.18, 3.20, 3.21 and
3.26) with supporting pages; Harris 1997, p.96 (PDF p.22); and Harris 1999,
p.312 (PDF p.14).

## File fingerprints

SHA256 of the 21 owned pairs. The A table identifies the audited versions. In
the C table, every pair equals the published candidate files. Only the five
Lean files with docstring edits differ from A on the Lean side. Each path is
relative to `Langlands/`.

| Pair stem | Lean in A | Markdown in A |
|---|---|---|
| ClassField/Global/ArchimedeanLocalHerbrand | `9200c8023ba6ed8575db035876c1d6ed5c123730e8b2a9c0dec20ff39ea6c8ac` | `168dda7af08c1c1818377727cc3bfc39951fc111acfe4e9c07f1c0011b38e4a9` |
| ClassField/Global/FundamentalClassStatement | `00fe196b13841da63a0091861995747d75e8329f589493ed48b7005e9851864d` | `0f164c6d9039c25c2de9432887cf5e21f50736e7e55ca5fc4f2ce99d1c3afff9` |
| ClassField/Global/IdeleArchimedeanTower | `0269abae0481fb149b79e8bdd3075842bbe4a92a93c70ae6754f823decb7d8f0` | `3f2b901e360e3acc1cb1d18f81cfea8b5ac24a0476ac60bff2080917c3270af6` |
| ClassField/Global/LocalUnitPowers | `2f1b6d39a6162f060fdc78e02fb7781bd9e461414cc79ec3514fa70bf0add37b` | `bc1fd6c693610f9f3fdb78a5064047dc6408c1ba2e42f4a8b4a37a5698c1e054` |
| ClassFieldTheory/Local/ClassFormationCupLawsStatement | `102bac4b5f222d80458249399e83f68b64850f2313550e900fc835ff730181db` | `991d5111c6e66119636314f5c50463473dbbe317c6dc49dbc5588359978ce2db` |
| ClassFieldTheory/Local/PrimeBreakUnramifiedBaseChangeStatement | `ac0c88c93dd0dc7e96d4be650178a9a6388d54f8cc4400b733e8ec5394ff54d1` | `211a3b0e3af6ffdfd39464dc98717077ee782b80035b213c9e3ac323b89cf715` |
| ClassFieldTheory/Local/ResidueNormalization | `5f2be88f053f5ddf6ad1e06695b0032ae37c94b97c003c63b94802719956fb88` | `178409ea7ba1e240a26a8af13a648d7151e4705adf3430b52ad67bca4de0f746` |
| Cohomology/AcyclicResolution/Comparison | `ba6205f88550c64391b68e53cd51d560b7af9b9a4a2b99190535ad5bbf0d9cac` | `79f85e4dfd0201a9ae031916d61ac6e3989822bac21fae63b4c7cc3891995e03` |
| Cohomology/CompactSoft/Statement | `aea658d2b6884e26aba065420a2a3b23ad22b7fdb6bbe7661bd15131404370c4` | `631f221b4e1dd7e6374dd8184b7072b9fcb1a60ca18f63e795eb14b09e80a524` |
| Cohomology/Continuous/FiniteQuotientSystem | `1d776689929557262abb17733aa6c52782cb1070cf349ca887bef283f80b07e7` | `ee34f3d9f53786665a6200a5f8f42826a4f3e49010c9272f378aca00572de79d` |
| Cohomology/DivisibleSystem/InvariantTransition | `abed2fdcb90f6310ad462da1b0876fa30bee70e2e186e5fe05a46bd1c02902bb` | `28e22cac8d7e686f02dbc57c78d31f18d35520575af7f51eb34a758e428bdc52` |
| Cohomology/EquivariantGodement/Statement | `cb0e1606cae9f86069295539028a9d610c29214b26effb0da6dc16def3336efb` | `fb09f5e70363ce03c90359ae6ddba0018e3951ecd97ed30eee6fcf690adc857d` |
| Cohomology/HerbrandQuotient | `8bc001f70c696f1e4b9ebdab83719d65c54703867cbe14dafd2167442c5a4474` | `d39375157236029c53bb34eed97700bc33c109ec972606332a58388ca7d3f081` |
| Cohomology/SmoothCompactComparison/Statement | `4596fe278814dbf6dcfb08fbe1a0d65b501795788dd2852b8d73c6949a3ac922` | `98926953515159245ee343e6cdd0ee34f92b3b487b6fde5f29f5874b4befb985` |
| Cohomology/SmoothGodementComparison/Invariants | `55df370f72949947debbd3017c3c9749399639c63da18fec29266900d736c5b6` | `84de938d3ec09e1b882dedc9f2d6e4c4d751c7e476421170dfd5ab12630f4d39` |
| Cohomology/SmoothGodementComparison/Statement | `d9ba661d50b20563827f5e2d16a686350deb36bdc0cd49f7e6a0e44f8694cd99` | `f49b7389193a5b086f113f8bb38a3b60b4b37df787a302f7f58746ca828768c3` |
| Cohomology/SmoothGodementComparison/Transformation | `0532d12593427cd2791a579566ca94c9dc238c9a4c4b0262a95a750d5a6c5807` | `3bc81eba54340a683c538a0b02b7d2f80590c78497e177d5e3a866aafeb15e1e` |
| Cohomology/SupercuspidalRestriction/Statement | `a7523f22a08cfed3a4774ea53bd795940e1864e1cf1910f9b6f35d5a46424742` | `14c5012fd7e8c43361c1fd0b2ca5e0b2ad0e08569e139cec0429d126f2b1cfea` |
| Cohomology/Tate/CohomologicalTrivialityStatement | `2fc9da6f181f5af956ad051d39346e30fe7b5555038e3f5fd07d11e1e6d5bd90` | `da78709b25cf114dc24066919b2284d1ffc9d2bd6ca1d406d076fdd754ba6d71` |
| Cohomology/Tate/CupProof | `2c3acda2714ee9709a09017e07ea0c52f1888642d048cdd4a3103c243d200076` | `d619301e63df61fbb9cb3296b2bb5c0a7dca1573d47346f6bf2bbdb4acbae368` |
| Global/Arithmetic/KummerSecondInequality | `b4dcb3be27ad8fec2f2e4b4e0d2e2db40fdd8b4ac7b15b7b36f4d80c7e06d33d` | `4227bff6952f8a53e9ad92b4e0a28d05c8dcab8ccd25d3f1f7dad7e1d61c43e4` |

| Pair stem | Lean in C | Markdown in C |
|---|---|---|
| ClassField/Global/ArchimedeanLocalHerbrand | `461dc614634f47f3be28b454ca6339f6090af9fdee310e662d37d1cf58d635ac` | `0c40970a96d46799dcc1cd30da57e655f4d5f1cb725b7badf3625c99aa1b02fe` |
| ClassField/Global/FundamentalClassStatement | `00fe196b13841da63a0091861995747d75e8329f589493ed48b7005e9851864d` | `8774502e9fac72c53a557b5575c3625def2bf2d37c903e4271b5ac7af15cb4e9` |
| ClassField/Global/IdeleArchimedeanTower | `0269abae0481fb149b79e8bdd3075842bbe4a92a93c70ae6754f823decb7d8f0` | `eda57565f587f43f3c095716c52a33c3ee9ee59e1dcd5c792c1dbfe106e17b76` |
| ClassField/Global/LocalUnitPowers | `b5eee65243d045be1e6fd88e9ae3e7f8f4af3339d859140c451fadaed6ea2a2b` | `2b9cca1191893c713bab522bded687f936d34ff103f83acdb837d73486cd970f` |
| ClassFieldTheory/Local/ClassFormationCupLawsStatement | `102bac4b5f222d80458249399e83f68b64850f2313550e900fc835ff730181db` | `5d30220169e23170a6d3c9a33bad933db229f0d9ba9c25e35c25f2b33bdf9cd4` |
| ClassFieldTheory/Local/PrimeBreakUnramifiedBaseChangeStatement | `ac0c88c93dd0dc7e96d4be650178a9a6388d54f8cc4400b733e8ec5394ff54d1` | `65c91ea7106f3217a2e3c1ea084f3d139ab5a0242d1a0e0c1a925781b235b9a6` |
| ClassFieldTheory/Local/ResidueNormalization | `5f2be88f053f5ddf6ad1e06695b0032ae37c94b97c003c63b94802719956fb88` | `5efb2d416ac5130f976de414cd0577866b949f96f7f85f1dc73cac043efbfc27` |
| Cohomology/AcyclicResolution/Comparison | `ba6205f88550c64391b68e53cd51d560b7af9b9a4a2b99190535ad5bbf0d9cac` | `12e98fc1ca52b218e200a33f80d8116a84e7622704373ff6d68934c478b415c3` |
| Cohomology/CompactSoft/Statement | `aea658d2b6884e26aba065420a2a3b23ad22b7fdb6bbe7661bd15131404370c4` | `20074df5c99bd1378e781a78108fa66a1152cc6cb408dfbe24923fdbf67e4718` |
| Cohomology/Continuous/FiniteQuotientSystem | `1d776689929557262abb17733aa6c52782cb1070cf349ca887bef283f80b07e7` | `b393212d389f6faee61d9f6e0596815a2e32504829f8d0a7b8ca0893f2456bd2` |
| Cohomology/DivisibleSystem/InvariantTransition | `abed2fdcb90f6310ad462da1b0876fa30bee70e2e186e5fe05a46bd1c02902bb` | `ac51bed299d1ff0e8efccab224406aae6539c3180c17c5c55600f5b7de7896b4` |
| Cohomology/EquivariantGodement/Statement | `cb0e1606cae9f86069295539028a9d610c29214b26effb0da6dc16def3336efb` | `170be40c0bee800abf035114b5cad97f5b8ef35921f06c28e9197320707235ba` |
| Cohomology/HerbrandQuotient | `8bc001f70c696f1e4b9ebdab83719d65c54703867cbe14dafd2167442c5a4474` | `b47008062e1a8b66ee1ec8e405890bcb42f08adcf2ff9e5daa443c61ec8e5ab3` |
| Cohomology/SmoothCompactComparison/Statement | `4596fe278814dbf6dcfb08fbe1a0d65b501795788dd2852b8d73c6949a3ac922` | `db763b2fa6fc60de81434cc82f71ec7cc439d5ec96e2f564c313e1c3556b5db5` |
| Cohomology/SmoothGodementComparison/Invariants | `18de39ad143a7e16f3661a017b9ab40545285498ce160525e51fe9f92e493726` | `411fb6eae4738a4e562fe8dea63b1f60b8d842004d7052ba31457af24973b7e9` |
| Cohomology/SmoothGodementComparison/Statement | `d9ba661d50b20563827f5e2d16a686350deb36bdc0cd49f7e6a0e44f8694cd99` | `2e3876001277b164ae9a6f5aa735f541608c84eee76db4a622319a905d1cd07f` |
| Cohomology/SmoothGodementComparison/Transformation | `f7be004503eee721ef489954a8cf541a5f1cbb8ecd4af2ca7747920957871248` | `4bdc029021b471042af7f5e653925fa9cfbec586f1be8c7e49bb70343ec36a17` |
| Cohomology/SupercuspidalRestriction/Statement | `524f730fda3195fe217a03cbad30ed659724f0558f4dd14556cc393d704c2e25` | `8a1de9c5b08445809a004208901e34110bb41212523b71b2322dad33f9370227` |
| Cohomology/Tate/CohomologicalTrivialityStatement | `2fc9da6f181f5af956ad051d39346e30fe7b5555038e3f5fd07d11e1e6d5bd90` | `2c50db974310fb58ddcb40b7715c7a37ecf6da350cc680e7a65aefedb3263e7b` |
| Cohomology/Tate/CupProof | `2c3acda2714ee9709a09017e07ea0c52f1888642d048cdd4a3103c243d200076` | `756ae22af1cdedf5b95ee4a677a84dd9553417f00ceb1b0412e14a3dbb71a8e4` |
| Global/Arithmetic/KummerSecondInequality | `b4dcb3be27ad8fec2f2e4b4e0d2e2db40fdd8b4ac7b15b7b36f4d80c7e06d33d` | `4dd4d36e8f2fce5950037c14e704a075020cc1692dfe94dc26a97bf00b05c4b1` |

The audit report has SHA256
`d9a25f35dc2d7bef0351ba0891db168b0c3cc797a281d0a9944e930fe43d5eeb`.
