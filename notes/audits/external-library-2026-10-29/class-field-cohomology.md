# External Library audit 2026-10-29: class field theory, cohomology and global arithmetic

This note records the verdicts for the 19 findings P3-004–P3-011, P3-020–P3-022,
P3-050–P3-056 and P3-058 of the external Library audit of 2026-10-29. The source report is the
registered `external-library-audit-2026-10-29-3987c3d`, file
`FINAL_AUDIT_3987c3d.md` (rows 67–74, 88–90, 135–141 and 143). Its allegations
were treated as unverified. They were checked against complete Lean
declarations, section variables, universes, paired Markdown, the original
source where one is cited, and the record of the corrections that entered
the Library.

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

The 21 audited file pairs (see the fingerprints below) were followed through
the Library history. `b58bd42aee6a565b689f0f0c008506e23b1b6560` leaves them
byte-identical to A. The corrections changed them in
`bc8de2287e5c24972c55277b2aa9611523dfc5dc` (keys H, Q, C1, C2, G),
`64f062d4c57e9cc6f8151bc80364bc55c16272c5` (A1),
`6a6c913c7339c50634dd74722034032e7a167d97` (U, R, F1, F2, T1),
`cde31751c7864199419ad8fae8b7f3474639ba24` (T2, A2) and
`3c5f92411ab2bcef7d4e5ae82c66a7ae30ea3fdf` (S, V, W, K). The intermediate
heads `047f3489`, `c8ae014c`, `f35c1c21` and `9330fa8d` leave them
byte-identical to `6a6c913c`. In the Library's history, `9330fa8d` is the
previous head of `cde31751`, and `cde31751` the previous head of `3c5f9241`.
Among the audited pairs, these two commits change only the files of the six keys
published in them. So no other publication repaired or reintroduced any finding. The comparison
snapshot is Library `3c5f92411ab2bcef7d4e5ae82c66a7ae30ea3fdf` (C below). At
C all 19 findings are repaired, and every audited pair is byte-identical to the
files of each published candidate that contains it. The later head
`d1abfe1f26a6fdf1d986073e68c049e12c3f6ea5` only adds another audit note and
changes `wiki/README.md`, so every Lean file and every audited pair there is
byte-identical to C.

### Corrections

Each correction is a focused change; none changes a Lean statement or proof
target, and none edits a file outside the pairs concerned. For six of the
corrections an earlier, identical version did not enter the Library; the
version that did is listed in the correction table.

### Lean evidence

The Lean environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. The statements,
hypotheses and universes of the proved declarations cited in this note were
read from their complete declarations in the Library source, at the lines
given in the ledger. `lean_check` probes, which are not Library files,
added the following machine checks.

- A first diagnostic ran before C. It printed
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
- A second diagnostic ran at C with
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
- A diagnostic for P3-004 imports only
  Mathlib. It proves `FiniteDimensional F E` for `F E : Type` under
  `[Field F] [Field E] [NumberField E] [Algebra F E]`, with no errors and three
  style warnings. The Library variables (CF/Global/ArchimedeanLocalHerbrand.lean:95)
  have `F E : Type u`; the argument does not depend on the universe.
- A diagnostic for P3-053 reported no
  errors or warnings. It elaborates `acyclicResolutionComparisonStatement` at
  `AcyclicResolutionComparisonStatement.{u + 1, u, u + 1, u}` (the hypothesis
  of `comparisonIso`, Coh/SmoothGodementComparison/Transformation.lean:128 at C) and
  `AcyclicResolutionComparisonStatement.{u + 1, u, u', v'}` (the hypothesis of
  `sheafComparisonIso`, Invariants.lean:136 at C), and `resolutionLiftStatement`
  at `ResolutionLiftStatement.{u + 1, u}`.

An axiom list shows only that a declaration is proved without `sorryAx` or an
added axiom. A printed type that is only a statement name does not show what
the statement says. The content, hypotheses and scope of each cited statement
come from reading its Lean source. The corrected modules of some findings
were checked by compilation only. Their counterexamples were checked by hand, not in Lean.

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
| P3-050 (a): fundamental class | Holds | CF/Global/FundamentalClassStatement.md:92 says "Global invariants are not formalized" and md:155–156 calls global invariant maps later work and the proof separate work. `GlobalInvariantStatement` (CF/Global/InvariantStatement.lean:119) with its invariant-map interface is published and proved by `globalInvariantStatement` (InvariantProof.lean:20); `globalFundamentalClassStatement` (FundamentalClassProof.lean:35) proves this module's statement. | Key F1 (md:92–101, 163–168 at C). The targets keep their hypotheses (relative class formation and arithmetic normalization). |
| P3-050 (b): idele tower | Holds | CF/Global/IdeleArchimedeanTower.md:51 says "`GlobalInvariantStatement` remains open". | Key F2 (md:51–54 at C). |
| **P3-051** | **Holds** | CFT/Local/ClassFormationCupLawsStatement.md:46–48 says that a proof of `TateCupIsomorphism` "can be applied to it once that proof exists"; md:80–81 says Tate's theorem is to be proved separately. `tateCupIsomorphism : TateCupIsomorphism.{u}` (Coh/Tate/TateTheoremProof.lean:191) and `classFormationTateIsomorphisms` (CFT/Local/ClassFormationTateIsomorphismsProof.lean:95) are proved. | Key T1; repaired at C (md:47–51, 83–85). The conditional interface is kept. |
| **P3-052** | **Holds** | CFT/Local/PrimeBreakUnramifiedBaseChangeStatement.md:58–61 says `PrimeTotallyRamifiedBreak` "is not yet proved". `primeTotallyRamifiedBreak : PrimeTotallyRamifiedBreak.{u, v}` (CFT/Local/PrimeRamificationBreakProof.lean:13) proves it. This module's own statement is proved separately by `primeBreakUnramifiedBaseChange` (PrimeBreakUnramifiedBaseChangeProof.lean:17). | Key T2; repaired at C (md:58–70): cites `primeTotallyRamifiedBreak` as the proof and `primeBreakUnramifiedBaseChange` as the separate proof of this module's statement. |
| **P3-053** | **Holds** | See the subrows. | Key A1; repaired at C. |
| P3-053 (a): comparison | Holds | Coh/AcyclicResolution/Comparison.md:119–131 calls `AcyclicResolutionComparisonStatement` unproved and plans a proof; md:176–191 says the same of the independence and naturality statements. `acyclicResolutionComparisonStatement` (Coh/AcyclicResolution/ComparisonProof.lean:247), `resolutionComparisonIndependenceStatement` (IndependenceProof.lean:22) and `resolutionComparisonNaturalityStatement` (NaturalityProof.lean:21) are proved. | Rewritten (md:126–131, 177–190, 197–199 at C). The explicit hypotheses of `comparisonNatIso` are kept. |
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
1.6–1.7, printed p.22 (PDF p.31). This passage was read. No erratum
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
At C only proofs outside the Library existed, as in P3-022 (b). That note is
not one of the pairs concerned; this is recorded here for a later correction.

## Corrections and the commits where they entered the Library

Each correction is a focused change whose entry pair is the corrected pair.
It edits only Markdown and docstrings of the pairs concerned. Every
correction was built with Lake when it entered the Library.

| Key | Findings | Publication |
|---|---|---|
| H | P3-004, P3-005 | Library `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |
| Q | P3-011 | Library `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |
| C1 | P3-008 | Library `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |
| C2 | P3-009 | Library `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |
| G | P3-010, P3-020, P3-021 | Library `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |
| A1 | P3-053 | Library `64f062d4c57e9cc6f8151bc80364bc55c16272c5` |
| U | P3-006 | Library `6a6c913c7339c50634dd74722034032e7a167d97` |
| R | P3-007 | Library `6a6c913c7339c50634dd74722034032e7a167d97` |
| F1 | P3-050 (a) | Library `6a6c913c7339c50634dd74722034032e7a167d97` |
| F2 | P3-050 (b) | Library `6a6c913c7339c50634dd74722034032e7a167d97` |
| T1 | P3-051 | Library `6a6c913c7339c50634dd74722034032e7a167d97` |
| T2 | P3-052 | Library `cde31751c7864199419ad8fae8b7f3474639ba24` |
| V | P3-055 | Library `3c5f92411ab2bcef7d4e5ae82c66a7ae30ea3fdf` |
| W | P3-056 | Library `3c5f92411ab2bcef7d4e5ae82c66a7ae30ea3fdf` |
| K | P3-058 | Library `3c5f92411ab2bcef7d4e5ae82c66a7ae30ea3fdf` |
| A2 | P3-054 | Library `cde31751c7864199419ad8fae8b7f3474639ba24` |
| S | P3-022 | Library `3c5f92411ab2bcef7d4e5ae82c66a7ae30ea3fdf` |

A machine build is not a check of meaning.

### Sources read when the corrections were checked

The following original-source checks were recorded for the corrections. H: Milne VII.2, printed pp.203, 205–206 (PDF pp.212,
214–215). Q: Artin–Tate, printed pp.5–6 and 11 (PDF pp.14–15, 20). U: Milne
I.1.6–1.7, printed p.22 (PDF p.31), and Artin–Tate VI.1, printed p.20 (PDF
p.29). R: Serre, *Local Fields*, I.7 pp.20–22, XIII.2 pp.190–191 and XIII.4
pp.196–198, Henniart 1.1 p.439, and the 2019 Serre corrections (the p.191
erratum concerns Proposition 4(a) and is not relevant). C1: Serre X.3 p.154
(PDF p.160) and VII.5 pp.115–116. F1: Artin–Tate preliminaries, VI.1,
VII.3–4 and XIV.3, and Tate 1979. T1: Serre XI.2–3 pp.167–169 and IX.8
pp.148–149, with the corrections. For T2, V, W, K, A2 and S the later check is
listed first. T2: Serre V.3 p.83 (PDF p.90) and V.4 pp.87–88 (PDF
pp.94–95), with the 2019 corrections (PDF pp.2–3), in both checks. V: Serre
IX, Theorem 4 and Corollary, printed p.140, through Theorems 13–14, printed
pp.148–149 (PDF pp.146–155), with the corrections (earlier: Serre IX
§§2–8, with the corrections). W: Serre VIII.3, printed pp.130–132 (PDF
pp.136–138), especially Proposition 5 on p.131, with the corrections
(earlier: Serre VIII.3, Proposition 5, with the corrections). K:
Artin–Tate VI.3, printed pp.24–27 (PDF pp.33–36), and its appended errata (PDF
p.202), in both checks. A2: Cartan–Eilenberg V, Proposition 1.1a, printed
p.78 (PDF p.100), and V.3, printed pp.82–83 (PDF pp.104–105); Harris 1999,
section 2, printed pp.304–305 (PDF pp.6–7); and, for unchanged context,
Berkovich 1.5, pp.10–12, and Grothendieck 1957, 2.4, printed p.148 (PDF
p.30). S: Bernstein–Zelevinsky 1976, printed pp.34–36 (3.18, 3.20, 3.21 and
3.26) with supporting pages; Harris 1997, p.96 (PDF p.22); and Harris 1999,
p.312 (PDF p.14).

## File fingerprints

SHA256 of the 21 audited pairs. The A table identifies the audited versions. In
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
