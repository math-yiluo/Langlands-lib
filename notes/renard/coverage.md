# Renard 2026: coverage ledger and execution boundaries

This is the initial ledger for the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`, revision 2, maintained by Worker 6.
It records inspected passages and preserves every other section as an explicit
audit backlog. It does **not** claim complete assertion-level inventory or
completed formalization. The detailed first-pass rows are in
[the initial passage audit](initial-passages.md).
Reading extents and task-status observations below describe that initial pass.
The replacement corrects its annihilator orientation and module-completion
scope. The dated updates below record selected later reading and child-task
developments; the remaining initial-pass rows retain their original scope.

The [small-projective and original-module progress note](category-module-progress.md)
records selected verified publications and pending work checked on 30 October
2026. It supplements, rather than revises, the initial reading and status rows
below.

The [C.II quotient and finite-localization audit](stable-quotients.md), updated
31 October 2026 by Worker 709, records the published stable-endomorphism lemma,
its separate quotient exact-sequence proof, the actual localization
constructions and the internal stable-ideal finite-localization theorem.
It also records the published additive-to-scalar generation comparisons and
their actual finite-localization consequence under three explicit additive
generation premises. The source-facing nonunital finiteness comparison remains
open. Only the C.II navigation row below is updated by that audit.

The [A.III.1 endomorphism-localization progress note](endomorphism-localization.md),
dated 31 October 2026 by Worker 709, verifies the published kernel/exhaustion,
quotient-comparison, extension-converse, surjective-map and B-linear
universal-property proofs. It updates the A.III navigation row only; categorical
packaging, localization exactness, representability and other A.III assertions
remain open. All other initial-pass statuses retain their stated date and scope.

The [C.III coefficient, decomposition and common-basis progress note](integer-lattice-coefficients.md),
dated 1 November 2026 by Worker 709, verifies the published tuple/representation
equivalence and the representation and supplied-tuple coefficient proofs.
It also verifies the standalone all-integer binomial and polynomial-coefficient
statement and proof, the simultaneous generalized-weight decomposition
proof, and the internal arbitrary-field common-basis proof for supplied commuting
nilpotents. It updates only the C.III navigation row. Support identification, common
triangular blocks and their multivariable factorization formulas remain
obligations; the note does not claim completion of C.III.

The [C.I commutative-dimension progress note](commutative-dimension.md), updated
1 November 2026 by Worker 709, records the published exact real-power bounds,
actual nilpotent maximum, transport, base cases and filtration. It now verifies
nine further intermediate proofs: endpoint, complement generation and
restriction, monotonicity, head/tail estimates, maximizing complement, actual
joint decomposition, finite-sum power assembly and the normalized numerical
contradiction. Nineteen newer construction, statement and proof pairs match
the supplied Library `1741653e5f4f861282ff64d062269adbcc65c686`; older audits
retain their recorded commits. The floor recurrence, maximum power bound by
the source induction, and actual nilpotent-block reduction have published
statements and separate open proof tasks. This refresh updates only the C.I
navigation row below and does not close C.I or the whole-book program.

The [I.4.2 coefficient-convention audit](duality-coefficient-conventions.md),
dated 1 November 2026 by Worker 6, records the source passages, a conjugation
example separating commuting actions from equality of recovered coefficients,
and the remaining sufficient-input comparison and full-source obligations.
It updates only the I.4 navigation row. The audit itself supplies no Lean result
and does not close either duality comparison or decide the intended convention.
A later direct check on 1 November 2026 verified regular-factor statement
`b860ee57-1ca6-4a9a-812d-dbe23320fcf4` as accepted and public. Its declaration is
`Langlands.Algebra.RenardRegularCoefficientStatements.RegularCoefficientComparisons`;
it states sufficient-input coefficient equalities and compatibility for the actual
regular actions. The separate proof task
`b5c77a5a-3a42-4403-a140-2cebcd49de63` was ready without an executor or artifact.
These statements leave the tensor-dual equivalences and full-source coefficient
convention open.

## Reference and reading record

The governing reference is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026:

- Registered source: `renard-2026-representations-groupes-reductifs-padiques`.
- File: `/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
- SHA-256: `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
- Length: 296 PDF pages. In the numbered body, PDF page = printed page + 6.

Worker 6 checked the title, date, page count and full file hash. The source
passages read for this initial plan are PDF pages 1, 5–7, 9–16, 36–39 and
109–111. The bibliography entries [10], [21], [26], [29] and [42] were also
located on PDF pages 287–289. Extraction of the remaining pages is not a claim
to have read them. In particular, the proof of I.1.5 continues beyond the
current reading boundary.

The 2026 preface identifies a replacement for the former incorrect injectivity
proof of (VI.5.1.3). Its current proof must be audited directly; an earlier
edition's argument is not evidence for this item. No project Renard errata file
was found in the initial local search. The author-site address in the preface
returned HTTP 404 during that search; this does not establish that no errata
exist. Review `b2ff6d20-2c13-4811-8514-46ae8eee3e2a` subsequently reports a working author page at `perso.pages.math.cnrs.fr/users/david.renard/`, a matching 2026 PDF hash, and separately labeled 2010 errata. Worker 6 subsequently read the registered 2010 correction relevant to I.5.1, as recorded below. This does not close the audit of other corrections or further errata discovery.

## I.5.1 assertion update, 1 November 2026

Worker 6 read the original I.5.1 on printed p.26 / PDF32, including both proofs.
The algebra is complex and idempotented, and the module is nondegenerate for its
original, possibly nonunital action. Each actual fixed space `eM` has exactly the
complex coefficients recovered from that action. No global finite dimension or
separately supplied complex structure on the original carrier is assumed.

| Source assertion, all at printed p.26 / PDF32 | Lean declaration or design | Checked status and obligation |
| --- | --- | --- |
| Unnumbered definition: every `eM` is finite-dimensional | `Langlands.Algebra.NonUnitalModuleAdmissible.IsAdmissible` | Candidate `72e9e547-d03b-4bea-982a-30a3e55205ad` passed machine validation and independent review `cb965063-f768-4b0e-81c6-1687e47d1842` by Reviewer 7124. Direct fetch still reported staged and nonpublic. It uses actual `FixedPart` and exactly `NonUnitalModuleCorner.complexModule`, with independent algebra/carrier universes. Publication remains required. |
| Unnumbered proposition: admissibility iff the canonical inclusion into the nondegenerate bidual is an isomorphism | Draft `Langlands.Algebra.NonUnitalModuleAdmissibilityStatements.AdmissibleIffEvaluationBijective` | Specifies bijectivity of exactly `NonUnitalModuleDual.evaluation hA hM`. Statement task `f37fd8da-fde3-44fc-b66b-632fc07dfd1d` revision 1 was freshly inspected as ready with no executor or artifact and is gated on the definition. Shared draft revision 1 is unreviewed. A complete private proof compiles, as described below; statement and proof publication remain required. |
| Unnumbered corollary, first conclusion: the nondegenerate dual of an admissible module is admissible | Draft `Langlands.Algebra.NonUnitalModuleAdmissibilityStatements.AdmissibleDual` | Same task/draft. Selects exactly the actual `dualAction hA hM`, the opposite algebra and the published dual nondegeneracy witness. A complete private proof transfers finite dimension through the actual fixed-part duality and canonical scalar equality. No proof candidate or acceptance is claimed. |
| Unnumbered corollary, second conclusion: an admissible module is simple iff its nondegenerate dual is simple | Draft `Langlands.Algebra.NonUnitalModuleAdmissibilityStatements.AdmissibleSimpleIffDualSimple` | Same task/draft. Uses `CategoryTheory.Simple` on the actual `NondegenerateModuleCat` objects and `dualObject`. A complete private proof uses actual-dual separation, exactness and canonical reflexivity by the alternate categorical route below. Independent review and publication remain required. |

The shared draft also supplies aggregate `AdmissibilityDuality`. Recovery check
`53a184f9-ef0b-4a5a-8559-a6d62a4f3625` compiled the definition and private statement
draft with zero errors/warnings and confirmed that aggregate returns `Prop`.
This is private development evidence, not independent acceptance.

The internal comparison construction
`Langlands.Algebra.NonUnitalModuleFixedBidualMaps.toOrdinaryBidual` and its reverse
have candidate `8178576d-8bad-4dfb-aa7c-ec71322a26ae`. Fresh exact fetches of this
candidate and admissibility candidate `72e9e547-d03b-4bea-982a-30a3e55205ad`
still reported staged and nonpublic, despite successful machine validation and
unqualified independent reviewer approvals. Comparison statement task
`485c30f0-5929-44b9-a329-565bed443c9a` revision 1 was freshly inspected as ready
with no executor or artifact, gated on the exact comparison construction
candidate. Its unreviewed shared draft revision 1 states both inverse equations
and the square with the exact canonical evaluation as
`NonUnitalModuleFixedBidualStatements.FixedBidualComparisons`.

Worker 6 completed private proofs of both comparison equations, the evaluation
square and all three source consequences. The combined private theorem
`Langlands.Algebra.NonUnitalModuleAdmissibilityProof.admissibilityDuality`
compiled and was inspected afresh in diagnostic
`96a6b841-d621-4c21-819f-224aa21eff19`: zero errors or warnings, independent
algebra/carrier universes, and only `propext`, `Classical.choice` and `Quot.sound`
as axioms. This check overlays the unpublished statement/comparison pairs and
the import correction described below. It supplies no exact-target proof
acceptance against a published statement.

The private reflexivity proof uses published actual-dual separation for
injectivity. In the forward direction, a fixing idempotent puts a given actual
bidual vector in a fixed space; finite-dimensional ordinary reflexivity and
the comparison square supply its preimage under the exact evaluation. In the
converse, surjectivity and injectivity of that evaluation, together with its
original A-linearity, give surjectivity of ordinary evaluation on each fixed
space. Mathlib's reflexivity criterion then gives its finite dimension for
precisely the recovered complex coefficients. Dual admissibility uses the
published actual fixed-part duality separately.

The private simplicity proof takes an alternate categorical route to the source
annihilator argument. Separation makes each actual dual functor faithful, and
the published exactness results reverse monomorphisms to epimorphisms. These
properties reflect simplicity through the actual dual. For an admissible
module, the exact canonical evaluation is an isomorphism by the private
reflexivity proof; transporting simplicity to that actual bidual and reflecting
through the opposite dual proves the other implication. This is a proof
development over the original objects and actions, not an assumed dual
equivalence. Independent semantic review remains necessary.

Jointly importing canonical bidual evaluation and the actual-dual exactness
closure exposed a duplicate generated declaration for a local full-dual
instance. Dedicated correction task
`5df049aa-15bc-4ff1-942d-5c8098c45fc1` revision 1 was freshly inspected as ready
with no executor or artifact and a complete unreviewed shared draft revision 1.
It explicitly names the three local instances in
`NonUnitalModuleDualMapExactnessProof`, preserving Worker 702's proof bodies,
the published exact target, actions, coefficient structures and all four
universes. The private joint-import regression and original-theorem inspection
passed in diagnostic `7328574a-5749-4d1b-bc78-4ede7f20e61d`.
This is an import compatibility prerequisite, not a new exactness assertion.
The complete I.5.1 proofs remain private until their exact statements,
comparison prerequisites and this correction are published; subsequent proof
candidates still require independent review, build and exact-target validation.

Worker 6 also read the registered `renard-2010-corrections-complements`, SHA-256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`, PDF1–2,
especially its correction to the printed 2010 p.29 reflexivity proof. The 2026
text incorporates the converse through the ordinary algebraic bidual of each
`eM`. The private fixed-space comparison and canonical evaluation proof follows
that corrected route. The original proof of the corollary uses the fixed
spaces for dual admissibility and annihilators for simplicity; the private
categorical simplicity proof above takes a different route to the same
statement. Neither source reading nor private compilation closes the remaining
review and publication obligations.
I.5.2 and the rest of I.5 retain their audit and implementation obligations.

## Scope and evidence rules

The book program covers Chapters I–VII, Appendices A–C, mathematical assertions
in the chapter notes, and unnumbered assertions. Its priority is below Task 0.
Existing owners, suspended work and user controls remain unchanged.

For Chapters VI–VII, the chosen generality is an explicit framework over actual
groups, topologies, subgroups, decompositions, lattices, roots, Weyl actions and
maps. Chapter V external structural results may be named, itemized hypotheses
where the source imports them without proof. In-book structural derivations
remain proof obligations. Representation-theoretic conclusions such as
admissibility, Bernstein decomposition, second adjointness and classification
cannot be inserted into that structural hypothesis list. A general
algebraic-group/Bruhat–Tits realization is a separately tracked extension.

The framework must retain positive-characteristic local fields wherever the
source permits them. GL-specific implementations are specialization candidates,
not proofs of arbitrary reductive statements. Every conditional result must
display its remaining hypotheses.

The ledger uses the following distinctions:

| Status | Meaning |
| --- | --- |
| Backlog | A section is located, but its individual assertions have not all been read and classified. |
| Read/open | The listed passage has been read; the stated implementation or correspondence obligation remains open. |
| Definition task | A focused construction contract is published; this alone supplies no Lean result. |
| Candidate | An immutable contribution exists; validation, independent review and publication are distinct further facts. |
| Reuse lead | An exact declaration or module has been inspected, but the complete Renard correspondence has not been closed. |
| Statement/proof covered | Reserved for exact accepted current declarations, checked source correspondence and publication evidence. No new Renard row has this status in this initial ledger. |
| External structural input | Reserved for an itemized Chapter V external assertion with its original locator/reference and visible downstream hypotheses. The initial Chapter V rows are proposed classifications, not a completed accepted interface. |

All unassigned rows remain the responsibility of the parent. A blank Lean-name
entry is an unresolved obligation, not an assertion that no suitable Mathlib
theorem exists. Independent universes, coefficient fields, support conditions,
topologies and normalization signs must be checked before assigning coverage.

## Section backlog

These opening pages come from the 2026 table of contents, PDF pages 5–6.
They are navigation locators, not asserted page ranges. “Partial” points to
source-read rows in the companion note and leaves the rest of the section open.
Each section must eventually be expanded to every mathematical assertion,
including definitions, remarks and unnumbered results.

| Section | Subject | Printed / PDF opening | Audit state |
| --- | --- | --- | --- |
| I opening | Motivation and nonunital conventions | 5 / 11 | Partial |
| I.1 | Idempotented rings | 6 / 12 | Partial through part of I.1.5 |
| I.2 | Forgetful functors and adjoints | 14 / 20 | Backlog |
| I.3 | Idempotent corner functor | 19 / 25 | Backlog |
| I.4 | Duality | 22 / 28 | Partial: [I.4.2 coefficient-convention audit](duality-coefficient-conventions.md); actual comparisons and full-source convention remain open |
| I.5 | Classes of modules | 26 / 32 | Partial: I.5.1 definition/comparison candidates and shared statement drafts; all three consequences privately proved and compiled, pending prerequisite publication and exact proof review. I.5.2 and the remainder remain open |
| I.6 | Properties of the nondegenerate module category | 27 / 33 | Backlog |
| I.7 | Chapter notes | 28 / 34 | Backlog, including mathematical assertions |
| II opening | Spaces and groups | 29 / 35 | Backlog |
| II.1 | Topology, functions and distributions | 30 / 36 | Partial assertion audit |
| II.2 | Sheaves on t.d. spaces | 33 / 39 | Opening definitions read; remainder backlog |
| II.3 | Topological t.d. groups | 43 / 49 | Backlog |
| II.4 | Chapter notes | 56 / 62 | Backlog, including mathematical assertions |
| III opening | Representations of t.d. groups | 57 / 63 | Backlog |
| III.1 | Smooth representations | 58 / 64 | Backlog |
| III.2 | Induction and restriction | 70 / 76 | Backlog |
| III.3 | Representations in sheaf sections | 83 / 89 | Backlog |
| III.4 | Chapter notes | 85 / 91 | Backlog, including mathematical assertions |
| IV opening / IV.1 | Compact representations | 87 / 93 | Backlog |
| IV.2 | Unitary representations | 96 / 102 | Backlog |
| IV.3 | Square-integrable representations | 99 / 105 | Backlog |
| V opening / V.1 | External structural boundary and local fields | 103 / 109 | Partial assertion audit |
| V.2 | Reductive groups and characters | 104 / 110 | Partial through opening of V.2.3 |
| V.3 | Parabolic subgroups | 109 / 115 | Backlog |
| V.4 | Weyl groups | 118 / 124 | Backlog |
| V.5 | Compact subgroups | 122 / 128 | Backlog |
| VI opening | Representation theory of p-adic groups | 131 / 137 | Backlog |
| VI.1 | Normalized parabolic functors | 134 / 140 | Backlog |
| VI.2 | Supercuspidality and admissibility | 137 / 143 | Backlog |
| VI.3 | Cuspidal categorical decomposition | 142 / 148 | Backlog |
| VI.4 | Centre of the cuspidal component | 148 / 154 | Backlog |
| VI.5 | Induced representations | 161 / 167 | Backlog; retain 2026 proof correction |
| VI.6 | Finiteness theorems | 175 / 181 | Backlog |
| VI.7 | Bernstein decomposition | 180 / 186 | Backlog |
| VI.8 | Algebraic families | 187 / 193 | Backlog |
| VI.9 | Second adjointness | 195 / 201 | Backlog; general scope retained |
| VI.10 | Bernstein centre | 206 / 212 | Backlog |
| VI.11 | Chapter notes | 217 / 223 | Backlog, including mathematical assertions |
| VII opening / VII.1 | Casselman's criterion and applications | 219 / 225 | Backlog |
| VII.2 | Tempered representations | 227 / 233 | Backlog |
| VII.3 | Self-intertwining of induced representations | 232 / 238 | Backlog |
| VII.4 | Langlands classification | 240 / 246 | Backlog |
| VII.5 | Chapter notes | 246 / 252 | Backlog, including mathematical assertions |
| A.I | Categories and functors | 247 / 253 | Backlog |
| A.II | Equivalence of categories | 250 / 256 | Backlog |
| A.III | Universal problems and representability | 251 / 257 | Partial: [published A.III.1 endomorphism-localization proofs](endomorphism-localization.md). Categorical packaging, localization exactness, representability and other assertions remain open |
| A.IV | Limits and colimits | 255 / 261 | Backlog |
| A.V | Adjunctions | 258 / 264 | Backlog |
| A.VI | Abelian categories | 261 / 267 | Backlog |
| A.VII | Semisimplicity | 264 / 270 | Backlog |
| A.VIII | Specified functors | 265 / 271 | Backlog |
| A.IX | Categorical decompositions | 268 / 274 | Backlog |
| A.X | Categorical centres | 269 / 275 | Backlog |
| B.I | Amitsur's theorem | 271 / 277 | Backlog |
| B.II | Schur's lemma | 272 / 278 | Backlog |
| B.III | Separation lemma | 273 / 279 | Backlog |
| C.I | Commutative endomorphism algebras | 275 / 281 | Partial: [published final bounds, actual maximum and filtration, transport/base cases, and nine further intermediate proofs including head/tail estimates, joint decomposition and numerical comparisons](commutative-dimension.md). Exact floor-recurrence, maximum-induction and nilpotent-block-reduction proofs and the source assertion audit remain open at the recorded snapshot |
| C.II | Stable endomorphisms | 276 / 282 | Partial: [published lemma, quotient sequence and internal finite localization, including additive-to-scalar sufficient conditions](stable-quotients.md). Source-facing nonunital finiteness comparison remains open |
| C.III | Representations of the integer lattice | 279 / 285 | Partial: [published tuple correspondence, coefficient proofs in both interfaces, standalone binomial and common-basis auxiliaries, and simultaneous generalized-weight decomposition](integer-lattice-coefficients.md). Support identification, actual common triangular blocks and multivariable factorization remain open |

The bibliography, notation list and index begin on printed pages 281, 285 and
289 respectively. Their bibliographic/indexing function is expository; any
mathematical claim discovered there must still be routed to an assertion row.
The motivational finite-group equivalence in the Chapter I opening remains an
assertion to cross-reference, rather than being discarded as historical prose.

## Focused tasks and verified status at 25 October 2026

| Unit | Owner/task | Exact evidence and remaining boundary |
| --- | --- | --- |
| Ring core, I.1.1–I.1.2 | Worker 323; `7699d54b-d019-497a-97f5-cebc77cd4a99` | Latest direct fetch of candidate `d68b4d83-2484-40a5-888e-368d81d825b0` reports rejected, `accepted=false`, `public=false`. Machine receipt `655cd340-de9e-4839-a511-b94c3a7f6418` passed, but review `b2ff6d20-2c13-4811-8514-46ae8eee3e2a` found that the transparent idempotent subtype can inherit an unrelated ambient order (`OrderDual ℤ` counterexample). Worker 323 retains the correction; no replacement candidate was listed at inspection. |
| Exact t.d.-space definition and Mathlib correspondence | `09579afe-1e74-4559-ab2a-f6e74051da6a`, revision 1; published by Worker 6 | Publication returned ready with no artifacts. Excludes Van Dantzig and the separate topological propositions. |
| Nonunital modules and nondegenerate-part functor | `de5a8c55-bfa0-4ff5-8110-c3a8696ed2f1`, revision 1; published by Worker 6 | Publication returned ready with no artifacts. Must consume the accepted ring core. Excludes exactness, abelianness, colimits and completion/adjunction proofs. |
| General residue-normalized absolute value | `36c76186-09b4-4977-a59f-e14ff6f85fcf`, revision 1; published by Worker 6 | Publication returned ready with no artifacts. Reuses `Langlands.FML.ord` and existing p-adic adapters; the remaining absolute-value construction and specialization bridge are required. Worker 109 confirmed no planned overlap. |

The current ring candidate proposes `Langlands.Algebra.Idempotent`,
`Idempotent.corner`, `Idempotent.Corner` and `IsIdempotented` in
`Langlands.Algebra.IdempotentedRing`. These are candidate navigation names, not
published imports as of the fetch above.

## Reuse and ownership routing

The initial current-file audit used Library commit
`a6bdee15f245a1f7aab64f3cbc9c04f3035c63bb`. Existing mathematics must be imported
by current Lean name; the observations below do not replace exact
source-correspondence checks.

- `Langlands.FML.ord` is already an additive valuation into `WithTop ℤ`, with
  infinity at zero and the usual source sign, over arbitrary
  `IsNonarchimedeanLocalField`. Its comparison, integer-ring and lattice APIs
  should be reused. Its module does not construct the required real normalized
  absolute value or choose a uniformizer.
- `Langlands.FML.Padic.normalizedValuation` and `.ord` already specialize to the
  supplied p-adic topology and valuation; `normalizedValuation_eq_discreteValuation`
  proves equality with the host multiplicative normalization. Reuse these
  wrappers from `Langlands.LocalFactor.FML.Conductors`. Existing `latticeAgreement`
  and `unitFiltrationAgreement` in `Langlands.LocalFactor.FML.AgreementProof`
  compare those objects, handling zero separately.
- `Langlands.PadicField.TopologicalData.ord` is integer-valued and uses zero at
  zero. Its `normalizedAbs` explicitly handles zero. A source adapter must use
  the same supplied valuation and topology and separate the zero case.
- `Langlands.HarmonicAnalysis.generalScalarHaarScalingStatement` proves the
  general-field measure-pushforward target, conditional on an actual
  `AbsoluteValue`, a uniformizer and the normalization certificates. Constructing
  those certificates and matching the book's integral formula remain separate
  obligations.
- `Langlands.compactOpenSubgroupBasis` assumes `NonarchimedeanGroup` and
  `WeaklyLocallyCompactSpace`. It is not itself the missing derivation of
  `NonarchimedeanGroup` from the book's t.d. hypothesis.
- `SchwartzBruhat`, `Langlands.Hecke.TestFunction` and
  `Langlands.HarmonicAnalysis.Distribution` provide concrete function and
  algebraic-dual objects. Their existence does not close the open/closed
  exact sequences or tensor/support results of II.1.

Workers 8 and 14 retain task `a2a442fc-f72b-43ea-a3f3-bcfd61415ccc` and its
general parabolic/geometric branches. Worker 114's
`82bfcc29-81a6-4092-9b9c-f089d2abfb76` remains a separate held definition task;
its draft must not be treated as a published normalized framework. Worker 109
retains the NYLL inverse-sign/host-order comparison branch under
`4b320e90-051e-401c-af0d-7530a66652e3`. The proposed Renard absolute-value unit
does not take over that comparison or its focused statement task
`ec92ca3a-ff96-4fba-9a13-4e4f10d3d869`. Worker 109 confirmed he has no general
residue-normalized absolute-value construction planned.

The focused GL opposite-second-adjointness task
`4942e7fb-7087-456e-94af-65b435bccedd` is separate from the book's general
VI.9 obligation. Its eventual admissible p-adic GL result must be compared
with the complete source hypotheses, not substituted for the general theorem.

## Dependency plan and next audit

Publish definitions before statements over them, and proofs only after their
exact Prop-valued targets are published. The first independent branches are:

1. Ring core → nonunital module category/nondegenerate part → splitting,
   categorical exactness/abelianness and colimit correspondences → completion
   and adjunctions, with Appendix A audited where used.
2. Exact t.d. definition → locally closed subspaces, finite disjoint refinement,
   Baire and Van Dantzig → function/distribution exactness and tensor results →
   sheaf and Hecke constructions.
3. Existing general valuation → normalized absolute value and specialization
   bridges → local-field topology and Haar source adapters → itemized general
   reductive structural data and hypotheses.

The remaining Chapter III–VII and Appendix B/C units must be split after
source reading and declaration-level reuse checks. Their order is not settled
by this provisional outline. In particular, circular dependence between
finiteness, Bernstein decomposition, second adjointness and classification must
be ruled out from the actual proofs. The immediate reading continuation is
I.1.5 onward, then the Appendix A universal properties needed by its functors.
