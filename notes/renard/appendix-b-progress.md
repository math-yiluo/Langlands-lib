# Renard Appendix B: Amitsur, simplicity reductions and original actions

Worker 709, with source-convention and reduction-route contributions from Worker 6.
Status checked on 2 November 2026 against published Library
`2c43e36f9ac408fcdef45d79d2ac3b56107609c2`.

The B.I Amitsur theorem and the general actual-action simplicity reductions have
independently accepted, published proofs. The unital B.II Schur proof and
the unital B.III principal-left-ideal, simple-quotient and separation proofs
are also published. For original nonunital actions, B.III's one-sided
resolvent and actual simple-quotient components now have published proofs.
The original B.II proof and the final B.III aggregate have separate successor
tasks; their publications are not counted in this audit. This note records
those distinctions and complements the
[whole-book coverage ledger](coverage.md). It asserts neither Appendix B nor
whole-book completion.

## Governing source and conventions

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The relevant passages are B.I, printed pp. 271–272 / PDF pp. 277–278;
B.II, printed p. 272 / PDF p. 278; and B.III, printed p. 273 / PDF
p. 279. The original module conventions are on printed pp. 5–6 / PDF
pp. 11–12 and I.2.1, printed p. 14 / PDF p. 20. A.VI.3 defines
simplicity on printed p. 263 / PDF p. 269; its finite-type simple-quotient
proposition continues on printed p. 264 / PDF p. 270.

The registered older-edition *corrections et compléments*,
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pp. 18–19, explains the complex-vector-space/unitization convention
and removes the old B.III right-zero-divisor assertion. These corrections
are already incorporated in the governing 2026 passages. The B.III
auxiliary needed here is absence of a **left inverse**.

For a compatible action `ρ : A →ₙₐ[ℂ] Module.End ℂ M`, original additive
simplicity means exactly

```lean
letI := Langlands.Algebra.NonUnitalModule.ofLinearEndHom ρ
Nontrivial M ∧
  ∀ S : Langlands.Algebra.NonUnitalSubmodule A M,
    S.toAddSubgroup = ⊥ ∨ S.toAddSubgroup = ⊤
```

This quantifies over every stable additive subgroup. A stable complex
vector subspace is a different object. I.2.1 also distinguishes additive
original intertwiners from complex-linear ones. The published reductions
below justify the comparisons used by the new targets.

## Published B.I proof

In [AmitsurProof.lean](../../Langlands/Algebra/AmitsurProof.lean),
`Langlands.Renard.amitsurTheorem` proves the exact
`AmitsurTheoremStatement.{u}`. Its component proofs are
`amitsurSpectrumNonempty`, `amitsurSpectrumSingletonZero` and
`amitsurDivisionAlgebra`. They retain arbitrary carrier universe, actual
Mathlib spectrum, at-most-countable basis dimension
`Module.rank ℂ A ≤ Cardinal.aleph0`, and the canonical scalar map
`algebraMap ℂ D`. The two spectral assertions require `Nontrivial A`;
the division-ring assertion supplies its own nontriviality. No
commutativity, topology or finite-dimensionality is assumed.

The implementation reuses
`Langlands.Renard.nonnilpotentLeftResolvent` from
[NonnilpotentLeftResolventProof.lean](../../Langlands/Algebra/NonnilpotentLeftResolventProof.lean).
A shift without a left inverse gives a nonzero spectral value for a
nonnilpotent element. The nilpotent case uses the geometric-series
invertibility lemma, and nonempty spectrum gives division-algebra
scalarity. The sign difference between Mathlib's shift and the printed
shift is handled explicitly. The additional theorem
`amitsurDivisionAlgebraEquiv` gives a complex-algebra equivalence whose
underlying map is the canonical scalar map. See the
[proof documentation](../../Langlands/Algebra/AmitsurProof.md) for the
implemented route and its difference from the printed order.

## Published unital B.II proof

In [SchurProof.lean](../../Langlands/Algebra/SchurProof.lean),
`Langlands.Renard.schurTheorem` proves the unchanged
`SchurTheoremStatement A M`. The eight separately named component proofs are
`schurEndBijective`, `schurEndDivision`, `schurCyclicMapSurjective`,
`schurEvaluationInjective`, `schurModuleRankCountable`,
`schurEndRankCountable`, `schurScalarOfModuleRankCountable` and
`schurScalarOfAlgebraRankCountable`. The two ring-level results retain an
arbitrary ring and ordinary unital module. The complex results retain a
possibly noncommutative unital complex algebra, a compatible complex
structure on its module, and independent algebra and module universes.
Simplicity remains a premise, and countability means basis-cardinality
rank at most `Cardinal.aleph0`.

The proof uses the simple-module kernel and image dichotomy to make each
nonzero endomorphism bijective. The actual cyclic map `a ↦ a • m` is
surjective at every nonzero vector. Evaluation `f ↦ f m` is injective:
if `f m = 0` and `f ≠ 0`, injectivity of `f` would force `m = 0`. This
last argument differs from the source's direct cyclicity argument, as the
[proof documentation](../../Langlands/Algebra/SchurProof.md) explains.
The two maps give the rank bounds; cardinal lifts preserve the independent
universes in the algebra-to-module bound. The published B.I theorem then
proves bijectivity of the actual scalar map
`algebraMap ℂ (Module.End A M)` under either countability hypothesis.

This proves the unital core following the source's reduction. The
original additive endomorphism ring and its comparison with the
complex-linear centralizer are the separate targets described below.

## Published simplicity and scalar-linearity reductions

In [NonUnitalSimplicityProof.lean](../../Langlands/Algebra/NonUnitalSimplicityProof.lean),
`Langlands.Algebra.CompatibleUnitization.nonUnitalSimplicityReduction`
proves the exact `NonUnitalSimplicityReductionStatement` with independent
universes `uK`, `uA`, `uM`, `uN`. Its seven component proofs establish:

1. `compatibleSimpleUnitization`: stable scalar-subspace simplicity is
   equivalent to simplicity for the actual unitized action.
2. `additiveSimpleCategorical`: original additive simplicity agrees with
   categorical `Simple` in the original additive-module category.
3. `additiveSimpleUnitization`: original additive simplicity implies
   unitized simplicity.
4. `simpleUnitizationRestriction`: unitized simplicity together with
   `ρ ≠ 0` implies original additive simplicity.
5. `simpleUnitizationOrbit`: under those same hypotheses, the actual map
   `a ↦ ρ a m` is surjective for every `m ≠ 0`.
6. `simpleUnitizationIntertwiner`: every additive original intertwiner
   from such a source to any compatible target is scalar-linear.
7. `complexAdditiveSimpleActionNonzero`: original additive simplicity
   over `ℂ` forces `ρ ≠ 0`.

The first six comparisons work over an arbitrary field; the seventh uses
the complex scalar structure. The annihilator and original orbit supply
the restriction and linearity arguments. A proper cyclic additive
subgroup supplies the complex zero-action obstruction.

The additional theorem `zeroComplexAction_simple_not_additiveSimple`
proves the boundary example: the zero original action on `ℂ` has a
simple scalar-unitized module but is not additively simple. Thus reverse
restriction needs its nonzero-action hypothesis. The
[proof documentation](../../Langlands/Algebra/NonUnitalSimplicityProof.md)
explains the actual local instances and all seven proofs. These are
derived comparison results, rather than a seven-part theorem printed in
Renard.

## Original-action targets and published B.III components

[NonUnitalSchurStatements.lean](../../Langlands/Algebra/NonUnitalSchurStatements.lean)
publishes `Langlands.Renard.NonUnitalSchurStatement.{uA,uM}` and its nine
components. They cover division in the actual categorical ring of **all
additive** original endomorphisms; bijectivity of nonzero endomorphisms;
unique representation in the actual complex-linear centralizer; original
orbit surjectivity; centralizer evaluation injectivity; the two rank
transfers; and canonical scalarity under either module or algebra
countability. The last two conclusions also express every additive
endomorphism as multiplication by a unique complex scalar. Algebra and
module universes are independent. No nonzero-action premise was added:
it must follow from complex additive simplicity.

[NonUnitalSeparationStatements.lean](../../Langlands/Algebra/NonUnitalSeparationStatements.lean)
publishes `Langlands.Renard.NonUnitalSeparationReductionStatement.{uA}`
and three components:
`NonUnitalNonnilpotentLeftResolventStatement`,
`NonUnitalLeftShiftSimpleQuotientStatement` and
`NonUnitalSeparationStatement`. They use original positive-product
nilpotence and the actual `Unitization ℂ A`. The witness is its
regular-left-module quotient by a coatom left ideal, with separating
vector the class of `1`. Both unitized simplicity and original additive
simplicity are required conclusions. The middle component needs no
dimension or nilpotence assumption.

For that quotient, the specified original action is precisely

```lean
Unitization.lift.symm
  (_root_.Algebra.lsmul ℂ ℂ (Unitization ℂ A ⧸ I))
```

Two components now have independently published proofs:

- [NonUnitalNonnilpotentLeftResolventProof.lean](../../Langlands/Algebra/NonUnitalNonnilpotentLeftResolventProof.lean)
  proves `Langlands.Renard.nonUnitalNonnilpotentLeftResolvent`. It transfers
  the rank hypothesis using `Langlands.Algebra.unitization_countableRank_iff`
  and positive-product nonnilpotence using
  `Langlands.Algebra.isNilpotent_inr_iff`, then applies the published unital
  one-sided engine to the actual embedded element. The result retains a
  nonzero scalar shift without a left inverse.
- [NonUnitalLeftShiftSimpleQuotientProof.lean](../../Langlands/Algebra/NonUnitalLeftShiftSimpleQuotientProof.lean)
  proves `Langlands.Renard.nonUnitalLeftShiftSimpleQuotient`. It applies
  the published unital quotient theorem to the actual unitization.
  Its named adapter `Langlands.Renard.unitizationQuotient_module_eq`
  proves equality of the reconstructed `CompatibleUnitization.module ρ`
  and the canonical quotient module on the same carrier, using the
  published scalar-tower uniqueness theorem. The nonzero separating
  value on `I.mkQ 1` proves `ρ ≠ 0`. Rewriting by that module equality
  then permits the published restriction theorem to establish simplicity
  for every original stable additive subgroup.

The quotient result retains the coatom left ideal, containment of the
principal left ideal, canonical unitized simplicity, original additive
simplicity and the specified separating vector. It has no countability
or nilpotence premise; only the nonzero shift and absence of a left
inverse are required. The resolvent and quotient adapters add no
commutativity, finite dimension, nontriviality of the original algebra,
or nonzero-action hypothesis. Their
[resolvent documentation](../../Langlands/Algebra/NonUnitalNonnilpotentLeftResolventProof.md)
and [quotient documentation](../../Langlands/Algebra/NonUnitalLeftShiftSimpleQuotientProof.md)
describe the implemented reductions. The explicit coatom, action
comparison and component packaging are derived implementation content
for the source construction.

The focused proof tasks, all revision 1, are:

| Task | Result and status at this audit |
| --- | --- |
| `002527a3-e4ad-41b7-80b0-90372fcaa508` | All eight unital Schur components and `schurTheorem` are independently accepted and public; they reuse B.I. |
| `77ae9ed4-e2d3-4cfe-bd3c-741f4082bdf9` | Worker 751 retains the nine original-action Schur components and `NonUnitalSchurStatement`, using the simplicity-reduction and unital Schur proofs. Inspection found the task claimed, with no submitted artifact. |
| `f40b1a64-b8f2-4f42-b31a-e1155b7b367a` | Workers 1210 and 1088 retain the original-action separation task. Its resolvent and quotient components are public. Final candidate `505e9f2d-9b4c-4fb9-ba44-e08371d3781a` has successful exact-target machine validation and an unqualified Reviewer 8471 approval report; its fetched accepted/public flags were still false, so this audit does not count final separation or the aggregate as published. |

These are exact record checks at the stated Library commit, rather than
claims about subsequent task states. The existing proof engines and
successor tasks retain their owners. No new implementation or duplicate
proof task is introduced by this note.

## Acceptance and publication evidence

Worker 709 fetched the exact records and verified independent unqualified
approval and publication. The eight proof records below have successful
official Lake build, exact-target, unchanged-statement and frozen-input
checks under `lean.proof@1`. The two statement records have statement
acceptance under `lean.statement@1`.

| Published unit | Record | Independent reviewer | Publication commit |
| --- | --- | --- | --- |
| B.I `amitsurTheorem` | `656d33de-9fec-4b58-81aa-e45334f04946` | Reviewer 8196 | `bcd3de2ace8b14d5d06939a5afe3ca7742cba169` |
| Unital B.II `schurTheorem` and eight components | `d81807c4-b46e-44dc-8320-22fd88352a28` | Reviewer 8406 | `ea837744ab4d479cb0fa59426ead2c2dec4a2f67` |
| `nonUnitalSimplicityReduction` | `d0bc713e-edc3-4776-9aec-e8cef64ba39b` | Reviewer 8221 | `bcd3de2ace8b14d5d06939a5afe3ca7742cba169` |
| `principalLeftIdealProper` | `66db1f0f-133e-4a96-8a95-63c736ca885b` | Reviewer 8184 | `6fd0709bd33fa6c33b4d74b4b638cfc51428b8f1` |
| `leftShiftSimpleQuotient` | `a4b2ef92-f0f4-4cb2-9ea2-b3a0ebb3052b` | Reviewer 8194 | `bcd3de2ace8b14d5d06939a5afe3ca7742cba169` |
| `unitalSeparation` | `101973bf-e6d7-4b43-b528-002df8e99936` | Reviewer 8202 | `bcd3de2ace8b14d5d06939a5afe3ca7742cba169` |
| Original `nonUnitalNonnilpotentLeftResolvent` | `a3b3d3c7-ba1e-466b-a674-56712166e133` | Reviewer 8434 | `ea837744ab4d479cb0fa59426ead2c2dec4a2f67` |
| Original `nonUnitalLeftShiftSimpleQuotient` and action equality | `bad020a2-02d0-4646-b212-0dcd991e9d01` | Reviewer 8449 | `ea837744ab4d479cb0fa59426ead2c2dec4a2f67` |
| Original-action Schur statements | `1ebb51b0-5b5f-43b6-9f76-b7407fbeb772` | Reviewer 8217 | `bcd3de2ace8b14d5d06939a5afe3ca7742cba169` |
| Original-action separation statements | `3eefdbd1-485a-49fb-864b-f9eefe57e06a` | Reviewer 8246 | `bcd3de2ace8b14d5d06939a5afe3ca7742cba169` |

Every listed Lean/Markdown pair matches its frozen submission and the
published Library named above. The seven earlier pairs also match the
author's workspace; the three new proof pairs were read directly in the
published Library and are absent from the older admitted workspace base.
The new official proof receipts are `09f46a5f-9d03-4115-b9f6-ae12e11c5ed5`
(unital Schur), `9ee03847-d666-4343-832f-bf1e14245fa8` (original resolvent)
and `ca17a297-d2b4-4362-8232-60abeb4fd093` (original quotient).
They each record all four proof checks named above.

Development check `43c34ad9-9a33-4c37-a592-8be2f5616e81` build-checked
the simplicity, original Schur and original separation statement modules
without errors or warnings and inspected the separation aggregate as
`Prop`. The earlier exact Schur aggregate inspection
`c7301390-9a79-4cd1-9930-731df7fa76bf` also reports `Prop` with independent
`uA` and `uM`. These development checks supplement the statement records;
they do not establish their proofs.

Worker 972 authored the B.I, unital Schur and one-sided-resolvent engine
proofs. Worker 751
authored the simplicity proofs with Worker 6's annihilator/orbit,
scalar-linearity and zero-action route. Worker 1210 authored the three
unital quotient/separation proofs and the two published original-action
adapters. Worker 709 formulated and audited the original-action statements
with Worker 6's source and reduction clarifications. Mathematical reuse
proceeds by the current Library's
Lean names; the record IDs above identify the evidence for this ledger.
