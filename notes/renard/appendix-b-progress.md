# Renard Appendix B: Amitsur, simplicity reductions and original actions

Status checked on 2 November 2026 against Library
`2c43e36f9ac408fcdef45d79d2ac3b56107609c2`. On the same day the final
original B.III proof was recorded against Library
`47b67c4eb87954cf163f3a88bb94b9cbae2edbf0`. The original B.II proof, which
first appeared at `cd11fff8febbab050837bbdac5d8d37b10233370`, was checked
later; its unchanged pair is present in Library
`545ccb3366b363dc0fe0a6d000b281a88d7c2407`.

The B.I Amitsur theorem and the general actual-action simplicity reductions have published proofs. The unital B.II Schur proof and
the unital B.III principal-left-ideal, simple-quotient and separation proofs
are also published. For original nonunital actions, all three B.III
components and the exact B.III aggregate now have published proofs. The
original B.II aggregate and all nine components also have
published proofs. This note records
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
complex-linear centralizer are covered by the separate original-action
proof described below.

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

## Published original-action Schur proof and B.III components

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

In [NonUnitalSchurProof.lean](../../Langlands/Algebra/NonUnitalSchurProof.lean),
`Langlands.Renard.nonUnitalSchur` proves exactly
`NonUnitalSchurStatement.{uA,uM}` by packaging all nine named component
proofs. The proof derives `ρ ≠ 0`, unitized simplicity and scalar
linearity from the published simplicity reductions. Its actual
function-preserving ring equivalences compare all additive original
endomorphisms with the complex-linear centralizer and then with the
unitized endomorphism ring. They transfer the published unital
division, bijectivity, evaluation and scalarity results.

The original orbit map has domain `A`, and evaluation has domain the
actual centralizer. Their surjectivity and injectivity give the two
countable-rank bounds, with cardinal lifts retaining independent `uA`
and `uM`. The proof preserves the canonical scalar algebra map and
proves unique scalar multiplication for every additive original
endomorphism under either countability hypothesis. It adds no unit,
finite-dimension or scalar-linearity premise. The
[proof documentation](../../Langlands/Algebra/NonUnitalSchurProof.md)
describes the nine components and actual equivalences.

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

All three components and the aggregate now have independently published
proofs:

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
- [NonUnitalSeparationProof.lean](../../Langlands/Algebra/NonUnitalSeparationProof.lean)
  proves `Langlands.Renard.nonUnitalSeparation`. It passes the scalar `z`
  from the resolvent component to the quotient component for the same
  `a`, keeps that quotient, action and separating class, and omits only
  the principal-left-ideal containment conjunct.
  `Langlands.Renard.nonUnitalSeparationReduction` has exactly the type
  `NonUnitalSeparationReductionStatement.{uA}`. It introduces the algebra
  and its four instances and returns the three named theorems.

The quotient result retains the coatom left ideal, containment of the
principal left ideal, canonical unitized simplicity, original additive
simplicity and the specified separating vector. It has no countability
or nilpotence premise; only the nonzero shift and absence of a left
inverse are required. The resolvent, quotient and final proofs retain the
arbitrary universe `uA` and add no commutativity, finite dimension,
nontriviality of the original algebra, two-sided-ideal, quotient-ring or
nonzero-action hypothesis. Every element of a zero algebra is nilpotent,
so the final component holds vacuously there. Their
[resolvent documentation](../../Langlands/Algebra/NonUnitalNonnilpotentLeftResolventProof.md),
[quotient documentation](../../Langlands/Algebra/NonUnitalLeftShiftSimpleQuotientProof.md)
and [final proof documentation](../../Langlands/Algebra/NonUnitalSeparationProof.md)
describe the implemented reductions. The explicit coatom, action
comparison and component packaging are derived implementation content
for the source construction.

The focused proofs are:

- Unital B.II: all eight unital Schur components and `schurTheorem` are
  published; they reuse B.I.
- Original-action B.II: the nine original-action Schur components and exact
  aggregate `nonUnitalSchur`, using the simplicity-reduction and unital Schur
  proofs, first appeared in the Library at
  `cd11fff8febbab050837bbdac5d8d37b10233370`.
- Original-action B.III separation: its resolvent, quotient and final
  separation proofs, including the exact aggregate, first appeared in the
  Library at `47b67c4eb87954cf163f3a88bb94b9cbae2edbf0`.

## In the Library

The ten proofs below were checked by a Lake build against their exact
targets, with the statements and their inputs unchanged. The two statement
modules were checked as statements.

| Published module | First appeared at Library commit |
| --- | --- |
| B.I `amitsurTheorem` | `bcd3de2ace8b14d5d06939a5afe3ca7742cba169` |
| Unital B.II `schurTheorem` and eight components | `ea837744ab4d479cb0fa59426ead2c2dec4a2f67` |
| Original B.II `nonUnitalSchur` and nine components | `cd11fff8febbab050837bbdac5d8d37b10233370` |
| `nonUnitalSimplicityReduction` | `bcd3de2ace8b14d5d06939a5afe3ca7742cba169` |
| `principalLeftIdealProper` | `6fd0709bd33fa6c33b4d74b4b638cfc51428b8f1` |
| `leftShiftSimpleQuotient` | `bcd3de2ace8b14d5d06939a5afe3ca7742cba169` |
| `unitalSeparation` | `bcd3de2ace8b14d5d06939a5afe3ca7742cba169` |
| Original `nonUnitalNonnilpotentLeftResolvent` | `ea837744ab4d479cb0fa59426ead2c2dec4a2f67` |
| Original `nonUnitalLeftShiftSimpleQuotient` and action equality | `ea837744ab4d479cb0fa59426ead2c2dec4a2f67` |
| Original `nonUnitalSeparation` and aggregate `nonUnitalSeparationReduction` | `47b67c4eb87954cf163f3a88bb94b9cbae2edbf0` |
| Original-action Schur statements | `bcd3de2ace8b14d5d06939a5afe3ca7742cba169` |
| Original-action separation statements | `bcd3de2ace8b14d5d06939a5afe3ca7742cba169` |

Every listed Lean/Markdown pair matches the Library at the commit named
above. Every file of the three original B.III proofs was compared with Library
`47b67c4eb87954cf163f3a88bb94b9cbae2edbf0`; all are byte-identical there.

The original B.II proof was checked by a Lake build against its exact
target. Its Lean/Markdown files match Library
`545ccb3366b363dc0fe0a6d000b281a88d7c2407`.

A separate build checked
the simplicity, original Schur and original separation statement modules
without errors or warnings and inspected the separation aggregate as
`Prop`. An earlier inspection of the exact Schur aggregate also reports
`Prop` with independent `uA` and `uM`. These checks concern the statements;
they do not establish their proofs.

Mathematical reuse proceeds by the Library's Lean names.
