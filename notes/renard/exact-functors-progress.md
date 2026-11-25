# Renard A.VIII.1: exact functors, finite preservation and faithfulness

This source and Library audit, dated 3 November 2026, uses the
specifications, implementations and companion pages of the modules below, and
a later correction of the homology-statement page. Seven published modules
cover the sequence definitions, finite
preservation comparisons, derived short-complex and homology comparisons,
and faithfulness criteria. This note supplements the [whole-book
ledger](coverage.md). A.VIII.2 retains its separate Hom, projective,
generator and smallness obligations; see the [category and module progress
note](category-module-progress.md).

## Governing source

The original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
retained at
`central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
The complete governing pages, printed265–266 / PDF271–272, were reread for
this audit. A.VIII's opening preservation motivation and the beginning of
A.VIII.2 on PDF272 delimit the passage.

The supplementary author errata, registered as
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were read at PDF18–19. The old-p.308 correction replaces faithfulness by
exactness in the preservation argument. The governing 2026 text already
incorporates this change. Both PDF fingerprints were recomputed during this
audit. No further discrepancy was found in the A.VIII.1 passage compared
here.

## Source-to-declaration correspondence

All project declarations in the following tables have prefix
`Langlands.Renard.`. The actual Mathlib classes retain their own namespaces.
Links lead to the published companions and their same-stem Lean files.

| Original assertion and locator | Actual interface or published result |
| --- | --- |
| A.VIII.1 opening, printed265–266 / PDF271–272: an additive functor induces a group homomorphism on each Hom group | Actual `CategoryTheory.Functor.Additive` and `Functor.mapAddHom` for `F : C ⥤ D`; the project uses these interfaces directly. |
| A.VIII.1, PDF272: preservation of every exact sequence `0 → X → Y → Z` | [`SequenceLeftExact`](../../Langlands/CategoryTheory/RenardExactFunctor.md): every `S : ShortComplex C` with `S.Exact` and `Mono S.f` maps to a middle-exact complex whose first map is mono. There is no `Epi S.g` premise. |
| Same paragraph: preservation of every exact sequence `X → Y → Z → 0` | `SequenceRightExact`: every middle-exact `S` with `Epi S.g` maps to a middle-exact complex whose second map is epi. There is no `Mono S.f` premise. |
| Same paragraph: exact means left and right exact | `SequenceExact` is precisely `SequenceLeftExact F ∧ SequenceRightExact F`. The three `sequenceLeftExact_iff`, `sequenceRightExact_iff` and `sequenceExact_iff` laws unfold the definitions by `Iff.rfl`. |
| Same paragraph: contravariant convention | `ContravariantSequenceLeftExact`, `ContravariantSequenceRightExact` and `ContravariantSequenceExact` apply those same predicates to the actual additive functor `F : Cᵒᵖ ⥤ D`. The names are unchanged when passing to the opposite category. |
| Following paragraph, PDF272: left exact functors preserve finite limits, right exact functors preserve finite colimits | Forward directions of [`SequenceLeftExactFiniteLimitsStatement` and `SequenceRightExactFiniteColimitsStatement`](../../Langlands/CategoryTheory/Renard/FinitePreservationStatements.md), proved by [`sequenceLeftExactFiniteLimits` and `sequenceRightExactFiniteColimits`](../../Langlands/CategoryTheory/Renard/FinitePreservation.md). Their reverse implications and the joint `SequenceExactFinitePreservationStatement` are derived comparisons. |
| Faithfulness paragraph, PDF272: injectivity on Hom sets | Actual `CategoryTheory.Functor.Faithful`; the project does not replace its map-injectivity field. |
| Same paragraph: reflection of zero morphisms suffices for faithfulness of an additive functor | Sufficient direction of [`FaithfulZeroMorphismCriterionStatement`](../../Langlands/CategoryTheory/Renard/FaithfulnessStatements.md), proved by [`faithfulZeroMorphismCriterion`](../../Langlands/CategoryTheory/Renard/Faithfulness.md). Necessity is an elementary derived extension. |
| Final A.VIII.1 lemma, PDF272: an exact functor reflecting zero objects is faithful | `SequenceExactReflectsZeroFaithfulStatement`, proved by `sequenceExactReflectsZeroFaithful`. Its antecedents are the source sequence exactness and `∀ X, IsZero (F.obj X) → IsZero X`. |
| Argument before that lemma, PDF272, citing A.VI.2(5): use the epi/mono image factorization | The same proof derives mono and epi preservation and uses actual `Abelian.factorThruImage`, `Abelian.image` and `Abelian.image.ι`. This is an implemented step in the faithfulness proof; these modules do not declare a separate general image-comparison theorem. |

The following three equivalences are internal comparisons with Mathlib.
Renard supplies the sequence definitions and the forward finite-preservation
assertions above; the passage does not separately state these equivalences.

| Derived proposition | Exact content and published proof |
| --- | --- |
| [`SequenceExactShortComplexStatement`](../../Langlands/CategoryTheory/Renard/ExactnessHomologyStatements.md) | `SequenceExact F ↔ ∀ S : ShortComplex C, S.Exact → (S.map F).Exact`, proved by [`sequenceExactShortComplex`](../../Langlands/CategoryTheory/Renard/ExactnessHomology.md). |
| `SequenceExactShortExactStatement` | `SequenceExact F ↔ ∀ S : ShortComplex C, S.ShortExact → (S.map F).ShortExact`, proved by `sequenceExactShortExact`. Here `ShortExact` retains both endpoint conditions. |
| `SequenceExactHomologyStatement` | `SequenceExact F ↔ F.PreservesHomology`, proved by `sequenceExactHomology`. The right side is Mathlib's actual kernel-and-cokernel preservation class. |

## Scope, sizes and proof routes

Every statement and proof retains the same four independent universes:

```lean
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive]
```

The objects and Hom types of the two categories need not share a universe.
The aggregate proofs add no exactness, preservation, faithfulness,
smallness, module or representation premise. The faithfulness lemma keeps
exactness and zero-object reflection as implication antecedents within its
statement.

`PreservesFiniteLimits F` and `PreservesFiniteColimits F` quantify over
actual finite category shapes, including empty and disconnected ones.
Mathlib also transports these classes to finite shapes in higher universes.
There is no nonempty or connected index restriction. For the homology
comparison, `Functor.PreservesHomology` requires preservation of the kernel
and cokernel diagrams of every morphism, using `parallelPair f 0`.
It is not a project-defined exactness predicate.

The finite-preservation proof identifies the source's one-sided conditions
with entries 2 of `Functor.preservesFiniteLimits_tfae` and
`Functor.preservesFiniteColimits_tfae`. It uses `.out 2 4` in each case to
reach the actual preservation classes. `and_congr` combines the two
equivalences. The resulting aggregate, in order, is
`FinitePreservationComparisonStatement F`: left comparison, right
comparison, then joint comparison. Its exact proof is
`finitePreservationComparison`.

The short-complex/homology proof first obtains the same two-sided finite
preservation equivalence privately. It then uses `Functor.exact_tfae`
with `.out 4 2`, `.out 4 1` and `.out 4 3` for middle exactness, short
exactness and `PreservesHomology`, respectively. In this pinned Mathlib,
these are the one-based entry numbers used by `List.TFAE.out`.
`ExactnessHomologyComparisonStatement F` conjoins those three comparisons
in that order; its exact proof is `exactnessHomologyComparison`.
The modules supply this class equivalence. They add no chain-complex functor
or natural homology comparison isomorphism.

The zero-morphism criterion proves necessity from faithfulness. For
sufficiency, additivity sends `f - g` to zero when `F.map f = F.map g`;
zero reflection then gives injectivity. The exact-plus-zero-reflection
proof follows the source's image-factorization route. The sequence
hypotheses first give preservation of monomorphisms and epimorphisms.
If `F.map f = 0`, cancelling the mapped image inclusion shows that the
mapped factor-through-image map is zero. That map is epi, so its target
`F.obj (Abelian.image f)` is a zero object. Zero-object reflection makes
the original image zero, and the original image factorization yields
`f = 0`. `FaithfulnessCriteriaStatement F` pairs the zero-morphism
criterion with the exact-plus-zero-reflection lemma; its exact aggregate
proof is `faithfulnessCriteria`.

The native sources read for these comparisons are pinned at Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`:

| Registered source | Native file and role |
| --- | --- |
| `mathlib-shortcomplex-exactfunctor-5ed296525643` | `Mathlib/Algebra/Homology/ShortComplex/ExactFunctor.lean`: the two one-sided TFAE theorems, `exact_tfae`, and the mono/epi preservation helpers used in the faithfulness proof. |
| `mathlib-finite-preservation-5ed296525643` | `Mathlib/CategoryTheory/Limits/Preserves/Finite.lean`: actual finite-shape preservation classes and transport to higher universes. |
| `mathlib-shortcomplex-preserveshomology-5ed296525643` | `Mathlib/Algebra/Homology/ShortComplex/PreservesHomology.lean`: the actual kernel/cokernel preservation class. |

## Independent acceptance and publication

The following seven modules are in the Library. The definition module
contains the source predicates and their definitional unfolding laws;
the statement modules establish proposition interfaces. The three proof
modules have the separate exact-target checks recorded below.

| Module | First appeared at Library commit |
| --- | --- |
| Sequence definitions | `67af6154336bd44f956040f5e7b99ecfe6ff7d5c` |
| Finite-preservation statement | `83bd84354679646bd127657889be51d0b580ed3b` |
| Finite-preservation proof | `cb6a47b2390bdcd0be78fac0552b7fd5c46cd51b` |
| Short-complex/homology statement | `83bd84354679646bd127657889be51d0b580ed3b` |
| Short-complex/homology proof | `cb6a47b2390bdcd0be78fac0552b7fd5c46cd51b` |
| Faithfulness statement | `83bd84354679646bd127657889be51d0b580ed3b` |
| Faithfulness proof | `cb6a47b2390bdcd0be78fac0552b7fd5c46cd51b` |

Each proof below was checked by a Lake build against its exact target, with
the statement and its inputs unchanged.
The declarations have prefix `Langlands.Renard.`.

| Exact aggregate proof | Unchanged proposition target |
| --- | --- |
| `finitePreservationComparison` | `FinitePreservationComparisonStatement` |
| `exactnessHomologyComparison` | `ExactnessHomologyComparisonStatement` |
| `faithfulnessCriteria` | `FaithfulnessCriteriaStatement` |

A later documentation-only correction of `ExactnessHomologyStatements.md`
updated its proof-status prose; it first appeared in the Library at
`bc8de2287e5c24972c55277b2aa9611523dfc5dc`. The Lean statement is unchanged.

The audit compared the seven Lean files with their first published versions
and with Library `2faf3958c75f10a7bf2ecb9aa2175419e234781a`: all match. Six
Markdown companions also match their first versions; the homology
statement companion instead matches the later correction.
All fourteen paired files agree with that Library. A separate build
compiled the three proof roots
`Langlands.CategoryTheory.Renard.FinitePreservation`,
`Langlands.CategoryTheory.Renard.ExactnessHomology` and
`Langlands.CategoryTheory.Renard.Faithfulness` with zero errors or warnings.

A.VIII.1's source assertions and the explicitly derived comparisons above
have published implementations. A.VIII.2's Hom functors,
projectives, generators and small-projective equivalence remain separate,
with the boundaries recorded in the
[category and module note](category-module-progress.md). This audit
declares no completion of A.VIII, Appendix A or the whole book.
