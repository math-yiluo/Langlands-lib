# Renard A.VIII.1: exact functors, finite preservation and faithfulness

Worker 709, 3 November 2026. This source and publication audit uses the
specifications, implementations and companions of Workers 6, 595, 633,
691, 894, 910 and 912, and Worker 1055's later homology-statement prose
correction. Their contributions are distinguished below. Seven independently
accepted and published units cover the sequence definitions, finite
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
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
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
| Argument before that lemma, PDF272, citing A.VI.2(5): use the epi/mono image factorization | The same proof derives mono and epi preservation and uses actual `Abelian.factorThruImage`, `Abelian.image` and `Abelian.image.ι`. This is an implemented step in the faithfulness proof; these units do not declare a separate general image-comparison theorem. |

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
The units supply this class equivalence. They add no chain-complex functor
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
`5ed2965256430c3649e86755f9576b54eca72435`, under
`/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib`:

| Registered source | Native file and role |
| --- | --- |
| `mathlib-shortcomplex-exactfunctor-5ed296525643` | `Mathlib/Algebra/Homology/ShortComplex/ExactFunctor.lean`: the two one-sided TFAE theorems, `exact_tfae`, and the mono/epi preservation helpers used in the faithfulness proof. |
| `mathlib-finite-preservation-5ed296525643` | `Mathlib/CategoryTheory/Limits/Preserves/Finite.lean`: actual finite-shape preservation classes and transport to higher universes. |
| `mathlib-shortcomplex-preserveshomology-5ed296525643` | `Mathlib/Algebra/Homology/ShortComplex/PreservesHomology.lean`: the actual kernel/cokernel preservation class. |

## Independent acceptance and publication

The following seven candidates are all accepted and published. Each has
an independent approval without qualifications. The definition unit
contains the source predicates and their definitional unfolding laws;
statement acceptance establishes proposition interfaces. The three proof
units have the separate exact-target validations recorded below.

| Unit and task (all revision 1) | Candidate | Independent review | Integration | Library commit |
| --- | --- | --- | --- | --- |
| Sequence definitions; `a81a381c-6f47-41c9-a3e9-64866ab68b3f` | `75e698f7-0c5f-48e6-9615-f0cc8b6e3951` | Reviewer 3167; `5b90c05b-0339-45c6-9b4a-dab851f04aab` | `d5b50d04783e434fa5f61400f61037f0` | `67af6154336bd44f956040f5e7b99ecfe6ff7d5c` |
| Finite-preservation statement; `e2039435-dc17-46af-b839-614fefcf48aa` | `09327623-61e2-452e-9387-9118ad0b429d` | Reviewer 3716; `7d3ac924-711a-4133-b2be-a66c60d611fc` | `96e4db712616496faca7d3a88958b68a` | `83bd84354679646bd127657889be51d0b580ed3b` |
| Finite-preservation proof; `a38c5f8d-65c9-48e8-8437-be85ec8956ce` | `d6212831-0e9e-4ff6-b44b-476d3ad7a37b` | Reviewer 4021; `02182c46-e1a0-4961-82d7-21a01fa220a6` | `68dfccaad62b4740a71ae23010b9f503` | `cb6a47b2390bdcd0be78fac0552b7fd5c46cd51b` |
| Short-complex/homology statement; `2344b69e-42b7-4a4b-b933-e5e9641547cd` | `d597bb9f-9acd-4223-9115-be2438aafb22` | Reviewer 3721; `94e73676-c0b8-4a9b-8c75-a1087f4cafee` | `cbb1fa44838446498f85d95809597cb0` | `83bd84354679646bd127657889be51d0b580ed3b` |
| Short-complex/homology proof; `cdad15c8-b3ea-4a61-ae52-16eb9c231935` | `bb2e1621-544d-4e29-82ef-2f0261055892` | Reviewer 4014; `4d00ccce-02f3-4d5d-b0db-5250302bf9cf` | `176a43812d964d3989956dead6899880` | `cb6a47b2390bdcd0be78fac0552b7fd5c46cd51b` |
| Faithfulness statement; `19e362c6-cee3-4e20-9b36-de02bd65ffd2` | `41a405f3-6517-48b4-8a46-92a8cebb83cf` | Reviewer 3722; `c10b2335-7c0d-4eb9-9b95-e8c21a6bcdee` | `525ae26c38e8445fb914783b49353521` | `83bd84354679646bd127657889be51d0b580ed3b` |
| Faithfulness proof; `de554aa3-6de1-4931-b993-796330c7ff96` | `5afe0694-7192-4024-ae30-63bb9ce7e086` | Reviewer 4023; `634ff8f8-38e8-47a1-b4c9-e03738a54527` | `494b82e30b3a42e4aaca90f043905ec0` | `cb6a47b2390bdcd0be78fac0552b7fd5c46cd51b` |

Each proof validation below reports `proof_accepted: true` and checks
`lake-build`, `exact-target`, `unchanged-statement` and `frozen-inputs`.
The declarations have prefix `Langlands.Renard.`.

| Exact aggregate proof | Validation receipt | Unchanged proposition target |
| --- | --- | --- |
| `finitePreservationComparison` | `b60745fa-72a9-4ed0-8599-75cafd0b1fd7` | `FinitePreservationComparisonStatement` |
| `exactnessHomologyComparison` | `051aa8fd-a9ec-4acb-a930-32cd09e352d4` | `ExactnessHomologyComparisonStatement` |
| `faithfulnessCriteria` | `60cd19a2-9d03-4aad-8094-abb104017a29` | `FaithfulnessCriteriaStatement` |

The later documentation-only correction
`dc4bfc25-e736-4117-99c9-8caf53e86162`, task
`06ead821-4af1-4b24-bc9c-3c7c5b9b850a`, updates attribution and proof status
in `ExactnessHomologyStatements.md`. Reviewer 4618 approved it without
qualifications in review task `444f6894-19d7-40de-a871-4e72529a53b2`.
Integration `209d9dc6b9be46098d83950df2b744c9` published it at
`bc8de2287e5c24972c55277b2aa9611523dfc5dc`. The Lean statement is unchanged.

The audit compared the seven Lean files with their frozen submissions,
publication commits and current Library
`2faf3958c75f10a7bf2ecb9aa2175419e234781a`: all match. Six original
Markdown companions also match those original submissions; the homology
statement companion instead matches the later approved correction.
All fourteen current paired files agree with that Library. Recovery check
`c23047f0-ceb0-4240-ab9d-403a6958bcb9` compiled the three proof roots
`Langlands.CategoryTheory.Renard.FinitePreservation`,
`Langlands.CategoryTheory.Renard.ExactnessHomology` and
`Langlands.CategoryTheory.Renard.Faithfulness` with zero errors or warnings.
This development check is separate from the original proof-acceptance
receipts. Integration's source-compilation validation likewise does not
replace those exact-target receipts.

Worker 6 supplied the definitions and statement specifications and the
finite-preservation and faithfulness proof drafts. Workers 595, 633 and
691 performed the corresponding source/interface checks and submissions.
Worker 894 implemented the short-complex/homology proof; Workers 910 and
912 checked and submitted the finite-preservation and faithfulness proofs.
Worker 1055 supplied the later proof-status correction. This synthesis
retains all their authorship and introduces no new mathematical artifact.

A.VIII.1's source assertions and the explicitly derived comparisons above
have verified published implementations. A.VIII.2's Hom functors,
projectives, generators and small-projective equivalence remain separate
work, with existing owners and the boundaries recorded in the
[category and module note](category-module-progress.md). This audit
declares no completion of A.VIII, Appendix A or the whole-book task.
