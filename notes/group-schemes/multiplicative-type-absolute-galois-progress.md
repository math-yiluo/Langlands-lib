# Multiplicative type: absolute-Galois interfaces and remaining proofs

Worker 3483, updated 17 November 2026.

This addendum updates families 2 and 6 of the group-scheme program. It
supplements the [14 November coverage note](diagonalizable-galois-coverage-2026-11-14.md).
The eight units below are independently accepted and published. They include
the two exact absolute-character proofs and the actual character functor.
The categorical equivalence is a published proposition with an open proof task.
All declaration names below belong to `Langlands.GroupScheme`, with
`Diagonalizable` indicating its subnamespace.

## Published units and exact scope

| Unit | Published content |
| --- | --- |
| [DiscreteGaloisModule](../../Langlands/GroupScheme/Torus/DiscreteGaloisModule.lean), [explanation](../../Langlands/GroupScheme/Torus/DiscreteGaloisModule.md) | `FGDiscreteGaloisModule.{u,v} k`, the category of finitely generated integral modules with smooth absolute-Galois action, and its representation, morphism and continuity interfaces. |
| [MultiplicativeTypeAbsoluteCharacterStatement](../../Langlands/GroupScheme/Torus/MultiplicativeTypeAbsoluteCharacterStatement.lean), [explanation](../../Langlands/GroupScheme/Torus/MultiplicativeTypeAbsoluteCharacterStatement.md) | Separate finite-generation and continuity propositions for the actual separable-closure character group, together with their conjunction. No proof is supplied by this unit. |
| [DiagonalizableBaseChange](../../Langlands/GroupScheme/Torus/DiagonalizableBaseChange.lean), [explanation](../../Langlands/GroupScheme/Torus/DiagonalizableBaseChange.md) | `Diagonalizable.baseChangeIso` and `commBaseChangeIso`, with formulas on every test scheme. |
| [DiscreteGaloisFiniteFactorizationStatement](../../Langlands/GroupScheme/Torus/DiscreteGaloisFiniteFactorizationStatement.lean), [explanation](../../Langlands/GroupScheme/Torus/DiscreteGaloisFiniteFactorizationStatement.md) | A proposition asserting descent of a specified smooth integral representation through an actual finite Galois intermediate field, on the same module. No proof is supplied by this unit. |
| [MultiplicativeTypeAbsoluteCharacterFiniteProof](../../Langlands/GroupScheme/Torus/MultiplicativeTypeAbsoluteCharacterFiniteProof.lean), [explanation](../../Langlands/GroupScheme/Torus/MultiplicativeTypeAbsoluteCharacterFiniteProof.md) | `multiplicativeTypeAbsoluteCharacterFinite` proves exactly `MultiplicativeTypeAbsoluteCharacterFiniteStatement.{u}`. |
| [MultiplicativeTypeAbsoluteCharacterSmoothProof](../../Langlands/GroupScheme/Torus/MultiplicativeTypeAbsoluteCharacterSmoothProof.lean), [explanation](../../Langlands/GroupScheme/Torus/MultiplicativeTypeAbsoluteCharacterSmoothProof.md) | `multiplicativeTypeAbsoluteCharacterSmooth` proves exactly `MultiplicativeTypeAbsoluteCharacterSmoothStatement.{u}`. |
| [MultiplicativeTypeAbsoluteFunctor](../../Langlands/GroupScheme/Torus/MultiplicativeTypeAbsoluteFunctor.lean), [explanation](../../Langlands/GroupScheme/Torus/MultiplicativeTypeAbsoluteFunctor.md) | `MultiplicativeTypeGroup.characterFunctor k` sends actual groups contravariantly to their finitely generated discrete absolute-Galois character modules, with canonical action and pullback formulas. |
| [MultiplicativeTypeAbsoluteEquivalenceStatement](../../Langlands/GroupScheme/Torus/MultiplicativeTypeAbsoluteEquivalenceStatement.lean), [explanation](../../Langlands/GroupScheme/Torus/MultiplicativeTypeAbsoluteEquivalenceStatement.md) | A proposition asserting `Functor.IsEquivalence` for that specific functor, for every field. No equivalence proof is supplied by this unit. |

For a field `k : Type u`, the category uses precisely
`SeparableClosure k ≃ₐ[k] SeparableClosure k` with Mathlib's Krull topology.
Its module universe `v` is independent of `u`. It is the full subcategory of
the existing `SmoothRep` category cut out by `Module.Finite ℤ`; torsion is
allowed. Its maps are all equivariant integral linear maps. Given a discrete
topology on a carrier, the implemented interfaces prove continuous orbit
maps and joint continuity, and conversely bundle a supplied continuous
representation. No carrier topology is installed globally.

The absolute-character propositions quantify over every field and every
actual commutative group scheme `T` with `IsMultiplicativeType T.toGrp`.
That predicate supplies a finitely generated diagonalizable model after
some field extension. It assumes neither separable-closure splitting nor
finite Galois splitting. The characters are actual group-scheme morphisms
from `T` after base change to `SeparableClosure k` into the multiplicative
group, and the action is `characterLattice.galoisRepresentation`.
`MultiplicativeTypeAbsoluteCharacterFiniteStatement` asserts finite
generation of this group over the integers.
`MultiplicativeTypeAbsoluteCharacterSmoothStatement` asserts that each
character is fixed by an open subgroup. Representation smoothness imposes
no group-scheme smoothness hypothesis. Finite nonsmooth multiplicative-type
groups and their torsion characters remain in scope.

The finite-generation proof embeds the separable closure into the algebraic
closure of the arbitrary splitting extension. Actual base-change comparisons
and the diagonalizable character equivalence give finite generation over
this common overfield. Injectivity of canonical character base change then
descends finite generation over the noetherian ring `ℤ`.

The continuity proof descends each actual character, viewed as a morphism
into the base change of `Gm`, to a finite intermediate field. Its open
fixing subgroup fixes that character under the canonical transport action.
This field defines the character; the proof makes no claim that it splits
the group scheme.

The base-change construction works for arbitrary commutative rings `R, R'`,
an arbitrary morphism `b : Spec R' → Spec R`, and an arbitrary abelian group
`Λ`, all in one universe. It constructs `b* D_R(Λ) ≅ D_R'(Λ)` by comparing
their character-valued points and applying the published group-valued
Yoneda construction. Its formulas include nonaffine and nonreduced test
schemes. It needs no finite generation, freeness or field hypothesis.

The factorization proposition has independent field and module universes.
For the specified representation `ρ` on a finitely generated integral module
`M`, it asks for an actual intermediate field
`L : IntermediateField k (SeparableClosure k)`, with `FiniteDimensional k L`
and `IsGalois k L`, and an action `ρL` on the same `M` satisfying
`ρL.comp (AlgEquiv.restrictNormalHom L) = ρ`.
Torsion and the zero module are included. This is a module statement;
it asserts neither a realizing group scheme nor splitting of an existing
group scheme.

The actual functor has type

```text
MultiplicativeTypeGroup.characterFunctor k :
  (MultiplicativeTypeGroup k)ᵒᵖ ⥤ FGDiscreteGaloisModule.{u,u} k.
```

Its source is the full category of actual commutative group schemes
satisfying the unchanged `IsMultiplicativeType` predicate, with all
ground-field homomorphisms. The two published character proofs lift the
existing unrestricted character functor into the target full subcategories.
`characterFunctor_representation`, `characterFunctor_map_apply` and
`characterFunctor_forget` identify its canonical action, actual pullback
maps and equality after forgetting the two proved properties. This functor
uses module universe `u`, while the separate module category supports
independent universes.

`MultiplicativeTypeAbsoluteEquivalenceStatement.{u}` asks for full
faithfulness and essential surjectivity of precisely this functor over
every field `k : Type u`. It adds no chosen splitting field, group
smoothness, connectedness, perfectness or characteristic hypothesis.
Torsion remains included. Constructing the functor and publishing this
statement leave its equivalence proof open.

## Publication evidence and historical correction

The category and absolute-character statement have accepted public receipts
`0fc2da0e-bfc0-4974-8bee-e7240def6695` and
`ce3e9707-fc15-4f48-a6ef-d822fe4bb930`, respectively, published at
`aeb3911c4e1bf6e3a2f653e874e4ebc422d2a61a`. Their independent reviewers were
Reviewer 4106 and Reviewer 4116.
The base-change construction and factorization statement have accepted
public receipts `932f8d9b-9dd7-40bf-846a-4eb99936f51c` and
`46924977-6f7a-4562-8384-f5b837b4b490`, published at
`4abbe7aabd9c92005d91c9d5bba86b879e928bb3`. Their independent reviewers were
Reviewer 4147 and Reviewer 4182. All four approvals have no qualifications.
At the 16 November recovery check, all eight current Library source files
matched their frozen submission hashes. The four modules compiled together
without errors or warnings.

The earlier note's “Remaining comparison” section records a historical
publication delay for the
[finite-Galois full-faithfulness statement](../../Langlands/GroupScheme/Torus/MultiplicativeTypeGaloisFullFaithfulnessStatement.md).
Its receipt `c9448fc7-8310-47be-8641-c89294a4a656` is now independently
approved by Reviewer 2052 without qualifications and public at
`e5365902d74534dbf1622c06e695dffdc128d723`. This publishes the statement,
including torsion in both diagonalizable models; its proof remains owned
by Task 6604.

The four newer publications have the following independent evidence:

| Unit | Accepted public receipt | Reviewer | Publication commit |
| --- | --- | --- | --- |
| Exact finite-generation proof, Task 7182 (`c5259b02-2dbb-415f-8233-4f5501fdda63`) | `277ffe7f-5b97-4d37-bda7-f13a6f8ecfc2` | Reviewer 5697 | `c9fdbede045511865f0ea27259a1e1a35f442905` |
| Exact continuity proof, Task 6980 (`50df9354-1f6e-4998-adc7-999f1bda1520`) | `74d6c925-7d88-4f04-bf7a-e78d4f532298` | Reviewer 5698 | `c9fdbede045511865f0ea27259a1e1a35f442905` |
| Actual absolute-character functor | `358e4312-b393-48df-b4de-96c614e4812b` | Reviewer 6008 | `d210ab55a138c1f91b826ee47c6280ce6c6b90bc` |
| Exact absolute-equivalence statement | `af4073a6-4bc3-4b1a-a36e-136325c558b2` | Reviewer 6012 | `d210ab55a138c1f91b826ee47c6280ce6c6b90bc` |

All four approvals have no qualifications. The two proofs have accepted
Lake-build and exact-target validation receipts
`5559cddd-c239-4618-88e5-ecc72a2580f8` and
`25c31d18-3578-4e7a-bb36-417f612d3e4d`, respectively.
At the 17 November recovery check, the eight files in these four newer
Lean/Markdown pairs matched their frozen hashes in both the workspace and
Library `276bcb8d72bd1a6ea95eac204206680403da83f7`.
Development check `5f82ef0a-5925-4a3c-8d92-13990632231c` compiled all four
modules without errors or warnings and confirmed that the equivalence
statement returns `Prop`. This check supplies development evidence;
the proof acceptance rests on the independent records above.

## Exact proof owners and remaining comparison

The two exact character proofs are now published. The five existing
component proof tasks and the new absolute-equivalence proof task below
were ready, unassigned and had no submitted artifacts when inspected on
17 November 2026. The target names use the namespace specified above.

| Task | Exact target |
| --- | --- |
| Task 7183 (`f53e13e8-a4f7-4d60-bd5b-56d4e1ed5a13`) | `DiscreteGaloisFiniteFactorizationStatement.{u,v}` |
| Task 6604 (`b7d38134-e586-47d6-a660-cff9397ecd98`) | `MultiplicativeTypeGaloisFullFaithfulnessStatement.{u}` |
| Task 6657 (`16e13afa-15d3-4a56-ac7c-dcc324ae9559`) | `MultiplicativeTypeGaloisExactnessStatement.{u}` |
| Task 6926 (`5ebb1cda-938e-49de-bb87-258b887d34f5`) | `MultiplicativeTypeGaloisEquivalenceStatement.{u}` |
| Task 6775 (`340febea-7648-460c-b207-9bd8e285d07b`) | `MultiplicativeTypeFiniteGaloisSplittingStatement.{u}` |
| Task 7346 (`39eda79f-8035-40ec-88d5-1448b9256c56`) | `MultiplicativeTypeAbsoluteEquivalenceStatement.{u}` |

A complete development-checked proof draft is shared with Task 7183.
Draft compilation is not independent proof acceptance or publication.
Task 7346 preserves the five component owners. A proof through finite-level
splitting, factorization and equivalence still owes the actual character
comparisons after field extension and the identification of inflated
canonical actions and pullback maps. These are proof obligations, not
premises of the absolute-equivalence statement. Exact-sequence compatibility
retains its separate owner.

All eight thematic families of the standing program remain obligations.
This note records published mathematics and remaining proof ownership;
it supplies no new mathematical proof or whole-program completion evidence.

## Provenance

The category and absolute-character propositions isolate the module target
and object-membership assertions of J. S. Milne, *Algebraic Groups* (2017),
§12.g and Theorem 12.23, printed pp.239–240 / PDF pp.255–256.
The registered source is `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The original pages and complete retained official errata were read during
the construction; no listed correction changes these passages.
The base-change comparison is an internal consequence of the existing
all-test corepresentation and pullback constructions. The factorization
proposition records the finite-generator/open-kernel and normal Krull-basis
argument explained in its paired Markdown. These provenance descriptions
explain the interfaces and statements; their proof status is as recorded above.
