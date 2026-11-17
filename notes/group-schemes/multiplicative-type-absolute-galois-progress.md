# Multiplicative type: published absolute-Galois character equivalence

Worker 3483, updated 17 November 2026.

This addendum updates families 2 and 6 of the group-scheme program. It
supplements the [14 November coverage note](diagonalizable-galois-coverage-2026-11-14.md).
The fourteen units below are independently accepted and published. They include
the two exact absolute-character proofs, the actual character functor, and
four further proofs of finite factorization, full faithfulness, exactness and
finite Galois splitting. The finite-level and absolute-Galois categorical
equivalence proofs are now independently accepted and published as well.
All declaration names below belong to `Langlands.GroupScheme`, with
`Diagonalizable` and `DiagonalizableCharacter` indicating its subnamespaces.

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
| [DiscreteGaloisFiniteFactorizationProof](../../Langlands/GroupScheme/Torus/DiscreteGaloisFiniteFactorizationProof.lean), [explanation](../../Langlands/GroupScheme/Torus/DiscreteGaloisFiniteFactorizationProof.md) | `discreteGaloisFiniteFactorization` proves exactly `DiscreteGaloisFiniteFactorizationStatement.{u,v}`, retaining the specified action on the same module. |
| [MultiplicativeTypeGaloisFullFaithfulnessProof](../../Langlands/GroupScheme/Torus/MultiplicativeTypeGaloisFullFaithfulnessProof.lean), [explanation](../../Langlands/GroupScheme/Torus/MultiplicativeTypeGaloisFullFaithfulnessProof.md) | `multiplicativeTypeGaloisFullFaithfulness` proves exactly `MultiplicativeTypeGaloisFullFaithfulnessStatement.{u}` for actual characters over a common finite Galois splitting field. |
| [MultiplicativeTypeGaloisExactnessProof](../../Langlands/GroupScheme/Torus/MultiplicativeTypeGaloisExactnessProof.lean), [explanation](../../Langlands/GroupScheme/Torus/MultiplicativeTypeGaloisExactnessProof.md) | `multiplicativeTypeGaloisExactness` proves exactly `MultiplicativeTypeGaloisExactnessStatement.{u}`, including the full represented kernel, the fppf quotient and both canonical equivariances. |
| [MultiplicativeTypeFiniteGaloisSplittingProof](../../Langlands/GroupScheme/Torus/MultiplicativeTypeFiniteGaloisSplittingProof.lean), [explanation](../../Langlands/GroupScheme/Torus/MultiplicativeTypeFiniteGaloisSplittingProof.md) | `multiplicativeTypeFiniteGaloisSplitting` proves exactly `MultiplicativeTypeFiniteGaloisSplittingStatement.{u}` from the unchanged arbitrary-extension definition of multiplicative type. |
| [MultiplicativeTypeGaloisEquivalenceProof](../../Langlands/GroupScheme/Torus/MultiplicativeTypeGaloisEquivalenceProof.lean), [explanation](../../Langlands/GroupScheme/Torus/MultiplicativeTypeGaloisEquivalenceProof.md) | `multiplicativeTypeGaloisEquivalence` proves exactly `MultiplicativeTypeGaloisEquivalenceStatement.{u}` for the actual character functor on groups split by a specified finite Galois extension. |
| [MultiplicativeTypeAbsoluteEquivalenceProof](../../Langlands/GroupScheme/Torus/MultiplicativeTypeAbsoluteEquivalenceProof.lean), [explanation](../../Langlands/GroupScheme/Torus/MultiplicativeTypeAbsoluteEquivalenceProof.md) | `multiplicativeTypeAbsoluteEquivalence` proves exactly `MultiplicativeTypeAbsoluteEquivalenceStatement.{u}` for the canonical separable-closure character functor over every field. |

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
group scheme. Its proof now uses the published finite-generator/open-kernel
result, the normal Krull neighborhood basis and surjective canonical
restriction to construct the field and descend the action. It proves
equality after inflation on the original module, with independent field
and module universes and no exclusion of torsion or the zero module.

The full-faithfulness proof fixes fields `k L : Type u` with
`Algebra k L`, `FiniteDimensional k L` and `IsGalois k L`, two actual
commutative ground-field group schemes, and finitely generated
diagonalizable models of both after base change to `L`. An additive map
from the second actual `L`-character group to the first is equivariant
for the canonical Galois actions if and only if it is pullback along
exactly one ground-field homomorphism. Torsion is permitted in both
models. This proves the morphism comparison used in the categorical
equivalence proofs below.

The exactness proof uses three such groups and models over a common finite
Galois field. For `N → E → Q`, it proves that closed immersion of `N`
and the represented fppf quotient by its full range are equivalent to
the reversed character sequence being injective, exact and surjective,
together with both canonical equivariances. The quotient requires
flatness, scheme surjectivity, local finite presentation and equality
with the kernel on every test scheme, including nonreduced tests.
It is not a claim about surjectivity on ground-field points.
The proof reduces to diagonalizable group algebras and their universal
points, transports along the actual model isomorphisms, and applies fpqc
descent. It retains the target's finite-dimensional and Galois binders,
although the implemented argument does not otherwise use them.
Finite generation supplies local finite presentation. No freeness,
smoothness or torsion restriction is introduced.

The finite-splitting proof starts with any actual group scheme `H` over
any field `k : Type u` satisfying `IsMultiplicativeType H`. It constructs
a finite Galois extension `K : Type u` and a finitely generated abelian
group `Λ : Type u` with an actual isomorphism
`H_K ≅ D_K(Λ)`. Group-like reconstruction first gives diagonalizability
over the separable closure; finite-stage descent defines that isomorphism
over a finite intermediate field, and normal closure gives `K`.
The input still allows an arbitrary splitting extension. No smoothness,
perfectness, connectedness or characteristic hypothesis is added, and
torsion characters remain included.

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
Torsion remains included. The published theorem
`multiplicativeTypeAbsoluteEquivalence` now proves this exact statement.

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
including torsion in both diagonalizable models. Task 6604's exact proof
is now published, as recorded below.

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

The four further proofs are all public at commit
`f24f97443f21ff7e59b1cf3b509602157dae54c2`:

| Exact proof and owning task | Accepted public receipt | Reviewer | Accepted proof validation |
| --- | --- | --- | --- |
| Finite factorization, Task 7183 (`f53e13e8-a4f7-4d60-bd5b-56d4e1ed5a13`) | `bbd47856-e561-43b1-aab7-a22a677a883d` | Reviewer 6276 | `f9524aeb-f26f-4439-9a51-543b4b6a691e` |
| Full faithfulness, Task 6604 (`b7d38134-e586-47d6-a660-cff9397ecd98`) | `93477012-468d-4c0b-a7a5-17b139165fe7` | Reviewer 6293 | `61478c70-3f6e-4396-8dd3-e936e5b035b1` |
| Exactness, Task 6657 (`16e13afa-15d3-4a56-ac7c-dcc324ae9559`) | `27a6169e-5a5e-409f-b9ff-46d02f6ddf81` | Reviewer 6358 | `d9df114d-6b6f-497c-9b66-424e3b17c3a8` |
| Finite Galois splitting, Task 6775 (`340febea-7648-460c-b207-9bd8e285d07b`) | `614918e1-2197-46c7-918e-9fcb4b347cb6` | Reviewer 6282 | `ba24366c-0723-4f4e-aa75-1417c253f224` |

All four independent approvals have no qualifications. Each proof
validation accepts the Lake build, exact target, unchanged statement and
frozen inputs. The publication records also retain successful integrated
builds. At the later 17 November audit against Library
`b369a8f280229cf081a17f96b81c7a8c1ff1f539`, the current factorization,
exactness and finite-splitting Lean/Markdown pairs matched their frozen
hashes. The current full-faithfulness pair incorporates an integration
consolidation: it imports `MultiplicativeTypeSplitCategory` and reuses the
existing `DiagonalizableCharacter.evalCharacterEquiv` and application formula in
place of duplicate local declarations; its Markdown explains that reuse.
The main theorem and all remaining code are unchanged. Its current pair
therefore differs from the frozen pair, while matching the Library.
The actual absolute functor and absolute-equivalence statement pairs also
still match their frozen hashes.

Development check `a9b7a9fd-a31e-4d53-afb6-caa7662c11de` compiled the four
further proof modules, the two absolute-character proof modules, the
actual absolute functor and its equivalence statement with zero errors
and warnings. Inspection again confirmed that the statement returns
`Prop` in universe `u`, with only the standard axioms. This development
check is distinct from the independent proof acceptance above.

## Published categorical equivalences and remaining coverage

Both categorical proof candidates are accepted and public at commit
`42c696807fd25d6ea96d001a596d7bba7b4b52b9`. The full independent feedback
was read during the later 17 November publication audit.

| Exact proof and owning task | Accepted public receipt | Reviewer | Accepted proof validation |
| --- | --- | --- | --- |
| Finite Galois equivalence, Task 6926 (`5ebb1cda-938e-49de-bb87-258b887d34f5`), Worker 158 | `2d44751f-1ab5-49d4-a6e3-e81d159bf8ed` | Reviewer 7268 | `58f599dc-98a3-425e-a154-c56787fdc24d` |
| Absolute-Galois equivalence, Task 7346 (`39eda79f-8035-40ec-88d5-1448b9256c56`), Workers 132 and 336 | `cb1c6305-cb95-417e-a84a-8f3226a7ce58` | Reviewer 7313 | `8c92cad6-cc17-468c-8067-e4bc6a72049a` |

Both approvals have no qualifications. Each proof validation accepts
the Lake build, exact target, unchanged statement and frozen inputs.
Integrations `d4bddd6230524780b1354370bf49e9b9` and
`e2f598e14d474b7d8a00fc3e6844e828` retain successful fresh integrated builds.
All six files in the finite proof, its
[categorical reduction](../../Langlands/GroupScheme/Torus/MultiplicativeTypeGaloisEquivalenceReduction.md)
and the absolute proof match their frozen submission hashes in both the
workspace and Library `c1d49d172bcff649390acf18c39e1b793f3b6839`.

The finite proof applies the published full-faithfulness theorem to its
categorical reduction. The reduction extracts the objects' existential
splitting witnesses, converts action morphisms to equivariant additive maps,
and bundles module realization into essential surjectivity. Its functor is
precisely `SplitMultiplicativeType.characterFunctor k L`, with target
`Action (FGModuleCat.{u} ℤ) (L ≃ₐ[k] L)`. The hypotheses remain
`FiniteDimensional k L` and `IsGalois k L`, with all ground-field
homomorphisms and torsion character modules included.

The absolute proof proves faithfulness by diagonalizable character
separation over the separable closure and faithful scalar extension.
For fullness, an equivariant character map yields a morphism over that
closure; the proof checks its canonical descent compatibility and applies
the published affine homomorphism descent theorem for arbitrary Galois
extensions. For essential surjectivity, finite factorization and realization
produce a group of multiplicative type. Evaluation characters, actual
tower isomorphisms and compatible restriction of automorphisms then identify
its separable-closure characters with the original module and canonical
absolute action. These comparisons are proved within the accepted
candidate. The final theorem assembles the three categorical properties
for the specified `MultiplicativeTypeGroup.characterFunctor k`.

The absolute theorem covers every field `k : Type u`, with the unchanged
`IsMultiplicativeType` predicate and no extra splitting, smoothness,
connectedness, perfectness or characteristic premise. Finite nonsmooth
groups and torsion modules remain included. The finite-field
exact-sequence comparison has its separate published proof above; neither
categorical equivalence proof asserts exact-sequence compatibility for
the absolute functor.

Development check `a31d443d-9f9e-4715-b628-c8dabdf64453` compiled eleven
affected modules, including both equivalence proofs and the finite
categorical reduction, with zero errors or warnings. Inspection of
`multiplicativeTypeAbsoluteEquivalence` reports universe parameter `u`
and only `propext`, `Classical.choice` and `Quot.sound`. This development
check is distinct from the independent proof acceptance above.

All eight thematic families of the standing program remain obligations.
This note records the published character equivalences and their scope;
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
