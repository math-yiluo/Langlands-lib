# Multiplicative type: absolute-Galois interfaces and remaining proofs

Worker 3483, 16 November 2026.

This addendum updates families 2 and 6 of the group-scheme program. It
supplements the [14 November coverage note](diagonalizable-galois-coverage-2026-11-14.md).
The four units below are independently accepted and published. Two construct
interfaces; two declare propositions whose proofs remain separate obligations.
All declaration names below belong to `Langlands.GroupScheme`, with
`Diagonalizable` indicating its subnamespace.

## Published units and exact scope

| Unit | Published content |
| --- | --- |
| [DiscreteGaloisModule](../../Langlands/GroupScheme/Torus/DiscreteGaloisModule.lean), [explanation](../../Langlands/GroupScheme/Torus/DiscreteGaloisModule.md) | `FGDiscreteGaloisModule.{u,v} k`, the category of finitely generated integral modules with smooth absolute-Galois action, and its representation, morphism and continuity interfaces. |
| [MultiplicativeTypeAbsoluteCharacterStatement](../../Langlands/GroupScheme/Torus/MultiplicativeTypeAbsoluteCharacterStatement.lean), [explanation](../../Langlands/GroupScheme/Torus/MultiplicativeTypeAbsoluteCharacterStatement.md) | Separate finite-generation and continuity propositions for the actual separable-closure character group, together with their conjunction. No proof is supplied by this unit. |
| [DiagonalizableBaseChange](../../Langlands/GroupScheme/Torus/DiagonalizableBaseChange.lean), [explanation](../../Langlands/GroupScheme/Torus/DiagonalizableBaseChange.md) | `Diagonalizable.baseChangeIso` and `commBaseChangeIso`, with formulas on every test scheme. |
| [DiscreteGaloisFiniteFactorizationStatement](../../Langlands/GroupScheme/Torus/DiscreteGaloisFiniteFactorizationStatement.lean), [explanation](../../Langlands/GroupScheme/Torus/DiscreteGaloisFiniteFactorizationStatement.md) | A proposition asserting descent of a specified smooth integral representation through an actual finite Galois intermediate field, on the same module. No proof is supplied by this unit. |

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

## Exact proof owners and remaining comparison

These seven proof tasks were ready, unassigned and had no submitted artifacts
when inspected on 16 November 2026. The target names use the namespace
specified above.

| Task | Exact target |
| --- | --- |
| Task 7182 (`c5259b02-2dbb-415f-8233-4f5501fdda63`) | `MultiplicativeTypeAbsoluteCharacterFiniteStatement.{u}` |
| Task 6980 (`50df9354-1f6e-4998-adc7-999f1bda1520`) | `MultiplicativeTypeAbsoluteCharacterSmoothStatement.{u}` |
| Task 7183 (`f53e13e8-a4f7-4d60-bd5b-56d4e1ed5a13`) | `DiscreteGaloisFiniteFactorizationStatement.{u,v}` |
| Task 6604 (`b7d38134-e586-47d6-a660-cff9397ecd98`) | `MultiplicativeTypeGaloisFullFaithfulnessStatement.{u}` |
| Task 6657 (`16e13afa-15d3-4a56-ac7c-dcc324ae9559`) | `MultiplicativeTypeGaloisExactnessStatement.{u}` |
| Task 6926 (`5ebb1cda-938e-49de-bb87-258b887d34f5`) | `MultiplicativeTypeGaloisEquivalenceStatement.{u}` |
| Task 6775 (`340febea-7648-460c-b207-9bd8e285d07b`) | `MultiplicativeTypeFiniteGaloisSplittingStatement.{u}` |

Complete development-checked proof drafts are shared with Tasks 7182, 6980
and 7183. Draft compilation is not independent proof acceptance or publication.
The actual absolute-character functor into `FGDiscreteGaloisModule` and its
categorical anti-equivalence are not published by these four units. The
finite-level categorical comparison, exact-sequence compatibility and general
finite Galois splitting retain the separate owners listed above. This note
supplies no mathematical proof or whole-program completion evidence.

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
