# Character equivalence and exactness for groups of multiplicative type

This addendum, last updated on 18 November 2026, updates families 2 and 6 of the group-scheme program. It
supplements the [14 November coverage note](diagonalizable-galois-coverage-2026-11-14.md).
The Library contains proofs of the finite-level and
absolute-Galois character equivalences and their short exact sequence
comparisons. The absolute results use the canonical character functor over
the separable closure of an arbitrary field.
All declaration names below belong to `Langlands.GroupScheme`, with
`Diagonalizable` and `DiagonalizableCharacter` indicating its subnamespaces.

## Published modules and exact scope

| Module | Published content |
| --- | --- |
| [DiscreteGaloisModule](../../Langlands/GroupScheme/Torus/DiscreteGaloisModule.lean), [explanation](../../Langlands/GroupScheme/Torus/DiscreteGaloisModule.md) | `FGDiscreteGaloisModule.{u,v} k`, the category of finitely generated integral modules with smooth absolute-Galois action, and its representation, morphism and continuity interfaces. |
| [MultiplicativeTypeAbsoluteCharacterStatement](../../Langlands/GroupScheme/Torus/MultiplicativeTypeAbsoluteCharacterStatement.lean), [explanation](../../Langlands/GroupScheme/Torus/MultiplicativeTypeAbsoluteCharacterStatement.md) | Separate finite-generation and continuity propositions for the actual separable-closure character group, together with their conjunction. No proof is supplied by this module. |
| [DiagonalizableBaseChange](../../Langlands/GroupScheme/Torus/DiagonalizableBaseChange.lean), [explanation](../../Langlands/GroupScheme/Torus/DiagonalizableBaseChange.md) | `Diagonalizable.baseChangeIso` and `commBaseChangeIso`, with formulas on every test scheme. |
| [DiscreteGaloisFiniteFactorizationStatement](../../Langlands/GroupScheme/Torus/DiscreteGaloisFiniteFactorizationStatement.lean), [explanation](../../Langlands/GroupScheme/Torus/DiscreteGaloisFiniteFactorizationStatement.md) | A proposition asserting descent of a specified smooth integral representation through an actual finite Galois intermediate field, on the same module. No proof is supplied by this module. |
| [MultiplicativeTypeAbsoluteCharacterFiniteProof](../../Langlands/GroupScheme/Torus/MultiplicativeTypeAbsoluteCharacterFiniteProof.lean), [explanation](../../Langlands/GroupScheme/Torus/MultiplicativeTypeAbsoluteCharacterFiniteProof.md) | `multiplicativeTypeAbsoluteCharacterFinite` proves exactly `MultiplicativeTypeAbsoluteCharacterFiniteStatement.{u}`. |
| [MultiplicativeTypeAbsoluteCharacterSmoothProof](../../Langlands/GroupScheme/Torus/MultiplicativeTypeAbsoluteCharacterSmoothProof.lean), [explanation](../../Langlands/GroupScheme/Torus/MultiplicativeTypeAbsoluteCharacterSmoothProof.md) | `multiplicativeTypeAbsoluteCharacterSmooth` proves exactly `MultiplicativeTypeAbsoluteCharacterSmoothStatement.{u}`. |
| [MultiplicativeTypeAbsoluteFunctor](../../Langlands/GroupScheme/Torus/MultiplicativeTypeAbsoluteFunctor.lean), [explanation](../../Langlands/GroupScheme/Torus/MultiplicativeTypeAbsoluteFunctor.md) | `MultiplicativeTypeGroup.characterFunctor k` sends actual groups contravariantly to their finitely generated discrete absolute-Galois character modules, with canonical action and pullback formulas. |
| [MultiplicativeTypeAbsoluteEquivalenceStatement](../../Langlands/GroupScheme/Torus/MultiplicativeTypeAbsoluteEquivalenceStatement.lean), [explanation](../../Langlands/GroupScheme/Torus/MultiplicativeTypeAbsoluteEquivalenceStatement.md) | A proposition asserting `Functor.IsEquivalence` for that specific functor, for every field. No equivalence proof is supplied by this module. |
| [DiscreteGaloisFiniteFactorizationProof](../../Langlands/GroupScheme/Torus/DiscreteGaloisFiniteFactorizationProof.lean), [explanation](../../Langlands/GroupScheme/Torus/DiscreteGaloisFiniteFactorizationProof.md) | `discreteGaloisFiniteFactorization` proves exactly `DiscreteGaloisFiniteFactorizationStatement.{u,v}`, retaining the specified action on the same module. |
| [MultiplicativeTypeGaloisFullFaithfulnessProof](../../Langlands/GroupScheme/Torus/MultiplicativeTypeGaloisFullFaithfulnessProof.lean), [explanation](../../Langlands/GroupScheme/Torus/MultiplicativeTypeGaloisFullFaithfulnessProof.md) | `multiplicativeTypeGaloisFullFaithfulness` proves exactly `MultiplicativeTypeGaloisFullFaithfulnessStatement.{u}` for actual characters over a common finite Galois splitting field. |
| [MultiplicativeTypeGaloisExactnessProof](../../Langlands/GroupScheme/Torus/MultiplicativeTypeGaloisExactnessProof.lean), [explanation](../../Langlands/GroupScheme/Torus/MultiplicativeTypeGaloisExactnessProof.md) | `multiplicativeTypeGaloisExactness` proves exactly `MultiplicativeTypeGaloisExactnessStatement.{u}`, including the full represented kernel, the fppf quotient and both canonical equivariances. |
| [MultiplicativeTypeFiniteGaloisSplittingProof](../../Langlands/GroupScheme/Torus/MultiplicativeTypeFiniteGaloisSplittingProof.lean), [explanation](../../Langlands/GroupScheme/Torus/MultiplicativeTypeFiniteGaloisSplittingProof.md) | `multiplicativeTypeFiniteGaloisSplitting` proves exactly `MultiplicativeTypeFiniteGaloisSplittingStatement.{u}` from the unchanged arbitrary-extension definition of multiplicative type. |
| [MultiplicativeTypeGaloisEquivalenceProof](../../Langlands/GroupScheme/Torus/MultiplicativeTypeGaloisEquivalenceProof.lean), [explanation](../../Langlands/GroupScheme/Torus/MultiplicativeTypeGaloisEquivalenceProof.md) | `multiplicativeTypeGaloisEquivalence` proves exactly `MultiplicativeTypeGaloisEquivalenceStatement.{u}` for the actual character functor on groups split by a specified finite Galois extension. |
| [MultiplicativeTypeAbsoluteEquivalenceProof](../../Langlands/GroupScheme/Torus/MultiplicativeTypeAbsoluteEquivalenceProof.lean), [explanation](../../Langlands/GroupScheme/Torus/MultiplicativeTypeAbsoluteEquivalenceProof.md) | `multiplicativeTypeAbsoluteEquivalence` proves exactly `MultiplicativeTypeAbsoluteEquivalenceStatement.{u}` for the canonical separable-closure character functor over every field. |
| [MultiplicativeTypeAbsoluteExactnessStatement](../../Langlands/GroupScheme/Torus/MultiplicativeTypeAbsoluteExactnessStatement.lean), [explanation](../../Langlands/GroupScheme/Torus/MultiplicativeTypeAbsoluteExactnessStatement.md) | The proposition compares closed subgroup and represented fppf quotient sequences with short exact sequences under `MultiplicativeTypeGroup.characterFunctor k`. |
| [MultiplicativeTypeAbsoluteExactnessProof](../../Langlands/GroupScheme/Torus/MultiplicativeTypeAbsoluteExactnessProof.lean), [explanation](../../Langlands/GroupScheme/Torus/MultiplicativeTypeAbsoluteExactnessProof.md) | `multiplicativeTypeAbsoluteExactness` proves exactly `MultiplicativeTypeAbsoluteExactnessStatement.{u}` for every field and every pair of composable morphisms of actual groups of multiplicative type. |

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

## Checks and first appearance in the Library

The category and the absolute-character statement first appeared at Library
commit `aeb3911c4e1bf6e3a2f653e874e4ebc422d2a61a`; the base-change
construction and the factorization statement at
`4abbe7aabd9c92005d91c9d5bba86b879e928bb3`. All eight Library source files of
these four modules were checked against the versions that first entered the
Library. The four modules compiled together without errors or warnings.

The earlier note's “Remaining comparison” section concerns the
[finite-Galois full-faithfulness statement](../../Langlands/GroupScheme/Torus/MultiplicativeTypeGaloisFullFaithfulnessStatement.md).
That statement first appeared at Library commit
`e5365902d74534dbf1622c06e695dffdc128d723`, including torsion in both
diagonalizable models. Its exact proof is in the Library, as recorded below.

| Module | First appeared at Library commit |
| --- | --- |
| Exact finite-generation proof | `c9fdbede045511865f0ea27259a1e1a35f442905` |
| Exact continuity proof | `c9fdbede045511865f0ea27259a1e1a35f442905` |
| Actual absolute-character functor | `d210ab55a138c1f91b826ee47c6280ce6c6b90bc` |
| Exact absolute-equivalence statement | `d210ab55a138c1f91b826ee47c6280ce6c6b90bc` |

The two proofs were checked for Lake build and exact target. The eight
files in these four Lean/Markdown pairs were checked against Library
`276bcb8d72bd1a6ea95eac204206680403da83f7`, where they match the versions
that first entered the Library. A compilation of all four modules completed
without errors or warnings and confirmed that the equivalence statement
returns `Prop`.

Four further exact proofs are in the Library at commit
`f24f97443f21ff7e59b1cf3b509602157dae54c2`: finite factorization
(`discreteGaloisFiniteFactorization`), full faithfulness
(`multiplicativeTypeGaloisFullFaithfulness`), exactness
(`multiplicativeTypeGaloisExactness`) and finite Galois splitting
(`multiplicativeTypeFiniteGaloisSplitting`).

Each proof was checked for Lake build, exact target, unchanged statement and
unchanged inputs. At Library `b369a8f280229cf081a17f96b81c7a8c1ff1f539`, the
factorization, exactness and finite-splitting Lean/Markdown pairs matched the
versions that first entered the Library. The full-faithfulness pair in the
Library differs from the version first written: it imports
`MultiplicativeTypeSplitCategory` and reuses the
existing `DiagonalizableCharacter.evalCharacterEquiv` and application formula in
place of duplicate local declarations; its Markdown explains that reuse.
The main theorem and all remaining code are unchanged.
The actual absolute functor and absolute-equivalence statement pairs also
still matched.

A compilation of the four further proof modules, the two absolute-character
proof modules, the actual absolute functor and its equivalence statement
completed with zero errors and warnings. Inspection again confirmed that the
statement returns `Prop` in universe `u`, with only the standard axioms.

## Published categorical equivalences

Both categorical proofs are in the Library at commit
`42c696807fd25d6ea96d001a596d7bba7b4b52b9`: the finite Galois equivalence
(`multiplicativeTypeGaloisEquivalence`) and the absolute-Galois equivalence
(`multiplicativeTypeAbsoluteEquivalence`).

Each proof was checked for Lake build, exact target, unchanged statement and
unchanged inputs. All six files in the finite proof, its
[categorical reduction](../../Langlands/GroupScheme/Torus/MultiplicativeTypeGaloisEquivalenceReduction.md)
and the absolute proof were checked against Library
`c1d49d172bcff649390acf18c39e1b793f3b6839`, where they match the versions
that first entered the Library.

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
absolute action. These comparisons are proved within the absolute
proof. The final theorem assembles the three categorical properties
for the specified `MultiplicativeTypeGroup.characterFunctor k`.

The absolute theorem covers every field `k : Type u` and every object of
`MultiplicativeTypeGroup k`. The category includes finite nonsmooth groups
and the character functor takes values in modules that may have torsion.

A compilation of eleven affected modules, including both equivalence proofs
and the finite categorical reduction, completed with zero errors or warnings.
Inspection of `multiplicativeTypeAbsoluteEquivalence` reports universe
parameter `u` and only `propext`, `Classical.choice` and `Quot.sound`.

## Published absolute-Galois exactness

For `i : N ⟶ E` and `q : E ⟶ Q` in `MultiplicativeTypeGroup k` over any
field `k : Type u`, the theorem identifies two conditions. First, `i` is
a closed immersion and `q` is a represented fppf quotient by its range.
The quotient predicate gives flatness, surjectivity and local finite
presentation for `q`, and requires equality of the kernel range with
the range of `i` on every test scheme. Second, the actual character
pullbacks along `q` and `i` are injective at the first term, exact at the
middle term and surjective at the last term. Those pullbacks are
morphisms of `FGDiscreteGaloisModule.{u,u} k` and already carry their
equivariance. The theorem includes torsion character modules and finite
nonsmooth groups.

The proof supplies diagonalizable models over `SeparableClosure k`, applies
fpqc descent to the subgroup and quotient conditions, and invokes the
split theorem for the transported maps. Evaluation of characters gives
the commuting squares that transfer injectivity, exactness and surjectivity
to the actual pullbacks. This proves the short exact sequence clause of
Milne 2017, Theorem 12.23, p.240, using the split clause of Theorem 12.9(b),
pp.233–234. [Proof explanation](../../Langlands/GroupScheme/Torus/MultiplicativeTypeAbsoluteExactnessProof.md)

| Module | First appeared at Library commit |
| --- | --- |
| Absolute exactness statement | `db14afe3373dd1e402e436b7f53a35a278f3ee90` |
| Absolute exactness proof | `bb9e086196d00484fd52204977452d922bf3c660` |

The proof was checked for Lake build, exact target, unchanged statement and
unchanged inputs. The Lean and Markdown pairs were checked against Library
`f050c0b1b525624bc32c1e7c25a8d2841bb2d4e0`, where they match the versions
that first entered the Library. A rebuild of the thirteen affected modules
completed with zero errors or warnings, and
`multiplicativeTypeAbsoluteExactness` was inspected in universe `u`.

These results supply the multiplicative-type character comparison in
families 2 and 6. The other obligations of the eight families are recorded
in their ledgers.

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
