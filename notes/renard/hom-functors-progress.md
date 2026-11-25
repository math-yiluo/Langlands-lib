# Renard A.VIII.2: Hom functors, object properties and basic comparisons

The original passage and six published Lean/Markdown pairs were checked on
4 November 2026. This map covers the
beginning of A.VIII.2 through the projective nonzero-Hom criterion. The
[A.VIII.1 source map](exact-functors-progress.md) supplies the general
sequence-exactness and faithfulness results used here. The later smallness,
finite-support, finite-type, module-equivalence, converse and presentation
assertions have their own published modules, mapped in the
[category/module source map](category-module-progress.md).
Neither this note nor the six publications declares A.VIII.2 complete.

## Governing source and assertion map

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Its retained file is
`central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
The passage is A.VIII.2, printed pages 266–267 / one-based PDF272–273.
The surrounding A.VIII.1 on printed266/PDF272 fixes additive functors
between abelian categories and interprets contravariance on the opposite.

In the table, the two construction names have namespace
`Langlands.CategoryTheory.Renard`; all other names have namespace
`Langlands.Renard`. Every row concerns an actual object `P` of an arbitrary
abelian category `C : Type u` with `Category.{v} C`. Object and Hom
universes are independent.

| Original assertion and locator | Published declaration or exact proof | Status and correspondence |
| --- | --- | --- |
| Covariant integer-module-valued Hom functor, printed266/PDF272, final display | `preadditiveCoyonedaInt P` in [HomFunctors](../../Langlands/CategoryTheory/Renard/HomFunctors.md) | Actual carrier `P ⟶ X`, map by postcomposition, canonical integer action; construction and intrinsic laws published |
| Contravariant Hom functor, printed267/PDF273, opening display | `preadditiveYonedaInt P` in the same pair | Actual carrier `X ⟶ P`, map by precomposition on `Cᵒᵖ`; construction and intrinsic laws published |
| Both Hom functors are left exact, printed267/PDF273, sentence after the display | `CovariantHomLeftExactStatement P` and `ContravariantHomLeftExactStatement P`, proved by `covariantHomLeftExact P` and `contravariantHomLeftExact P` | Covariant and opposite-category left sequence conditions proved |
| Projective object, printed267/PDF273, first paragraph | `HomProjective P` in [HomObjectProperties](../../Langlands/CategoryTheory/Renard/HomObjectProperties.md) | Defined by `SequenceExact` of the actual covariant Hom functor |
| Injective object, same paragraph | `HomInjective P` | Defined by `ContravariantSequenceExact` of the actual contravariant Hom functor |
| Generator, same paragraph | `HomGenerator P` | Defined by faithfulness of the actual covariant Hom functor |
| Cogenerator, same paragraph | `HomCogenerator P` | Defined by faithfulness of the actual contravariant Hom functor |
| Progenerator, same paragraph | `HomProgenerator P` | Exactly `HomProjective P ∧ HomGenerator P`; no smallness condition |
| A projective object is a progenerator iff it maps nontrivially to every nonzero object, same paragraph; sufficiency invokes A.VIII.1 | `ProjectiveProgeneratorCriterionStatement P`, proved by `projectiveProgeneratorCriterion P` | Full source criterion proved with its projectivity premise |

The five `homProjective_iff`, `homInjective_iff`, `homGenerator_iff`,
`homCogenerator_iff` and `homProgenerator_iff` lemmas only expose the five
definitions by `Iff.rfl`. The substantive dictionaries below are separate
results.

## Actual maps, actions and exactness conventions

The construction reuses Mathlib's `preadditiveCoyonedaObj P` and
`preadditiveYonedaObj P`, then restricts scalars along the canonical integer
ring maps. It already works with `Preadditive C`; the object properties
and comparison theorems use `Abelian C`. For `g : X ⟶ Y`, the maps are

```text
Hom(P, X) → Hom(P, Y),  f ↦ f ≫ g,
Hom(Y, P) → Hom(X, P),  h ↦ g ≫ h.
```

The source's displayed composition labels are reversed under ordinary
composition notation. The published construction companion explains the
type-correct reading above. The two forgetful composites to additive
groups are definitionally the corresponding preadditive coyoneda and
yoneda functors, with identity-component natural isomorphisms also supplied.
Integer scalar multiplication is checked against the actual restricted
module structure and ordinary repeated addition on each Hom group.

The endomorphism-module functors have values in unital modules.
Mathlib's `End.mul_def` gives `r * s = s ≫ r`. On `P ⟶ X`, the action is
`MulOpposite.op r • f = r ≫ f`, encoding a right `End P`-module as a left
`(End P)ᵐᵒᵖ`-module. On `X ⟶ P`, the left action is `r • h = h ≫ r`.
The integer-module carriers have universe `v`; no equation between `u`
and `v`, or concrete realization of the objects of `C`, is required.
These unital endomorphism-module values are distinct from the original
possibly nonunital additive-action categories used elsewhere in the book.

`SequenceLeftExact F` tests every exact short complex with monomorphic
first map and requires exactness and a monomorphic first map after applying
`F`. The final input map need not be epic. The right condition tests
every exact short complex with epic final map, without requiring an initial
monomorphism. `SequenceExact F` contains both conditions.
The contravariant predicates apply the same definitions to the actual
functor on `Cᵒᵖ`. In particular, contravariant left exactness sends an exact
`X → Y → Z → 0` to `0 → Hom(Z,P) → Hom(Y,P) → Hom(X,P)`.
The public definitions retain these full tests; the proof uses the checked
comparison with short exact inputs.

## Derived comparisons and exact proof targets

The following dictionaries are derived from the source definitions and
Mathlib's native categorical predicates; they are not separately numbered
assertions of Renard.

| Published proposition | Published clause theorem | Meaning |
| --- | --- | --- |
| `HomProjectiveComparisonStatement P` | `homProjectiveComparison P` | `HomProjective P ↔ CategoryTheory.Projective P`, lifting every map from `P` through every epimorphism |
| `HomInjectiveComparisonStatement P` | `homInjectiveComparison P` | `HomInjective P ↔ CategoryTheory.Injective P`, extending every map to `P` along every monomorphism |
| `HomGeneratorComparisonStatement P` | `homGeneratorComparison P` | `HomGenerator P ↔ CategoryTheory.IsSeparator P`, testing all parallel arrows by all maps from `P` |
| `HomCogeneratorComparisonStatement P` | `homCogeneratorComparison P` | `HomCogenerator P ↔ CategoryTheory.IsCoseparator P`, the full dual parallel-arrow test |

The exact aggregate targets are

```text
HomExactnessComparisonStatement P :=
  CovariantHomLeftExactStatement P ∧
  ContravariantHomLeftExactStatement P ∧
  HomProjectiveComparisonStatement P ∧
  HomInjectiveComparisonStatement P

HomGeneratorCriteriaStatement P :=
  HomGeneratorComparisonStatement P ∧
  HomCogeneratorComparisonStatement P ∧
  ProjectiveProgeneratorCriterionStatement P

ProjectiveProgeneratorCriterionStatement P :=
  HomProjective P →
    (HomProgenerator P ↔
      ∀ Y : C, ¬CategoryTheory.Limits.IsZero Y →
        ∃ f : P ⟶ Y, f ≠ 0)
```

All conjunctions are right associated. The two aggregate theorems
`homExactnessComparison P` and `homGeneratorCriteria P` have only the
common arbitrary abelian-category context and the object `P` as
parameters. Projectivity occurs inside the third clause of the second
target. No enough-projectives, enough-injectives, cocompleteness, smallness
or generation premise is added to either aggregate.

The statement pairs are
[HomExactnessComparisonStatements](../../Langlands/CategoryTheory/Renard/HomExactnessComparisonStatements.md)
and [HomGeneratorCriteriaStatements](../../Langlands/CategoryTheory/Renard/HomGeneratorCriteriaStatements.md).
They contain Prop-valued definitions, and their separate proof pairs are
[HomExactnessComparison](../../Langlands/CategoryTheory/Renard/HomExactnessComparison.md)
and [HomGeneratorCriteria](../../Langlands/CategoryTheory/Renard/HomGeneratorCriteria.md).

## Implemented proof routes

The Hom left-exactness proofs use finite-limit preservation of the
group-valued preadditive Hom functors. The published forgetful identities
and reflection through integer modules give finite-limit preservation of
the actual integer-module functors. The published
`sequenceLeftExactFiniteLimits` then gives the source sequence condition
on `C` and on `Cᵒᵖ`.

For the lifting dictionaries, a private helper proves that an additive
left exact functor between abelian categories is sequence exact iff it
preserves epimorphisms. Its reverse direction uses Mathlib's equivalence
between the short-exact-input right condition and the full right condition.
A second helper transfers epimorphism preservation through the ordinary
forgetful functor from integer modules to types. The actual Hom maps then
meet Mathlib's projective and injective lifting tests. These helpers are
internal proof steps whose hypotheses are discharged in the public
theorems.

The generator dictionaries transfer faithfulness through the faithful
forgetful functor to additive groups and reuse Mathlib's preadditive
separator and coseparator comparisons. Necessity in the nonzero-Hom
criterion applies the separator test to `𝟙 Y` and `0`: if every
`P ⟶ Y` is zero, then `Y` is a zero object. Sufficiency uses the
source route through A.VIII.1, implemented by the published
`sequenceExactReflectsZeroFaithful`. Projectivity supplies exactness of
the covariant Hom functor. If its value at `Y` is zero, the actual
module carrier `P ⟶ Y` is subsingleton; the proposed nonzero morphism
therefore forces `Y` to be zero. This establishes zero-object reflection
and hence faithfulness without treating an abstract object of `C` as
a set of elements.

## Errata and provenance

The supplementary source
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
is retained at
`literature/Renard — Représentations des groupes réductifs p-adiques- corrections et compléments (2010 edition errata).pdf`.
Its PDF18–19 corrections for old printed308–309 replace faithfulness by
exactness in the image-factorization argument, identify sufficiency in
the nonzero-Hom criterion, and replace `X` by `P` in the later smallness
definition. The 2026 source already contains these changes. These older
errata do not govern the current numbering and contain no correction
to the two displayed Hom-map labels. No `notes/errata` directory existed
in the workspace or the pinned Library at this audit.

The original gives no separate external bibliography appeal for this
basic group of assertions; the criterion explicitly invokes A.VIII.1.
Restriction of scalars, the four native-predicate dictionaries and the
aggregate conjunctions are implementation choices or derived packaging.
The construction and statement companions identify that distinction,
and the proof companions describe the routes implemented above.

## In the Library

Each module below is in the Library. The two proofs were checked by a Lake
build against their exact targets, with the statements and their inputs
unchanged. The definition and statement modules were checked for builds and
declaration kinds; these checks do not themselves certify the substantive
proof targets.

| Module | Kind | First appeared at Library commit |
| --- | --- | --- |
| Hom functors | definition | `b9a5677e7d9363960d4c8b6705892ed2b9e28155` |
| Five object properties | definition | `d8425b466384657b53f6106e0310f36fe92afff2` |
| Hom exactness/comparison statements | statement | `cb6a47b2390bdcd0be78fac0552b7fd5c46cd51b` |
| Hom exactness/comparison proofs | proof | `61f87bbe6fe6e5ffe1387e9640956e5d8d8c9fc5` |
| Generator/criterion statements | statement | `cb6a47b2390bdcd0be78fac0552b7fd5c46cd51b` |
| Generator/criterion proofs | proof | `b7a6ea71635c439ae131d5b451e5f403e32dc1c7` |


All twelve paired files agree with Library
`fd5d309e44e7f2f66516fa1781a0112c4e3a56ac` and
`53cc630ee154a6ce8960bfee141c7227de200002`.
Two separate builds also compiled both proof modules
with zero errors or warnings.

## Retained obligations

This note does not enlarge the scopes of the six modules. The later group
has separate published modules: finite-support factorization, the source
finite-type comparison, regular-module small progenerators, two-term
presentations, the forward endomorphism-module equivalence, transport
along equivalences and the converse. The
[category/module note](category-module-progress.md) records their
statements and proof routes, with its explicit audit dates. Its original-action/nonunital branches remain distinct from the
unital right-endomorphism-module theorem. Other Appendix A assertions and
all remaining chapters and appendices remain obligations of the
whole-book coverage ([coverage.md](coverage.md)).
