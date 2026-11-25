# Renard A.II.2: equivalence criterion, representatives and vector spaces

The Library modules below were checked through 3 November 2026.
The construction, statement and proof pairs agree with their first published
versions and are unchanged in Library `e01d121751dd80ba2ce2d21544b43f6e8df18007`.
This supplements the [whole-book coverage ledger](coverage.md) with the
sufficient equivalence criterion, the representative-subcategory comparison,
and the exact equivalence in the fixed-dimension example. A.I and the other A.II
assertions retain their separate obligations.
The correspondence maps in the final section are verified at Library
`f3b542a2044236604234c42094d278dbc4167f40`.

## Governing source and composition convention

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
retained at
`central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
The original A.II.1–2, printed pp.250–251 / PDF256–257, was read, including
the natural-transformation definition, quasi-inverse definition, fixed-dimension
example and final unnumbered sufficient criterion. PDF257 was also inspected
visually. A.I.1, printed p.247 / PDF253, supplies the composition convention.

The boxed quasi-inverse definition on PDF257 exchanges the identity-category
subscripts. Both A.I.1 and the immediately preceding strict-inverse paragraph
use conventional composition: for `F : C ⥤ D` and `G : D ⥤ C`, conventional
`GF` acts on `C` and `FG` acts on `D`. Lean writes composition in application
order, so the correctly typed conclusion is

```text
F ⋙ G ≅ 𝟭 C,      G ⋙ F ≅ 𝟭 D.
```

The published statement and proof explicitly document this correction.
The registered older supplement `renard-2010-corrections-complements`,
SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was checked at PDF18–19 for appendix corrections. Those pages contain no
correction of these subscripts. This bounded supplementary check does not
replace the governing 2026 source.

## Exact assertion and implemented proof

The [statement pair](../../Langlands/CategoryTheory/Renard/EquivalenceCriterionStatements.md)
defines `Langlands.Renard.EquivalenceCriterionStatement C D`.
For every actual functor `F : C ⥤ D`, its hypotheses require surjectivity
and injectivity of each actual Hom map, and, for every `Y : D`, an object
`X : C` with `Nonempty (F.obj X ≅ Y)`. The conclusion existentially binds
one reverse functor `G : D ⥤ C` and both natural isomorphisms displayed above.
Their `Nonempty` wrappers make existence propositional; the isomorphisms
themselves live in the actual functor categories and include naturality.
No triangle identity is added to the source's quasi-inverse condition.

The [proof pair](../../Langlands/CategoryTheory/Renard/EquivalenceCriterion.md)
exports `Langlands.Renard.equivalenceCriterion` with exactly that statement
as its target. It installs Mathlib's `Functor.Full`, `Functor.Faithful`
and `Functor.EssSurj` from the three given hypotheses. These give
`Functor.IsEquivalence`, from which `Functor.asEquivalence` constructs an
actual equivalence. The witness for `G` is `F.asEquivalence.inverse`;
the two isomorphisms are its `unitIso.symm` and `counitIso`. The inverse
uses object preimages and morphism lifts through the full functor, and
faithfulness supplies the functor laws.

This is reuse of Mathlib at pinned commit
`5ed2965256430c3649e86755f9576b54eca72435`. Renard cites [28],
Theorem 1.13, and [25], Theorem 2.3.5, without a proof on PDF257.
The implementation does not claim to transcribe either reference's proof,
and this note claims no independent reading of them.

The categories have independent object and Hom universes:
`C : Type u₁` with `Category.{v₁} C` and `D : Type u₂` with
`Category.{v₂} D`. There is no additional nonemptiness, smallness,
additive, abelian or finiteness premise. The theorem proves the source's
sufficiency direction.

## In the Library

| Module | First appeared at Library commit |
| --- | --- |
| Statement | `7543113c99690e18b45f3b22d252e8cf77c3964e` |
| Exact proof | `286dd3b743f0437d22db0e793222073b9424e3eb` |

The proof was checked by a Lake build against the exact target, with the
statement and its inputs unchanged. The source correction and the
Lean/Markdown agreement were also checked.

A separate compilation of both modules completed with zero errors or
warnings and inspected four independent universe parameters. Its only
reported axioms are `propext`, `Classical.choice` and `Quot.sound`.

## The representative-subcategory comparison

The source discussion at A.II.2, printed pp.250–251 / PDF256–257, chooses
one representative of each isomorphism class and retains every ambient
morphism between chosen objects. The original pages were read, including
a fresh visual inspection on 3 November.

The [construction pair](../../Langlands/CategoryTheory/Renard/RepresentativeSubcategory.md)
defines `Langlands.Renard.representativeObjects C` as the actual range
of Mathlib's `fromSkeleton C`, and
`Langlands.Renard.RepresentativeSubcategory C` as its full subcategory.
`representativeInclusion C` is the actual inclusion;
`representativeOf X` and `representativeIso X` supply a selected object
and its actual isomorphism to each ambient object `X`.
`representative_eq_of_iso` proves equality of isomorphic selected objects.

The [statement pair](../../Langlands/CategoryTheory/Renard/RepresentativeSubcategoryStatements.md)
defines `Langlands.Renard.RepresentativeSubcategoryEquivalenceStatement C`.
Its [exact proof](../../Langlands/CategoryTheory/Renard/RepresentativeSubcategoryProof.md)
is `Langlands.Renard.representativeSubcategoryEquivalence`.
The proof applies the published general criterion to
`representativeInclusion C`. The inclusion's actual Hom maps are surjective
and injective because the subcategory is full. The witness for each ambient
object is `representativeOf X`, with `representativeIso X`.
The criterion then supplies one reverse functor and both actual natural
isomorphisms, with the identity-subscript correction above.

This comparison retains independent object and Hom universes
`C : Type u` with `[Category.{v} C]`. It adds no nonemptiness, smallness,
finiteness, additive or abelian premise, and includes the empty category.
It does not prescribe the reverse functor's object map or assert a strict
inverse or uniqueness.

| Module | First appeared at Library commit |
| --- | --- |
| Construction | `9d1720cbedcfd184cf48bf36249fc3029583cafa` |
| Statement | `fe38b3e353a7b1fb30017218b2ee1f7f87f979fd` |
| Exact proof | `405ff58c5df69766419c9941161444531c1979ae` |

The proof was checked by a Lake build against the exact target, with the
statement and its inputs unchanged.

## The fixed-dimension vector-space equivalence

The example at A.II.2, printed p.251 / PDF257, compares all vector spaces
of one prescribed dimension `n` with the one-object category on `kⁿ`,
retaining all linear maps. The original example and following paragraph
on choices of bases were reread visually on 3 November.

The published [construction pair](../../Langlands/CategoryTheory/Renard/FixedDimensionVectorSpaces.md)
defines `Langlands.Renard.FixedDimensionVectorSpaces k n` using actual
`ModuleCat k` objects with both `FiniteDimensional k X` and
`Module.finrank k X = n`. Keeping both conditions is necessary at `n = 0`,
since finrank alone may vanish for an infinite-dimensional space.
The coordinate object is `ULift.{v} (Fin n → k)`.
`OneObjectVectorSpaceCategory k n` is the actual full singleton
subcategory on that object, and `fixedDimensionVectorSpaceInclusion k n`
is its inclusion. Every linear endomorphism is retained, including
noninvertible ones. `coordinateVectorSpaceIso k n X` constructs an actual
isomorphism to each dimension-`n` object using `LinearEquiv.ofFinrankEq`.

The field universe `u` and additional carrier-universe parameter `v`
are independent, with carriers in `Type (max u v)`. The construction works
for every field and every natural `n`, including zero, with no
characteristic, field-size or positivity restriction.

This construction first appeared in the Library at
`405ff58c5df69766419c9941161444531c1979ae`; its files were checked against
that version. A separate compilation completed with zero errors or warnings.

The published [statement pair](../../Langlands/CategoryTheory/Renard/FixedDimensionVectorSpacesStatements.md)
defines `Langlands.Renard.FixedDimensionVectorSpaceEquivalenceStatement k n`.
It binds one actual reverse functor from `FixedDimensionVectorSpaces k n`
to `OneObjectVectorSpaceCategory k n`, and requires both actual natural
isomorphisms for that same functor. The conclusion uses the correctly typed
identity categories described above.

The [exact proof](../../Langlands/CategoryTheory/Renard/FixedDimensionVectorSpacesProof.md)
is `Langlands.Renard.fixedDimensionVectorSpaceEquivalence`.
It applies the published general criterion to the prescribed inclusion.
The full-subcategory inclusion supplies surjectivity and injectivity of
every actual Hom map; `oneObjectVectorSpace k n` and
`coordinateVectorSpaceIso k n X` supply essential surjectivity for each
ambient object `X`. The criterion then constructs one reverse functor and
both natural isomorphisms, including naturality and inverse laws.
The objectwise coordinate isomorphisms are inputs to this construction.
The theorem retains the arbitrary field, independent universes and every
natural dimension, including zero, with no additional premise.

| Module | First appeared at Library commit |
| --- | --- |
| Statement | `a89596feabc7e1db11dbefead1032c9cfc0d1409` |
| Exact proof | `428fa7c08e2fd98ecc08fa4e170f793c3c868556` |

An inspection of the statement confirms a Prop-valued definition with
independent `u` and `v`. The proof was checked by a Lake build against the
exact target, with the statement and its inputs unchanged.

SHA256 comparisons match the proof pair as first published with Library
`e01d121751dd80ba2ce2d21544b43f6e8df18007`.
The four recursively imported Langlands Lean/Markdown pairs are unchanged
between the proof's base, its first publication and that Library.
A separate build recompiles the published statement and proof with zero
errors or warnings; the proof inspection retains independent `u` and `v` and
reports only `propext`, `Classical.choice` and `Quot.sound`.

## Source map and remaining work

| Passage | Coverage and remaining obligation |
| --- | --- |
| A.I selected definitions and assertions, printed pp.247–249 / PDF253–255; A.II.2 full/faithful paragraph, printed p.251 / PDF257 | The published [elementary categorical source map](elementary-categories-source-map.md) compares introductory notation, A.I.1 inverses and cancellation, A.I.2 monic factors and conditional binary/indexed GLB/LUB definitions and uniqueness, A.I.4 initial/terminal/zero uniqueness and characterization, and A.II.2 fullness, faithfulness and actual full-subcategory inclusion. This is direct correspondence documentation, including finite and empty family conventions, not a new Lean artifact. |
| A.I.5, printed p.250 / PDF256: product, opposite and four named duality pairs | The published [category-construction and duality map](category-constructions-source-map.md) compares product/opposite categories, mono/epi, subobject/quotient with unchanged order, initial/terminal and kernel/cokernel, including zero-object compatibility and the two typed cokernel-zero corrections. |
| A.II.1, printed p.250 / PDF256: natural transformations and natural isomorphisms | The published [direct Mathlib source map](category-constructions-source-map.md) compares the component family, naturality square, functor category, identity and vertical composition, inverse natural transformations and identity functor. |
| A.II.2, printed p.251 / PDF257: quasi-inverse and fully faithful, essentially surjective sufficient criterion | The published statement and exact proof establish the criterion above, including the documented identity-subscript correction. |
| A.II.2, same page: vector-space example | Actual fixed-dimension category, full singleton coordinate category, inclusion, coordinate isomorphisms, equivalence statement and exact proof are published as above. The example concerns one fixed dimension, rather than all finite-dimensional spaces together. |
| A.II.2, printed pp.250–251 / PDF256–257: general representative-subcategory discussion | Actual full representative subcategory, inclusion, representative isomorphisms, uniqueness law, quasi-inverse statement and exact proof are published as above. |
| Remaining A.I and A.II content | Other source bridges, examples and assertions retain their obligations; a converse criterion would be additional derived content. |

The direct source map
([category-constructions-source-map](category-constructions-source-map.md))
also compares the product and opposite categories in A.I.5. It first appeared
in the Library at `e01d121751dd80ba2ce2d21544b43f6e8df18007`. It documents
direct Mathlib reuse, with no new Lean artifact.

Its duality extension first appeared in the Library at
`690e7bce992fb723bd66806fa2db3acd6dc07d78`. It supplies the four
named duality-pair correspondences listed above.

The elementary source map
([elementary-categories-source-map](elementary-categories-source-map.md))
first appeared in the Library at `f3b542a2044236604234c42094d278dbc4167f40`.
A correction made when it entered the Library identifies the full/faithful
paragraph as the one beginning “Le foncteur” after the vector-space example,
rather than the opening paragraph of A.II.2.
Both maps document direct reuse; their cited Library proofs are recorded
above or in their paired Markdown. A.I.3 and the other A.I–A.II assertions,
examples and constructions retain their separate obligations.

This focused audit makes no A.I, A.II, Appendix A or whole-book completion
declaration.
