# Renard A.II.2: equivalence criterion, representatives and vector spaces

Worker 709 verified the publications below through 3 November 2026.
The construction, statement and proof pairs agree with their frozen submissions
and remain unchanged in Library `a2d087f74722634cb074d51ac39abb6a1543151d`.
This supplements the [whole-book coverage ledger](coverage.md) with the
sufficient equivalence criterion, the representative-subcategory comparison,
and the construction in the fixed-dimension example. A.I and the other A.II
assertions retain their separate obligations.

## Governing source and composition convention

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
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

## Independent acceptance and publication

Exact fetches report both candidates accepted and public.

| Unit | Candidate and authorship | Independent review | Publication |
| --- | --- | --- | --- |
| Statement | `7fd0ac10-e1db-4d5f-b3e6-da7d2375f304`, Worker 709 | Reviewer 9220, review task `e64628a8-864c-4a62-b567-08aa444ada0d`; unqualified approval | Integration `565a9e9b7e524cb18c14053786d43c07`, Library `7543113c99690e18b45f3b22d252e8cf77c3964e` |
| Exact proof | `1b81864e-a45f-4c00-a314-e84a17bea5a4`, Worker 1158 with Worker 709 as coauthor | Reviewer 9310, review task `1c08481f-ab9d-4f25-a1c3-d8a5a756dbbb`; unqualified approval | Integration `b4d19c8e78014c66bc277f636ab2323b`, Library `286dd3b743f0437d22db0e793222073b9424e3eb` |

Statement validation `691acf77-714c-476d-9fcf-0136e46df9e3` is accepted.
Proof validation `19ad668a-4555-466b-b978-829d1003f738` accepts Lake build,
exact-target, unchanged-statement and frozen-inputs checks under
`lean.proof@1`. The independent semantic reviews also verify the source
correction and Lean/Markdown agreement. Worker 709's implementation
attribution is retained in the proof pair.

A recovery compilation of both modules,
`dd07d3f8-39b0-495f-ba42-8e1c977ef92e`, completed with zero errors or
warnings and inspected four independent universe parameters. Its only
reported axioms are `propext`, `Classical.choice` and `Quot.sound`.
This development check supplies no additional mathematical acceptance;
proof acceptance rests on the exact candidate's machine and review receipts.

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

| Unit | Candidate and authorship | Independent review | Publication |
| --- | --- | --- | --- |
| Construction | `3c0c8e64-7561-4170-a603-6a322a051dc3`, Worker 709 | Reviewer 9582, review task `fd5440f9-410c-495f-841c-785a9774e4bf`; unqualified approval | Integration `36359437d16e416aa9104983ac53eee7`, Library `9d1720cbedcfd184cf48bf36249fc3029583cafa` |
| Statement | `4edfbd2a-aee6-44f3-a57a-2495d9d132c7`, Worker 709 | Reviewer 9689, review task `792508b2-0754-4771-b41d-cfb8dc5bee3d`; unqualified approval | Integration `57823dd58c3045749d53fd468519d108`, Library `fe38b3e353a7b1fb30017218b2ee1f7f87f979fd` |
| Exact proof | `2b2971c4-58bc-42ad-a727-688f9043f67a`, Worker 1158 with Worker 709 as coauthor | Reviewer 9900, review task `28d6a294-cdf6-466b-8c89-3461bbf23ef9`; unqualified approval | Integration `f18665986b0542a6b419db1e15fd294d`, Library `405ff58c5df69766419c9941161444531c1979ae` |

Proof validation `7c58c717-efbe-4611-94e4-8969c2c67acc` accepts Lake build,
exact-target, unchanged-statement and frozen-inputs checks. The full
integrated semantic reports were read. Acceptance and publication, rather
than the task's completion report alone, support this coverage claim.

## The fixed-dimension vector-space construction

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

Candidate `3985c1e3-aaec-4266-bcf4-8db62e405f7f`, authored by Worker 709,
was independently approved without qualifications by Reviewer 9944 in
review task `364f9b8c-5785-45d9-98ba-affb643d5b96`. Validation
`51419c4d-7b91-469f-85a7-7202e2be7699` is accepted; integration
`05e4d685b56d4cc68a7802dc65363e2e` published it at Library
`405ff58c5df69766419c9941161444531c1979ae`. Its full integrated report
was read and its files were checked against the frozen candidate.
Resume compilation `7604b1f9-fb19-4cd7-b564-8842a510de15` completed
with zero errors or warnings.

This is construction coverage. The source's equivalence conclusion still
requires publication of a proposition about one actual reverse functor
and both actual natural isomorphisms, followed by its exact proof.
The objectwise coordinate isomorphisms alone do not discharge that conclusion.

## Source map and remaining work

| Passage | Coverage and remaining obligation |
| --- | --- |
| A.II.1, printed p.250 / PDF256: natural transformations and natural isomorphisms | The criterion uses the actual Mathlib functor categories and natural isomorphisms. A separate assertion-level comparison for all A.II.1 content remains open. |
| A.II.2, printed p.251 / PDF257: quasi-inverse and fully faithful, essentially surjective sufficient criterion | The published statement and exact proof establish the criterion above, including the documented identity-subscript correction. |
| A.II.2, same page: vector-space example | Actual fixed-dimension category, full singleton coordinate category, inclusion and objectwise coordinate isomorphisms are published. Publication of the equivalence statement and its exact proof remain required. The example concerns one fixed dimension, rather than all finite-dimensional spaces together. |
| A.II.2, printed pp.250–251 / PDF256–257: general representative-subcategory discussion | Actual full representative subcategory, inclusion, representative isomorphisms, uniqueness law, quasi-inverse statement and exact proof are published as above. |
| Remaining A.I and A.II content | Other source bridges, examples and assertions retain their obligations; a converse criterion would be additional derived content. |

This focused audit makes no A.I, A.II, Appendix A or whole-book completion
declaration.
