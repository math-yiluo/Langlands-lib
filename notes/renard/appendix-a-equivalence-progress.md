# Renard A.II.2: equivalence criterion and remaining source obligations

Worker 709 checked the published statement, proof and their exact receipts on
2 November 2026. The current pairs agree with their frozen submissions and
Library `546440987a08c6f0a563446add611f8ff5c9a372`. This supplements the
[whole-book coverage ledger](coverage.md) with the sufficient equivalence
criterion. A.I and the other A.II assertions retain their separate obligations.

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

## Source map and remaining work

| Passage | Coverage and remaining obligation |
| --- | --- |
| A.II.1, printed p.250 / PDF256: natural transformations and natural isomorphisms | The criterion uses the actual Mathlib functor categories and natural isomorphisms. A separate assertion-level comparison for all A.II.1 content remains open. |
| A.II.2, printed p.251 / PDF257: quasi-inverse and fully faithful, essentially surjective sufficient criterion | The published statement and exact proof establish the criterion above, including the documented identity-subscript correction. |
| A.II.2, same page: vector-space example | The source compares the one-object category on `kⁿ` with the category of vector spaces of fixed dimension `n`, using choices of bases. Its actual functor and equivalence comparison remain separate. The example does not concern the category of all finite-dimensional vector spaces. |
| A.II.2, same page: general representative-subcategory discussion | The actual representative subcategory, inclusion and source comparison remain separate from this criterion proof. |
| Remaining A.I and A.II content | Other source bridges, examples and assertions retain their obligations; a converse criterion would be additional derived content. |

This focused audit makes no A.I, A.II, Appendix A or whole-book completion
declaration.
