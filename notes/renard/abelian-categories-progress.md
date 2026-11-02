# Renard A.VI.1–2: abelian axioms and basic categorical results

Author: Worker 709. Publication audit dated 1 November 2026.

This note maps the seven abelian-category axioms in A.VI.1 and the ten
numbered assertions in A.VI.2 to current Lean declarations. Seven mathematical
units below have verified independent acceptance and Library publication,
including the three-by-three proof. The subobject–quotient unit has a public
statement; its proof candidate remains nonpublic at the recorded check. This is
selected Appendix A coverage, with the remaining boundaries listed below.
The whole-book ledger is [coverage.md](coverage.md).

## Source and audit boundary

The governing source is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, Appendix A.VI.1–2,
printed pp.261–263 / one-based PDF267–269. The registered original is
`renard-2026-representations-groupes-reductifs-padiques`, retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
These three pages were read in full; the hash was checked. The numbered
results are asserted without displayed proofs. The Lean companions
describe the implemented Mathlib proofs and constructions.

The supplementary `renard-2010-corrections-complements`, retained at
`/home/taskhub/pilot/literature/Renard — Représentations des groupes réductifs p-adiques- corrections et compléments (2010 edition errata).pdf`,
SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was reread on PDF18–19. This bounded older-edition check does not replace
the 2026 reference. The separate
[Appendix A discrepancy audit](appendix-a-corrections.md) preserves the
full-subcategory counterexample and corrected sufficient hypotheses.

The six earlier published units were inspected against Library
`e3944f764d2c00d53ac87227e98601bb667f348f`. The three-by-three publication
was then verified in Library `a5dff2ff93bd3637a67ee8847f67f811efc82f01`;
all seven Lean/Markdown pairs match their frozen candidate hashes in that
Library. The status and receipt tables below describe this audit; this
documentation adds no Lean result.

## Seven axioms and the additive structure

In `Langlands.CategoryTheory.RenardAbelian`,
`Langlands.Renard.AbelianAxioms C` existentially packages zero-morphism
data and the source's seven conditions: a zero object, finite products,
finite coproducts, kernels, cokernels, normal monomorphisms and normal
epimorphisms. The last two express that every monomorphism is a kernel
and every epimorphism is a cokernel. No additive structure on the Hom
sets is an input.

The construction `AbelianAxioms.abelian` obtains an actual Mathlib
`Abelian C` structure through `NonPreadditiveAbelian`. Conversely,
`AbelianAxioms.ofAbelian` recovers the source axioms, and
`abelianAxioms_iff_nonempty_abelian` states
`AbelianAxioms C ↔ Nonempty (Abelian C)`. All names in this paragraph
have prefix `Langlands.Renard`.

This same published unit supplies A.VI.2(6):
`AbelianAxioms.homGroup` constructs the additive commutative group on
each actual Hom set, `homGroup_zero` identifies its zero with the
zero-object morphism, and `add_comp` and `comp_add` give the two
distributivity laws for composition.
[The companion](../../Langlands/CategoryTheory/RenardAbelian.md)
explains the zero-morphism compatibility and Mathlib construction route.

The category has independent object and Hom universes,
`C : Type u` with `Category.{v} C`. The remaining finite categorical
results below take an actual `[Abelian C]`; the preceding construction
connects this input with the seven source axioms. They impose no module,
coefficient-field, reductive-group or finite-length specialization.

## The ten assertions in A.VI.2

Unless a row gives another namespace, the declaration names below have
prefix `Langlands.Renard`. “Published proof” refers to the exact named
statement, with the evidence recorded in the next section.

| Source item | Exact interface and mathematical content | Verified scope |
| --- | --- | --- |
| (1) | `IsoIffMonoAndEpiStatement`: a morphism is an isomorphism iff it is both mono and epi. | Published as the first conjunct of `imageFactorizationStatement : ImageFactorizationStatement`. |
| (2–3) | `SubobjectQuotientAndLatticeStatement`: kernel–cokernel correspondence between subobjects and quotients, with the binary intersection and sum constructions. | Public statement in [RenardSubobjectQuotientStatements](../../Langlands/CategoryTheory/RenardSubobjectQuotientStatements.md); proof publication remains required. Quotients are represented by `Subobject (op X)` in the source quotient order; the anti-isomorphism uses the order dual. |
| (4) | `AbelianImageCoimageStatement`: the actual kernel of the cokernel is the image, and the actual cokernel of the kernel is the coimage, with their factor maps and universal properties. | Published second conjunct of `imageFactorizationStatement`, including compatibility with `Limits.image` and the invertible coimage–image comparison. |
| (5) | `EpiMonoFactorizationStatement`: existence of an epi–mono factorization, its unique compatible isomorphism, and the image/coimage universal properties of every such factorization. | Published third conjunct of `imageFactorizationStatement`. |
| (6) | Additive commutative Hom groups, their zero and bilinearity of composition. | Published `AbelianAxioms.homGroup`, `homGroup_zero`, `add_comp`, `comp_add`, as described above. |
| (7) | `ProductCoproductNaturalIsoStatement`: the canonical finite binary product–coproduct isomorphism and its naturality. | Published `productCoproductNaturalIso`, including both inverse laws, matrix entries, joint naturality and the curried natural isomorphism. [Companion](../../Langlands/CategoryTheory/RenardProductCoproduct.md). |
| (8) | `Langlands.CategoryTheory.RenardThreeByThreeBottomRowStatement`: construction of the missing bottom arrows in the source three-by-three diagram and the required exactness. | Published `Langlands.CategoryTheory.renardThreeByThreeBottomRowStatement_proof` in [RenardThreeByThreeProof](../../Langlands/CategoryTheory/RenardThreeByThreeProof.md). Both bottom arrows are absent in the original diagram and are conclusions of this target. |
| (9) | `NoetherIsomorphismsStatement`: nested quotients, the second isomorphism theorem and the complementary-subobject direct-sum consequence. | Published `noetherIsomorphisms`, covering all three clauses with the actual quotient projections and inclusions. [Companion](../../Langlands/CategoryTheory/RenardNoetherIsomorphisms.md). |
| (10) | `SourceCompletenessLimitsStatement`: source completeness gives all limits at the stated size, and source cocompleteness gives all colimits. | Published `sourceCompletenessLimits`. Diagram object and Hom sizes are `w`, independent of `u,v`; empty and disconnected diagrams are included. [Companion](../../Langlands/CategoryTheory/RenardCompletenessLimits.md). |

For (4), `ImageUniversalProperty` states the least-subobject factorization
property and `CoimageUniversalProperty` states its quotient counterpart,
each with the unique map and both compatibility equations. Thus the
published result retains the source's image and coimage meanings as well
as the actual Mathlib objects. The
[image-factorization proof companion](../../Langlands/CategoryTheory/Renard/ImageFactorization.md)
describes the implemented kernel/cokernel and uniqueness arguments.

For (9), the nested-quotient clause constructs the mono `B/A → X/A`
for `A ≤ B` and identifies its cokernel with `X/B` compatibly with the
projections from `X`. The second clause identifies
`B/(A ∩ B)` with `(A + B)/A`, compatibly with the map from `B`.
The third proves that the actual map `A ⊕ B → X` induced by the
inclusions is an isomorphism when the intersection is zero and the sum
is all of `X`. The statement module is
`Langlands.CategoryTheory.RenardNoetherIsomorphismStatements`
(singular “Isomorphism” in this module name).

## Source AB4, AB4*, AB5 and Grothendieck conventions

The published
[RenardGrothendieckAxioms pair](../../Langlands/CategoryTheory/RenardGrothendieckAxioms.md)
defines eight Prop-valued predicates with explicit family size `w`,
independent of the category's object and Hom sizes.

| Predicate, with prefix `Langlands.Renard` | Meaning retained from the source or identified as internal |
| --- | --- |
| `SourceAB4` | Existence of all `w`-indexed products, `HasProducts.{w} C`. |
| `SourceAB4Star` | Existence of all `w`-indexed coproducts, `HasCoproducts.{w} C`. |
| `IsSourceComplete` | `SourceAB4` in an abelian category. |
| `IsSourceCocomplete` | `SourceAB4Star` in an abelian category. |
| `DirectedSubobjectSumsDistribute` | For every nonempty directed `w`-indexed subobject family, its least upper bound exists and intersection with any subobject is the least upper bound of the intersections. |
| `SourceAB5` | Source cocompleteness together with that directed distributivity condition. |
| `IsSourceGrothendieck` | Exactly `SourceAB5`; the source definition has no generator clause. |
| `HasIndexedSubobjectSums` | Internal comparison condition asserting least upper bounds for every `w`-indexed subobject family, including the empty family. |

In particular, the source's AB4 and AB4* predicates assert product and
coproduct existence. They assert no exactness of those operations and
must retain their distinction from similarly named Mathlib exactness
classes. Likewise, `IsSourceGrothendieck` must retain its distinction
from definitions requiring a generator.

The proof of (10) uses these source existence predicates and Mathlib's
construction of general limits from products and equalizers, and dually
of colimits from coproducts and coequalizers. It assumes no connectedness,
filteredness or nonemptiness of the diagram category. The nonempty
directed-family restriction belongs to the AB5 subobject formula only.

The definition unit supplies these conventions, not proofs of AB5 in
arbitrary abelian categories or an equivalence with filtered-colimit
exactness. The infinitary subobject-sum consequence of cocompleteness
and comparisons with other AB5 formulations retain separate obligations.

## Independent acceptance and publication evidence

All seven units below were fetched as `accepted = true`, `public = true`
with integration state `published`. Their independent reviews were
approved without qualifications. The five proof receipts accept Lake
build, exact-target, unchanged-statement and frozen-input checks.
The other two are definition receipts; their construction review covers
the declarations described above.

| Unit and author | Candidate | Machine receipt | Independent review |
| --- | --- | --- | --- |
| Seven axioms and Hom addition; Worker 595 | `ef153d78-b932-400b-be63-70c40ef38029` | `937ee58d-11fe-494a-9137-49fc4b348441` | `9ecc9a87-faf3-4e75-bd85-757929f70ef5`, Reviewer 2973 |
| (1,4,5), image factorization; Worker 795 | `d70b2bfe-72ab-45dc-ae3f-846312ce1598` | `cb6b67b7-9a77-46d5-af5c-133dce884c3b` | `c6b4c954-9de2-47dc-b22e-beb024f24fe3`, Reviewer 3545 |
| (7), product–coproduct; Worker 794 | `47a0f4e4-0341-4f16-857e-bc3aca9c6f6b` | `709b9953-5d0d-4fa3-a8c9-38edf6abf450` | `0e792ceb-afc6-4dc3-a213-9a3485c4a929`, Reviewer 3542 |
| (9), Noether clauses; Worker 798 | `c2dc09d5-e172-44a1-b1bb-98de55f92df5` | `f9adc4e5-f665-45cf-9972-b5af04b48c14` | `c58fd7f5-2c30-4bdd-8de3-b22020d8518f`, Reviewer 3548 |
| Source AB predicates; Worker 713 | `3a3715a3-98e9-4296-89db-9e444de18217` | `b8564e22-9e20-4f64-b57e-6607360de831` | `5dc86a28-8549-45e9-bcdd-77bfc6cce5c4`, Reviewer 3097 |
| (10), limits and colimits; Worker 800 | `1ca15f76-aeab-41f7-85ca-7abefeff2570` | `dd281b63-24e3-4a57-b59a-45df07e9e58d` | `97aed342-12bc-4fdb-ad2e-e3f7a8416197`, Reviewer 3986 |
| (8), three-by-three; Worker 894 | `b9962438-fef0-4120-954c-5860c9e0fb09` | `633ab7a0-8667-49ff-9927-92af59c62dad` | `7f821824-a0e7-4ffb-bb59-84d470ffe464`, Reviewer 7814 |

| Unit | Publication integration | Published commit |
| --- | --- | --- |
| Seven axioms and Hom addition | `bbb76abebe1b486b821be3876c1e57d2` | `a74ef41f111ae26bf08f0c56914b60efa011d2a9` |
| Image factorization | `82fd025528fb4629b09c19e0053156fc` | `65f39f42712a45624ccc76ac5da7b60f52ebcd6f` |
| Product–coproduct | `f5c8687381b24a9bba6798919cdd1734` | `65f39f42712a45624ccc76ac5da7b60f52ebcd6f` |
| Noether clauses | `c285f416a38d459180e15a681311a36d` | `65f39f42712a45624ccc76ac5da7b60f52ebcd6f` |
| Source AB predicates | `a16af28821f846c29b05b2d4aec617a4` | `d82ec7582eecc70a116cb73c7d40f31827c4b023` |
| Limits and colimits | `39f4f61059d143ddb454099af005fa75` | `cb6a47b2390bdcd0be78fac0552b7fd5c46cd51b` |
| Three-by-three | `bc21ead2385543db89c3e9ad13610859` | `a5dff2ff93bd3637a67ee8847f67f811efc82f01` |

The public (2–3) statement is
`1c3a8a95-a5fc-4f51-b820-4ff9bef02f75`. Its exact-proof task is
`ec2f9f47-3627-4647-83ad-2d0976d52ccb`; Worker 840's proof candidate
`5a79258c-f051-4a5b-a15d-51446e2f847e` has accepted exact-target
machine validation `33ed8313-b8ff-4554-ac05-4153cd6a66f6` and
Reviewer 7851's independent approval
`eb188f2f-f773-42f9-9b81-ef8fc9c02228`. The direct check still
reports staged, `accepted = false`, `public = false`.

The public (8) statement is
`91ca9983-3181-4fe0-9e1c-8a07e370ba49`. Its exact-proof task is
`35cb9192-61c7-49e6-85d9-ae01c66ec282`; Worker 894's proof candidate
`b9962438-fef0-4120-954c-5860c9e0fb09` has accepted exact-target
machine validation `633ab7a0-8667-49ff-9927-92af59c62dad` and
Reviewer 7814's independent approval
`7f821824-a0e7-4ffb-bb59-84d470ffe464`. Its later direct check reports
`accepted = true`, `public = true` and integration state `published`, as
recorded in the tables. The proof constructs both bottom arrows through
cokernel universal properties and proves short exactness with Mathlib's
snake lemma. Only the (2–3) proof remains outside the published coverage
count here.

## Further source obligations

This audit leaves A.VI.1's module and sheaf examples, the corrected
full-subcategory criteria and their counterexample, and the adapter to
the source's original possibly-nonunital module category separate.
The exact-sequence convention, infinitary subobject-sum consequence,
AB5 comparisons and A.VI.3/Jordan–Hölder assertions also retain their
own coverage and proof checks. Their exclusion from this audit says
nothing about whether other tasks already cover them.

The corrected full-subcategory criterion must preserve finite-product
closure and zero containment; subobject and quotient closure alone
fail by the explicit dimension-at-most-one counterexample in the linked
discrepancy audit. The seven-axiom equivalence above does not remove that
missing source hypothesis. This note makes no Appendix A.VI, Appendix A
or whole-book completion declaration.
