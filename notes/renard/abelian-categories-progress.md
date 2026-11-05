# Renard A.VI.1–2: abelian axioms and basic categorical results

Author: Worker 709. Seven-unit audit dated 1 November 2026; sheaf and
presheaf prerequisite update dated 4 November 2026; proof, criterion and
sheaf updates dated 5 November 2026.

This note maps the seven abelian-category axioms in A.VI.1 and the ten
numbered assertions in A.VI.2 to current Lean declarations. Eight mathematical
units below have verified independent acceptance and Library publication,
including the three-by-three and subobject–quotient proofs. Every numbered
A.VI.2 row therefore cites a published proof or construction of its exact Lean
interface. This is selected Appendix A coverage, with the remaining boundaries
listed below. The 5 November update also verifies the five published proofs
for the corrected full-subcategory criteria and their counterexample. The
sheaf/presheaf section records ten published units. They include the
normalized-presheaf abelianness and star-obstruction proofs, the composite
chosen-basis/Mathlib equivalence and the exact proof of both sufficient-size
sheaf targets. The whole-book ledger is [coverage.md](coverage.md).

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
Library. The 5 November additions were verified against Library
`a9f12d1e4a0823c676b8a7b9292f17ea7c1d08ee` and the current Library
`0d12b7d171600d15516e52ee508d3aaca3e9cf9e`, which leaves those pairs
unchanged. Each added A.VI.2 and criterion Lean/Markdown pair has the same
hashes in its frozen candidate, both Libraries and the workspace; the
sheaf section records its own hash checks. The status and receipt tables
below describe these audits; this documentation adds no Lean result.

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
| (2–3) | `SubobjectQuotientAndLatticeStatement`: kernel–cokernel correspondence between subobjects and quotients, with the binary intersection and sum constructions. | Published `subobjectQuotientAndLatticeStatement` in [RenardSubobjectQuotientProof](../../Langlands/CategoryTheory/RenardSubobjectQuotientProof.md), proving the public statement in [RenardSubobjectQuotientStatements](../../Langlands/CategoryTheory/RenardSubobjectQuotientStatements.md). Quotients are represented by `Subobject (op X)` in the source quotient order; the anti-isomorphism uses the order dual. |
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

All eight units below were fetched as `accepted = true`, `public = true`
with integration state `published`. Their independent reviews were
approved without qualifications. The six proof receipts accept Lake
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
| (2–3), subobject–quotient; Worker 840 | `5a79258c-f051-4a5b-a15d-51446e2f847e` | `33ed8313-b8ff-4554-ac05-4153cd6a66f6` | `eb188f2f-f773-42f9-9b81-ef8fc9c02228`, Reviewer 7851 |

| Unit | Publication integration | Published commit |
| --- | --- | --- |
| Seven axioms and Hom addition | `bbb76abebe1b486b821be3876c1e57d2` | `a74ef41f111ae26bf08f0c56914b60efa011d2a9` |
| Image factorization | `82fd025528fb4629b09c19e0053156fc` | `65f39f42712a45624ccc76ac5da7b60f52ebcd6f` |
| Product–coproduct | `f5c8687381b24a9bba6798919cdd1734` | `65f39f42712a45624ccc76ac5da7b60f52ebcd6f` |
| Noether clauses | `c285f416a38d459180e15a681311a36d` | `65f39f42712a45624ccc76ac5da7b60f52ebcd6f` |
| Source AB predicates | `a16af28821f846c29b05b2d4aec617a4` | `d82ec7582eecc70a116cb73c7d40f31827c4b023` |
| Limits and colimits | `39f4f61059d143ddb454099af005fa75` | `cb6a47b2390bdcd0be78fac0552b7fd5c46cd51b` |
| Three-by-three | `bc21ead2385543db89c3e9ad13610859` | `a5dff2ff93bd3637a67ee8847f67f811efc82f01` |
| Subobject–quotient | `68ce2dd6455e47dea50ec8f1923474fc` | `4f2e1785a3faf187359b2dcec3c8bdbe4a70e762` |

The public (2–3) statement is
`1c3a8a95-a5fc-4f51-b820-4ff9bef02f75`. Its exact-proof task is
`ec2f9f47-3627-4647-83ad-2d0976d52ccb`. Worker 840's proof candidate
`5a79258c-f051-4a5b-a15d-51446e2f847e` was first recorded here as staged
and nonpublic. Its 5 November direct check reports `accepted = true`,
`public = true` and integration state `published`. The theorem
`Langlands.Renard.subobjectQuotientAndLatticeStatement` holds for every
`C : Type u` with `Category.{v} C` and `[Abelian C]`, adding no
well-poweredness, smallness or module hypothesis. The proof takes Mathlib's
order isomorphism `Abelian.subobjectIsoSubobjectOp X` between `Subobject X`
and the order dual of `Subobject (op X)`. Its inverse laws and `le_iff_le`
give the two inverse clauses and both order reversals. The two
representative formulas hold by definitional unfolding of `Subobject.lift`.
The binary laws are `le_inf_iff` and `sup_le_iff` for Mathlib's lattice on
`Subobject X`, built from pullbacks and from images of coproduct maps.

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
snake lemma. With the (2–3) publication, no numbered A.VI.2 row waits for
a proof of its exact interface. This is not an Appendix A.VI completion
claim; the obligations below remain.

## Further source obligations

This audit leaves A.VI.1's module example and the adapter to the source's
original possibly-nonunital module category separate. The sheaf example
has the partial coverage recorded in its section below. The exact-sequence
convention, infinitary subobject-sum consequence, AB5 comparisons and
A.VI.3/Jordan–Hölder assertions also retain their own coverage and proof
checks. Their exclusion from this audit says nothing about whether other
tasks already cover them.

The corrected full-subcategory criterion must preserve finite-product
closure and zero containment; subobject and quotient closure alone
fail by the explicit dimension-at-most-one counterexample in the linked
discrepancy audit. The seven-axiom equivalence above does not remove that
missing source hypothesis. The next section records the published proofs of
both corrected criteria and of the counterexample. This note makes no
Appendix A.VI, Appendix A or whole-book completion declaration.

## Corrected full-subcategory criteria and counterexample, 5 November 2026

The A.VI.1 sentence on printed p.261 / PDF267 says that every full
subcategory of A-mod closed under submodules and quotients is abelian. It
has no zero-object or finite-product hypothesis. The linked discrepancy audit
gives the dimension-at-most-one counterexample. Worker 633's public statement
module
[AbelianSubcategoryStatement](../../Langlands/CategoryTheory/AbelianSubcategoryStatement.md)
states two strengthened sufficient criteria and three counterexample
targets. Worker 894 published one exact proof for each target under task
`514d7109-dfe5-46d8-a712-30d5879691f0`. All names have prefix
`Langlands.CategoryTheory`.

| Target | Published theorem and implemented route |
| --- | --- |
| `AbelianOfKernelsCokernelsFiniteProducts C P` | [`abelianOfKernelsCokernelsFiniteProducts_proof`](../../Langlands/CategoryTheory/AbelianSubcategoryKernelsProof.md): for every abelian `C : Type u` with `Category.{v} C` and every `P : ObjectProperty C`, zero containment and closure under kernels, cokernels and finite products give `Nonempty (Abelian P.FullSubcategory)`. Mathlib's instance in `Abelian/Subcategory.lean` supplies the structure. |
| `AbelianOfSubobjectsQuotientsFiniteProducts C P` | [`abelianOfSubobjectsQuotientsFiniteProducts_proof`](../../Langlands/CategoryTheory/AbelianSubcategorySubobjectsProof.md): the same conclusion from zero containment, closure under all ambient subobjects and quotients, and finite-product closure. Mathlib's `ObjectProperty/Kernels.lean` instances derive kernel and cokernel closure from the monic kernel and epic cokernel legs. |
| `DimensionLEOneClosedUnderSubobjectsQuotients K` | [`dimensionLEOneClosedUnderSubobjectsQuotients_proof`](../../Langlands/CategoryTheory/DimensionLEOneClosureProof.md): for every field `K : Type u`, the property `FiniteDimensional K V ∧ Module.finrank K V ≤ 1` on `ModuleCat.{u} K` contains a zero object and is closed under every ambient monomorphism and epimorphism. |
| `DimensionLEOneLineHasNoBinaryProduct K` | [`dimensionLEOneLineHasNoBinaryProduct_proof`](../../Langlands/CategoryTheory/DimensionLEOneNoProductProof.md): the actual line has no binary product with itself in that full subcategory. The universal property makes the two projections jointly surjective onto `K × K`, contradicting dimension at most one. |
| `DimensionLEOneNotAbelian K` | [`dimensionLEOneNotAbelian_proof`](../../Langlands/CategoryTheory/DimensionLEOneNotAbelianProof.md): an assumed Mathlib abelian structure supplies finite products in the fixed induced category, which the no-product theorem refutes. |

The two criteria are sufficient corrections derived from Mathlib, not
verbatim assertions of Renard and not claimed to be necessary. Together with
the closure theorem, the last two theorems show that the finite-product
hypothesis cannot be dropped. They are internal derived content, following the
discrepancy audit. The counterexample uses unital `ModuleCat.{u} K` with
module carriers in the field's universe. Its embedding into the source's
possibly-nonunital module category remains a separate adapter obligation.

All five candidates were fetched as `accepted = true` and `public = true`,
with unqualified independent approvals. Each proof receipt accepts Lake build,
exact-target, unchanged-statement and frozen-input checks.

| Target / candidate | Machine receipt | Independent reviewer / review task | Integration / commit |
| --- | --- | --- | --- |
| Kernel criterion / `d43d5feb-0758-4e8d-9d98-23369e0dc49a` | `7b8f133e-6ecb-4a9b-97cb-329ec4c4692a` | Reviewer 7965 / `636d8ddb-68d9-44a0-98d4-d56785030d7b` | `b0ae6e8898ba488e89934fafdc9e8cd6` / `aa1400a0eb858f7fdc607a5bb736d8f7a705fa10` |
| Subobject criterion / `be88fa6f-cb10-4a4c-b90a-65beaa5c4b61` | `f57f930c-deee-41cc-9a51-11ac3d6fffeb` | Reviewer 7967 / `068f7dd8-afac-4694-8886-6064cf00ded1` | `de42de5e1989491a86308a8349d87b2b` / `aa1400a0eb858f7fdc607a5bb736d8f7a705fa10` |
| Closure / `e3ddcc90-248a-40f1-a22b-04850a8c8212` | `276b7aaa-8cde-4a88-882a-e3f12fd0e05e` | Reviewer 7969 / `e951ebb0-5963-4da4-8665-07a9fce5e34c` | `fd31216c0d0d424d93f1b3b1b6ad74ca` / `aa1400a0eb858f7fdc607a5bb736d8f7a705fa10` |
| No product / `44ecd2b1-5bc1-46e0-bf3f-09c99f0631ad` | `70251bff-0466-4ec7-b966-6c1b31f03f01` | Reviewer 7970 / `d526d8e7-1ddd-4484-ae1e-b12de34aa327` | `e842db00a2b6482cb56d6d59e02fa1f7` / `aa1400a0eb858f7fdc607a5bb736d8f7a705fa10` |
| Not abelian / `62422faf-3a99-4605-988a-8f7a2c0d89d8` | `050878a3-0fe9-483d-91c0-f958439cb56d` | Reviewer 8025 / `544cd493-933b-4c32-bebe-b2fd43153ddb` | `abff13684723447aa9f931542045b597` / `b1c8a5e809be36100da09da81385a7ca6789ae80` |

## A.VI.1 sheaf and presheaf prerequisites, 4–5 November 2026

The example on printed p.261 / PDF267 includes abelian-group sheaves
and presheaves on an arbitrary topological space. Worker 709 reread
that example and the II.2.1 definitions on printed pp.33–34 / PDF39–40
for this branch. The source presheaves form the normalized full
subcategory `Langlands.Sheaf.Renard.Presheaf B`; abelianness of the raw
functor category alone does not establish the normalized example.
The four publications recorded on 4 November supply two constructions and
two statement pairs. The 5 November update adds four more: the exact
normalized-presheaf proof, the star obstruction statements and their exact
proof, and the chosen-basis/all-open equivalence. A second 5 November update
adds the composite chosen-basis/Mathlib equivalence and the exact proof of
both sufficient-size sheaf targets. The remaining successors are
distinguished explicitly.

### The published all-open comparison

Worker 1594, with Worker 709's source audit and universe-safe comparison
route, constructed
`Langlands.Sheaf.Renard.AllOpenMathlib.equivalence.{u,v}` in
[AllOpenMathlibSheaf](../../Langlands/Sheaf/Renard/AllOpenMathlibSheaf.md):

```text
BasisSheaf.{u,v} (allOpenBasis X) ≌
  TopCat.Sheaf AddCommGrpCat.{v} (TopCat.of X).
```

This is the actual equivalence requested by definition task
`81f01a25-7878-4134-9ca4-d903603c3c18`. It preserves independent space
and original section universes, the actual groups, restrictions and
natural transformations. The two functors precompose with the published
`LocallyConstantScalar.allOpenFunctor` and `basisInclusion`. The source's
literal overlap-compatibility and unique-gluing condition is equivalent
to the actual Mathlib site condition. The implemented proof passes through
the underlying type-valued presheaf and preservation and reflection of
existing limits; it requires neither sheafification nor existence of all
limits at the space's size. Normalization follows from empty-cover gluing.
The actual unit and counit act as identity on original sections, with
naturality, inverse and triangle laws. Arbitrary independently indexed
covers and empty cases are included.

This construction proves a category comparison. It supplies no abelianness
result. Transporting abelianness from Mathlib must still discharge the
precise sheafification and section-size premises. The published arbitrary
chosen-basis comparison is recorded below.

### The published normalized-presheaf statements

Worker 1595's statement pair
[PresheafAbelianStatements](../../Langlands/Sheaf/Renard/PresheafAbelianStatements.md),
from task `ca7e40d3-9cbe-44c4-8b09-74139d6edb9e`, defines in
`Langlands.Sheaf.Renard`:

| Proposition at independent universes u and v | Exact body |
| --- | --- |
| `PresheafAbelianStatement.{u,v} B` | `Nonempty (CategoryTheory.Abelian (Presheaf.{u,v} B))` |
| `PresheafAbelianAxiomsStatement.{u,v} B` | `Langlands.Renard.AbelianAxioms (Presheaf.{u,v} B)` |

The supplied topology and basis are arbitrary. The full subcategory keeps
the actual original section groups, restrictions and natural transformations.
It requires trivial sections on each empty basis open, with a vacuous
condition if the basis omits that open. No abelianness, normalization
closure, sheafification, size relation or extra topological property is a
premise. The existing `abelianAxioms_iff_nonempty_abelian` relates the two
bodies; no parallel axiom package is introduced.

### The published normalized-presheaf proof

Worker 1595 also proved both statements under exact-proof task
`2e405776-930f-43f8-a41f-5634b85df700`, in
[PresheafAbelianProof](../../Langlands/Sheaf/Renard/PresheafAbelianProof.md).
The theorems `Langlands.Sheaf.Renard.presheafAbelianStatement B` and
`presheafAbelianAxiomsStatement B` hold for every `X : Type u` with its
supplied topology and every `B : OpenBasis X`, at the original independent
section universe v. They add no size, sheafification or topological premise.

The proof shows that the empty-value normalization property of the raw
functor category contains a zero object and is closed under subobjects,
quotients and finite products. These four instances are
`isNormalized_containsZero`, `isNormalized_isClosedUnderSubobjects`,
`isNormalized_isClosedUnderQuotients` and
`isNormalized_isClosedUnderFiniteProducts`. Each argument evaluates on an
empty basis open: a mono into, or an epi out of, a zero group has zero
source or target, and a limit of zero groups is zero. Mathlib's
`Abelian/Subcategory.lean` instance then gives the `presheafAbelian`
instance on the unchanged full subcategory. The source-axiom form follows
from `abelianAxioms_iff_nonempty_abelian`. This proves the normalized-presheaf
part of the example at the stated generality; the sheaf part below remains
separate.

### The published sufficient-size sheaf statements

Worker 1153, with Worker 709's source and size design, published
[SheafAbelianStatements](../../Langlands/Sheaf/Renard/SheafAbelianStatements.md)
under task `1c102f4c-05fd-423b-bb6b-1b58d5bbb28e`. Its two closed
Prop-valued definitions are
`Langlands.Sheaf.Renard.BasisSheafAbelianStatement.{u,v}` and
`BasisSheafAbelianAxiomsStatement.{u,v}`. Each universally quantifies
`X : Type u`, its supplied topology and `B : OpenBasis X`; the conclusions
are respectively existence of `CategoryTheory.Abelian` data and the
existing source `AbelianAxioms` on `BasisSheaf.{u,max u v} B`.

The actual normalized section functors, literal sheaf condition and natural
transformations are retained. Neither target assumes sheafification,
abelianness, closure under categorical operations, a category comparison
or any extra topology or cover-size condition. Empty spaces and bases
omitting the empty open remain included.

The independent parameters are u and v; section carriers explicitly lie
in `Type (max u v)`. This is a sufficient general section size, with no
necessity claim for each space or basis. It is internal formalization data,
rather than a printed hypothesis or an error attributed to Renard. These
statements make no unrestricted assertion about `BasisSheaf.{u,v} B`.

Both targets now have the published exact proof recorded below, which
transports Mathlib's abelian sheaf category along the published composite
equivalence.

### The published star-space diagram, obstruction statements and proof

Worker 1301 implemented Worker 709's internal diagram in
[StarDiagram](../../Langlands/Sheaf/Renard/StarDiagram.md), under task
`b0105955-9a21-492e-b97d-62fbc7fb4718`. All names here have prefix
`Langlands.Sheaf.Renard.StarDiagram`. For `I : Type u`, `topology I`
on `Option I` has opens the empty set and the sets containing `none`.
The actual `F`, `G` and `Ti i` are objects of
`BasisSheaf.{u,v} (allOpenBasis (Option I))`, at independent section
universe v. `F` and `G` have lifted integer coefficients on nonempty
opens. `F` doubles restriction from a leaf-containing open to `{none}`;
`G` has identity restrictions there. `Ti i` is the lifted `ZMod 2`
skyscraper at `some i`.

The actual map `f : F ⟶ G` doubles on leaf-containing opens and is the
identity on `{none}`; `gi i : G ⟶ Ti i` reduces coefficients modulo two.
The module proves restrictions, normalization, arbitrary-cover gluing,
functor and naturality laws, injectivity of every component of `f`, and
zero components of `f ≫ gi i`. All constructions include empty I and
impose no relation between u and v. These are published intrinsic laws
of an actual diagram, without a hypothetical cokernel premise.

Worker 1599 published the obstruction statements in
[StarCokernelScopeStatements](../../Langlands/Sheaf/Renard/StarCokernelScopeStatements.md),
under statement task `6416418d-565b-498f-951f-bc24c29350be`. In the same
namespace, `CokernelSectionInjectionStatement.{u,v}` asserts, for every
`I : Type u`, every actual `c : CokernelCofork f` and `IsColimit c`, the
proposition `Nonempty (I ↪ Sections c.pt.obj.obj (whole I))`.
`UndersizedNoCokernelStatement.{v}` and `UndersizedNotAbelianStatement.{v}`
specialize to `I := Type v`, with space universe v+1 and section universe v.
They assert `¬ HasCokernel f` and the absence of any Mathlib abelian structure
on that actual category. `CokernelScopeStatements.{u,v}` conjoins the three
targets without outer premises. The module also proves `f_comp_gi_eq_zero`
and `sheafHomEquiv_zero_app` for the canonical pointwise zero morphisms.

Worker 1038 proved the aggregate under exact-proof task
`bf7c2dbf-867c-41be-8001-917a5201699f`, as
`cokernelScopeStatements` in
[StarCokernelScopeProof](../../Langlands/Sheaf/Renard/StarCokernelScopeProof.md).
For each leaf, the proof glues the `c.π`-image of integer one on that leaf's
open with zero on the other members of `starCover`, using the literal
basis-sheaf gluing in the supplied vertex. Compatibility holds because
`c.π` vanishes on every leafless open, where `f` is the identity. The
factorizations of the mod-two maps `gi i` through the colimit separate these
global sections, giving the injection; empty I gives the empty function. For
`I := Type v`, a cokernel would make `Type v` small in `Type v`, contradicting
`not_small_type`. An abelian structure supplies such a cokernel after
transport along the unique `HasZeroMorphisms` structure.

The diagram and the proved obstructions are internal derived content,
motivated by A.VI.1 and using the II.2.1 interfaces. They are not printed
in Renard and attribute no error to the book. The negative results concern
only this star specialization and make no necessity claim for other spaces.
They are independent of the positive sufficient-size sheaf target, whose
section universe `max u v` is at least v+1 here, and of normalized-presheaf
abelianness.

### Publication evidence for the 4 November prerequisites

All four candidates below were independently accepted, with unqualified
reviews, and published at commit
`50c05a5877c13ea23a52ea298c0ec2bd6fdb0817`. The complete independent
and integrated reports were read and their common fields agree. Their
frozen Lean/Markdown pairs match the publication tree, the then-current audit
base `8b0bca33e42af34d78809e9fae6a20b0e296117c` and workspace.
The machine receipts check the respective construction or statement;
none is an exact-proof receipt for an abelianness or obstruction target.

| Unit / author | Candidate | Machine receipt | Independent reviewer / review task |
| --- | --- | --- | --- |
| All-open equivalence; Worker 1594 with Worker 709 | `c98d755f-bead-4f25-ba97-f23c47cf0f6f` | `f2eab6bd-6a2f-49cf-a40f-08c6ea66fb30` | Reviewer 13116 / `01a6bc46-a643-4726-bebf-f60de0f35173` |
| Normalized-presheaf statements; Worker 1595 | `e3f15ef9-1314-4309-93ec-18a66c3f2cb8` | `aa81c658-6458-45d0-9862-9415d12759c7` | Reviewer 13156 / `f9e502d6-7090-474b-9fe6-dabe6c57c633` |
| Sufficient-size sheaf statements; Worker 1153 with Worker 709 | `6bcb8bd5-5def-4c64-8b29-d15b33dfa582` | `bbd315df-79d4-4597-8684-07049c27771c` | Reviewer 13169 / `dd9fce49-d4ac-47e2-8e26-a76602bcfd1c` |
| Star diagram; Worker 1301 with Worker 709 | `735eb5b6-796d-4903-93b2-0da307653ee2` | `4d9b8254-c9f2-4482-9367-54621ecb8017` | Reviewer 13194 / `e7d7ec9a-c9c9-4677-b212-9b6826442ac5` |

| Unit | Publication integration |
| --- | --- |
| All-open equivalence | `4f9f9c8cc9504d8888d578d43ab8e50d` |
| Normalized-presheaf statements | `044ae79e39424ff09f6eccaa1e9b1fc3` |
| Sufficient-size sheaf statements | `e83f21ac0a2a4542a4196e9eabfbfb56` |
| Star diagram | `038a5b2f73c54616be27b96067127219` |

### The published chosen-basis/all-open equivalence

Worker 1594 constructed, under task `bbc1d9a5-4933-4677-b7ae-0184c69a2087`,
the actual equivalence in
[BasisAllOpenEquivalence](../../Langlands/Sheaf/Renard/BasisAllOpenEquivalence.md):

```text
Langlands.Sheaf.Renard.BasisAllOpen.equivalence.{u,v} B :
  BasisSheaf.{u,max u v} B ≌ BasisSheaf.{u,max u v} (allOpenBasis X).
```

Its source assertion is the final paragraph of II.2.1, printed p.37 / PDF43.
The functor `extension B` sends a chosen-basis sheaf to compatible families
of its original sections over the basis opens inside each open. Its inverse
is the existing `sheafBasisRestriction B`. The theorem `unique_basis_glue`
gives gluing for covers indexed in any universe w, and
`extension_familySheafCondition` gives the literal all-open sheaf condition.
`extension_isNormalized` and `extension_empty_zero` give normalization. The
actual `unitIso` and `counitIso` compare original sections, and
`extension_unit_counit` proves the triangle law. The section universe
`max u v` is explicit internal size data; the construction makes no
arbitrary original-v extension claim. It is a category comparison and
supplies no abelianness proof.

### Publication evidence for the 5 November additions

All four candidates below were fetched as `accepted = true` and
`public = true`, with unqualified independent approvals. The two proof
receipts accept Lake build, exact-target, unchanged-statement and
frozen-input checks. The statement and definition receipts accept Lake
build, declaration-kind and reference checks. For all four, the complete
independent and integrated reports were read and their common fields agree.
The first three frozen Lean/Markdown pairs match
Library `a9f12d1e4a0823c676b8a7b9292f17ea7c1d08ee`, the current Library
`0d12b7d171600d15516e52ee508d3aaca3e9cf9e` and the workspace. For the star
proof, the Markdown is identical in the frozen candidate, the current Library
and the workspace. The integrated Lean differs from the frozen file only by
naming its local topology instance `starCokernelScopeTopology`.

| Unit / author | Candidate | Machine receipt | Independent reviewer / review task |
| --- | --- | --- | --- |
| Normalized-presheaf proof; Worker 1595 | `c1d386ea-5845-4a90-b766-3da562ad37e4` | `f1f161a9-f16e-4213-81b2-b0a901dd9199` (proof) | Reviewer 13653 / `453c7fa5-3cd5-404c-b417-dc7c8b111020` |
| Star obstruction statements; Worker 1599 | `0d3adc37-e086-4c4a-b569-e83d1282d667` | `76baa571-0b8f-405c-9f6d-1e3be386c9e5` (statement) | Reviewer 13644 / `deb1b086-ec40-44b5-a519-33af6c6e1795` |
| Chosen-basis equivalence; Worker 1594 | `c4c1f560-2c7c-498b-a9c1-f0f6c90be179` | `2c954800-7111-494b-a5d6-084d514c0fd7` (construction) | Reviewer 13709 / `1a9d4783-99ca-4f8e-8825-5a26c44e88ad` |
| Star obstruction proof; Worker 1038 | `41193286-b04a-41c4-b04d-64fd170019f7` | `11f35e42-a745-42e0-8704-e504f1a69a1c` (proof) | Reviewer 13892 / `f89c03fa-9eed-4596-8b5d-1186f3c6e4fb` |

| Unit | Publication integration | Published commit |
| --- | --- | --- |
| Normalized-presheaf proof | `76b0201730aa47019a2c4d974ca8dd7a` | `476a152fd90d846bcb20b9897f53829a768b822c` |
| Star obstruction statements | `4acdd83262b74f17aec044eebb32ddc4` | `476a152fd90d846bcb20b9897f53829a768b822c` |
| Chosen-basis equivalence | `18073be37831463f8bbda68fa0abea60` | `409542525904dd50036abafdafb8ad1459eadade` |
| Star obstruction proof | `607828dba9f44bcb9d2cea546e4c0e85` | `0d12b7d171600d15516e52ee508d3aaca3e9cf9e` |

### The published composite chosen-basis/Mathlib equivalence

Worker 1153 implemented, under task `bbc1d9a5-4933-4677-b7ae-0184c69a2087`,
the composite in
[BasisMathlibSheafEquivalence](../../Langlands/Sheaf/Renard/BasisMathlibSheafEquivalence.md):

```text
Langlands.Sheaf.Renard.BasisMathlib.equivalence.{u,v} B :
  BasisSheaf.{u,max u v} B ≌
    TopCat.Sheaf AddCommGrpCat.{max u v} (TopCat.of X).
```

It is the actual composition of `BasisAllOpen.equivalence.{u,v} B` with
`AllOpenMathlib.equivalence` at section universe `max u v`. Worker 1594's
compatible-family core and all-open comparison are reused by Lean name;
Worker 709 supplied the task specification, source audit and universe
design. The module exposes the forward and reverse functors, section,
restriction and morphism formulas, and the evaluated unit, counit and
triangle laws. No sheafification, abelianness or comparison certificate is
an input. The record classifies it as internal elaboration of the II.2.1
equivalence on printed p.37 / PDF43. It proves no abelianness statement.

### The published sufficient-size sheaf proof

Worker 1153, with Worker 709's proof draft, source audit and universe
argument, proved both targets under exact-proof task
`ad6365e1-89a5-47a3-8a7c-eede875029c7`, in
[SheafAbelianProof](../../Langlands/Sheaf/Renard/SheafAbelianProof.md).
The theorems `Langlands.Sheaf.Renard.basisSheafAbelianStatement` and
`basisSheafAbelianAxiomsStatement` have exactly the types
`BasisSheafAbelianStatement.{u,v}` and
`BasisSheafAbelianAxiomsStatement.{u,v}`. Thus, for every `X : Type u` with
its supplied topology and every `B : OpenBasis X`, the actual category
`BasisSheaf.{u,max u v} B` is abelian and satisfies the seven source axioms.
The task is completed.

The implemented route has four steps.

1. A local instance restricts Mathlib's preservation of filtered colimits by
   the forgetful functor of `AddCommGrpCat.{max u v}` to index size u, by
   `preservesFilteredColimitsOfSize_shrink`. With this instance, Mathlib's
   concrete sheafification supplies `HasSheafify` for the opens of
   `TopCat.of X`, and its sheaf instances make
   `TopCat.Sheaf AddCommGrpCat.{max u v} (TopCat.of X)` abelian.
2. Finite products on the basis-sheaf category come from
   `Adjunction.hasLimitsOfShape_of_equivalence` applied to the forward functor
   of `BasisMathlib.equivalence.{u,v} B`.
3. `abelianOfEquivalence` along that functor gives the definition
   `basisSheafAbelian`. It keeps the existing componentwise preadditive
   structure of the full subcategory and is not a global instance.
4. The source-axiom form follows from the reverse direction of
   `abelianAxioms_iff_nonempty_abelian`.

This transport proof is internal derived content; Renard lists the example
without a proof. The proof assumes no relation between u and v, and no
nonemptiness, separation, compactness or total disconnectedness. Its axiom
report lists only `propext`, `Classical.choice` and `Quot.sound`. The section
universe `max u v` is the sufficient size fixed by the statements. The proof
says nothing about the original-value category `BasisSheaf.{u,v} B` and makes
no necessity claim for `max u v`. By the star obstruction above, the
original-value category is not abelian for the star space on `Type v` at
section universe v.

### Publication evidence for the second 5 November update

Both candidates below were checked as published, with unqualified
independent approvals. The complete independent and integrated reports were
read; their twelve common fields agree, and each integration ran a fresh
integrated build. Each frozen Lean/Markdown pair matches the current
Library `81bddf38b8069213a7ace261e56ea16dd84f3721` and the workspace. The
imported statement pair `SheafAbelianStatements` is unchanged there.

| Unit / author | Candidate | Machine receipt | Independent reviewer / review task |
| --- | --- | --- | --- |
| Composite equivalence; Worker 1153 | `bf448972-6482-4d38-8d60-881a356302b2` | `06222e5d-a5d0-4580-af84-16d57e100b13` (construction) | Reviewer 13898 / `e7006c65-77ef-41fc-8ea8-4c6e2b431d15` |
| Sheaf proof; Worker 1153 with Worker 709 | `c6d6b19b-fc7c-4172-9a52-c87cb24faeff` | `bad6a19c-2e96-47f6-aa6d-e008b67eef2f` (proof) | Reviewer 14378 / `f8900262-fec4-487d-ade5-a6ad0329adb0` |

| Unit | Publication integration | Published commit |
| --- | --- | --- |
| Composite equivalence | `ec7cd0be30054ac3af39d9403361704e` | `58c925cc173d944d4bb579be5c971ee1a5896d28` |
| Sheaf proof | `93778c6dfcc94184bb1efcb13740a870` | `1831431f93603e52c73600a2a900dd42d7f18deb` |

The construction receipt accepts Lake build, declaration-kind and reference
checks. The proof receipt accepts Lake build, exact-target,
unchanged-statement and frozen-input checks against
`BasisSheafAbelianStatement`. The reviewer also checked the second theorem
against `BasisSheafAbelianAxiomsStatement`.

### Remaining sheaf obligations

The sheaf and normalized-presheaf parts of the A.VI.1 example now have
published proofs, at the section universes stated above. The source example
is not thereby completed in every formal reading. Scalar and module
enhancements, compact-section comparisons and the other source obligations
above retain their scope. No Appendix A.VI completion is declared.
