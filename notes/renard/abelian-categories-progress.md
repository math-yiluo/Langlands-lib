# Renard A.VI.1–2: abelian axioms and basic categorical results

Seven-module audit dated 1 November 2026; sheaf and
presheaf prerequisite update dated 4 November 2026; proof, criterion and
sheaf updates dated 5 November 2026; module-example update dated
6 November 2026.

This note maps the seven abelian-category axioms in A.VI.1 and the ten
numbered assertions in A.VI.2 to current Lean declarations. Eight mathematical
modules below are in the Library,
including the three-by-three and subobject–quotient proofs. Every numbered
A.VI.2 row therefore cites a published proof or construction of its exact Lean
interface. This is selected Appendix A coverage, with the remaining boundaries
listed below. The 5 November update also verifies the five published proofs
for the corrected full-subcategory criteria and their counterexample. The
sheaf/presheaf section records ten published modules. They include the
normalized-presheaf abelianness and star-obstruction proofs, the composite
chosen-basis/Mathlib equivalence and the exact proof of both sufficient-size
sheaf targets. The 6 November update records four published modules for the
module part of the A.VI.1 example list. They prove abelianness of the
original category A−mod and of the nondegenerate subcategory, which gives
M(A) at a unital ring. The whole-book ledger is [coverage.md](coverage.md).

## Source and audit boundary

The governing source is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, Appendix A.VI.1–2,
printed pp.261–263 / one-based PDF267–269. The registered original is
`renard-2026-representations-groupes-reductifs-padiques`, retained at
`central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
These three pages were read in full; the hash was checked. The numbered
results are asserted without displayed proofs. The Lean companions
describe the implemented Mathlib proofs and constructions.

The supplementary `renard-2010-corrections-complements`, retained at
`literature/Renard — Représentations des groupes réductifs p-adiques- corrections et compléments (2010 edition errata).pdf`,
SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was reread on PDF18–19. This bounded older-edition check does not replace
the 2026 reference. The separate
[Appendix A discrepancy audit](appendix-a-corrections.md) preserves the
full-subcategory counterexample and corrected sufficient hypotheses.

The six earlier published modules were inspected against Library
`e3944f764d2c00d53ac87227e98601bb667f348f`. The three-by-three publication
was then verified in Library `a5dff2ff93bd3637a67ee8847f67f811efc82f01`;
all seven Lean/Markdown pairs match, in that Library, the hashes of the
versions checked. The 5 November additions were verified against Library
`a9f12d1e4a0823c676b8a7b9292f17ea7c1d08ee` and Library
`0d12b7d171600d15516e52ee508d3aaca3e9cf9e`, which leaves those pairs
unchanged. Each added A.VI.2 and criterion Lean/Markdown pair has the same
hashes in the version checked and in both Libraries; the
sheaf section records its own hash checks. The status tables
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

This same published module supplies A.VI.2(6):
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

The definition module supplies these conventions, not proofs of AB5 in
arbitrary abelian categories or an equivalence with filtered-colimit
exactness. The infinitary subobject-sum consequence of cocompleteness
and comparisons with other AB5 formulations retain separate obligations.

## In the Library

All eight modules below are in the Library. The six proofs were each checked
by a Lake build against the exact target, with the statement and its inputs
unchanged. The other two are definitions; their checks cover the
declarations described above.

| Module | First appeared at Library commit |
| --- | --- |
| Seven axioms and Hom addition | `a74ef41f111ae26bf08f0c56914b60efa011d2a9` |
| Image factorization | `65f39f42712a45624ccc76ac5da7b60f52ebcd6f` |
| Product–coproduct | `65f39f42712a45624ccc76ac5da7b60f52ebcd6f` |
| Noether clauses | `65f39f42712a45624ccc76ac5da7b60f52ebcd6f` |
| Source AB predicates | `d82ec7582eecc70a116cb73c7d40f31827c4b023` |
| Limits and colimits | `cb6a47b2390bdcd0be78fac0552b7fd5c46cd51b` |
| Three-by-three | `a5dff2ff93bd3637a67ee8847f67f811efc82f01` |
| Subobject–quotient | `4f2e1785a3faf187359b2dcec3c8bdbe4a70e762` |

The (2–3) statement and its proof are in the Library. The theorem
`Langlands.Renard.subobjectQuotientAndLatticeStatement` holds for every
`C : Type u` with `Category.{v} C` and `[Abelian C]`, adding no
well-poweredness, smallness or module hypothesis. The proof takes Mathlib's
order isomorphism `Abelian.subobjectIsoSubobjectOp X` between `Subobject X`
and the order dual of `Subobject (op X)`. Its inverse laws and `le_iff_le`
give the two inverse clauses and both order reversals. The two
representative formulas hold by definitional unfolding of `Subobject.lift`.
The binary laws are `le_inf_iff` and `sup_le_iff` for Mathlib's lattice on
`Subobject X`, built from pullbacks and from images of coproduct maps.

The (8) statement and its proof are in the Library, as recorded in the
table. The proof constructs both bottom arrows through
cokernel universal properties and proves short exactness with Mathlib's
snake lemma. With the (2–3) proof, every numbered A.VI.2 row has a proof of
its exact interface in the Library. This does not complete Appendix A.VI;
the obligations below remain.

## Further source obligations

The 1 November audit left A.VI.1's module example and the adapter to the
source's original possibly-nonunital module category separate. The module
example now has the published proofs recorded in the 6 November section
below. The embedding of the unital counterexample into the original category
remains separate. The sheaf example has the partial coverage recorded in its
section below. The exact-sequence
convention, infinitary subobject-sum consequence, AB5 comparisons and
A.VI.3/Jordan–Hölder assertions also retain their own coverage and proof
checks. Their exclusion from this audit says nothing about whether other
notes or modules already cover them.

The corrected full-subcategory criterion must preserve finite-product
closure and zero containment; subobject and quotient closure alone
fail by the explicit dimension-at-most-one counterexample in the linked
discrepancy audit. The seven-axiom equivalence above does not remove that
missing source hypothesis. The next section records the published proofs of
both corrected criteria and of the counterexample. This note does not
claim that Appendix A.VI, Appendix A or the whole book is complete.

## Corrected full-subcategory criteria and counterexample, 5 November 2026

The A.VI.1 sentence on printed p.261 / PDF267 says that every full
subcategory of A-mod closed under submodules and quotients is abelian. It
has no zero-object or finite-product hypothesis. The linked discrepancy audit
gives the dimension-at-most-one counterexample. The public statement
module
[AbelianSubcategoryStatement](../../Langlands/CategoryTheory/AbelianSubcategoryStatement.md)
states two strengthened sufficient criteria and three counterexample
targets. The Library has one exact proof for each target. All names have prefix
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

All five proofs are in the Library. Each was checked by a Lake build against
the exact target, with the statement and its inputs unchanged.

| Target | First appeared at Library commit |
| --- | --- |
| Kernel criterion | `aa1400a0eb858f7fdc607a5bb736d8f7a705fa10` |
| Subobject criterion | `aa1400a0eb858f7fdc607a5bb736d8f7a705fa10` |
| Closure | `aa1400a0eb858f7fdc607a5bb736d8f7a705fa10` |
| No product | `aa1400a0eb858f7fdc607a5bb736d8f7a705fa10` |
| Not abelian | `b1c8a5e809be36100da09da81385a7ca6789ae80` |

## A.VI.1 module examples, 6 November 2026

The example list on printed p.261 / PDF267 begins with the category
A−mod of left modules over a ring A. The next sentence presents M(A), the
unital left modules over a unital ring A, as a full subcategory of A−mod
closed under submodules and quotients. The source concludes that it is
abelian by the unrestricted criterion discussed above. Under the conventions
on printed pp.5–6 / PDF11–12, rings need not be unital and actions need not
satisfy a unit law. PDF267 was reread for this update. Four published
modules prove abelianness of both module categories. Names in this section have prefix `Langlands.Algebra`.

| Source item | Published statement and proof | Implemented route |
| --- | --- | --- |
| A−mod | [`NonUnitalModuleAmbientAbelianStatement`](../../Langlands/Algebra/NonUnitalModuleAmbientAbelianStatements.md), proved by [`nonUnitalModuleAmbientAbelianStatement`](../../Langlands/Algebra/NonUnitalModuleAmbientAbelianProof.md) with the named instance `NonUnitalModuleCat.abelian A` | For every `A : Type uA` with `NonUnitalRing A`, Mathlib's `abelianOfEquivalence` is applied to the published functor `IntegerUnitization.extendFunctor A`, with target `ModuleCat.{uM} (Unitization ℤ A)`. It transfers Mathlib's abelian structure to the original category. `NonUnitalModuleCat.abelian_toPreadditive` proves by `rfl` that the resulting Hom groups are the published pointwise `NonUnitalModuleCat.preadditive A`. |
| Nondegenerate subcategory | [`NondegenerateModuleAbelianStatement`](../../Langlands/Algebra/NondegenerateModuleAbelianStatements.md), proved by [`nondegenerateModuleAbelianStatement`](../../Langlands/Algebra/NondegenerateModuleAbelianProof.md) with the named data `NondegenerateModuleCat.abelian A hA` | For `hA : IsIdempotented A`, the published `nondegenerateModuleClosureStatement A hA` gives zero containment and closure of `nondegenerateProperty A` under ambient subobjects, quotients and finite products. Mathlib's instance in `Abelian/Subcategory.lean` then builds abelian data on the actual full subcategory, using the ambient instance. `NondegenerateModuleCat.abelian_toPreadditive` proves by `rfl` agreement with `Preadditive.fullSubcategory (nondegenerateProperty A)`. |

In all four modules the ring universe uA and carrier universe uM are
independent. The two proofs and the nondegenerate statement check both
unequal assignments `(0,1)` and `(1,0)` explicitly. The ambient category
admits zero rings, zero carriers and zero actions. No unit-action law, field,
nontriviality or finiteness hypothesis is added, and no abelian structure or
closure certificate is an input. The equalities of preadditive
structures matter because Mathlib's `Abelian` is data: existence alone would
not fix the Hom groups.

For a unital ring, two published lemmas specialise the second row. For every
`R : Type u` with `Ring R`, `IsIdempotented.of_ring R`, in
`Langlands/Algebra/IdempotentedRing.lean`, makes `R` idempotented with local
unit `1`. `isNondegenerate_iff_isUnitalModule`, in
`Langlands/Algebra/NonUnitalModule.lean`, proves
`IsNondegenerate R M ↔ IsUnitalModule R M` for every original module `M`.
The right side is the elementwise unit law `(1 : R) • m = m`. Hence the object
property of `NondegenerateModuleCat R` is pointwise equivalent to the unit law.
So `NondegenerateModuleCat.abelian R (IsIdempotented.of_ring R)` is abelian
data, with the inherited Hom groups, on the full subcategory of R−mod formed
by the unital modules. This is M(R) as the source describes it. This
specialisation is assembled here from published lemmas; no separate closed
theorem for unital rings is published. Mathlib's `ModuleCat R`, whose objects
carry a `Module R` structure, is a separate model of unital modules. Mathlib
makes it abelian by `ModuleCat.abelian`, and the A.VI.3 full-module targets
use that model. It is not literally a full subcategory of
`NonUnitalModuleCat R`. A search of Library
`26195cb4483eb6386dd05e2d230e7b8bf67af591` found no published equivalence
between it and `NondegenerateModuleCat R`.

The published proof does not use the source's unrestricted criterion. It
also proves zero containment and finite-product closure, the extra
hypotheses of the corrected criteria in the previous section, and then
applies Mathlib's instance directly. It does not invoke
`Langlands.CategoryTheory.abelianOfSubobjectsQuotientsFiniteProducts_proof`.
Both corrected criteria quantify over every abelian category, so the ambient
instance makes them applicable to full subcategories of
`NonUnitalModuleCat A`; no such instantiation is separately published. The
dimension-at-most-one counterexample remains in unital `ModuleCat K`.

The closure dependency is the published `nondegenerateModuleClosureStatement`
in `Langlands.Algebra.NondegenerateModuleClosureProof`; this update does
not audit its checks. The [I.5.2–I.6 module-category note](module-classes-category-properties.md)
records the same nondegenerate abelianness proof in its I.6 assertion map.
The A.VI.3 AB5 and AB6 assertions for these module examples are mapped in
the [A.VI.3 source map](jordan-holder-progress.md). Exactness of the inclusion
and of the nondegenerate-part functor, concrete kernel and cokernel formulas,
and scalar or tensor comparisons are outside this section.

All four modules below were checked on 6 November 2026 to be in the Library.
Each statement passed the statement checks: schema,
immutable content, reference integrity, exact-reference policy, Lake build and
declaration kind; this is not a proof. Each proof passed the proof
checks: a Lake build against the exact target, with the statement and its
inputs unchanged.

| Module | First appeared at Library commit |
| --- | --- |
| A−mod statement | `127ad790e7e947faeb397b6e2634daa0a46e344d` |
| A−mod proof | `ddcb24bcc9c4fe817800414f5fd5f3536da42760` |
| Nondegenerate statement | `7d8c1355c088b76a992b0af1690748d5ae7147b5` |
| Nondegenerate proof | `ddf3850e87ef10e9eabe230b50f772e4890d71bd` |

On 6 November 2026 the versions checked and Library
`26195cb4483eb6386dd05e2d230e7b8bf67af591` had the same
SHA256 for each file:

| Path under `Langlands/Algebra/` | SHA256 |
| --- | --- |
| `NonUnitalModuleAmbientAbelianStatements.lean` | `632de48a1f6b55a3cd3ca5218047f0bdef46fefde59aa868b8567e87f0931071` |
| `NonUnitalModuleAmbientAbelianStatements.md` | `c55d608bfc8f5e1e4295d06a3866ad7148452c48ce1f063b01e503cc3fcae71c` |
| `NonUnitalModuleAmbientAbelianProof.lean` | `dd143fb40b86880f732eb2be9cb8e21bd8070d718f9c43d701137292ac132cf9` |
| `NonUnitalModuleAmbientAbelianProof.md` | `fc508408259bcb822bf9ecce839478de3fb3820647a8d538c492f49a1738ce5e` |
| `NondegenerateModuleAbelianStatements.lean` | `3e411c8c8be7ffb6ae9d2512faead2b979535adb7ef32acb2e04f4035c5c53a1` |
| `NondegenerateModuleAbelianStatements.md` | `d3b29138e52a637624edd2b9f7a2c244d17da9d40dd90247f8dbf6f2ef5eb6ee` |
| `NondegenerateModuleAbelianProof.lean` | `a6646b07d9c9f0793b29f9522b99ee75a8fed91979df454f62257a7de0c004b9` |
| `NondegenerateModuleAbelianProof.md` | `1e6f169c99467cc79baffc6062b4755d63b1fbe23019e1f10e7ae4102e709209` |

## A.VI.1 sheaf and presheaf prerequisites, 4–5 November 2026

The example on printed p.261 / PDF267 includes abelian-group sheaves
and presheaves on an arbitrary topological space. That example and
the II.2.1 definitions on printed pp.33–34 / PDF39–40 were reread
for this branch. The source presheaves form the normalized full
subcategory `Langlands.Sheaf.Renard.Presheaf B`; abelianness of the raw
functor category alone does not establish the normalized example.
The four publications recorded on 4 November supply two constructions and
two statement pairs. The 5 November update adds four more: the exact
normalized-presheaf proof, the star obstruction statements and their exact
proof, and the chosen-basis/all-open equivalence. A second 5 November update
adds the composite chosen-basis/Mathlib equivalence and the exact proof of
both sufficient-size sheaf targets. What remains is
distinguished explicitly.

### The published all-open comparison

The Library constructs
`Langlands.Sheaf.Renard.AllOpenMathlib.equivalence.{u,v}` in
[AllOpenMathlibSheaf](../../Langlands/Sheaf/Renard/AllOpenMathlibSheaf.md):

```text
BasisSheaf.{u,v} (allOpenBasis X) ≌
  TopCat.Sheaf AddCommGrpCat.{v} (TopCat.of X).
```

This is an actual equivalence. It preserves independent space
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

The statement pair
[PresheafAbelianStatements](../../Langlands/Sheaf/Renard/PresheafAbelianStatements.md)
defines in
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

Both statements are proved in
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

The statement module
[SheafAbelianStatements](../../Langlands/Sheaf/Renard/SheafAbelianStatements.md)
is in the Library. Its two closed
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

The internal diagram is implemented in
[StarDiagram](../../Langlands/Sheaf/Renard/StarDiagram.md). All names here have prefix
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

The obstruction statements are in
[StarCokernelScopeStatements](../../Langlands/Sheaf/Renard/StarCokernelScopeStatements.md).
In the same
namespace, `CokernelSectionInjectionStatement.{u,v}` asserts, for every
`I : Type u`, every actual `c : CokernelCofork f` and `IsColimit c`, the
proposition `Nonempty (I ↪ Sections c.pt.obj.obj (whole I))`.
`UndersizedNoCokernelStatement.{v}` and `UndersizedNotAbelianStatement.{v}`
specialize to `I := Type v`, with space universe v+1 and section universe v.
They assert `¬ HasCokernel f` and the absence of any Mathlib abelian structure
on that actual category. `CokernelScopeStatements.{u,v}` conjoins the three
targets without outer premises. The module also proves `f_comp_gi_eq_zero`
and `sheafHomEquiv_zero_app` for the canonical pointwise zero morphisms.

The aggregate is proved as
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

### The 4 November prerequisites in the Library

The four modules of 4 November (the all-open equivalence, the
normalized-presheaf statements, the sufficient-size sheaf statements and the
star diagram) first appeared in the Library at commit
`50c05a5877c13ea23a52ea298c0ec2bd6fdb0817`. Their Lean/Markdown pairs, as
checked, match that commit and the audit base
`8b0bca33e42af34d78809e9fae6a20b0e296117c`.
Their checks are of the respective construction or statement; none is an
exact-proof check of an abelianness or obstruction target.

### The published chosen-basis/all-open equivalence

The Library constructs the actual equivalence in
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

### The 5 November additions in the Library

All four modules below are in the Library. The two proofs were each checked by
a Lake build against the exact target, with the statement and its inputs
unchanged. The statement and the definition were checked by a Lake build
and declaration-kind and reference checks. The first three Lean/Markdown
pairs, as checked, match
Library `a9f12d1e4a0823c676b8a7b9292f17ea7c1d08ee` and Library
`0d12b7d171600d15516e52ee508d3aaca3e9cf9e`. For the star
proof, the Markdown is identical in the version checked and in Library
`0d12b7d1`. The Lean file in the Library differs from the version checked only by
naming its local topology instance `starCokernelScopeTopology`.

| Module | First appeared at Library commit |
| --- | --- |
| Normalized-presheaf proof | `476a152fd90d846bcb20b9897f53829a768b822c` |
| Star obstruction statements | `476a152fd90d846bcb20b9897f53829a768b822c` |
| Chosen-basis equivalence | `409542525904dd50036abafdafb8ad1459eadade` |
| Star obstruction proof | `0d12b7d171600d15516e52ee508d3aaca3e9cf9e` |

### The published composite chosen-basis/Mathlib equivalence

The composite is implemented in
[BasisMathlibSheafEquivalence](../../Langlands/Sheaf/Renard/BasisMathlibSheafEquivalence.md):

```text
Langlands.Sheaf.Renard.BasisMathlib.equivalence.{u,v} B :
  BasisSheaf.{u,max u v} B ≌
    TopCat.Sheaf AddCommGrpCat.{max u v} (TopCat.of X).
```

It is the actual composition of `BasisAllOpen.equivalence.{u,v} B` with
`AllOpenMathlib.equivalence` at section universe `max u v`. The compatible-family core and all-open comparison are reused by Lean name.
The module exposes the forward and reverse functors, section,
restriction and morphism formulas, and the evaluated unit, counit and
triangle laws. No sheafification, abelianness or comparison certificate is
an input. It is classified as internal elaboration of the II.2.1
equivalence on printed p.37 / PDF43. It proves no abelianness statement.

### The published sufficient-size sheaf proof

Both targets are proved in
[SheafAbelianProof](../../Langlands/Sheaf/Renard/SheafAbelianProof.md).
The theorems `Langlands.Sheaf.Renard.basisSheafAbelianStatement` and
`basisSheafAbelianAxiomsStatement` have exactly the types
`BasisSheafAbelianStatement.{u,v}` and
`BasisSheafAbelianAxiomsStatement.{u,v}`. Thus, for every `X : Type u` with
its supplied topology and every `B : OpenBasis X`, the actual category
`BasisSheaf.{u,max u v} B` is abelian and satisfies the seven source axioms.

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

### The second 5 November update in the Library

Both modules below are in the Library, each after a fresh build of the
Library with it. Each Lean/Markdown pair, as checked, matches
Library `81bddf38b8069213a7ace261e56ea16dd84f3721`. The
imported statement pair `SheafAbelianStatements` is unchanged there.

| Module | First appeared at Library commit |
| --- | --- |
| Composite equivalence | `58c925cc173d944d4bb579be5c971ee1a5896d28` |
| Sheaf proof | `1831431f93603e52c73600a2a900dd42d7f18deb` |

The construction was checked by a Lake build and declaration-kind and
reference checks. The proof was checked by a Lake build against the exact
target `BasisSheafAbelianStatement`, with the statement and its inputs
unchanged; the second theorem was also checked against
`BasisSheafAbelianAxiomsStatement`.

### Remaining sheaf obligations

The sheaf and normalized-presheaf parts of the A.VI.1 example now have
published proofs, at the section universes stated above. The source example
is not thereby completed in every formal reading. Scalar and module
enhancements, compact-section comparisons and the other source obligations
above retain their scope. This note does not claim that Appendix A.VI is complete.
