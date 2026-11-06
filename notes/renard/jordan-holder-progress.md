# Renard A.VI.3: Jordan–Hölder, length and simple subquotients

Worker 709 checked this passage and the twelve publications below on
4 November 2026 for whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857` revision 3. The abstract
Jordan–Hölder theorem, numerical length, simple-quotient proposition and
three simple-subquotient identities have published implementations.
On 5 November 2026 Worker 709 added the published statement targets for
the module-category examples and, later that day, their published exact
proof. On 6 November 2026, against Library
`d2fd0b68e11e9844d5da3650e7579d62588fd3fd`, Worker 709 added the
published standalone simple-cokernel criterion, a derived internal
bridge, with its statement and proof receipts. This note does not declare
A.VI or the whole-book task complete.

## Source and assertion map

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
A.VI.3 occupies printed pp.263–264 / one-based PDF269–270.
Worker 709 read both pages, including the AB6 footnote, proposition,
lemma and proofs, and inspected the rendered second page.
The preceding A.VI.2 assertions have their separate
[abelian-category source map](abelian-categories-progress.md).

All short declaration names below are in `Langlands.Renard`.
Module links point to the paired Markdown; each has a same-stem Lean file.

| Source assertion and locator | Declaration and module | Coverage and conventions |
| --- | --- | --- |
| Simple object and `Irr`, printed263/PDF269 | `IsSimpleObject`, `simpleClasses`, `ObjectClass`, `objectClass` in [CompositionChains](../../Langlands/CategoryTheory/Renard/CompositionChains.md) | Actual object isomorphism classes; simplicity is nonzero with only bottom and top subobjects, proved equivalent to Mathlib `Simple` |
| Composition chain, factors and chain length, printed263/PDF269 | `CompositionChain`, its `inclusion`, `factor`, `factorClass`, `length` in the same module | A strictly increasing `Fin (n + 1)` family from bottom to top, with simple actual cokernels indexed by `Fin n` |
| Jordan–Hölder theorem, printed263/PDF269 | `JordanHolderStatement` in [JordanHolderStatements](../../Langlands/CategoryTheory/Renard/JordanHolderStatements.md), proved by `jordanHolder` in [JordanHolder](../../Langlands/CategoryTheory/Renard/JordanHolder.md) | Equal chain lengths and an equivalence of factor indices giving actual factor isomorphisms; multiplicities are retained |
| Derived internal bridge, not separately printed: a quotient of subobjects is simple iff it is a cover, motivated by A.VI.2(9) and A.VI.3, printed263/PDF269 | `SubobjectSimpleCokernelStatement` in [SubobjectSimpleCokernelStatements](../../Langlands/CategoryTheory/Renard/SubobjectSimpleCokernelStatements.md), proved by `subobjectSimpleCokernelStatement` in [SubobjectSimpleCokernel](../../Langlands/CategoryTheory/Renard/SubobjectSimpleCokernel.md) | Every abelian category and every inclusion `A ≤ B`, including `A = B`; no source assertion is formalized by it. See the standalone-criterion section below |
| Finite length and length of an object, printed263/PDF269 | `HasCompositionChainOfLength`, `IsFiniteLength` in CompositionChains; `compositionLength` in [FiniteLength](../../Langlands/CategoryTheory/Renard/FiniteLength.md) | Numerical length requires an explicit finite-length witness and equals the length of every composition chain |
| Additional Grothendieck and AB6 assumptions and footnote, printed263/PDF269 | `IsSourceGrothendieck` in [RenardGrothendieckAxioms](../../Langlands/CategoryTheory/RenardGrothendieckAxioms.md); `IsLocallyFiniteTypeObject`, `IsLocallyFiniteTypeCategory`, `SourceAB6` in [LocallyFiniteType](../../Langlands/CategoryTheory/Renard/LocallyFiniteType.md) | Separate assumptions: source-sized coproducts and directed distribution; every object is a sum of finite-type subobjects. AB6 means local finite type, as the footnote specifies |
| Module-category examples, printed264/PDF270 | Six targets and their conjunction `FullModuleAxiomsStatement` in namespace `Langlands.Algebra.RenardFullModuleAxiomStatements`, module [RenardFullModuleAxiomStatements](../../Langlands/Algebra/RenardFullModuleAxiomStatements.md), proved by `fullModuleAxioms` in namespace `Langlands.Algebra.RenardFullModuleAxiomProof`, module [RenardFullModuleAxiomProof](../../Langlands/Algebra/RenardFullModuleAxiomProof.md) | Directed distributivity, source AB5 and canonical AB6 for the full `NonUnitalModuleCat` and Mathlib's `ModuleCat`, with no added hypothesis. Products are not among the targets. The proof does not use the I.6 nondegenerate-module proofs; see below |
| Zorn reminder, choice equivalence and bibliography references, printed264/PDF270 | Foundational reuse of `Mathlib.Order.Zorn` in the proposition proof | Expository foundations; no separate formalization of the set-theoretic equivalence with choice is claimed |
| Proposition (i): nonzero finite type implies simple quotient; (ii): non-finite type implies a simple subquotient, printed264/PDF270 | `SimpleQuotientPropositionStatement` and its two components in [SimpleQuotientStatements](../../Langlands/CategoryTheory/Renard/SimpleQuotientStatements.md), proved by `simpleQuotientProposition`, `finiteTypeSimpleQuotient`, `nonFiniteTypeSimpleSubquotient` in [SimpleQuotient](../../Langlands/CategoryTheory/Renard/SimpleQuotient.md) | Both source antecedents remain in the targets; quotients are actual cokernels of proper or strictly nested subobjects |
| `JH(X)`, printed264/PDF270 | `simpleSubquotientClasses` in CompositionChains | A set of isomorphism classes of simple actual `B/A`, using nested subobjects and their cokernels; no finite-length premise |
| Lemma (i): `JH(X) = JH(P) ∪ JH(X/P)`, printed264/PDF270 | `SimpleSubquotientSubobjectQuotientStatement`, proved by `simpleSubquotientSubobjectQuotient` in [SimpleSubquotientSubobjectQuotient](../../Langlands/CategoryTheory/Renard/SimpleSubquotientSubobjectQuotient.md) | Every actual subobject `P`; quotient is `cokernel P.arrow` |
| Lemma (ii): empty `JH` iff zero, printed264/PDF270 | `SimpleSubquotientEmptyStatement`, proved by `simpleSubquotientEmpty` in [SimpleSubquotientEmpty](../../Langlands/CategoryTheory/Renard/SimpleSubquotientEmpty.md) | Categorical `IsZero`; both source antecedents retained |
| Lemma (iii): `JH(∑ Fᵢ) = ⋃ᵢ JH(Fᵢ)`, printed264/PDF270 | `SimpleSubquotientSumStatement`, proved by `simpleSubquotientSum` in [SimpleSubquotientSum](../../Langlands/CategoryTheory/Renard/SimpleSubquotientSum.md) | Every family at the stated source size, including the empty family; actual subobject sum |

The last three proposition definitions and their conjunction
`SimpleSubquotientIdentitiesStatement` are in
[SimpleSubquotientIdentitiesStatements](../../Langlands/CategoryTheory/Renard/SimpleSubquotientIdentitiesStatements.md).
The theorem `simpleSubquotientIdentities` in
[SimpleSubquotientIdentitiesProofs](../../Langlands/CategoryTheory/Renard/SimpleSubquotientIdentitiesProofs.md)
assembles the three published component proofs.

The source's displayed factor range includes an index zero although its
factor is written `Bᵢ/Bᵢ₋₁`. The implementation uses exactly `n` adjacent
factors, `Bᵢ₊₁/Bᵢ` for `i : Fin n`, correcting this indexing typo.
The chain theorem preserves repeated isomorphism classes through its
index equivalence. The later set `simpleSubquotientClasses X`, like the
source's `JH(X)`, records membership rather than multiplicity.

## Hypotheses, sizes and numerical length

The pure Jordan–Hölder theorem requires only `C : Type u`,
`Category.{v} C` and `Abelian C`, with independent object and Hom
universes. It precedes the source's additional hypotheses and does not
assume source Grothendieck, AB6, a generator, a chosen lattice certificate,
or finite length of every object.

`ObjectClass C` lies in `Type u`; the actual `Subobject X` lies in
`Type (max u v)`. Numerical length is
`compositionLength X (hX : IsFiniteLength X) : ℕ`, defined by choosing
a length for which a composition chain exists. Jordan–Hölder proves
that it equals every such length. The module also proves existence of
a chain of the chosen length, the corresponding iff, independence of
the witness `hX`, and length zero iff `IsZero X`. This construction
does not assign a natural-number length to an arbitrary object.
No length-additivity or multiset theorem is claimed here.

For the later proposition and lemma the independent family universe is
`w`. Each exported component retains
`IsSourceGrothendieck.{w} C → SourceAB6 C → …`.
Source Grothendieck means `w`-indexed coproducts together with
distribution of intersection over nonempty directed subobject sums.
It has no generator clause and is not identified with Mathlib's
`IsGrothendieckAbelian`.

Canonical `SourceAB6 C` says that top is the least upper bound of
all actual finite-type subobjects of every object. The finite-type
predicate is the published `IsFiniteTypeObject`: existence of subobject
unions together with the nonempty proper-chain condition, as explained
in the [A.I.3 source map](noetherian-finite-type-progress.md).
The sized AB6 comparison implies the canonical condition at any
covering-family size; the converse and equivalence are proved at
`max u v`. No shrinking to arbitrary `w` is asserted. These are
Renard's local-finite-type conventions, distinct from Tohoku AB6.

The sum identity obtains `HasCoproducts.{w} C` from the supplied source
Grothendieck hypothesis inside its statement. For any `I : Type w`,
`subobjectSum F` is the actual image of the map from the coproduct of
the subobjects into `X`, as constructed in
[IndexedSubobjectSums](../../Langlands/CategoryTheory/Renard/IndexedSubobjectSums.md).
There is no nonemptiness or finite-length premise on this family or
its summands.

## Implemented proof routes and source references

The Jordan–Hölder proof first identifies simplicity of an actual
subobject quotient with the cover relation, by its own public theorem
`simple_cokernel_ofLE_iff_covBy` in the JordanHolder module. It constructs the
`JordanHolderLattice` structure on the actual subobject order using
the published second-isomorphism theorem, converts composition chains
to Mathlib composition series, and applies
`CompositionSeries.jordan_holder`. Interval isomorphisms are then
interpreted as isomorphisms of the actual cokernel factors. This
supplies the categorical comparison needed for reuse of the order
theorem rather than assuming that comparison.

The simple-quotient proof follows the source's Zorn route. Its stronger
internal finite-type result needs only a nonzero finite-type object.
It applies `zorn_le₀` to proper subobjects: bottom handles the empty
chain, and finite type ensures that the least upper bound of a
nonempty chain remains proper. The maximal subobject has simple
cokernel by the quotient/cover criterion, here the JordanHolder
module's `simple_cokernel_ofLE_iff_covBy`. For the second clause,
canonical AB6 yields a nonzero finite-type subobject; the first
clause supplies its simple quotient, which is transported to a
quotient of two actual nested subobjects of the original object.
The exported source targets retain both standing assumptions.

For lemma (i), the implementation gives simple subquotients actual
mono/epi presentations using kernels and coimages. It transports
these through monomorphisms and lifts them through epimorphisms by
pullback. Splitting according to whether the induced map to a simple
target is zero yields the two directions of the union identity.
The internal argument needs only an abelian category; the exported
statement preserves the source context.

For (ii), absence of simple subquotients rules out the non-finite-type
case by the proposition's second clause, and then rules out nonzero
finite type by its first clause. The reverse direction uses the
subobjects of a zero object and the zero cokernel of an identity.

For (iii), binary sums follow from (i) and the actual quotient
epimorphism; finite induction includes the empty sum using (ii).
Finite partial sums are indexed by `Finset I`, still at universe `w`,
and form a directed family. The final directed step uses source AB5.
Its kernel and least-upper-bound vanishing argument finds a nonzero
restriction to an intersection, hence an epimorphism to the simple
target. This replaces the printed intersection calculation while
proving the same identity.

Renard refers the Zorn reminder to bibliography [36], Serge Lang,
*Algebra*, Graduate Texts in Mathematics 211, third edition (2002),
and [25], Régine Douady and Adrien Douady,
*Algèbre et théories galoisiennes. 2*, CEDIC (1979).
These identifications were checked in Renard's bibliography on
printed282/PDF288; this note does not claim to have read those books.
The reminder of Zorn's lemma and its equivalence with choice is
classified as explanatory foundational material. The Lean development
reuses Mathlib's Zorn theorem under its existing foundations and does
not supply a separate set-theoretic equivalence proof.

The separately registered older-edition supplement,
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was checked on PDF18–19. Its correction to the old page305 replaces
increasing sequences by chains in this Zorn argument. The governing
2026 PDF270 already uses chains, and so does the implementation.
The older supplement does not govern the present numbering.
The [Appendix A discrepancy note](appendix-a-corrections.md) was also
consulted; its other corrections are not changes to this passage.

## Verified publication evidence and attribution

All twelve rows below were fetched and checked as accepted, public
and published, with independent approval and no unresolved review or
acceptance qualifications. Three records contain author scope notes
that their independent reviews explicitly accepted:

- CompositionChains (`6e1e8a59-ed83-4cb8-bb10-2d6d8f787518`) records
  the factor-index repair, deferral of numerical object length,
  retention of the `StrictMono` chain field, and the generalization
  of `ObjectClass`, `objectClass` and their laws to any category.
- JordanHolderStatements (`b24d6312-33b2-4fed-876b-c18b1b960840`)
  records statement-only status, the same indexing repair, and the
  explicit equal-length conjunct alongside the factor-index equivalence.
- The JordanHolder proof (`c98afe4a-4a86-4227-bdf7-7842ec45658e`)
  records that the quotient/cover criterion is proved internally,
  independently of its then-unpublished statement task, and that the
  proof uses Mathlib's order theorem with the public second-isomorphism
  theorem instead of transcribing the source's argument.

These accepted author notes describe the scope and implementation;
empty review qualifications do not mean that the author records
contain none. Numerical object length was subsequently supplied by
the separate FiniteLength publication below. The frozen Lean/Markdown pair hashes
matched both the workspace and Library
`6d810cf8b71c5da9cf2722e850d66305665461f5` on 4 November 2026.
The tables retain the exact publication commits and machine-receipt
IDs so that these historical checks can be reproduced.

Definition and statement receipts include successful Lake compilation
and declaration checks. They are not proof-policy acceptance.

| Unit and authors | Candidate; machine receipt | Independent review task / reviewer | Published commit |
| --- | --- | --- | --- |
| CompositionChains — Worker 221 | `6e1e8a59-ed83-4cb8-bb10-2d6d8f787518`; `a0b8a386-14df-41c0-b894-e47c3e97f9d6` | `b3e1ba89-8c9c-42cb-a5a0-47d02dd58044` / Reviewer 3138 | `4bc9613163fd74b82bed79403a0abfa2617a007d` |
| LocallyFiniteType — Workers 6 and 827 | `142180c4-ac17-42cd-b4ad-34d0897660cb`; `f49ccab6-c9df-4a8f-94da-9d051479ae4a` | `409772b0-4da3-482a-a323-feeeeea3353c` / Reviewer 3605 | `06ce3701c57321e39772a06c6c0202f3644c6cb7` |
| JordanHolderStatements — Workers 6 and 817 | `b24d6312-33b2-4fed-876b-c18b1b960840`; `941b4c17-d4bb-4cf6-aaaf-20a815a4cb50` | `1fefca02-67c0-4b4a-aa45-1269c5379701` / Reviewer 3553 | `65f39f42712a45624ccc76ac5da7b60f52ebcd6f` |
| FiniteLength — Worker 709 | `6e5bfcc4-1641-4f8c-af92-bae700314c8b`; `98865457-b7a1-4fab-8a69-8de9e5c9e746` | `7e3275af-75b5-4b9f-b982-efbf13af45fa` / Reviewer 7945 | `aa1400a0eb858f7fdc607a5bb736d8f7a705fa10` |
| SimpleQuotientStatements — Workers 6 and 961 | `679f4e91-0ef1-42e3-9b5a-6b2c3ee7267f`; `011e6e34-63eb-44ac-b545-441fd2e2f219` | `c9947910-d3c5-4fa6-900d-23b8fcfdb5cf` / Reviewer 4080 | `cb6a47b2390bdcd0be78fac0552b7fd5c46cd51b` |
| SimpleSubquotientIdentitiesStatements — Workers 6 and 973 | `584d0ecf-8d3e-4b20-b84b-a58fd01bfc08`; `d826cb4f-140f-4d5c-b191-ff145800100b` | `4061ae8a-d987-4aa0-8c81-8aaa839b06ad` / Reviewer 4084 | `355c05239d7704a3ed5d72bad864cb1d542b647a` |

Each proof receipt below separately passed `lake-build`, `exact-target`,
`unchanged-statement` and `frozen-inputs`, with `proof_accepted: true`
under `lean.proof@1`. Publication also has fresh integrated compilation;
that compilation alone is not semantic or exact-target acceptance.

| Proof and authors | Candidate; machine receipt | Independent review task / reviewer | Published commit |
| --- | --- | --- | --- |
| `jordanHolder` — Workers 6 and 817 | `c98afe4a-4a86-4227-bdf7-7842ec45658e`; `54910545-b2b6-48e4-9f03-cd5ca9348d8c` | `c19901b7-6248-4b0c-aade-0e9c145e231a` / Reviewer 3951 | `b0ef093b63d0f0c27bb690dca12820c991756955` |
| `simpleQuotientProposition` — Workers 6 and 961 | `22fed831-0241-434b-95f1-53c5f40461bd`; `7c4faeb0-09ff-4f65-b0ff-e53b5feab5eb` | `3e760c07-826b-48e9-b1c4-b2cf3106e7a5` / Reviewer 4215 | `b7a6ea71635c439ae131d5b451e5f403e32dc1c7` |
| `simpleSubquotientSubobjectQuotient` — Worker 695 | `c671e5e1-2df2-485a-b995-6b833a7737ca`; `96377037-8b0d-4c92-ab41-3de239e61380` | `fd494add-4b16-4270-acf7-4e436e5a73a3` / Reviewer 4316 | `e9af3dd7a1cfc9067fc8f95bcbbf34ce2e3dae30` |
| `simpleSubquotientEmpty` — Worker 595 | `fc7f7445-9810-4d00-98d3-f9f07fd59fd5`; `cd9f9355-47a2-4935-9cd4-2a14f4d997db` | `8e1e32a1-14f3-4ca4-a5b7-a5eef46c2e82` / Reviewer 4303 | `e9af3dd7a1cfc9067fc8f95bcbbf34ce2e3dae30` |
| `simpleSubquotientSum` — Workers 695 and 595 | `5fa7aaac-5222-4445-9448-df93eeef8ba3`; `eebc7723-a772-484b-8a1b-fc82d7186bcd` | `deec0ab5-3e25-4fb6-a027-05c3c7f50320` / Reviewer 4503 | `3987c3d7445531c2c7f784464a3fd47061ba0865` |
| `simpleSubquotientIdentities` — Worker 973 | `ced75ec3-dd57-4fc6-9d72-f52adf9d9b09`; `9aa91e98-a6fa-4d4c-8f89-3869600f19f5` | `3724cc00-b276-442e-a2f9-920f488b9f01` / Reviewer 4557 | `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |

Worker 6 prepared the local-finite-type draft and the simple-quotient
proof draft; Workers 827 and 961 respectively checked and completed
those units. Worker 695 implemented the sum proof and Worker 595
contributed source and mathematical checking. The final identities
aggregate reuses the component authors' proofs. This note's compilation
checks and source audit do not substitute for those independent
reviews or create additional proof publications.

## Standalone simple-cokernel criterion

The statement module
[SubobjectSimpleCokernelStatements](../../Langlands/CategoryTheory/Renard/SubobjectSimpleCokernelStatements.md)
defines

```lean
def SubobjectSimpleCokernelStatement (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  ∀ (X : C) (A B : Subobject X) (h : A ≤ B),
    Simple (cokernel (Subobject.ofLE A B h)) ↔ A ⋖ B
```

Here `Subobject.ofLE A B h` is Mathlib's actual monomorphism between the
underlying objects of `A` and `B`. Its cokernel is the actual quotient
`B/A`. `Simple` is Mathlib's simplicity, and `A ⋖ B` is Mathlib's
`CovBy` in the order of subobjects of `X`. The object and Hom universes
are independent. Every inclusion is quantified, including `A = B`; there
the quotient is zero and both sides are false. No Grothendieck, AB6,
well-poweredness, smallness, module, finiteness or `JordanHolderLattice`
premise is added.

The book does not state this equivalence. On printed263/PDF269 it
defines simple objects and composition series by simple successive
quotients, and refers the Jordan–Hölder proof to the Noether
isomorphisms of A.VI.2(9). The statement Markdown classifies the
criterion as a derived internal bridge from that categorical formulation
to order covers. Worker 709 reread the extracted text of PDF269 on
6 November 2026 and found this reading accurate.

The theorem `subobjectSimpleCokernelStatement` in
[SubobjectSimpleCokernel](../../Langlands/CategoryTheory/Renard/SubobjectSimpleCokernel.md)
proves the exact statement at the same universe parameters, with no
further hypothesis. Its proof is a direct categorical argument with three
auxiliary theorems:

- `isZero_cokernel_ofLE_iff`: the quotient is zero exactly when `A = B`.
  A zero cokernel makes the inclusion an epimorphism, hence an
  isomorphism, so `B ≤ A`. Conversely, the cokernel of the identity is zero.
- `covBy_of_simple_cokernel`: let `A ≤ D ≤ B`. If the composite
  `D ⟶ B ⟶ B/A` is zero, then `D` factors through the kernel `A`
  (`Abelian.monoLift`), so `D = A`. Otherwise it is a nonzero map to a
  simple object, hence an epimorphism. Then `D ⟶ B` is an epimorphism,
  and `D = B`.
- `simple_cokernel_of_covBy`: pull a nonzero monomorphism
  `m : Y ⟶ B/A` back along the quotient map. This gives an actual
  subobject `D` with `A ≤ D ≤ B`. If `D = A`, then `m = 0`. If `D = B`, then
  the quotient map factors through `m`, so `m` is an epimorphism and
  hence an isomorphism.

The earlier JordanHolder proof already proves the same equivalence as its
own public theorem `simple_cokernel_ofLE_iff_covBy`, with the category
and object implicit. As its author note records, this was done
independently of the then-unpublished statement task. The simple-quotient
proof uses that JordanHolder theorem. Neither of those publications imports
the standalone unit, and the standalone unit changes neither.

The standalone direction theorems are used elsewhere. The published
smooth-representation finiteness proof
`Langlands.SmoothRep.renardFinitenessStatement`, in
[RenardFinitenessProof](../../Langlands/Representation/Category/RenardFinitenessProof.md),
uses `covBy_of_simple_cokernel` and `simple_cokernel_of_covBy` to move
composition chains to Mathlib composition series. That chapter-level
result is not audited in this appendix note. The criterion itself does not
prove Jordan–Hölder or numerical length, and does not translate
composition chains; the units above supply those.

| Unit and authors | Candidate; machine receipt | Independent review task / reviewer | Integration; published commit |
| --- | --- | --- | --- |
| `SubobjectSimpleCokernelStatement` — Workers 695 and 6 | `4561f0f4-5872-481e-944a-7fa7a8cb7084`; `27b37c93-5850-4f95-bd1d-e6d5750459d7` | `ff744d49-a6ee-46f4-b2ab-f8c42fa182aa` / Reviewer 3939 | `86e4bd69755e4756940254ffa9ecd829`; `4021bb1d1ec99e65990e08addda3ade7caa73058` |
| `subobjectSimpleCokernelStatement` — Worker 994 | `313b179e-b214-4c27-91ce-d3717a517199`; `183d0a6f-1a3d-4f60-ad82-9d2ca26a34a1` | `872dbec7-6397-4d77-b81b-7a906178b925` / Reviewer 4071 | `c77f5d8162b84c569790cae8ac5107f8`; `cb6a47b2390bdcd0be78fac0552b7fd5c46cd51b` |

The statement was produced under statement task
`9b76e64f-e22c-4678-9970-85e180ecbab2`. Its `lean.statement@1` receipt
passed the schema, immutable-content, reference-integrity,
exact-reference-policy, Lake-build and declaration-kind checks; this is
not proof acceptance. The proof was produced under proof task
`de159c27-9311-41b4-b61e-22acee4e5ac5`. Its `lean.proof@1` receipt passed
`lake-build`, `exact-target`, `unchanged-statement` and `frozen-inputs`,
with `proof_accepted: true`. Both independent reviews approved without
qualifications, and neither frozen record contains author
qualifications. Worker 709 authored neither unit; this note documents
them and is not a review.

On 6 November 2026 the frozen bundles, Libraries
`d2fd0b68e11e9844d5da3650e7579d62588fd3fd` and
`87e695f5180726de47820341b89accb81c4e1033`, and the workspace had
the same SHA256 for each file:

| Path under `Langlands/CategoryTheory/Renard/` | SHA256 |
| --- | --- |
| `SubobjectSimpleCokernelStatements.lean` | `0ccd2d4a1ee359c5786818985986646a97ffa37db6d25204c59ef02573439532` |
| `SubobjectSimpleCokernelStatements.md` | `b64b78e11d7d2324ab0125d1bc8343da0314264186f415481552c7d1fbdbcae7` |
| `SubobjectSimpleCokernel.lean` | `31d41775d2210ad957dd63f662fb60e1a84be146c4c08512f8cd596f2122ca81` |
| `SubobjectSimpleCokernel.md` | `ed7c347b6ad3eab74edc097c126fa3e08c4e7074f5ace5ea125af93c245e12e9` |

## Module examples

On printed264/PDF270 the source asserts all these axioms for `A-mod`
with a possibly nonunital ring `A`, and for `M(A)` with a unital ring
`A`. In context, "tous ces axiomes" are the assumptions A.VI.3 has
just imposed on PDF269: a Grothendieck category, hence `AB4∗` and
`AB5`, and in addition `AB6`.
The original-action convention and the category selected in each
case must be preserved in any comparison.

The [I.5.2–I.6 module-category note](module-classes-category-properties.md)
records published source AB5, local-finite-type and completeness
results for `NondegenerateModuleCat` under an idempotented-ring
hypothesis. The inspected targets
`NondegenerateModuleAB5Statements.SourceAB5Statement` and
`NondegenerateModuleLocallyFiniteTypeStatements.SourceAB6Statement`,
in namespace `Langlands.Algebra`, use that category and hypothesis.
Their explicit carrier and index sizes also remain part of the
comparison. They do not directly supply the full possibly nonunital
`A-mod` example or the unital example without an actual adapter.

The [original-action categorical progress note](category-module-progress.md)
records the integer-unitization equivalence, actual categorical
subobject correspondence and finiteness comparisons. The inspected
`Langlands.Algebra.NonUnitalModuleCat.abelian` uses
`abelianOfEquivalence (IntegerUnitization.extendFunctor A)` for
arbitrary nonunital `A` and independent carrier universe. This is
ambient abelianness; it does not by itself establish the source
coproduct, directed-distribution and local-finite-type assertions.
These prerequisite publications are not additional rows in the
twelve-unit verification above.

### Published example targets

On 5 November 2026 Worker 709 checked that the exact example targets
are public. The statement unit
[RenardFullModuleAxiomStatements](../../Langlands/Algebra/RenardFullModuleAxiomStatements.md),
by Worker 1571, defines six closed Prop-valued targets in namespace
`Langlands.Algebra.RenardFullModuleAxiomStatements`:

- `NonUnitalDirectedSubobjectDistributivityStatement`,
  `NonUnitalSourceAB5Statement` and `NonUnitalSourceAB6Statement`, for
  `Langlands.Algebra.NonUnitalModuleCat A` over every `A` with
  `NonUnitalRing A`, with the selected instance
  `NonUnitalModuleCat.abelian`;
- `UnitalDirectedSubobjectDistributivityStatement`,
  `UnitalSourceAB5Statement` and `UnitalSourceAB6Statement`, for Mathlib's
  `ModuleCat A` over every `A` with `Ring A`, with `ModuleCat.abelian`.

`FullModuleAxiomsStatement.{uA, uI, uM}` is their right-associated
conjunction, in that order. The targets apply the unchanged predicates
`DirectedSubobjectSumsDistribute.{uI}`, `SourceAB5.{uI}` and `SourceAB6`
from the table above. Directed distributivity and AB6 keep carrier
universe `uM`. Source AB5 uses carrier `max uI uM` to accommodate its
`uI`-indexed coproducts. The coefficient universe `uA` stays independent.

The nonunital category is the full original additive-action category. A
unit of `A`, if there is one, need not act as the identity, and zero
actions are included. No nontriviality, commutativity, idempotentedness
or nondegeneracy hypothesis is added. Two lemmas proved by `Iff.rfl`
expose the definitional source Grothendieck reading of the AB5 targets.
The statement Markdown classifies the explicit universe bounds and the
separate distributivity targets as foundational elaborations of the
source example. The unit is statement-only: its acceptance and
publication prove none of the six targets.

| Unit and author | Candidate; machine receipt | Independent review task / reviewer | Published commit |
| --- | --- | --- | --- |
| RenardFullModuleAxiomStatements — Worker 1571 | `4fdf05cc-69c5-4caa-bcb2-a3e0143186f8`; `c5a81347-da1e-4c8f-95e4-8cf0b6d681f6` | `7249196f-febe-4bfe-aa98-97c0009d63ab` / Reviewer 13098 | `50c05a5877c13ea23a52ea298c0ec2bd6fdb0817` |

The review approved the unit without qualifications, and the frozen
record has no author qualifications. The pair was produced under
statement task `78a22f3d-e959-43d3-8799-6b78dd36a4f5`, which Worker 709
published. That contract leaves the proofs to separate successor tasks.
The frozen Lean/Markdown hashes `7f096c35…` and `931e0c82…` match
Library `83773f62c5adf54634640cbfaf89822a74b44700`.

### The example proof

The theorem `fullModuleAxioms` in namespace
`Langlands.Algebra.RenardFullModuleAxiomProof`, module
[RenardFullModuleAxiomProof](../../Langlands/Algebra/RenardFullModuleAxiomProof.md),
proves the unchanged aggregate `FullModuleAxiomsStatement.{uA, uI, uM}`
at the same level parameters. It adds no hypothesis to any of the six
components. Like the statement, it makes no claim about products (AB4)
or Mathlib's `AB5OfSize`.

The source gives no proof of the examples; the implemented proof uses the
standard module argument. Its generic transport lemmas need only an order
isomorphism from the subobjects of an object to the submodule lattice of
a module. Directed distributivity is transported from Mathlib's
`Directed.inf_iSup_eq`, which holds in the compactly generated lattice of
submodules. A subobject whose submodule is finitely generated is source
finite type: Mathlib's `Subobject.subobjectOrderIso`, `Submodule.mapIic`
and `ModuleCat.subobjectModule` identify its own subobjects with those of
a finite module. The published `ModuleFiniteType.finiteType_iff_finite`
and `finiteTypeFiniteSubcover`, in `Langlands.Renard`, and
`Langlands.Algebra.NonUnitalModuleFiniteness.hasFiniteSubcoverProperty_of_orderIso`
then transfer finite type. Local finite type follows because every cyclic
span `Submodule.span R {x}` is finitely generated.

For the full `NonUnitalModuleCat A`, the order isomorphism composes the
published `Langlands.Algebra.NonUnitalModuleFiniteness.subobjectExtendOrderIso`
with `ModuleCat.subobjectModule` over `Unitization ℤ A`. The `uI`-indexed
coproducts at carrier `max uI uM` are pulled back from
`ModuleCat (Unitization ℤ A)` along the published equivalence
`Langlands.Algebra.IntegerUnitization.extendFunctor A`, using Mathlib's
`Adjunction.hasColimitsOfShape_of_equivalence`. For Mathlib's
`ModuleCat A`, `ModuleCat.subobjectModule` supplies the isomorphism and
Mathlib supplies the coproducts. Neither case uses the I.6
nondegenerate-module proofs.

| Proof and authors | Candidate; machine receipt | Independent review task / reviewer | Published commit |
| --- | --- | --- | --- |
| `fullModuleAxioms` — Worker 937 with Worker 709 | `ea4778f4-ca1a-49f1-adc6-87967a9e5ac2`; `e2e06a1e-bd5c-45e0-8d78-7005efb9101f` | `428439c2-d5fb-4679-af43-9c701eff0733` / Reviewer 15180 | `819ea8d4de6f7dde4b0d7f879f58af405e135acf` |

The machine receipt passed `lake-build`, `exact-target`,
`unchanged-statement` and `frozen-inputs`, with `proof_accepted: true`
under `lean.proof@1`. Reviewer 15180 approved without qualifications,
and integration `0183c8c03a3a4fd7aa36d32496c3e9fa` published the pair.
Worker 709 wrote the Lean proof. Worker 937 rechecked it, edited its
Markdown and submitted it under proof task
`88e0f0a9-32bc-4e2b-a867-bb1aef836387`, which Worker 709 had published.
Worker 937's completion declaration
`c0aee20f-d606-43c0-9e8b-73fb7b0824c3` closed that task. Because Worker
709 coauthored the proof, this note is documentation, not independent
review.
On 5 November 2026 Worker 709 checked that the proof hashes
`dbd03997…` and `faeb02b5…` and the unchanged statement hashes
`7f096c35…` and `931e0c82…` match Library
`ffddfca241fd480a4fb3b8c9215b48c488d7f97b`.

Under the published reading of the examples, they now have an exact
proof. The other A.VI examples, corrected subcategory criteria and AB5
comparisons retain their separate entries in the
[A.VI.1–2 note](abelian-categories-progress.md) and
[whole-book ledger](coverage.md).
