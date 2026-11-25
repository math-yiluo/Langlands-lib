# Renard A.IV: limits, colimits and concrete abelian groups

Updated 5 November 2026. This note maps printed pages
256–258 / PDF262–264 to one published general definition module and four
published statement/proof pairs, plus the published concrete
filtered-colimit construction, statements and proof. It also records the
published statements identifying limits and colimits with universal arrows
for the diagonal and their published exact proof. It supplements the [whole-book
ledger](coverage.md) and [Appendix A corrections](appendix-a-corrections.md).
It introduces no Lean declaration and does not declare A.IV, Appendix A
or the book program complete.

## Source and corrections

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
retained at
`central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
PDF262–264 were read in full for the original audit; PDF263–264 were
read again for the concrete quotient modules, with PDF264 visually inspected.
The supplementary
2010 author errata, registered as `renard-2010-corrections-complements`,
SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were read at PDF18–19. Both source hashes were recomputed. The errata's
old-p.298 entry corrects the direct limit to a colimit; the 2026 text
already incorporates this. The older errata do not replace the reference
edition or repair the constant-transformation assertion on these pages.

The [published general bridge](../../Langlands/CategoryTheory/Renard/ConeBridge.md)
retains an internal diagnosis: nonemptiness of an index category
ensures faithfulness of the diagonal, but does not ensure fullness.
On `Discrete Bool`, the transformation from constant `PUnit` to constant
`Bool` with components `false` and `true` has no diagonal preimage.
`IsConnected` suffices for the auxiliary constant-Hom equivalence.
Connectedness is not imposed on general limits or colimits.

The limit prose's reversed parenthetical arrow is read as `Y ⟶ X`,
as required by the concrete formula after (A.IV.1.2). The colimit prose's
reversed arrows are read as `X ⟶ Y`, as required by its displayed
factorization. The elementary statements also correct the terminal
example's final `X` to the quantified `Y`; the ordered statements use
the inverse transitions fixed by `j → i`, despite the final subscript
interchange. The abelian product's projection target is `G_i`.
These repairs are explicit internal source diagnoses, not claims of an
author-issued correction.

## Exact source-to-declaration map

The prefixes in the tables below are:

| Prefix | Lean namespace |
| --- | --- |
| `B` | `Langlands.CategoryTheory.Renard` |
| `E` | `Langlands.Renard.ElementaryLimitColimit` |
| `O` | `Langlands.Renard.OrderedSystemLimit` |
| `S` | `Langlands.Renard.SubobjectLimit` |
| `G` | `Langlands.Renard.AbelianGroupLimit` |
| `F` | `Langlands.Renard.FilteredColimit` |
| `L` | `Langlands.Renard.LimitUniversalArrow` |

For example, `E.KernelStatement` means
`Langlands.Renard.ElementaryLimitColimit.KernelStatement`.

| Original assertion and locator | Actual Library declarations and meaning |
| --- | --- |
| A.IV.1 opening, printed256/PDF262: constant functor and diagonal | `B.diagonal` aliases `Functor.const`; `diagonal_obj_obj`, `diagonal_obj_map` and `diagonal_map_app` compute its actions. |
| Same opening: auxiliary constant-transformation assertion | Corrected `B.diagonal_faithful` under `Nonempty`, `diagonal_full` and `connectedConstantHomEquiv` under `IsConnected`; `twoPointTransformation_not_diagonal` proves the disconnected obstruction. |
| A.IV.1 definition, (A.IV.1.2) and subsequent concrete universal property, PDF262; A.IV.2 dual definition, PDF263 | Actual `Cone D` and `Cocone D` retain their vertices and natural legs. `B.ConeUniversal` and `CoconeUniversal` express unique factors into/out of those vertices; `coneUniversal_iff_nonempty_isLimit` and `coconeUniversal_iff_nonempty_isColimit` give direct witness conversions. |
| A.IV.1 remark and (A.IV.1.1), PDF262; A.IV.2 duality, PDF263 | `B.limitHomEquiv`, `colimitHomEquiv`, their component and naturality laws, and `limitNatIso` / `colimitNatIso` give the actual Hom and representing-functor comparisons, retaining the required universe lift. |
| A.IV.1 remark after the definition, PDF262: (ΔX, η) solves the left universal problem posed by Δ and D; A.IV.2 sentence after the definition, PDF263: a colimit solves the right problem | Statements with published exact proof `L.limitUniversalArrowStatements`: `L.LimitUniversalStatement` and `ColimitUniversalStatement` compare `IsLimit`/`IsColimit` of the actual cone/cocone with `CostructuredArrow.IsUniversal`/`StructuredArrow.IsUniversal` for `B.diagonal`; `L.LimitFactorizationStatement` and `ColimitFactorizationStatement` compare them with the A.III.1 unique-factorization property. Each clause is an equivalence; the converse is a derived strengthening. |
| A.IV.1 uniqueness remark, PDF262; A.IV.2 duality | `B.limitConeIso`, `colimitCoconeIso`, `limitPointIso` and `colimitPointIso` give canonical isomorphisms; the leg equations and `limitPointIso_eq` / `colimitPointIso_eq` express structure-preserving uniqueness. |
| A.IV.1 example 1, PDF262; A.IV.2 first dual example, PDF263 | `E.EmptyLimitStatement` and `EmptyColimitStatement`: supplied empty cones/cocones are universal iff their retained vertices are terminal/initial. |
| A.IV.1 example 2, PDF262–263; A.IV.2 second dual example | `E.KernelStatement` and `CokernelStatement`: the actual fork/cofork of a map and zero is universal iff every zero-composite arrow factors uniquely. |
| A.IV.1 example 3, PDF263; A.IV.2 third dual example | `E.ProductStatement` and `CoproductStatement`: actual fans/cofans on arbitrary families, including the binary cases, with all projection/injection equations. |
| A.IV.1 example 4 and (A.IV.1.3), PDF263; A.IV.2 fourth dual example | `E.PullbackStatement` and `PushoutStatement`: actual cospan/span cones/cocones and unique factors for compatible pairs. |
| A.IV.1 example 5, PDF263 | `O.InverseLimitStatement` characterizes a supplied cone on `D : Iᵒᵖ ⥤ C`, with transition from `j` to `i` for `i ≤ j`. |
| A.IV.2 explicit direct-system paragraph, PDF263 | `O.DirectLimitStatement` characterizes a supplied cocone on `D : I ⥤ C`, with transition from `i` to `j` for `i ≤ j`. |
| A.IV.1 example 6 and A.IV.2 union dual, PDF263; A.I.2 order-bound definitions, printed248/PDF254 | Derived exercise interpretation: `S.IntersectionLimitStatement` and `UnionColimitStatement` compare universality in the actual thin category `Subobject X` with `IsGLB` and `IsLUB` of `Set.range F`. |
| A.IV.2 abelian-group example, PDF263–264: product | `G.CartesianProductStatement`: the raw function product with coordinate projections is a product of the lifted factors. |
| Same example: direct sum | `G.DirectSumCoproductStatement`: the actual `DirectSum` with its single-coordinate inclusions is a coproduct of the lifted factors. |
| Same example: infinite-family finite-support description, PDF264 | `G.FiniteSupportComparisonStatement` gives an injective additive coordinate map, its exact finite-support range and the inclusion formulas. Its validity for every index type is an internal uniform strengthening. |
| Same example: finite-family full product, PDF264 | `G.FiniteProductCoproductStatement` states that the full product, with single-coordinate inclusions, is a coproduct under `Finite I`. |
| A.IV.2 final paragraphs, PDF264: quotient of the disjoint union by eventual equality, its group law and canonical maps | Published `F.Carrier`, `classOf`, `classOf_eq_iff`, `classOf_transition` and `exists_classOf` expose the literal quotient and relation. Under `Nonempty I`, `of`, `zero_eq_classOf`, `classOf_add`, `neg_classOf` and `of_comp` expose the inherited abelian-group operations and canonical homomorphisms. |
| Same paragraphs: compatible-family universal property | Published `F.diagram`, `cocone` and `lift` are actual constructions. `F.quotientColimitStatement` proves that exact cocone colimiting, and `compatibleFamilyLiftStatement` proves that exact lift factors each compatible family uniquely. |
| Same final paragraph: a representative vanishing in the colimit vanishes at some later stage | `F.eventualZeroStatement` proves the source implication. `eventualZeroIffStatement` proves the explicitly derived equivalence, using transition compatibility for the converse. |
| Internal empty-index completion of the displayed pairwise-directed convention | `F.carrier_isEmpty` proves that the literal quotient is empty. `emptyCocone` supplies the singleton zero-group vertex; `emptyColimitStatement` proves that this actual cocone is colimiting. |

The four closed statement aggregates, in their exact published order, are
`E.ElementaryLimitColimitStatements` (eight elementary components),
`O.OrderedSystemLimitStatements` (inverse, then direct),
`S.SubobjectLimitStatements` (intersection, then union), and
`G.AbelianGroupLimitStatements` (product, direct sum, finite-support
comparison, finite-product coproduct). Their exact aggregate proofs are,
respectively, `E.elementaryLimitColimitStatements`,
`O.orderedSystemLimitStatements_proof`, `S.subobjectLimitStatements` and
`G.abelianGroupLimitStatements`.

The fifth published aggregate, `F.FilteredColimitStatements`, conjoins
the quotient colimit, compatible-family lift, eventual-zero implication,
derived equivalence and empty-cocone targets, in that order. It is a
`Prop`-valued definition. The separately published proof
`F.filteredColimitStatements` establishes this exact conjunction.

The sixth published aggregate,
`L.LimitUniversalArrowStatements.{vJ,vC,uJ,uC}`, conjoins the limit
universal-arrow, limit factorization, colimit universal-arrow and colimit
factorization clauses, in that order. It quantifies over every index
category, including empty and disconnected ones, at four independent
universes. The factorization clauses quantify over morphisms of C, not over
arbitrary transformations between constant functors, consistently with the
diagonal-fullness diagnosis above. The separately published proof
`L.limitUniversalArrowStatements` establishes this exact conjunction.

## Hypotheses, constructions and implemented proofs

The general bridge retains independent index-object, index-Hom,
category-object and category-Hom universes. It uses actual Mathlib cone
and cocone data. `IsLimit` and `IsColimit` carry witnesses; `Nonempty`
turns their existence into `Prop`. The Hom natural isomorphisms retain
`uliftFunctor` to reconcile the Hom and cone-functor universes. Empty
indices retain the cone vertex, even though an empty constant functor
cannot recover that vertex. Canonical uniqueness concerns isomorphisms
preserving the legs.

The [elementary statement](../../Langlands/CategoryTheory/Renard/ElementaryLimitColimitStatements.md)
and [proof](../../Langlands/CategoryTheory/Renard/ElementaryLimitColimitProofs.md)
retain independent `vC`, `uC` and `uI`. Kernels and cokernels retain
`HasZeroObject` and the separately supplied compatible
`HasZeroMorphisms`; additivity and abelianness are not required.
The eight proofs use Mathlib's empty-cone/terminal equivalences and
kernel-fork, fan, pullback-cone and dual APIs. Forward directions extract
factors and use hom extensionality; reverse directions choose the
asserted unique factors and use the corresponding witness constructors.
These characterize supplied cones and cocones; they do not assert
existence of every shape in an arbitrary category.

The [ordered statement](../../Langlands/CategoryTheory/Renard/OrderedSystemLimitStatements.md)
and [proof](../../Langlands/CategoryTheory/Renard/OrderedSystemLimitProof.md)
retain independent `vC`, `uC`, `uI`, `PartialOrder I` and the source's
pairwise-upper-bound condition `IsDirectedOrder I`. They add no
`Nonempty I`. The proof constructs competing cones/cocones from the
inequality-compatible families, verifies naturality for every order
morphism, then applies `existsUnique` or `ofExistsUnique`. Reindexing
through `op`/`unop` gives the inverse case. No index element is selected;
empty and infinite indices remain covered. Directedness is retained
from the source although unused by these universal-property equivalences.

The [subobject statement](../../Langlands/CategoryTheory/Renard/SubobjectLimitStatements.md)
and [proof](../../Langlands/CategoryTheory/Renard/SubobjectLimitProof.md)
use the existing factorization order on `Subobject X`. Their three
universes are independent; there is no lattice, completeness,
well-poweredness or smallness premise. A range identity reconciles the
objects of `Discrete.functor F` with `Set.range F`. Mathlib's
`Preorder.isGLB_of_isLimit`, `isLimitOfIsGLB`, `isLUB_of_isColimit` and
`isColimitOfIsLUB` then prove both characterizations for the original
supplied cone or cocone. This is the derived interpretation of the
source exercise, with colimits in `Subobject X`. It asserts neither
existence of all bounds nor colimits of underlying representatives in
`C`. Empty families are retained.

The [abelian-group statement](../../Langlands/CategoryTheory/Renard/AbelianGroupLimitStatements.md)
and [proof](../../Langlands/CategoryTheory/Renard/AbelianGroupLimit.md)
retain independent index and group universes `uI` and `uG`. Each factor
is `AddCommGrpCat.of (ULift.{uI} (G i))` in
`AddCommGrpCat.{max uI uG}`, while the product and direct sum retain
their raw carriers. The product proof lowers components of a cone
through `AddEquiv.ulift` and collects them with `AddMonoidHom.pi`;
coordinate equality gives uniqueness. The direct-sum proof uses
`DirectSum.toAddMonoid` on the cocone legs after lifting the factors;
its generator formula and `DirectSum.addHom_ext` give factorization
and uniqueness. The coordinate-range proof uses injectivity of the
function coercion, `DFinsupp.finite_support`, `DFinsupp.mk` and the
single-coordinate formula. The finite-product proof transports the
extension through `DirectSum.addEquivProd`; it obtains `Fintype`
internally from `Finite`. There is no external decidable-equality or
enumeration premise. Empty families remain covered. No universal
properness claim is made for an infinite family's finite-support
subgroup.

The [concrete filtered-colimit construction](../../Langlands/CategoryTheory/Renard/FilteredColimit.md)
uses Mathlib's `DirectLimit G f`, literally the quotient of `Σ i, G i`
by equality at a common later stage. The inputs are a partial order
with `IsDirectedOrder I`, arbitrary abelian groups and additive
transitions with the intrinsic identity and composition
`DirectedSystem` laws. `classOf_eq_iff` is the quotient equality
criterion; `classOf_transition` and `exists_classOf` expose its native
representative API. With `Nonempty I`, the inherited group instance
supplies the well-defined operations. The displayed zero, common-stage
addition and negation formulas compute those operations. No injectivity,
finiteness or generation premise is imposed.

The actual diagram has factors `ULift.{uI} (G i)` in
`AddCommGrpCat.{max uI uG}`; its transitions lower, apply the original
transition and raise. The quotient cocone's legs lower and apply `of`.
The actual compatible-family lift uses quotient recursion and
`lift_classOf` computes it on every representative. Its target is an
arbitrary abelian group in independent universe `uH`. Thus the
[published statement](../../Langlands/CategoryTheory/Renard/FilteredColimitStatements.md)
retains independent `uI`, `uG` and `uH`. It requires categorical
universality of those exact data, and factorization and uniqueness of
that exact lift on the original components.

The [published concrete proof](../../Langlands/CategoryTheory/Renard/FilteredColimitProofs.md)
first proves factorization by `lift_classOf` and uniqueness by
`exists_classOf`. For a competing cocone, raising the original components
with `AddEquiv.ulift` converts its legs into a compatible family.
Its actual quotient lift gives the categorical descent; the component
formula and the just-proved uniqueness supply the `IsColimit` laws.
For eventual zero, `zero_eq_classOf` and `classOf_eq_iff` give a common
later stage where the element equals the transitioned zero. Every
transition preserves zero. The derived converse follows from `of_comp`
and zero preservation of the canonical maps. No universal property or
eventual-zero conclusion is assumed.

The empty case keeps a separate target. Pairwise directedness permits
an empty index, while the literal quotient is then empty and has no
group identity. This internal source diagnosis is recorded by
`carrier_isEmpty`. Under `IsEmpty I`, `emptyCocone` instead uses `PUnit`
as the singleton zero-group vertex with vacuous legs.
`EmptyColimitStatement` has neither a nonemptiness nor a directedness
premise. Its proof uses the zero additive homomorphism out of the
singleton vertex; factorization is vacuous and uniqueness follows because
every element equals zero. No change is made to the unrestricted general
ordered-system statements.

These published implementations reuse
Mathlib at pin `5ed2965256430c3649e86755f9576b54eca72435`; their
implemented proof routes are the ones described above.

## In the Library: first appearance and file identity

The first nine modules were audited at Library
`071b82c1a715daffe0334ad25311484eaba312b0`, including equality with the
commit at which each first appeared. The concrete construction and statement
were checked when they entered the Library; the first eleven modules were
checked on 3 November 2026 and the concrete proof on 4 November 2026.
At Library `442ff746325df5b6d721fee75d430a65c33d09f0`, the first
twenty-four mathematical files below have the displayed hashes. The new
proof pair also matches its first published version, and both imported
construction and statement pairs are unchanged from the preceding Library
commit. Reuse uses the Lean names above. The general bridge is a definition
module with short intrinsic laws, not a separate aggregate proof.

| Module | First appeared at Library commit |
| --- | --- |
| General bridge (definition) | `d20f8eabc581491c5dec30dea40e5e036293121f` |
| Elementary statements | `676ac944440098acb714f6b953083e88bb89c9c2` |
| Elementary proof | `4f255c2d810d0998369347f03338826ce587c35b` |
| Ordered statements | `676ac944440098acb714f6b953083e88bb89c9c2` |
| Ordered proof | `4f255c2d810d0998369347f03338826ce587c35b` |
| Subobject statements | `4f255c2d810d0998369347f03338826ce587c35b` |
| Subobject proof | `e3944f764d2c00d53ac87227e98601bb667f348f` |
| Abelian-group statements | `e3944f764d2c00d53ac87227e98601bb667f348f` |
| Abelian-group proof | `a5dff2ff93bd3637a67ee8847f67f811efc82f01` |
| Concrete filtered-colimit construction | `d651c06c32b90676853a4e79f91b86385a8cd650` |
| Concrete filtered-colimit statements | `b6ea11bf7c883ae0600a98215483c75ebf3c9d25` |
| Concrete filtered-colimit proof | `442ff746325df5b6d721fee75d430a65c33d09f0` |
| Universal-arrow statements | `542eaca02a9f2d14f175497b7bf6459436ac5c6d` |
| Universal-arrow proof | `50126e1b2b20b62d408b52dc3552f01089dd1d11` |

| Paired path stem under `Langlands/CategoryTheory/Renard/` | Lean SHA256 | Markdown SHA256 |
| --- | --- | --- |
| [ConeBridge](../../Langlands/CategoryTheory/Renard/ConeBridge.md) | `5e523b6f3b3d483c425edda8828e6879b463c672d3179c3763dd35f172b38afa` | `ccadd86fa0bd7de9521bf4f60560e207bca70a26f86622e39a13eac6f57a8b00` |
| [ElementaryLimitColimitStatements](../../Langlands/CategoryTheory/Renard/ElementaryLimitColimitStatements.md) | `475366b8ff67730e6e5e6d72e64b716f5001dff3a0a4bbce7d50e369c87751ef` | `0e9dd31e6bcc829b1a38d390ca8b27031de656fd95bcc3e06c13c60228214669` |
| [ElementaryLimitColimitProofs](../../Langlands/CategoryTheory/Renard/ElementaryLimitColimitProofs.md) | `0ad40291eb732e219c4203e97a5361b15afc3e04d0a47c637fa83e3848014f7c` | `f5d7ec704482f3cff44885f2a59b3bf509bae822df6fa25a1c89eaafe854030a` |
| [OrderedSystemLimitStatements](../../Langlands/CategoryTheory/Renard/OrderedSystemLimitStatements.md) | `0a19643259e966569d18cb94ef98d81ef4845191dbd6ae8dd837113a959c3a1f` | `e93c4efffec534df034b1fddfcbf47195cb0e5785ec8286016cd12f78e81e6cf` |
| [OrderedSystemLimitProof](../../Langlands/CategoryTheory/Renard/OrderedSystemLimitProof.md) | `efe3162a483f2548a7f2c55cba6f3322ef002574b4cb4a383ec2930105203ca8` | `40020fafcd4bfc27a9e6e3ceced56dd0afa8fa67554a7675666f7501ed1cca37` |
| [SubobjectLimitStatements](../../Langlands/CategoryTheory/Renard/SubobjectLimitStatements.md) | `01d5342d28f709bf8cf2e49c0db5f10d3f285abfcfa761b50c86f975cbd2bf23` | `08357646eebe1f8d3944076f2f4743aacee7d4b1960e5a2baec0bb2f9def954c` |
| [SubobjectLimitProof](../../Langlands/CategoryTheory/Renard/SubobjectLimitProof.md) | `3faf8fb1e15c11b15bef8109d7be79847d9c6ab98aa1e044cc688c7953a9de77` | `bf243e164e417e0071228feab0097448ebe6c9efbe62fe0ec9ead539decfecd4` |
| [AbelianGroupLimitStatements](../../Langlands/CategoryTheory/Renard/AbelianGroupLimitStatements.md) | `54a7f3f678eaf341b7a1052cceb229e62c49d7e81b81796fb3b48be99f3a6435` | `f5183596ff4fb4c9313b9ac674083c40fed2cfbe263055c3b58a957bdecc96a3` |
| [AbelianGroupLimit](../../Langlands/CategoryTheory/Renard/AbelianGroupLimit.md) | `4fc54f65cf2bda9a37e3288958206155db7287139fa15bd649ef8ccd445690c9` | `f3fff1434a05de29232ef5bbacbe9f6f53f4a0cd76e79229d71464e05f9b9273` |
| [FilteredColimit](../../Langlands/CategoryTheory/Renard/FilteredColimit.md) | `67e7eb9a18268aa1178c338b7409f97c54c551c12d5901bf2364b01e6659baaa` | `4a08faafc3c1a337cc435121da557272fb53a7c9b5802a7fb235517263d7aa09` |
| [FilteredColimitStatements](../../Langlands/CategoryTheory/Renard/FilteredColimitStatements.md) | `5e04ba0fecd6fde5c6423c2757d45a6b3ceb26ab7eb742f8fd13238c37c8fee3` | `f15ec8b33c8d9fc609317ef2114397ed68883b394656373576f0f214bca56134` |
| [FilteredColimitProofs](../../Langlands/CategoryTheory/Renard/FilteredColimitProofs.md) | `2b2702043d9d2b0d3c7ba42160509caa6f23db23b6d5145c3f51c34e5c75f466` | `00a10d58644c30a095592ed98278d4aa7a8917613098df2da083411322507e70` |
| [LimitUniversalArrowStatements](../../Langlands/CategoryTheory/Renard/LimitUniversalArrowStatements.md) | `aab427f9ad66f70a93589b303b335ecf80572c1f9bfa2811a61f7aaff4abfa97` | `0d29b3840f0e5969dab43d0ad1a2adea66556e017b4cbcd0a204389de2e472fa` |
| [LimitUniversalArrowProof](../../Langlands/CategoryTheory/Renard/LimitUniversalArrowProof.md) | `25dec70bbf3f3fad3c826726fdde9682ae68cd8eb87baa69d670f76e9ab181b1` | `6e1652b1d0d2703a66c2640fe8d5dfba336451eda865ebef0e5418461b0f14e1` |

A separate build of `ConeBridge`, `ElementaryLimitColimitProofs`,
`OrderedSystemLimitProof`, `SubobjectLimitProof` and `AbelianGroupLimit`
passed with zero errors and warnings. A further build passed both concrete
filtered-colimit modules with zero diagnostics and inspected
`F.FilteredColimitStatements` as a proposition with independent `uI`, `uG`
and `uH`; this is statement compilation, not a proof. The concrete proof was
checked by a Lake build against the exact target, the unchanged
`F.FilteredColimitStatements`, with its inputs unchanged.

The universal-arrow statements are in the Library; their check covers
statement compilation and declaration kind and proves none of the four
clauses. On 5 November 2026 the pair above was equal in Library
`dd78edadc914cf56ca81c595cee581a3570d415c`.

The universal-arrow proof `L.limitUniversalArrowStatements` proves the
unchanged aggregate at the independent universes `vJ vC uJ uC`. Its source
correspondence was checked. The factorization
clauses are proved directly. A limit witness supplies the factor
`h.lift (Cone.mk Y f)`, and `IsLimit.ofExistsUnique` gives the converse;
the colimit clause is dual. Both use componentwise equations and
transformation extensionality. The structured-arrow clauses compose these
with the published `leftCharacterization_proof` and
`rightCharacterization_proof` at the diagonal functor. No nonemptiness,
connectedness, size or existence-of-limits premise is added. The unique
factors remain morphisms of C.

The proof is in the Library. It was checked by a Lake build against the
exact target, with the statement and its inputs unchanged. At Library
`50126e1b2b20b62d408b52dc3552f01089dd1d11` the proof pair equals its first
published version and the statement pair keeps the hashes above.

## Retained obligations

The concrete quotient's five exact targets now have a
published proof. That proof retains the nonempty quotient's
hypotheses, independent universes and arbitrary additive directed systems,
and the separate empty singleton-cocone target. The eventual-zero converse
is explicitly derived; the empty target is an internal completion of the
source boundary. `O.DirectLimitStatement` characterizes an arbitrary
supplied cocone; the concrete proof establishes universality of the
particular published quotient. The II.2.1 basis-stalk construction remains
a distinct application.

The identification of the general definition with the earlier
universal-arrow terminology is proved: the published statements
`L.LimitUniversalArrowStatements` have the published exact proof
`L.limitUniversalArrowStatements`. Its converses and comma-category
clauses remain the derived formulations recorded in the statement module. Any additional cross-section
comparison and the other Appendix assertions retain their own obligations
unless an exact published correspondence is supplied. No general existence
theorem for arbitrary-category limits, ambient-category subobject
colimits, original nonunital-module construction, or section/book
completion follows from this note.
