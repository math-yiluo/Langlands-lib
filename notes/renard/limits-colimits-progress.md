# Renard A.IV: limits, colimits and concrete abelian groups

Worker 709, updated 4 November 2026, with Worker 6's source diagnosis and
filtered-colimit scope reconciliation and Worker 1153's concrete proof
and publication evidence. This note maps printed pages
256–258 / PDF262–264 to one published general definition unit and four
published statement/proof pairs, plus the published concrete
filtered-colimit construction, statements and proof. It supplements the [whole-book
ledger](coverage.md) and [Appendix A corrections](appendix-a-corrections.md).
It introduces no Lean declaration and does not declare A.IV, Appendix A
or the book program complete.

## Source and corrections

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
PDF262–264 were read in full for the original audit; PDF263–264 were
read again for the concrete quotient units, with PDF264 visually inspected.
The supplementary
2010 author errata, registered as `renard-2010-corrections-complements`,
SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were read at PDF18–19. Both source hashes were recomputed. The errata's
old-p.298 entry corrects the direct limit to a colimit; the 2026 text
already incorporates this. The older errata do not replace the reference
edition or repair the constant-transformation assertion on these pages.

The [published general bridge](../../Langlands/CategoryTheory/Renard/ConeBridge.md)
retains Worker 6's internal diagnosis: nonemptiness of an index category
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

For example, `E.KernelStatement` means
`Langlands.Renard.ElementaryLimitColimit.KernelStatement`.

| Original assertion and locator | Actual Library declarations and meaning |
| --- | --- |
| A.IV.1 opening, printed256/PDF262: constant functor and diagonal | `B.diagonal` aliases `Functor.const`; `diagonal_obj_obj`, `diagonal_obj_map` and `diagonal_map_app` compute its actions. |
| Same opening: auxiliary constant-transformation assertion | Corrected `B.diagonal_faithful` under `Nonempty`, `diagonal_full` and `connectedConstantHomEquiv` under `IsConnected`; `twoPointTransformation_not_diagonal` proves the disconnected obstruction. |
| A.IV.1 definition, (A.IV.1.2) and subsequent concrete universal property, PDF262; A.IV.2 dual definition, PDF263 | Actual `Cone D` and `Cocone D` retain their vertices and natural legs. `B.ConeUniversal` and `CoconeUniversal` express unique factors into/out of those vertices; `coneUniversal_iff_nonempty_isLimit` and `coconeUniversal_iff_nonempty_isColimit` give direct witness conversions. |
| A.IV.1 remark and (A.IV.1.1), PDF262; A.IV.2 duality, PDF263 | `B.limitHomEquiv`, `colimitHomEquiv`, their component and naturality laws, and `limitNatIso` / `colimitNatIso` give the actual Hom and representing-functor comparisons, retaining the required universe lift. |
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

The general bridge is Worker 610's implementation with Worker 6's
source diagnosis. The elementary statements are by Workers 709 and 695,
and their proof by Worker 1158. The ordered statements are by Worker 709
and proof by Worker 695. The subobject statements are by Worker 709 and
proof by Worker 840. The abelian-group statements are by Workers 709
and 937 and proof by Worker 695. Worker 709 authored the concrete
filtered-colimit construction and statements, with Worker 6's prior
source-scope reconciliation and retention of the empty-index boundary.
Worker 1153 authored the concrete five-part proof.
These published implementations reuse
Mathlib at pin `5ed2965256430c3649e86755f9576b54eca72435`; their
implemented proof routes are the ones described above.

## Verified acceptance, publication and file identity

The first nine units were audited at Library base
`071b82c1a715daffe0334ad25311484eaba312b0`, including equality with each
cited publication commit. The concrete construction and statement
receipts were verified on publication, including their frozen pairs.
The first eleven exact records were verified on 3 November 2026.
The concrete proof record was fetched on 4 November 2026 and is
accepted and public, with Reviewer 12926's independent approval without
qualifications and the published integration below. Its complete acceptance
report agrees with the integrated report in every common field.
At Library base `442ff746325df5b6d721fee75d430a65c33d09f0`, all
twenty-four mathematical files below retain the displayed hashes in
the workspace and Library. The new proof pair also matches its frozen
artifact, and both imported construction and statement pairs are unchanged
from the preceding Library base. The table gives exact archival evidence; reuse
uses the current Lean names above. The general bridge is a definition
unit with short intrinsic laws, not a separate aggregate proof record.

| Unit and exact task | Accepted publication | Independent review | Integration and Library commit |
| --- | --- | --- | --- |
| General bridge (definition); task `57165880-67cc-47a1-9761-3960f6543b0b` | `25bf9e9f-f37f-4eae-9010-b0441a3bf865` | Reviewer 3042; `2e099064-58fe-4b34-a2a8-a2b97b1276e0` | `a7144ff47cab4d38954b0885866c33e3`; `d20f8eabc581491c5dec30dea40e5e036293121f` |
| Elementary statements; task `c3d30624-2819-4880-9e8f-aeae7deefd62` | `3bd88773-11b2-48be-bdc3-8bbc4a7d088d` | Reviewer 7597; `8db96549-0bea-4d68-a4db-ffd66d6e9e5a` | `7ebbdf058662453f9476395eee7b1bd1`; `676ac944440098acb714f6b953083e88bb89c9c2` |
| Elementary proof; task `9e2071b5-8063-4fd9-a6a7-82b899839586` | `9f0b09c1-b8a3-450a-94c4-65d7fc785ad0` | Reviewer 7648; `9c31cb29-4ece-4c83-a5e9-970f477e2d8e` | `d495c23a54044a58a63dc9e43d86d80c`; `4f255c2d810d0998369347f03338826ce587c35b` |
| Ordered statements; task `dce29bd9-fedd-47d6-a101-2025e40b2b15` | `d57cb0f8-b86b-4335-8215-49386e68e504` | Reviewer 7620; `2b9a0d6d-65c5-4c5c-a4c1-302fdc27b51f` | `18456a343c8f461c98d3931524be3cc6`; `676ac944440098acb714f6b953083e88bb89c9c2` |
| Ordered proof; task `642ff030-25ae-460a-8640-7734777aeb4b` | `2709c19c-f6ee-447e-96c2-98d42dc54c99` | Reviewer 7668; `bac117d3-bce7-4a9b-aa65-0f648e15b1ef` | `2a53b7eb9fdb4d539111322ee289b80a`; `4f255c2d810d0998369347f03338826ce587c35b` |
| Subobject statements; task `ee3a58ca-a732-4688-bd68-20294fc66e2f` | `74110307-1661-4db7-b6f1-28001180d21b` | Reviewer 7633; `1fe3a5d9-ebaf-44a2-a86c-da248fb95dc6` | `3887368448b04a3494345213a67cd9de`; `4f255c2d810d0998369347f03338826ce587c35b` |
| Subobject proof; task `d6777962-fc47-48f4-9eae-db566e452454` | `db95c802-942f-4c4c-9993-abc85db2fa16` | Reviewer 7735; `361eb673-1e30-4906-9522-81d35d393dff` | `c3b84639be454f1693a6d852a2f8fb95`; `e3944f764d2c00d53ac87227e98601bb667f348f` |
| Abelian-group statements; task `01fe320c-fced-4500-8bbb-e6a2f9b63681` | `54fab975-e2de-420b-927b-6b4a9d24eb71` | Reviewer 7707; `6b4b58d7-3699-4199-a2b2-3bdad69d5738` | `a3de277e4aab4809bab31f500d48b69e`; `e3944f764d2c00d53ac87227e98601bb667f348f` |
| Abelian-group proof; task `164894cf-f28c-4353-9bdc-59b3dae749d4` | `29331b94-b957-4e70-8f6d-7da4d651effe` | Reviewer 7794; `1bd42485-e2c7-433a-ad3f-afb9adec08d4` | `4e5249f307274960a8857a645f57a368`; `a5dff2ff93bd3637a67ee8847f67f811efc82f01` |
| Concrete filtered-colimit construction; parent task `f5d1f399-a1f8-4ab5-a981-90b92abd4857` r3 | `3e406095-fce5-4c7e-912d-f54f789f4672` | Reviewer 11896; `cdfd6721-2fa3-4c52-b448-b9a2be72d5f0` | `0d9d2917356b4fbb98f15a495d3d4879`; `d651c06c32b90676853a4e79f91b86385a8cd650` |
| Concrete filtered-colimit statements; same parent r3 | `3d90ac79-1633-41dc-ad0e-776f6a3922ea` | Reviewer 12003; `b1783779-696b-4f87-b139-f1e13ad4d999` | `9f54d0209e134fc2ad77b7ff7f10e813`; `b6ea11bf7c883ae0600a98215483c75ebf3c9d25` |
| Concrete filtered-colimit proof; task `ce8400b5-29cb-422f-91f5-9cc761af2531` r1 | `5bd3407c-e5f4-401d-a136-1070af0b2b4d` | Reviewer 12926; `6467768b-8298-4828-b133-03e3756576c3` | `ed76a1a7cc24433e9ffc73674cec3db6`; `442ff746325df5b6d721fee75d430a65c33d09f0` |

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

Approved environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` also passed
a recovery check of `ConeBridge`, `ElementaryLimitColimitProofs`,
`OrderedSystemLimitProof`, `SubobjectLimitProof` and `AbelianGroupLimit`
with zero errors and warnings. This development check is separate from
the independent semantic approvals and publication evidence above.
The update-base check `f9edde4d-12a1-4fb6-9971-6c2e6f0d62ec` also
passed both concrete filtered-colimit modules with zero diagnostics and
inspected `F.FilteredColimitStatements` as a proposition with independent
`uI`, `uG` and `uH`. This is statement compilation, not proof acceptance.
For the concrete proof, exact machine receipt
`31839a59-e796-41c8-94bf-a92c2cc0a4d1` passed `lake-build`,
`exact-target`, `unchanged-statement` and `frozen-inputs` for the
unchanged `F.FilteredColimitStatements`. The published integration also
records a successful fresh build of integrated snapshot
`f496b3bc07c1ada71ba5874ed7da76904e9a7a40c1c51f0323cdebc1e51ccae6`.
These machine checks are distinct from the semantic reviews.

## Retained obligations

The concrete quotient's five exact targets now have an independently
accepted and published proof. That proof retains the nonempty quotient's
hypotheses, independent universes and arbitrary additive directed systems,
and the separate empty singleton-cocone target. The eventual-zero converse
is explicitly derived; the empty target is an internal completion of the
source boundary. `O.DirectLimitStatement` characterizes an arbitrary
supplied cocone; the concrete proof establishes universality of the
particular published quotient. The II.2.1 basis-stalk construction remains
a distinct application.

The identification of the general definition with the earlier
universal-arrow terminology, any additional cross-section comparison,
and the other Appendix assertions retain their own obligations unless
an exact published correspondence is supplied. No general existence
theorem for arbitrary-category limits, ambient-category subobject
colimits, original nonunital-module construction, or section/book
completion follows from this note. Existing owners, held work and
Worker 6's saved VI.3.3 wait are preserved.
