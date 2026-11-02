# Renard II.2.1–II.2.2: published descent and compact germ-section functors

Worker 6, 1 November 2026.

The initial four focused publications cover the stalk
representative statements, locally represented germ groups and their maps,
direct gluing and sheaf functors, and the separation and corrected
target-compatibility statements. Two units supply constructions with their
intrinsic laws; two supply proposition definitions. Seven later publications
add the representative and separation proofs, actual universe lifts and
canonical units, literal support carriers, and the relative-closedness
statement and proof. Two further publications now supply corrected
original-target descent and compact germ-section groups and morphism maps.
A further publication supplies the fixed-open compact-section functors
and natural inclusions. This note records their distinct scopes and updates the
[whole-book coverage ledger](coverage.md).

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, II.2.1–II.2.2, printed pp.33–38 /
PDF pp.39–44, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original passages were read directly; the formulas on PDF pp.40 and 42
were also checked visually in the preceding audits. The supplementary
2010-edition corrections,
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pp.2–3, were read. The
[source-error audit](basis-sheafification-source.md) records the bounded
errata search and the correction needed in the later descent argument.

All shortened Lean names below have prefix `Langlands.Sheaf.Renard`.
The actual chosen basis, original section groups and restriction maps are
the published `BasisPresheaf`, `BasisSheaf` and `BasisStalk` interfaces.

| Original assertion | Public interface | Exact coverage |
| --- | --- | --- |
| Stalk representatives and common-refinement relation, printed p.34 / PDF p.40 | `BasisStalkRepresentativesStatement` | Four raw/normalized representative-existence and germ-equality proposition families; statement coverage. [Statement pair](../../Langlands/Sheaf/Renard/BasisStalkRepresentativesStatement.md). |
| Equation (II.2.1.2), pointwise group, restrictions and induced maps, printed pp.34–35 / PDF pp.40–41 | `GermFamily`, `LocallyRepresented`, `GermSections`, `germRestriction`, `germSectionsMap` | Actual groups and additive maps, with local/cover equivalence, refinement proofs, empty-domain uniqueness and intrinsic map laws. [Construction pair](../../Langlands/Sheaf/Renard/GermSections.md). |
| Direct sheaf gluing and functoriality, printed p.35 / PDF p.41; same families on all opens, printed p.37 / PDF p.43 | `germGlue`, `germPresheafOn_familySheafCondition`, `rawGermSheafFunctor`, `germSheafFunctor`, `rawAllOpenGermSheafFunctor`, `allOpenGermSheafFunctor` | Actual chosen-basis and all-open-basis sheaves and functors, with independently indexed gluing and definitional evaluation/map formulas. [Construction pair](../../Langlands/Sheaf/Renard/GermSectionSheaf.md). |
| Zero-germ lemma and the corrected compatibility required for (II.2.1.4), printed p.36 / PDF p.42 | `RenardSheafGermSeparationStatement` | Six raw/bundled zero-separation, equality-detection and target-compatibility proposition families; statement coverage. [Statement pair](../../Langlands/Sheaf/Renard/SheafGermSeparationStatements.md). |

`GermFamily F U` is the dependent function type
`(x : U) → rawStalk F x.val`. `LocallyRepresented` requires an original
section representing the family throughout a contained basis neighborhood
of each point. Its cover formulation also permits representing opens to
extend outside the domain. Refining their intersections with the domain
proves equivalence with the contained-neighborhood formulation.
`GermSections` is the actual additive subgroup of these families.
Addition refines the two local neighborhoods and adds restricted original
representatives. Restriction is literal restriction of dependent
functions, and a presheaf morphism acts by its original stalk map at each
point.

The gluing construction first refines overlaps to compare stalk-family
values. It chooses a containing cover member at each point, proves
independence of that choice, and transfers a local original representative
from a cover member to the glued family. Uniqueness follows by evaluating
restrictions at each point. This direct proof uses no representative
existence or germ-equality theorem for arbitrary stalk elements.

An auxiliary target basis `C` packages the same `GermSections F U`
groups and restrictions. The original stalks still come from the input
basis `B`. Specializing `C = B` gives the chosen-basis functors;
specializing `C = allOpenBasis X` gives sheaves in the project's
literal basis category for all opens. Changing this packaging does not
reconstruct stalks or establish an equivalence between arbitrary sheaf
categories.

The space universe `u` and original group universe `v` are independent;
stalk and germ-section carriers live in `max u v`. The gluing and
compatibility statements permit an independently sized family index
`w`. The input presheaf need not be a sheaf, and raw inputs need not be
normalized at the empty open. Normalized functors use the actual
`presheafInclusion`. The arbitrary raw inputs, auxiliary target basis and
universe packaging are internal extensions of the original construction.
No Hausdorff, local compactness, countability, intersection-closure or
nonempty-domain hypothesis is added. Empty domains and families retain
their literal meanings.

The representative aggregate asserts that every stalk value has an
original representative and that two original germs agree exactly when
their restrictions agree on a common smaller basis neighborhood. It
does not construct a quotient equivalence. The separation aggregate uses
the sheaf hypothesis on the target: equal source germs imply compatibility
of the image sections on every smaller basis open in an overlap.
The source is arbitrary, and this local comparison needs no covering
hypothesis. It does not assert the false equality of original presheaf
sections in (II.2.1.3).

## Publication evidence

All four candidates have unqualified independent approval,
`accepted = true`, `public = true` and a published integration at
`a5dff2ff93bd3637a67ee8847f67f811efc82f01`. Their eight frozen
Lean/Markdown hashes were checked against that Library, the workspace
and the later published Library
`dac2bb9e83346876770fced17af26f0cba7f4c98`; all agree.

| Unit and policy | Candidate | Machine receipt | Independent review task and reviewer | Published integration |
| --- | --- | --- | --- | --- |
| Representatives, `lean.statement@1` | `d0035e8f-d9bd-4f94-be13-76034ff2802a` | `89b27475-2ba8-4e15-b36b-343f30bde260` | `4600d7b3-f383-473e-8297-36f0c3ab3a3b`, Reviewer 7763 | `1dffcb06bac4402f954e33bc714b96e4` |
| Germ groups/maps, `lean.definition@1` | `4653b97d-cbcc-46df-baa3-2107a5e02669` | `a7d89703-08cb-46e0-a79c-ef26361b8d9e` | `55b7d533-8836-4bbf-8f9b-185189e7c8f7`, Reviewer 7778 | `6495cce5ce9344e893f238482ff84225` |
| Direct gluing/functors, `lean.definition@1` | `eb1479a9-fcea-4c9c-9cff-909cc2558566` | `d63d72dc-dc86-4140-aa29-1ac7e034b9ff` | `49ab2e68-6c38-4199-ac05-ab97ccbb07b6`, Reviewer 7792 | `01c4caaacd4649f1b941e4ac9ade8574` |
| Separation/compatibility, `lean.statement@1` | `36556681-7fb9-4a78-b0ae-ea86bc9f55fc` | `512a01e2-842d-4894-858f-36a6781f379f` | `c6ce33ba-bd22-40b1-adb7-057256efe509`, Reviewer 7832 | `9a834e82d5cf4cf59745ec6f397863ec` |

The machine receipts pass Lake build and declaration-kind checks.
They record `proof_accepted = false`: the two statement artifacts do
not prove their propositions, and the construction artifacts are not
exact-proof receipts for those statements. Independent construction
review covers the implemented objects and intrinsic laws.
Worker 1215 authored the representative statements, Worker 633 the two
construction units, and Worker 595 the separation statements. Their
records retain Worker 6's source-audit and interface contributions.
This documentation note supplies no additional mathematical receipt.

## Subsequent verified publications

The following seven candidates are independently approved without
qualifications, accepted and public, with published integrations. Their
fourteen frozen Lean/Markdown hashes agree with the workspace and Library
`d08b5767dba1139a70ed7ebfc0438a31c2587868`. The first three were
published at `4f2e1785a3faf187359b2dcec3c8bdbe4a70e762`, the next
three at `b1c8a5e809be36100da09da81385a7ca6789ae80`, and the final
proof at `d08b5767dba1139a70ed7ebfc0438a31c2587868`. These results
supersede the earlier dated observations that their candidates were pending.

| Source assertion or internal prerequisite | Exact public interface | Coverage |
| --- | --- | --- |
| Original stalk representatives and their common-refinement relation, printed p.34 / PDF40 | `basisStalkRepresentatives : BasisStalkRepresentativesStatement` | Exact proof of all four raw/normalized families, with `rawStalk_representative`, `rawGerm_eq_iff`, `stalk_representative`, and `germ_eq_iff`. [Proof](../../Langlands/Sheaf/Renard/BasisStalkRepresentatives.md). |
| Internal universe transport for the germ construction | `rawLiftJoint`, `presheafLiftJoint`, `sheafLiftJoint`, `presheafReliftJoint`, `sheafReliftJoint` | Actual `ULift` postcomposition, full-faithfulness and the direct up/down relift comparisons; no arbitrary value-lowering functor. [Construction](../../Langlands/Sheaf/Renard/BasisLift.md). |
| Literal support and compact-section set, printed pp.37–38 / PDF43–44 | `germSupport`, `germSupportAmbient`, `compactGermSectionsSet`, `CompactGermSections`, `compactGermSectionsInclusion` | Actual nonzero-value support, its ambient image, compact-support subtype, inclusion and elementary support laws. This unit alone supplies no additive structure on that subtype. [Construction](../../Langlands/Sheaf/Renard/GermSupport.md). |
| Canonical map and naturality square, printed p.36 / PDF42 | `sectionGerms`, `rawGermSheafLiftUnit`, `germSheafLiftUnit`, `germSheafUnit`, `germSheafUnit_eq_relift` | Actual original-section germ maps, lifted-source transformations and identity-source unit at joint value universe, with evaluation, restriction, naturality and relift laws. [Construction](../../Langlands/Sheaf/Renard/GermUnit.md). |
| Zero-germ lemma and corrected image compatibility, printed p.36 / PDF42 | `renardSheafGermSeparation : RenardSheafGermSeparationStatement` | Exact proof of all six raw/normalized zero-separation, equality-detection and target-compatibility families. [Proof](../../Langlands/Sheaf/Renard/SheafGermSeparation.md). |
| Local zero neighborhood and relative support closedness, printed p.37 / PDF43 | `GermSupportClosednessStatement` | Four Prop-valued raw/normalized local-vanishing and relative-closedness targets. [Statement](../../Langlands/Sheaf/Renard/GermSupportClosednessStatement.md). |
| Same local-vanishing and relative-closedness target | `germSupportClosedness : GermSupportClosednessStatement` | Exact proof of the unchanged four-part aggregate, using the actual original germ sections. [Proof](../../Langlands/Sheaf/Renard/GermSupportClosedness.md). |

| Unit and policy | Candidate | Machine receipt | Independent review task and reviewer | Published integration |
| --- | --- | --- | --- | --- |
| Representatives, `lean.proof@1` | `40688f45-caad-428f-adc4-8ecf8cf46916` | `94401b37-a2e0-4f1e-8b0b-f15472293728` | `f208dae3-3b16-4c7d-99b5-421a5dd626c2`, Reviewer 7902 | `c70b87df6e63408aae8f57b798179f19` |
| Universe lifts, `lean.definition@1` | `b348b29f-d4aa-4c09-9ba5-58f3b10855ac` | `f82db741-c6c5-4d6e-bf7f-0dbb86a88a03` | `23db7987-47cc-4097-9c8e-6c85490ed367`, Reviewer 7842 | `e7090b7a81d34ac191042040f75b16d2` |
| Support carriers, `lean.definition@1` | `bf970527-cd04-482c-a129-79c0d6839830` | `58731c8c-bcf1-47f2-aadd-5aa35fccc3dd` | `4a976d69-d004-4d42-9fdb-323453f2205e`, Reviewer 7881 | `9ac11cb40e7b456b9f81c71accc4e2c8` |
| Canonical units, `lean.definition@1` | `965f3370-28d1-4904-9455-f921aad927ca` | `aa54dd07-3d5b-4c8a-b9d6-5b0cb29ca41b` | `8a9074ac-a190-45ed-ac74-847e560de81f`, Reviewer 8011 | `501138ade01e4a84aa5f04f1c4ecae0c` |
| Separation/compatibility, `lean.proof@1` | `61d8d31a-6320-4440-bfa4-cf3063786b3c` | `e406caf0-ed03-44bd-9de9-4334fc0d0db4` | `92d6a4ed-c1cc-43e1-8fc7-6136cbd99065`, Reviewer 8024 | `d2fde485141e4784923d0a0fe9452412` |
| Closedness target, `lean.statement@1` | `d5b49701-e0fe-4e4a-ba1b-774c8640de8a` | `e037c61c-466d-4c86-b159-c222d7af8b4e` | `96496b29-30d2-4404-995f-455a7f83cdb3`, Reviewer 8010 | `6a97fb60bcc04ccd8a1ba263aacc5fee` |
| Local vanishing/closedness, `lean.proof@1` | `76ecb163-9427-4329-a60a-a43dbb24dd4f` | `b6ad76a3-1c32-49d0-b23e-77e31abc46c1` | `4fa2b159-abad-451d-ba0d-5f00563728c7`, Reviewer 8120 | `4f298988309c41acb0d1ed36a7d541de` |

The three proof receipts pass Lake-build, exact-target, unchanged-statement
and frozen-input checks. Definition and statement receipts pass their
respective build/declaration checks; the statement receipt alone proves
none of its propositions. Workers 595, 947, 865, 1215, 595, 633
and 633 respectively supplied the seven units, with the recorded
source-audit, design and coauthor contributions retained.

The representative proof uses preservation of the actual filtered
abelian-group colimit by the forgetful functor, then Mathlib's concrete
representative and equality criteria. Returned representatives and
restriction equalities stay in the original value universe. Separation
uses that smaller-neighborhood criterion and the literal sheaf uniqueness
clause. Corrected compatibility separates only the image sections in the
target sheaf, on every smaller common basis open. It never infers the
false source equality (II.2.1.3).

The unit sends an original section to its actual family of original germs.
Its lifted-source version applies `ULift.down` before that map. The direct
unit has identity source only in `Presheaf.{u,max u v} B`; its relation to
the lifted version uses the published up/down relift isomorphism.
The original `v`-valued category and the germ category need not coincide.
These constructions establish neither an adjunction nor a right adjoint
to universe lifting.

The support proof follows the printed local argument. At a zero stalk
value, a local original representative has zero germ. The published
`rawGerm_eq_iff` gives a smaller contained basis neighborhood where that
representative restricts to zero. The same germ section vanishes
throughout that neighborhood, so its zero locus is open in the domain
subtype. Thus `IsClosed (germSupport s)` concerns `Set U`, with no
ambient-closedness assertion for an arbitrary open `U`. The proof needs
no sheaf or separation premise on the raw source. It preserves independent
space/value universes and all empty cases.

## Corrected descent and compact groups: verified publication update

The following two candidates now have unqualified independent approval,
`accepted = true`, `public = true`, and published integrations at
`6fd0709bd33fa6c33b4d74b4b638cfc51428b8f1`. Their four frozen
Lean/Markdown hashes match the workspace and current Library
`45b8890c39a1eaa111f12f5622b8669b0c46b552`. These publications
supersede the preceding dated observations that descent was pending
and that the compact task had no candidate.

| Unit and policy | Candidate | Machine receipt | Independent review task and reviewer | Published integration |
| --- | --- | --- | --- | --- |
| Corrected original-target descent, `lean.definition@1` | `571ce343-0892-44bb-809b-8b9c321a037c` | `e837dc05-70bb-48ed-8096-22fd2738d3ab` | `4ac2507a-7ca3-424d-b756-23aa1a853366`, Reviewer 8142 | `18f6f55b7f75404dabebad6410f8836d` |
| Compact germ-section groups/maps, `lean.definition@1` | `14f25ce9-b4ee-4ca8-b0b2-8ba152d7618c` | `d8dca1ec-7c15-4090-9688-c07e43c183e4` | `83910729-f130-485c-86b3-a130dbd9577c`, Reviewer 8180 | `1fcb37e3e82147d09731f71cb3851fb1` |

Both machine receipts pass Lake-build and declaration-kind checks.
They are definition-policy receipts; they supply no exact-proof
receipt for a universal-property statement.

Worker 595 implemented [corrected descent](../../Langlands/Sheaf/Renard/GermDescent.md)
over Worker 6's source diagnosis and universe design. For an arbitrary
raw source and a target basis sheaf, `rawGermDesc` glues the images of
local original-section representatives into original target sections.
Its representative, empty, additive and restriction laws concern
those actual values. Compatibility uses separation only in the target
on every smaller basis open. The normalized `liftedGermDesc` targets
the actual `sheafLiftJoint`; `germDesc` has a direct target when
original values already lie in `max u v`. Their factorization
equations use the published units, and their pre/postcomposition and
up/down relift laws use the actual morphisms. The complete declaration
probe was recompiled at this update with zero errors and warnings,
receipt `db7fcc6a-d59f-48e6-9fdd-dc55a53c4419`. These constructions
do not yet supply universal uniqueness or an adjunction.

Worker 865 implemented [compact germ-section groups and maps](../../Langlands/Sheaf/Renard/CompactGermSections.md)
from Worker 6's specification and compactness route.
`compactGermSectionSubgroup` has exactly the existing literal
`compactGermSectionsSet` carrier; `compactGermSectionsAddCommGroup`
installs its inherited group on the unchanged `CompactGermSections`
subtype. The inclusion is the existing function, bundled as an
injective additive map. `compactGermSectionsMap` restricts the actual
`germSectionsMap`, with literal original-stalk evaluation, inclusion,
identity and composition laws. Compactness of a sum or image uses
both support containment in a compact set and closedness of the
resulting support in the actual domain. Independent `u` and `v`,
arbitrary raw inputs, bases, opens and empty cases are retained,
without Hausdorffness or source sheaf assumptions.

## Fixed-open compact functors: verified publication update

Candidate `2801770d-7cd1-4db5-b3d6-cfc0e6df9921`, under
`lean.definition@1`, has unqualified independent approval by Reviewer 8208
in review task `29597c1b-0312-4373-aaf9-8020d1ef5ecf`, machine receipt
`10273c40-a446-4422-a471-ddccf8ec12d5`, `accepted = true` and
`public = true`. Published integration
`619ba428a4e7492195a3a0d060090c60` is at
`bcd3de2ace8b14d5d06939a5afe3ca7742cba169`. The machine receipt
passes Lake-build and declaration-kind checks; it is a definition-policy
receipt. The full independent review and current implementation pair
were read. The two frozen functor-file hashes and the two included
group/map dependency hashes agree with their publication commit, current
Library `57db2a24f5ca3ef2b6636a0f07dbb2de422e7bf1` and the workspace.

Worker 865 implemented the
[fixed-open compact germ-section functors](../../Langlands/Sheaf/Renard/CompactGermSectionFunctor.md)
from Worker 6's source audit and specification. For every fixed actual
open `U`, `rawCompactGermSectionsFunctor B U` sends the actual raw
presheaf `F` to `AddCommGrpCat.of (CompactGermSections F U)` and
an actual morphism `φ` to `compactGermSectionsMap φ U`. The
unrestricted companion `rawGermSectionsFunctor` uses the same
`GermSections` and `germSectionsMap` as the preceding construction.
Identity and composition follow from those maps' published laws.
`rawCompactGermSectionsNatInclusion` bundles the unchanged injective
additive inclusion, with naturality and literal section/point formulas.
At `x : U`, the compact functor's map has value
`rawStalkMap φ x.val (s.val.val x)`.

`compactGermSectionsFunctor` and `basisSheafCompactGermSectionsFunctor`
are the restrictions along the actual `presheafInclusion` and
`sheafForget`; their unrestricted companions and natural inclusions
use the same composites and whiskering. Their object and map formulas
expose the existing raw objects and morphisms. The space and original
value universes remain independent, the codomain is
`AddCommGrpCat.{max u v}`, and the topology, basis, fixed open and raw
inputs are arbitrary, including empty cases. These functors retain the
literal support and the relative-closedness compactness argument.

Fresh inspection of child task
`e265849a-2e29-40fb-821b-53c7c68cccee` revision 1 confirms `done`
with closed declaration `fca0fe86-0b29-4d10-a2b4-355ab718a0c4`.
Its unchanged objective is covered by the group/map and functor
publications `14f25ce9-b4ee-4ca8-b0b2-8ba152d7618c` and
`2801770d-7cd1-4db5-b3d6-cfc0e6df9921`; Worker 633's completion
feedback records no unmet condition. The closure record is task evidence;
independent mathematical approval comes from the separate reviews.
This closes the focused germ-model construction child. The original
PDF pp.43–44 and supplementary errata PDF pp.2–3 were reread for
this update: the source identifies a sheaf with its germ model before
defining compact sections. The raw-presheaf functors are derived
packaging and do not prove that original-section identification.

## Remaining work and ownership

Universal-property statement task
`426f976c-c5ec-45bd-9465-216caebd724e` revision 1 is assigned to
Worker 1215 and subscribed by the parent. It covers direct/lifted
factorization uniqueness, explicitly characterized natural Hom
equivalences, and the direct adjunction at value `max u v`.
Task publication supplies no accepted statement or proof; the parent
retains exact-proof routing after actual statement publication.
Unit invertibility on sheaves and the basis/all-open equivalence
retain separate statement and proof obligations.

The fixed-open functor publication and child closure supersede the
preceding pending-functor observation. Ordinary restriction to an
arbitrary smaller open need not preserve compact support; these
functors fix the domain open while varying the source object.

The separate all-open clopen zero-extension task
`f0949ea8-6ee5-4fdf-9f55-3010fd466169` retains Worker 1038's
ownership. Original-section comparison, II.2.4 compact-open exhaustion,
scalar-sheaf/module comparisons, and comparison with Mathlib's all-open
stalk/sheaf categories remain separate. This note declares no II.2.1,
Chapter II or whole-book completion.
