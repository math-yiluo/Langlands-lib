# Renard II.2.1: published germ families and statement boundaries

Worker 6, 1 November 2026.

Four focused units are independently accepted and published: the stalk
representative statements, locally represented germ groups and their maps,
direct gluing and sheaf functors, and the separation and corrected
target-compatibility statements. Two units supply constructions with their
intrinsic laws; two supply proposition definitions whose exact proofs remain
separate. This note records those distinctions and updates the
[whole-book coverage ledger](coverage.md).

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, II.2.1, printed pp.33–37 /
PDF pp.39–43, registered as
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

## Remaining work and ownership

The exact representative proof has task
`d16ae635-047f-4a69-acaf-fafe7da806ce` revision 1. At Worker 6's
direct check, candidate `40688f45-caad-428f-adc4-8ecf8cf46916`
passed machine Lake-build, exact-target, unchanged-statement and
frozen-input checks, but remained staged, unaccepted and nonpublic.
That candidate is excluded from the published count. The separate
separation-proof task
`a8dd4ece-f292-4ab5-8b2b-f4f5547440e5` revision 1 formally requires
publication of the representative proof.

Actual source-universe lifting belongs to task
`8f1f081b-0e4e-4bdc-adcf-0edc88c5afea` revision 1, Workers 947
and 1038. Canonical germ maps and natural units have task
`397a30ad-c817-468f-9f69-a379cbf3b64e` revision 1, requiring that
lift's publication. The original `v`-valued category and the germ
functor's `max u v`-valued category differ. A natural transformation
from the original object must use an actual lift to a common
codomain. A same-category adjunction can be formulated separately
at value universe `max u v`; these four publications establish
neither that adjunction nor a right adjoint to universe lifting.

Corrected descent, universal factorization, the actual Hom equivalence
and adjunction, unit invertibility on sheaves, and the basis/all-open
equivalence still require their focused constructions, statements and
proofs. No topology on the disjoint stalk union or comparison with
Mathlib's all-open stalk/sheaf categories is asserted here.

For II.2.2, Worker 865 retains support task
`14c42d15-028c-46b7-9243-8ccfa71d0de2`. Relative-closedness statement
task `60504f8d-38d8-4368-aa23-9f02f76ffe26` revision 1 explicitly
requires its support construction to be published. Its later exact
proof will also require the representative proof. Compact-section
structures, clopen zero extension, II.2.4 exhaustion and scalar-sheaf
comparisons remain separate. This note declares no II.2.1, Chapter II
or whole-book completion.
