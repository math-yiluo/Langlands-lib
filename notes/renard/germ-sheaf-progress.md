# Renard II.2.1–II.2.2: published germ universal property and compact-section functors

This note is dated 2 November 2026.

The initial four focused publications cover the stalk
representative statements, locally represented germ groups and their maps,
direct gluing and sheaf functors, and the separation and corrected
target-compatibility statements. Two modules supply constructions with their
intrinsic laws; two supply proposition definitions. Seven later publications
add the representative and separation proofs, actual universe lifts and
canonical units, literal support carriers, and the relative-closedness
statement and proof. Two further publications now supply corrected
original-target descent and compact germ-section groups and morphism maps.
A further publication supplies the fixed-open compact-section functors
and natural inclusions. The latest statement and exact-proof publications
establish the seven-part germ universal property and actual direct adjunction;
a separate publication states the five-part canonical-unit identification on
sheaves without proving it. This note records their distinct scopes and updates the
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

## In the Library

All four modules first appeared in the Library at
`a5dff2ff93bd3637a67ee8847f67f811efc82f01`. Their eight
Lean/Markdown hashes were checked against that Library and the later
Library `dac2bb9e83346876770fced17af26f0cba7f4c98`; all agree.

| Module | Kind |
| --- | --- |
| Representatives | statement |
| Germ groups/maps | definition |
| Direct gluing/functors | definition |
| Separation/compatibility | statement |

All four pass a Lake build and declaration-kind checks. The two
statement modules do not prove their propositions, and the construction
modules are not proofs of those statements.

## Subsequent modules

The following seven modules are in the Library. Their fourteen
Lean/Markdown hashes agree with Library
`d08b5767dba1139a70ed7ebfc0438a31c2587868`. The first three first
appeared in the Library at `4f2e1785a3faf187359b2dcec3c8bdbe4a70e762`,
the next three at `b1c8a5e809be36100da09da81385a7ca6789ae80`, and the
final proof at `d08b5767dba1139a70ed7ebfc0438a31c2587868`.

| Source assertion or internal prerequisite | Exact public interface | Coverage |
| --- | --- | --- |
| Original stalk representatives and their common-refinement relation, printed p.34 / PDF40 | `basisStalkRepresentatives : BasisStalkRepresentativesStatement` | Exact proof of all four raw/normalized families, with `rawStalk_representative`, `rawGerm_eq_iff`, `stalk_representative`, and `germ_eq_iff`. [Proof](../../Langlands/Sheaf/Renard/BasisStalkRepresentatives.md). |
| Internal universe transport for the germ construction | `rawLiftJoint`, `presheafLiftJoint`, `sheafLiftJoint`, `presheafReliftJoint`, `sheafReliftJoint` | Actual `ULift` postcomposition, full-faithfulness and the direct up/down relift comparisons; no arbitrary value-lowering functor. [Construction](../../Langlands/Sheaf/Renard/BasisLift.md). |
| Literal support and compact-section set, printed pp.37–38 / PDF43–44 | `germSupport`, `germSupportAmbient`, `compactGermSectionsSet`, `CompactGermSections`, `compactGermSectionsInclusion` | Actual nonzero-value support, its ambient image, compact-support subtype, inclusion and elementary support laws. This module alone supplies no additive structure on that subtype. [Construction](../../Langlands/Sheaf/Renard/GermSupport.md). |
| Canonical map and naturality square, printed p.36 / PDF42 | `sectionGerms`, `rawGermSheafLiftUnit`, `germSheafLiftUnit`, `germSheafUnit`, `germSheafUnit_eq_relift` | Actual original-section germ maps, lifted-source transformations and identity-source unit at joint value universe, with evaluation, restriction, naturality and relift laws. [Construction](../../Langlands/Sheaf/Renard/GermUnit.md). |
| Zero-germ lemma and corrected image compatibility, printed p.36 / PDF42 | `renardSheafGermSeparation : RenardSheafGermSeparationStatement` | Exact proof of all six raw/normalized zero-separation, equality-detection and target-compatibility families. [Proof](../../Langlands/Sheaf/Renard/SheafGermSeparation.md). |
| Local zero neighborhood and relative support closedness, printed p.37 / PDF43 | `GermSupportClosednessStatement` | Four Prop-valued raw/normalized local-vanishing and relative-closedness targets. [Statement](../../Langlands/Sheaf/Renard/GermSupportClosednessStatement.md). |
| Same local-vanishing and relative-closedness target | `germSupportClosedness : GermSupportClosednessStatement` | Exact proof of the unchanged four-part aggregate, using the actual original germ sections. [Proof](../../Langlands/Sheaf/Renard/GermSupportClosedness.md). |

| Module | Kind |
| --- | --- |
| Representatives | proof |
| Universe lifts | definition |
| Support carriers | definition |
| Canonical units | definition |
| Separation/compatibility | proof |
| Closedness target | statement |
| Local vanishing/closedness | proof |

The three proofs were checked by a Lake build against the exact target,
with the statement and its inputs unchanged. The definition and statement
modules pass their build and declaration checks; the statement module alone
proves none of its propositions.

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
This unit construction alone supplies no adjunction. The later exact proof
below constructs the direct germ adjunction at the joint value universe;
no right adjoint to universe lifting is asserted.

The support proof follows the printed local argument. At a zero stalk
value, a local original representative has zero germ. The published
`rawGerm_eq_iff` gives a smaller contained basis neighborhood where that
representative restricts to zero. The same germ section vanishes
throughout that neighborhood, so its zero locus is open in the domain
subtype. Thus `IsClosed (germSupport s)` concerns `Set U`, with no
ambient-closedness assertion for an arbitrary open `U`. The proof needs
no sheaf or separation premise on the raw source. It preserves independent
space/value universes and all empty cases.

## Corrected descent and compact groups

The following two modules first appeared in the Library at
`6fd0709bd33fa6c33b4d74b4b638cfc51428b8f1`. Their four
Lean/Markdown hashes match Library
`45b8890c39a1eaa111f12f5622b8669b0c46b552`.

| Module | Kind |
| --- | --- |
| Corrected original-target descent | definition |
| Compact germ-section groups/maps | definition |

Both pass a Lake build and declaration-kind checks. They are
definitions; they prove no universal-property statement.

[Corrected descent](../../Langlands/Sheaf/Renard/GermDescent.md)
follows the source diagnosis and universe design. For an arbitrary
raw source and a target basis sheaf, `rawGermDesc` glues the images of
local original-section representatives into original target sections.
Its representative, empty, additive and restriction laws concern
those actual values. Compatibility uses separation only in the target
on every smaller basis open. The normalized `liftedGermDesc` targets
the actual `sheafLiftJoint`; `germDesc` has a direct target when
original values already lie in `max u v`. Their factorization
equations use the published units, and their pre/postcomposition and
up/down relift laws use the actual morphisms. The complete declaration
probe was recompiled at this update with zero errors and warnings.
These constructions
supply the descent maps used in the later universal uniqueness and
adjunction proof below.

[Compact germ-section groups and maps](../../Langlands/Sheaf/Renard/CompactGermSections.md)
follow the specification and compactness route.
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

## Fixed-open compact functors

The fixed-open compact functors are a definition module that first appeared
in the Library at `bcd3de2ace8b14d5d06939a5afe3ca7742cba169`. It passes a
Lake build and declaration-kind checks. The two functor-file hashes and
the two included group/map dependency hashes agree with that commit and
Library `57db2a24f5ca3ef2b6636a0f07dbb2de422e7bf1`.

The
[fixed-open compact germ-section functors](../../Langlands/Sheaf/Renard/CompactGermSectionFunctor.md)
follow the source audit and specification. For every fixed actual
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

The original
PDF pp.43–44 and supplementary errata PDF pp.2–3 were reread for
this update: the source identifies a sheaf with its germ model before
defining compact sections. The raw-presheaf functors are derived
packaging and do not prove that original-section identification.

## Germ universal property and sheaf-unit statements, 2 November 2026

The following three modules are in the Library. Their six
Lean/Markdown hashes agree with Library
`facdf46f0abfca9e85d49d3a35285c513a96d886` and the later Library
`2c43e36f9ac408fcdef45d79d2ac3b56107609c2`. The sheaf-unit statements
are statements only.

| Module | Kind | First appeared at Library commit |
| --- | --- | --- |
| Germ universal-property statements | statement | `e99c4aa2f6dad3b56082dd8d27ac931e2e18f130` |
| Exact germ universal-property proof | proof | `facdf46f0abfca9e85d49d3a35285c513a96d886` |
| Canonical unit on sheaves, statements only | statement | `facdf46f0abfca9e85d49d3a35285c513a96d886` |

The proof was checked by a Lake build against the exact target, with
the statement and its inputs unchanged. The two statement modules pass
their build and declaration-kind checks and prove none of their
propositions.

The [universal statements](../../Langlands/Sheaf/Renard/GermUniversalStatements.md)
and [implemented proof](../../Langlands/Sheaf/Renard/GermUniversalProof.md)
cover Renard’s proposition and its proof on printed pp.35–37 / PDF41–43.
`germUniversal : GermUniversalStatement` proves all seven conjuncts:
direct and lifted factorization with uniqueness, direct and lifted descent
naturality, direct and lifted natural Hom equivalences, and the actual
direct adjunction. These are propositions about the published germ
functors, canonical units and literal descent maps.

`germSheaf_hom_ext` first shows that local original-section germ families
determine morphisms into a genuine target sheaf. Naturality compares
restrictions on a contained representing basis neighborhood; equality
detection in the target then gives equality of sections. This proves
`germDesc_unique` and `liftedGermDesc_unique`. The actual equivalences
`germHomEquiv` and `liftedGermHomEquiv` use unit precomposition as the
forward map and literal descent as the inverse. Only a morphism between
actual lifted presheaves is lowered in the arbitrary-original-universe
case. Their two inverse laws and source/target naturality are proved.

`germAdjunction` is constructed from the proved direct Hom equivalence
by `Adjunction.mkOfHomEquiv`, which establishes both triangle identities.
The implementation identifies its whole unit with `germSheafUnit`, its
Hom family with `germHomEquiv`, and its counit with
`germDesc (𝟙 G.obj)`. The direct adjunction is at original value universe
`max u v`; the separate lifted Hom equivalence retains arbitrary original
`v`. All supplied topologies, chosen bases, independent space/value
universes and empty cases remain included. The source presheaf is
arbitrary. The proof uses the corrected target-sheaf separation route,
not the invalid source-section equality (II.2.1.3).

This proof does not complete II.2.1.

The first remark on printed p.37 / PDF43 identifies an original sheaf
with its germ model by the canonical map. The new
[sheaf-unit statement pair](../../Langlands/Sheaf/Renard/SheafGermUnitIsoStatements.md)
expresses this separately as
`RenardSheafGermUnitIsoStatement`. Its five parts assert bijectivity of
`sectionGerms` on every basis open, invertibility of the lifted unit,
a lifted natural isomorphism, invertibility of the direct unit, and a
direct natural isomorphism. The natural isomorphisms’ forward maps are
required to be the actual canonical units after forgetting, and their
inverse maps the actual `liftedGermDesc` or `germDesc` of identity.
These are Prop-valued declarations only. The lifted assertions apply
at independent original `v`; the direct assertions use `max u v`.
Neither the statement module nor the universal-property proof proves
this aggregate; the Library proves it separately, as
`renardSheafGermUnitIso` (`Langlands/Sheaf/Renard/SheafGermUnitIsoProof.lean`).

## Remaining work

Canonical-unit invertibility and the specified natural isomorphisms on
sheaves have published statements, proved as `renardSheafGermUnitIso`
(above). The following source paragraph’s basis/all-open category
equivalence is constructed separately, in
`Langlands/Sheaf/Renard/BasisAllOpenEquivalence.lean`.

Ordinary restriction to an
arbitrary smaller open need not preserve compact support; these
functors fix the domain open while varying the source object.

The all-open clopen zero-extension, original-section comparison, II.2.4
compact-open exhaustion, scalar-sheaf/module comparisons, and comparison
with Mathlib's all-open stalk/sheaf categories are outside this note. This note declares no II.2.1,
Chapter II or whole-book completion.
