# Local class-field theory: constructions and statement coverage

This note maps the actual local-field, Galois, norm and quotient constructions
and the local class-field-theory proposition families to Library declarations,
original sources and dependencies. The statement families are `Prop`-valued
definitions. Their publication supplies theorem targets, not proofs of local
class-field theory or a selected canonical reciprocity map. The eleven statement
families below and their paired source documentation were checked in Library
commit `bfd2c6b428660be7889841323ce92565132580bb`.

Declarations are in the namespace `Langlands.LocalClassField` unless they
are written as `T.name`. In that case they are in
`Langlands.PadicField.TopologicalData` and take the supplied local-field data
`T : F.TopologicalData` of `F : PadicField p`. Names beginning with `Weil.`
are in `Langlands.Weil`. Each module's paired Markdown gives its exact
sources, conventions and proofs of intrinsic certificates.

## Modules

| Module | Content |
| --- | --- |
| [`Langlands.ClassFieldTheory.Local.Units`](../../Langlands/ClassFieldTheory/Local/Units.md) | Multiplicative topology, units, principal units, unit filtration, unit quotients, normalized order and valuation quotient |
| [`Langlands.ClassFieldTheory.Local.Norms`](../../Langlands/ClassFieldTheory/Local/Norms.md) | Field norms on units, norm images, norm quotients and tower maps |
| [`Langlands.ClassFieldTheory.Local.Galois`](../../Langlands/ClassFieldTheory/Local/Galois.md) | Topological abelianization maps, finite abelian extensions in the closure, restrictions, profinite absolute-Galois abelianization |
| [`Langlands.ClassFieldTheory.Local.Completion`](../../Langlands/ClassFieldTheory/Local/Completion.md) | Completion along open finite-index subgroups and its dense map |
| [`Langlands.ClassFieldTheory.Local.FiniteArtin`](../../Langlands/ClassFieldTheory/Local/FiniteArtin.md) | Finite norm-residue relations, finite transfer, finite norm/transfer compatibility, character transport |
| [`Langlands.ClassFieldTheory.Local.WeilAbelianization`](../../Langlands/ClassFieldTheory/Local/WeilAbelianization.md) | Topological abelianization of the Weil pullback, degree, inertia, unramified quotient |
| [`Langlands.ClassFieldTheory.Local.Transfer`](../../Langlands/ClassFieldTheory/Local/Transfer.md) | Continuous transfer, nested subgroups, fixing subgroups in the Galois group and the Weil pullback |
| [`Langlands.ClassFieldTheory.Local.ResidueNormalization`](../../Langlands/ClassFieldTheory/Local/ResidueNormalization.md) | Geometric Frobenius modulo inertia and finite-level geometric normalization |
| [`Langlands.ClassFieldTheory.Local.ReciprocityRelations`](../../Langlands/ClassFieldTheory/Local/ReciprocityRelations.md) | Single-field candidates, normalization, existence, character transport, relative norm/transfer squares |
| [`Langlands.ClassFieldTheory.Local.ReciprocitySystem`](../../Langlands/ClassFieldTheory/Local/ReciprocitySystem.md) | Families over all finite intermediate fields, coherence, normalization, existence and uniqueness |
| [`Langlands.ClassFieldTheory.Local.ReciprocitySystemStatement`](../../Langlands/ClassFieldTheory/Local/ReciprocitySystemStatement.md) | Published unconditional existence and uniqueness targets specialized to the actual geometric residue degree and canonical extension data |

The layout task "Consolidate local class-field modules under one topic
hierarchy" (task `295b0f1c`, Worker 63) moved the first seven modules from
`Langlands/LocalClassField/` to `Langlands/ClassFieldTheory/Local/`. The move
was first published at Library commit
`8728166c7a3a18d2d8347cd6c907cc2226768605`. It changed module paths only:
declaration names are unchanged, so the namespace `Langlands.LocalClassField`
used below is still correct. Each old module `Langlands.LocalClassField.X`
remains as a declaration-free re-export of `Langlands.ClassFieldTheory.Local.X`.
The old-to-new module table and the declaration-preservation ledger are in
the [migration ledger](../../Langlands/ClassFieldTheory/Local/Completion.md#topic-hierarchy-migration-ledger)
of the canonical `Completion` documentation.
New imports should use the canonical paths above.

## Required objects and their declarations

**Local fields and topology.** The fields are the Library's `PadicField p`
for every prime `p`, with supplied `TopologicalData` or the constructed
`PadicField.canonicalTopologicalData`. No new field structure is introduced.

**Multiplicative group, valuation units and principal units** (`Units`):
`T.multiplicativeTopology`, `T.valuationRing`, `T.unitSubgroup`,
`T.principalUnitSubgroup`, `T.integerUnitsEquiv`, `T.integerUnitsInclusion`,
`T.integerUnitsInclusionContinuous`, `T.residueUnits`,
`T.principalUnitsEquiv`.

**Unit filtration and quotients** (`Units`): `T.TruncatedIntegers`,
`T.truncatedReduction`, `T.truncatedUnitsReduction`,
`T.truncatedUnitsReductionContinuous`, `T.congruenceUnits`,
`T.unitFiltration`, `T.UnitQuotient`, `T.unitQuotientProjection`,
`T.unitQuotientReduction`, `T.unitQuotientProjectionContinuous`,
`T.unitQuotientReductionContinuous`.

**Valuation quotient** (`Units`): `T.orderHom`, `T.ValuationQuotient`,
`T.valuationQuotientProjection`, `T.valuationQuotientProjectionContinuous`.

**Norm maps, norm images and quotients** (`Norms`): `normUnits`,
`normSubgroup`, `normToImage`, `NormQuotient`, `normQuotientProjection`,
`normQuotientTowerProjection`, `normQuotientTowerNorm`; for local fields
`localInclusion`, `localNorm`, `localNormSubgroup`, `LocalNormQuotient`,
`localNormQuotientProjection`, `localNormQuotientTowerProjection`,
`localNormQuotientTowerNorm`. The norm is Mathlib's `Algebra.norm`.

**Finite abelian extensions and Galois groups** (`Galois`):
`FiniteAbelianExtension` with `field`, `galoisGroup`, `finiteGroup`,
`fixingOpenSubgroup`, `restriction`, `abelianRestriction`,
`restrictionOfLE`, `asPadicField`; `LocalFiniteAbelianExtension`.
The extensions are intermediate fields of Mathlib's `AlgebraicClosure`.

**Abelianizations with quotient topologies** (`Galois`,
`WeilAbelianization`): `abelianizationHausdorff`, `abelianizationProjection`,
`abelianizationLift`, `abelianizationLiftEquiv`, `abelianizationMap`,
`quotientNonarchimedean`; `absoluteAbelianizationProjection`,
`absoluteGaloisNonarchimedean`, `absoluteAbelianizationProfinite`,
`absoluteAbelianizationMap`, `localAbelianGaloisGroup`,
`localAbelianGaloisProjection`; `WeilQuotients.Abelianization`,
`WeilQuotients.projection`, `WeilQuotients.degree`,
`WeilQuotients.toGroupAbelianization`, `WeilQuotients.map`,
`localPullbackAbelianization`, `localPullbackToGalois`. These reuse
Mathlib's `TopologicalAbelianization` and the Library's `Weil.Pullback`.
The Weil abelianization is not identified with the compact Galois
abelianization; `WeilQuotients.toGroupAbelianization` is only a continuous
map.

**Unramified quotient** (`WeilAbelianization`): `WeilQuotients.inertia`,
`WeilQuotients.inertia_eq_image`, `WeilQuotients.UnramifiedQuotient`,
`WeilQuotients.unramifiedProjection`, `WeilQuotients.unramifiedDegreeEquivRange`,
and `WeilQuotients.unramifiedDegreeEquiv`, which takes surjectivity of the
degree map as a hypothesis. For the actual local Weil group the hypothesis
is the published `Weil.Local.localDegree_surjective F`, so the term
`WeilQuotients.unramifiedDegreeEquiv (Weil.Local.localResidueDegree F)
(Weil.Local.localDegree_surjective F)` identifies its unramified quotient
with the discrete integers `Weil.Degree` without further assumptions. This
term compiles, but it is not a named Library declaration.

**Completion and density** (`Completion`): `ContinuousProfinite.OpenFiniteQuotient`
with `Quotient`, `quotientDiscrete`, `projection`, `comap`, `quotientMap`;
`ContinuousProfinite.QuotientProduct`, `diagonal`, `imageClosure`,
`Completion`, `completionCompact`, `profiniteGroup`, `eta`, `eta_dense`,
`projection`, `productMap`, `map`; `LocalMultiplicative.profiniteCompletion`,
`LocalMultiplicative.completionMap`, `LocalMultiplicative.completionMap_dense`.
The completion uses only open finite-index subgroups of the given topology.
It is a different carrier from the noncompact group `Fˣ`.

**Finite-level norm-residue and Artin relations** (`FiniteArtin`):
`FiniteArtinFamily`, `FiniteNormResidueRelation`,
`FiniteArtinRestrictionRelation`, `FiniteArtinSystemRelation`,
`finiteFamilyOfHom`, `ProfiniteNormResidueRelation`, `finiteNormQuotientMap`,
`finiteNormResidueEquiv`.

**Finite-level geometric normalization** (`ResidueNormalization`):
`ResidueNormalization.geometricFrobeniusClass`,
`ResidueNormalization.HasGeometricResidueAction`,
`ResidueNormalization.GeometricNormalization` with its residue, uniformizer
and unit consequences, and the specializations in
`ResidueNormalization.Canonical` for every finite extension of `Q_p`.

**Transfer and compatibility in the correct directions** (`FiniteArtin`,
`Transfer`, `ReciprocityRelations`, `ReciprocitySystem`): finite
`finiteTransfer`, `finiteAbelianTransfer`, `finiteFixingGroupEquiv`,
`finiteGaloisInclusion`, `finiteGaloisAbelianInclusion`,
`finiteGaloisAbelianTransfer`, `FiniteNormCompatibility`,
`FiniteTransferCompatibility`; continuous `continuousTransfer`,
`transferToAbelianization`, `abelianizedTransfer`, `subgroupInclusion`,
`subgroupOfEquiv`, `subgroupAbelianInclusion`, `subgroupAbelianTransfer`,
`absoluteFixingFiniteIndex`, `absoluteTransferToFixing`,
`absoluteFixingAbelianInclusion`, `pullbackFixingSubgroup`,
`pullbackFixingSubgroup_open`, `pullbackFixingFiniteIndex`,
`pullbackTransferToFixing`, `pullbackFixingAbelianInclusion`; relations
`AbsoluteNormRelation`, `AbsoluteTransferRelation`, `WeilNormRelation`,
`WeilTransferRelation`, `RelativeWeilReciprocityRelation`. The field norm
corresponds to inclusion of abelianized groups and field inclusion to
transfer.

**Single-field reciprocity interfaces** (`ReciprocityRelations`,
`ReciprocitySystem`): `WeilReciprocityCandidate` (continuous isomorphisms
`W_F^ab → Fˣ`), `candidateGaloisHom`, `GeometricOrderRelation` (geometric
Frobenius corresponds to a uniformizer), `LocalReciprocityCandidateRelation`,
`CompletionComparisonRelation`, `LocalReciprocityExistence`,
`LocalReciprocityUniqueness`.

**Reciprocity systems** (`ReciprocitySystem`): `FiniteIntermediateExtension`
with `asPadicField`, `conj`, `unitsConjugation`, `unitsInclusion`,
`unitsNorm`, `galoisInclusion`, `galoisAbelianInclusion`,
`galoisAbelianTransfer`, `weilInclusion`, `weilAbelianInclusion`,
`weilAbelianTransfer`, `conj_mem_pullbackFixingSubgroup`, `weilConjugation`,
`weilAbelianConjugation`, `weilDegree`, `weilGaloisProjection`,
`weilGaloisAbelianProjection`; `CommonClosure.CandidateFamily`, `galoisHom`,
`NormRelation`, `TransferRelation`, `ConjugationRelation`,
`DensityRelation`, `CompletionRelation`, `CoherentFamilyRelation`,
`CoherentFamilyExistence`, `NormalizationRelation`,
`NormalizedSystemRelation`, `NormalizedSystemExistence`,
`NormalizedSystemUniqueness`, `canonicalData`.

**Character transport** (`FiniteArtin`, `WeilAbelianization`,
`ReciprocityRelations`): `NormTrivialCharacter`, `normQuotientCharacterEquiv`,
`characterTransport`, `finiteArtinCharacterEquiv`,
`WeilQuotients.characterDescent`, `weilCandidateCharacterEquiv`. Transport
along a reciprocity candidate is conditional on an explicitly supplied
candidate and never uses a section into the nonabelian Weil group.

## Actual reciprocity systems and their scope

- **Actual degree and published system specialization.** The generic
  reciprocity interfaces take the residue-degree map `φ` explicitly.
  The constructed geometric degree is
  `Langlands.Weil.Local.localResidueDegree F` in
  [`Langlands.Weil.Local.Assembly`](../../Langlands/Weil/Local/Assembly.md).
  Its pullback is the actual `Weil.Local.localWeilGroup F`. The published
  [`ReciprocitySystemStatement`](../../Langlands/ClassFieldTheory/Local/ReciprocitySystemStatement.md)
  supplies `CommonClosureReciprocityExistence`,
  `CommonClosureReciprocityUniqueness` and their conjunction
  `CommonClosureReciprocityTheorems`. They specialize the system relation
  to `φ := Weil.Local.localResidueDegree F` and
  `S := CommonClosure.canonicalData F`, and quantify every prime, finite
  p-adic base field and compatible base `T`. All finite intermediate fields
  in the chosen closure are included, including nonnormal ones. The degree
  remains the degree over `F` on every fixing subgroup.
- **Statement and proof boundary.** The system existence target concludes
  that a family satisfies the actual norm, transfer, conjugation, density,
  completion and geometric absolute-value relations; it does not assume
  such a family. The uniqueness target compares any two such families.
  These are independently reviewed, published proposition definitions.
  Proofs of these targets remain later work. The generic single-field
  interfaces above remain distinct from an actual-degree theorem target;
  the separate `WeilReciprocityTheorems` family below addresses the actual
  single-field formulation.
- **Canonical reciprocity map.** No canonical reciprocity map is defined. Its
  construction is a downstream obligation, which can be met only after the
  existence and uniqueness theorems are proved and published.
- **Comparisons not made here.** The fixing subgroups in a common closure
  are not identified with separately presented absolute Galois or Weil
  groups of the intermediate fields. Independence of the choice of closure
  is not addressed. Tate's condition (W4), the inverse-limit property of
  the Weil group itself, is not part of these relations.
- **No separate norm-residue condition in systems.** `NormalizedSystemRelation`
  has no finite norm-residue clause. The `ReciprocitySystem` Markdown gives
  an informal argument that, for the actual degree map and canonical data,
  the norm squares already force exact norm kernels and hence uniqueness.
  That argument is not proved in Lean.

## Local CFT theorem-statement families

All names in the first column are in `Langlands.LocalClassField`; the module
prefix is `Langlands.ClassFieldTheory.Local`. Each linked Markdown file gives
the precise Lean quantifiers, source locators, convention translation and
provenance. In the table, page numbers before the slash are the printed pages;
PDF numbers count from one in the retained originals.

| Family and declarations | Module | Original source | Actual objects and dependencies | Publication |
| --- | --- | --- | --- | --- |
| `NormGroupTheorems`: `FiniteNormProperties`, `NormSubgroupExistence` | [`NormStatement`](../../Langlands/ClassFieldTheory/Local/NormStatement.md) | Serre XIII.4 Prop.9, p.196/PDF201; XI.4 Props.3-4, pp.172-173/PDF178-179; XIV.6 Thm.1, p.218/PDF223 | Actual determinant norm, finite extensions, open finite-index subgroups, actual finite abelian intermediate extensions | Published statement |
| `NormCorrespondenceProperties`: `NormSubgroupLattice`, `NormSubgroupsSeparatePoints` | [`NormCorrespondenceStatement`](../../Langlands/ClassFieldTheory/Local/NormCorrespondenceStatement.md) | Serre XI.4 Prop.4, pp.172-173/PDF178-179; XIV.6 Cor.2, p.219/PDF224 | Actual norm images, composita/intersections of finite abelian intermediate fields, subgroup lattice | Published statement |
| `RelativeNormCompatibility`: `RelativeAbsoluteValueLaws`, `RelativeNormOrderLaws` | [`NormCompatibilityStatement`](../../Langlands/ClassFieldTheory/Local/NormCompatibilityStatement.md) | Serre I.4 pp.14-15/PDF22-23; II.1-2 pp.26-30/PDF34-38, II.5 p.36/PDF44; Tate 1.4.6 p.7/PDF16; derived normalized formulations | Spectral norms, normalized absolute values, integer orders, actual algebra maps and determinant norms | Published statement |
| `FiniteAbelianReciprocityTheorems`: `FiniteAbelianReciprocity`, `FiniteAbelianNormTransfer`, `FiniteAbelianRestriction` | [`FiniteReciprocityStatement`](../../Langlands/ClassFieldTheory/Local/FiniteReciprocityStatement.md) | Serre XIII.4 Props.8,10,12,13, pp.196-198/PDF201-203; VII.8 Props.7-8, p.121/PDF127 | Actual finite norm quotient, finite abelian Galois groups, norm/inclusion and transfer directions, geometric residue normalization | Published statement |
| `UnitNormTheorems`: `UnramifiedUnitNorms`, `UnramifiedNormMembership`, `UnramifiedCyclicNormQuotient`, `UnramifiedNormCharacterCriterion`, `AbelianUnitNormIndex` | [`UnitNormStatement`](../../Langlands/ClassFieldTheory/Local/UnitNormStatement.md) | Serre V.2 Props.1-3, pp.81-82/PDF88-89; XIII.4 pp.196-198/PDF201-203 | Actual unit congruence groups, norm, residue degree, unramified finite extensions; independent base/extension universes | Published statement |
| `ProfiniteReciprocityTheorems` | [`ProfiniteReciprocityStatement`](../../Langlands/ClassFieldTheory/Local/ProfiniteReciprocityStatement.md) | Serre XI.3-5 pp.169-175/PDF175-181; XIII.4 pp.196-198/PDF201-203; XIV.4 Ex.2 p.214/PDF219; XIV.6 pp.218-219/PDF223-224 | Actual Galois abelianization, finite norm-residue maps, open-finite-quotient multiplicative completion, genuine coset-product transfer | Published statement |
| `FiniteCharacterConductorTheorems`: filtration comparison, inertia/first-lower images, rational Artin-sum equality, levels and unramified/tame criteria | [`FiniteConductorStatement`](../../Langlands/ClassFieldTheory/Local/FiniteConductorStatement.md) | Serre VI.2 pp.100-102/PDF107-109, IV.3 pp.73-76/PDF80-83, XV.2 pp.227-228/PDF232-233; Tate 3.2.6 p.13/PDF22 | Actual finite Galois representation, rational fixed-space conductor, least principal-unit conductor, profinite normalized relation | Published statement |
| `FiniteUpperReciprocityTheorems`: natural/real upper-unit images, unconditional norm levels, finite-character conductor and last detected break | [`UpperReciprocityStatement`](../../Langlands/ClassFieldTheory/Local/UpperReciprocityStatement.md) | Serre IV.3 pp.73-76/PDF80-83, VI.2 p.102/PDF109, XV.2 pp.227-228/PDF232-233 | Genuine inverse Herbrand and upper groups; real nonnegative levels use ceiling; finite abelian quotients | Published statement |
| `WeilReciprocityTheorems`: unique existence, completion, inertia, arbitrary unramified quasicharacters/twists, norm character | [`WeilReciprocityStatement`](../../Langlands/ClassFieldTheory/Local/WeilReciprocityStatement.md) | Tate 1.1-1.4 pp.3-7/PDF12-16, 4.1.3 p.20/PDF29; Serre XI.3-5 and XIV.6 | Actual localResidueDegree, actual Weil pullback and topological abelianization; strong geometric/profinite normalization | Published statement |
| `CommonClosureReciprocityTheorems`: unconditional normalized-system existence and uniqueness | [`ReciprocitySystemStatement`](../../Langlands/ClassFieldTheory/Local/ReciprocitySystemStatement.md) | Tate 1.1 pp.3-4/PDF12-13, 1.4.1/1.4.6 pp.6-7/PDF15-16; Serre XI.3-5, XIII.4, XIV.6 | Every actual finite intermediate field including nonnormal fields, actual norms/inclusions/transfers/conjugation, canonical extension data, actual degree, completion | Published statement |
| `AbsoluteUpperReciprocityTheorems`: actual inertia image, natural/real upper-unit images, arbitrary-quasicharacter conductor levels and detected break | [`AbsoluteReciprocityStatement`](../../Langlands/ClassFieldTheory/Local/AbsoluteReciprocityStatement.md) | Serre IV.3 pp.74-76/PDF81-83; XIII.4 pp.197-198/PDF202-203; XIV.6 p.219/PDF224; XV.2 pp.227-228/PDF232-233; Tate 3.2.6 | Absolute upper intersection over all finite Galois restrictions; its actual abelianized image; literal reciprocity images of character kernels | Published statement |

The norm/residue and reciprocity diagrams use geometric normalization:
the inverse of the image of a uniformizer acts on the residue field by
`x ↦ x^q`. The source comparison explicitly inverts Serre's arithmetic
normalization. Subgroup images, norm kernels and conductors are unchanged
by that inversion.

The finite-conductor family retains the rational Artin sum and compares it
with the existing natural multiplicative conductor after coercion to the
rationals. The real upper-filtration statements use the natural ceiling
only after passage to abelian quotients. They do not assert integral jumps
or eventual triviality for the absolute nonabelian filtration. The absolute
quasicharacter statements use the literal reciprocity image of the character
kernel, without replacing it by a closure or asserting extension of an
infinite-image quasicharacter to the whole profinite Galois group.

## Prerequisite and proof boundaries

Every prime and every finite extension of `Q_p` remains in scope. The
constructed `PadicField.canonicalTopologicalData` supplies a realization for
every field; a parameter `T : F.TopologicalData` is not an unfulfilled
all-fields existence hypothesis. Actual local residue and Weil degree,
finite and absolute upper ramification, unit filtrations, continuous
abelianization and determinant norms are independent constructions reused
by the targets. The common-closure family uses canonical extension data
and arbitrary compatible base data, as described above.

The cohomological prerequisite assignment "Formalize local class formations,
invariant maps and Tate reciprocity statements" (task
`c7513fdc-eb44-48b5-8734-001f18050403`, revision 1) separately
requires genuine coefficient actions and maps, unconditional local
class-formation realization, all-integer Tate cup isomorphisms and the
`n = -2` comparison. It is a coherent published assignment under the host's
permission to decompose substantial prerequisites. Its remaining mathematical
obligations are not counted as published statements here.

Published [`Langlands.ClassFieldTheory.Local.CohomologyExistence`](../../Langlands/ClassFieldTheory/Local/CohomologyExistence.md) states
absolute H1 vanishing and the H2 description by the actual `Q/Z`, together
with relative H1 and the denominator image of the finite invariant map.
`Invariants`, `FundamentalClasses`, `MultiplicativeFormation` and
`InvariantCompatibility` provide data and predicates; they do not by
themselves assert simultaneous unconditional realization of that data.
The full compatible local realization and all-degree Tate cup/functoriality
family remain in that prerequisite assignment. [`TateNormQuotient`](../../Langlands/ClassFieldTheory/Local/TateNormQuotient.md) identifies
degree-zero Tate cohomology of `Lˣ` with the actual norm quotient, and is not
the all-degree Tate reciprocity theorem.

The local residue/inertia, normalization and Herbrand arithmetic families
have their own assignments. The source derivations of the reciprocity targets
use their mathematical conclusions, but these targets do not duplicate their
proofs. In particular, `Langlands.Ramification.Padic.AbsoluteHerbrandArithmetic`
in [`Herbrand.AbsoluteStatement`](../../Langlands/LocalFactor/Ramification/Herbrand/AbsoluteStatement.md)
is an arithmetic statement family; publication
of that target is not a proof of the absolute upper image theorem.

Proofs of the reciprocity, existence, ramification-image and conductor targets
remain separate work. A future selected reciprocity map must follow proved
existence and uniqueness. Comparison with separately presented extension
fields and independence of the closure presentation remain distinct from the
common-closure system theorem. No proof of local CFT or rank-one LLC is claimed
by this statement coverage map.

## Original-source identities

The original sources used here are Serre, *Local Fields*, English translation,
GTM 67 (1979), registered as `serre-1979-local-fields`, and Tate, *Number
Theoretic Background*, Corvallis Part II (1979), registered as
`tate-1979-number-theoretic-background`. Their retained SHA256 fingerprints are
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112` and
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`, respectively.
The linked paired Markdown files specify original pages and distinguish direct
source formulations from derived normalizations or consequences. The informal
common-closure uniqueness derivation and absolute kernel-image conductor
derivations are documented as derivations, not implemented Lean proofs.
