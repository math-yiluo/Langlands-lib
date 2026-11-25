# Local Weil and Weil–Deligne statements: declaration coverage

This note maps the statement families of the local Weil and Weil–Deligne
theorem-statement framework to Library declarations. Every listed target is a `Prop`-valued
definition. None is a theorem unless the "Proofs" section names a proof module.
Each module's paired Markdown gives the declaration-level source locators,
the derivations of non-verbatim clauses and the dependency hashes.

## Conventions shared by all modules

- Geometric Frobenius has degree `+1`, and the norm satisfies `ν(Φ) = q⁻¹`.
- Special blocks are uncentered: `S_m` has weights `ν^j` for `0 ≤ j < m`,
  monodromy raises `j`, and `ker N` is the top weight `ν^(m-1)`.
- The dual pair is `(r^∨, −Nᵀ)`, and `(σ ⊗ S_m)^∨ ≅ (σ^∨ ⊗ ν^(1-m)) ⊗ S_m`.
- Frobenius semisimplicity does not imply `N = 0`. Ordinary semisimplicity of
  a pair is `N = 0` together with semisimplicity of the Weil representation.
- Continuity bridge (`RepresentationContinuity`): fix a topological group `W`
  and an open subgroup `I` that is compact and nonarchimedean, such as the
  profinite inertia of a local Weil group. For a finite-dimensional complex
  representation with its usual topology, continuity ⟺ open inertia kernel ⟺
  finite inertia image together with closed inertia kernel. The nonarchimedean
  hypothesis is needed. For example, `W = S¹ × ℤ` with `I = S¹ × {0}`, acting
  on `ℂ` through `S¹`, is continuous with infinite inertia image. Finite inertia
  image alone does not give continuity either.

## Exact versions

All rows below refer to the Library snapshot at commit
`18fac9a1ce0cc1ae5ed2c754ff093194569c18e3` (2026-10-20). Each module is
identified by the SHA-256 of its Lean file and its paired Markdown.

| Module | Lean SHA-256 | Markdown SHA-256 |
| --- | --- | --- |
| `Weil/Representation/Continuity` | `eee2597523d9d1d9a295004aa895361618ece11bf8b6547b9ee5cefa48fd62ab` | `14b3d17fed09138b9f5ef6f11d5e354297933a0a06eb8c0b4260c69e76d339fa` |
| `Weil/Representation/ContinuityBridgeStatement` | `b4a1097153b56888d7bf4e57a1b67abc7829e0293ece673959b976a79440ed4e` | `47a98aea45b2a0971c7447b31895acbb3bab88ef041e09b176cc209dec8f8c7f` |
| `Weil/Representation/Structure` | `c692c4ee4aa3aa30cb100463154a0b5a5aca75291b8b1c0b4342c78a24ed75ab` | `ee54cfd7eeb0f56b084edc97879ee59c2af02fbfa3427e5589321dda03f8939a` |
| `Weil/Representation/Operations` | `283dddd18a7022d99ba6e7ab4a2b497053f48582996fe4c9502826f994836dd9` | `03606e2aecb33f39ed50f5fab65315ec8a5fea1589f21608bfe60f34ee9e8352` |
| `Weil/Representation/UnitaryStatement` | `4b84f940514bc9e0c50a64d2381b4725a0747090995723ce37d8ae23f661e1ad` | `ed2824f9fc03078ea893082b2c8f8fe7dabdec64804c9dc5943c1fdbf9dca0db` |
| `Weil/Representation/RestrictionInduction` | `a26a26746ad00baf008b56c2e0b7d09964458dbfed61cc7b67337ce1484cef15` | `26ed35b3ab2adc03af6744244a123ce969ea10f301d8c1a181c4934c7921baeb` |
| `WeilDeligne/LinearAlgebraStatements` | `31dab68f45eca19af6533a9ae09933e55a974a4027c20c990b066f07fc42eddc` | `f652112f152961ef7247c0345b6a712ccf62ea2941ead3ec1f85bfe56b608f69` |
| `WeilDeligne/FrobeniusStatements` | `1fb0329d6d33b89fec0770e8e97058265c82526e671ccf19b01c8218ee3ae5aa` | `241c27a5bd9d8f23b59a017443a9d195a379db4f7ee4f9cb058e71ebc85023f5` |
| `WeilDeligne/OperationStatements` | `acfaa88b6e9073af019b74dedc2ffde341e581186b30831040e3dbbdc0b395fe` | `c616ef86f27f56a011704193f64e7373941e8a1fa4e4ea2bba1cf5769a32e86b` |
| `WeilDeligne/ParameterRelationStatements` | `d64c91bcadfaf0a3250250cb1bc1ddfe177ca2a2c91d370eec404d4f2ea87a0e` | `3347b44a6ac06b7546e776a29c09b5b1555710e177357378df5c15c106dade1f` |
| `WeilDeligne/RestrictionInductionStatement` | `c90cc6f473513ae932cb4d7f346f64b01964a00e04a19dc4b70811e0ec03a5b4` | `c02eb1fe919dcf165b586dc838eb44a43b77d2b1dec74b19ca696e57f80d5cb9` |
| `WeilDeligne/BlockStatements` | `2f4ab84697214a1da71331d727f2bbbdbd5e5606e9e8e29621eda10dd756718f` | `5bb4d37397e3dee3657eb99cb99219e91ce7ec1034ed061853712f32ec1c2b89` |
| `Weil/Local/RepresentationStatements` | `882918221b7cdd5f4f3347e553452c1d47cc5d9c6d4a6d64aae0a605d01b297d` | `e3c658c34884c2e8f6cf589b6caed2352eb94d8c1e7512820de7d15b5873b120` |
| `Weil/Local/ExtensionStatements` | `dcfa1419aaa94aa8d49888d63d82ffcae853429e4792e617731fa9b36e12a74a` | `0aed68ae0544e279b0efd74532f1617cc921533a531e3936b3f9b08a652cc95a` |

## Generic targets (arbitrary groups, explicit inertia, degree and norm)

| Family | Declarations | Module |
| --- | --- | --- |
| Continuity bridge | `Langlands.Weil.RepresentationContinuity` | [`Weil/Representation/Continuity`](../../Langlands/Weil/Representation/Continuity.md) |
| Bundled versus normed-carrier continuity | `RepresentationContinuityCompatibility` (proved in `ContinuityBridgeProof`) | [`Weil/Representation/ContinuityBridgeStatement`](../../Langlands/Weil/Representation/ContinuityBridgeStatement.md) |
| Finite image, Galois type, unramified reductions | `UnramifiedReduction`, `FiniteImageExtension`, `RepresentationStructure` | [`Weil/Representation/Structure`](../../Langlands/Weil/Representation/Structure.md) |
| Operations, invariance, rank and determinant, character normalization | `RepresentationIsomorphismInvariance`, `RepresentationRankDeterminant`, `RepresentationExactSequenceInvariants`, `RepresentationOperationClosure`, `RepresentationCharacterNormalization`, `RepresentationOperations` | [`Weil/Representation/Operations`](../../Langlands/Weil/Representation/Operations.md) |
| Unitarity | `Langlands.FiniteRepresentation.UnitaryOperations` | [`Weil/Representation/UnitaryStatement`](../../Langlands/Weil/Representation/UnitaryStatement.md) |
| Weil restriction and induction | `RepresentationRestriction`, `RepresentationInductionFiniteness`, `RepresentationInductionTopology`, `RepresentationInductionReciprocity`, `RepresentationInductionCompatibility` | [`Weil/Representation/RestrictionInduction`](../../Langlands/Weil/Representation/RestrictionInduction.md) |
| WD kernel stability, irreducibility, semisimplicity | `WeilDeligneRepresentation.LinearAlgebra.Statement` | [`WeilDeligne/LinearAlgebraStatements`](../../Langlands/WeilDeligne/LinearAlgebraStatements.md) |
| Frobenius semisimplification: existence, choice independence, relation to semisimplicity | `WeilDeligneRepresentation.Frobenius.Statement` and its components, for example `CorrectionExistence`, `ChoiceIndependence`, `PairUniqueness`, `WeilSemisimplicityComparison` | [`WeilDeligne/FrobeniusStatements`](../../Langlands/WeilDeligne/FrobeniusStatements.md) |
| WD operation laws | `WeilDeligneRepresentation.OperationLaws.Statement`. The version in the Library gives `ParameterPreservation`, `ContinuityPreservation` and `Statement` an explicit `[IsTopologicalGroup G]` binder. An earlier version had declared it as an unused section variable, so it did not bind. | [`WeilDeligne/OperationStatements`](../../Langlands/WeilDeligne/OperationStatements.md) |
| Class-level dual and twist relations for parameters | `WeilDeligneRepresentation.ParameterRelationLaws.Statement` | [`WeilDeligne/ParameterRelationStatements`](../../Langlands/WeilDeligne/ParameterRelationStatements.md) |
| WD restriction and induction | `WeilDeligneRepresentation.RestrictionInductionStatements` (13 conjuncts, including `SemisimplificationDegreeRescaling`) | [`WeilDeligne/RestrictionInductionStatement`](../../Langlands/WeilDeligne/RestrictionInductionStatement.md) |
| Blocks: tensor, dual and twist identities; invariants and kernels; decomposition existence and uniqueness; criteria; Frobenius-semisimple classification; parameter normal form | `WeilDeligneRepresentation.Blocks.Statement` (15 conjuncts) and `Blocks.IsIndecomposable` | [`WeilDeligne/BlockStatements`](../../Langlands/WeilDeligne/BlockStatements.md) |

## Targets on the actual local Weil group

These targets use the constructed `localWeilGroup F` of `F : PadicField p`
(`Weil/Local/Assembly`) and the extension constructors of
`Weil/Local/ExtensionParameters`.

| Family | Declarations | Module |
| --- | --- | --- |
| Continuity, Galois type, unramified correction and twist, character classification and normalization, norm faithfulness | `Langlands.Weil.Local.LocalWeilRepresentationStatements` (9 conjuncts) | [`Weil/Local/RepresentationStatements`](../../Langlands/Weil/Local/RepresentationStatements.md) |
| Hypotheses consumed by the generic Frobenius and block targets | `LocalFrobeniusHypothesesFor` (`NormCompatible` and compact degree kernel). Surjectivity is the proved `localDegree_surjective`, and `localInertia F` is the degree kernel by `rfl`. | same module |
| Restriction and induction along `extensionWeilMap F E f` | `Langlands.Weil.Local.LocalExtensionStatements` (6 conjuncts: preservation and reflection, Frobenius-semisimple parameters, semisimplification with residue-degree rescaling, two-sided reciprocity, operations) | [`Weil/Local/ExtensionStatements`](../../Langlands/Weil/Local/ExtensionStatements.md), on the constructors in [`Weil/Local/ExtensionParameters`](../../Langlands/Weil/Local/ExtensionParameters.md) |

## Using the generic targets at the actual local field

The generic Frobenius and block targets quantify over a degree `d`, a residue
cardinality `q`, `Function.Surjective d`, `NormCompatible d q`, and, for the
normal form, `CompactSpace d.ker`. At `d = (localDegree F).toMonoidHom` and
`q = F.canonicalTopologicalData.residueCardinality`, these inputs are
`localDegree_surjective` and `LocalFrobeniusHypothesesFor`. The latter follows
from `LocalAssemblyProperties` and `residueCardinality_gt_one`. The local Weil
group has the `IsTopologicalGroup` instance of the pullback. Local restatements
of the Frobenius and block targets are therefore unnecessary.

## Proofs

The proofs are in separate modules:
- `RepresentationOperationClosure`: [`OperationClosureProof`](../../Langlands/Weil/Representation/OperationClosureProof.md).
- `RepresentationRankDeterminant`: [`RankDeterminantProof`](../../Langlands/Weil/Representation/RankDeterminantProof.md).
- `RepresentationContinuityCompatibility`: [`ContinuityBridgeProof`](../../Langlands/Weil/Representation/ContinuityBridgeProof.md).
- `UnitaryOperations`: [`UnitaryProof`](../../Langlands/Weil/Representation/UnitaryProof.md).
- `RepresentationContinuity`: [`ContinuityProof`](../../Langlands/Weil/Representation/ContinuityProof.md).
- `RepresentationIsomorphismInvariance`: [`IsomorphismInvarianceProof`](../../Langlands/Weil/Representation/IsomorphismInvarianceProof.md).
- `RepresentationExactSequenceInvariants`: [`ExactSequenceProof`](../../Langlands/Weil/Representation/ExactSequenceProof.md).
- `RepresentationCharacterNormalization`: [`CharacterNormalizationProof`](../../Langlands/Weil/Representation/CharacterNormalizationProof.md).

- `UnramifiedReduction`: [`UnramifiedReductionProof`](../../Langlands/Weil/Representation/UnramifiedReductionProof.md).
- `FiniteImageExtension`: [`FiniteImageExtensionProof`](../../Langlands/Weil/Representation/FiniteImageExtensionProof.md).
- `RepresentationStructure`: [`StructureProof`](../../Langlands/Weil/Representation/StructureProof.md).

## Not covered here

- L-, ε- and γ-identities are not stated here; they belong to the arithmetic
  local-factor statements.
- The local Langlands correspondence assertion is not stated here; it belongs
  to the statement of the correspondence itself.
- Transitivity of local induction in towers is not stated.
- The transfer formula for the determinant of an induced representation is not
  stated, because it needs the reciprocity map.
