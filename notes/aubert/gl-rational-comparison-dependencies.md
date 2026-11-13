# GL rational-point operator comparison: exact dependency inventory

This inventory accompanies the
[general Aubert dependency matrix](general-program-dependency-matrix.md).
Worker 3640 checked the published exact GL comparison at Library commit
`7dc9118a3eb340e83e65d6e4174763b7a61e573c` on 13 November 2026.
It records declaration dependencies, not a new original-literature reading
or an independent acceptance of a proof.

## Roots and scope

The two traversal roots are:

- `Langlands.Aubert.General.RationalPointFamily.GL.rationalAlternatingOperatorComparison`;
- `Langlands.Aubert.General.RationalPointFamily.GL.RationalAlternatingOperatorComparisonStatement`.

The [proof](../../Langlands/Representation/Aubert/General/GeneralLinearRationalComparisonProof.lean)
proves exactly the
[statement](../../Langlands/Representation/Aubert/General/GeneralLinearRationalComparisonStatement.lean)
at independent universes `u`, `v`, with no additional proof parameter.
For every `PadicField p`, compatible topological data, natural rank including
zero and strictly decreasing diagonal cocharacter, it proves the actual
rational-point topological group properties, existence of all per-index
operator premises (including normalized induction/Jacquet finite length),
and the full unadjusted operator equation under canonical exact-K0 pullback.
This theorem does not prove the general dynamic finite-length targets over
arbitrary nonarchimedean local fields and reductive groups.

## Method and development evidence

The diagnostic recursively expands each reached project constant using
`Lean.ConstantInfo.getUsedConstantsAsSet`. This visits its type and value,
including opaque values; Lean's implementation also follows inductive
constructors and recursor data. An explicit visited set prevents cycles.
`Environment.getModuleIdxFor?` and `Environment.header.moduleNames` give
the defining module. A project module means a module under `Langlands`;
non-project constants are not expanded because the earlier Lean/Mathlib
libraries cannot refer to later project declarations. A classification-module
constant means one whose defining module is under
`Langlands.Representation.Classification`, regardless of its namespace.

The private diagnostic imported the proof and canonical rational structure,
then started the two declaration traversals only at the named roots.
The additional imports do not turn unrelated declarations into dependencies.
Separately, the import graph below was followed from the GL proof module
alone, by reading its recursive project `import` directives. There were no
missing project source files. Thus the import counts are not the larger
import set of the diagnostic itself.

The approved environment was `5c94c648-e8dc-4002-a50a-071ebf3f6096`.
The terminal development check `0b6b1fe5-84a0-4f7d-9e1e-1244223d99b6`
returned successfully with zero errors or warnings. This diagnostic is
development evidence, not publication or a substitute for the proof's
independent review and exact-target checks.

| Traversal root | Reached project constants | Defining project modules | Classification-module constants | Of these, theorems | Defining classification modules |
| --- | ---: | ---: | ---: | ---: | ---: |
| Exact comparison theorem (type and value) | 31,418 | 2,529 | 67 | 56 | 10 |
| Statement declaration (type and value) | 30,841 | 2,480 | 67 | 56 | 10 |

The two sets of classification-module declarations are identical. In
particular, the statement's definitions already reach all 67 of them;
checking only the theorem's visible extra premises would miss this.
The proof-only import graph has 3,262 project modules including its root,
and 14 classification modules. Importing a module does not establish that
any of its declarations is reached from either root.

## Interpretation

The closure includes the published arbitrary-Levi normalized-induction
finite-length theorem
`Langlands.Classification.normalizedInductionFiniteLength`, the GL
Jacquet-length helper `Langlands.Parabolic.normalizedJacquetFiniteLength`,
and the actual supercuspidal-product embedding and finite-length theorems
`Langlands.Classification.irreducibleProductEmbedding` and
`Langlands.Classification.irreducibleProductFiniteLength`. These dependencies
come through the actual matrix operator and its finite-length packages.
The comparison transports those packages and does not remove their
representation-theoretic dependencies.

The paired accounts of
[NormalizedProductFiniteLengthProof](../../Langlands/Representation/Classification/NormalizedProductFiniteLengthProof.md),
[IrreducibleProductFiniteLengthProof](../../Langlands/Representation/Classification/IrreducibleProductFiniteLengthProof.md),
[IrreducibleProductEmbedding](../../Langlands/Representation/Classification/IrreducibleProductEmbedding.md)
and [FiniteLengthProof](../../Langlands/Representation/Classification/FiniteLengthProof.md)
describe the actual finite-length, cuspidal-embedding and Jacquet arguments.
Membership in the classification directory alone is not evidence that a
Langlands quotient theorem is used. The complete directory-provenance
inventory below reaches finite-length and supercuspidal helpers, but no
segment-classification declaration or full Langlands-quotient classification
theorem. It supports that precise distinction, not a blanket claim that the
GL comparison is independent of representation theory or eligible for an
upstream consumer's route restrictions.

A separate name check found 55 reached constants with `classif` in their
names outside classification modules. Their modules concern group schemes,
coordinate/topology constructions and the geometric-lemma orbit
representatives. The orbit names are
`Langlands.Geometric.OrderedDoubleCosets.classifiedRepresentatives` and its
two generated proof helpers. These names do not denote representation
classification theorems. Module provenance and the explicit inventory are
used instead of treating a name substring as a dependency verdict.

## Complete classification-module declaration inventory

The following 67 names include private and generated constants. “Theorem”
refers to Lean's theorem constant kind; “Other” includes definitions and
compiler-generated auxiliary definitions. A declaration is counted once,
regardless of how many paths reach it. The same list applies to both roots.

### [FiniteLengthProof](../../Langlands/Representation/Classification/FiniteLengthProof.lean)

| Exact Lean declaration | Kind |
| --- | --- |
| `Langlands.FiniteLengthAssembly.complementaryProjection` | Other |
| `Langlands.FiniteLengthAssembly.complementaryProjection._proof_1` | Theorem |
| `Langlands.FiniteLengthAssembly.complementaryProjection._proof_2` | Theorem |
| `Langlands.FiniteLengthAssembly.complementaryProjection_surjective` | Theorem |
| `Langlands.FiniteLengthAssembly.finiteLength_comp_surjective_iff` | Theorem |
| `Langlands.FiniteLengthAssembly.finiteLength_normalizedJacquet_of_refinements` | Theorem |
| `Langlands.FiniteLengthAssembly.finiteLength_of_complement` | Theorem |
| `Langlands.FiniteLengthAssembly.finiteLength_of_complement._simp_1_2` | Theorem |
| `Langlands.FiniteLengthAssembly.finiteLength_of_complement._simp_1_3` | Theorem |
| `Langlands.FiniteLengthAssembly.finiteLength_of_injective` | Theorem |
| `Langlands.FiniteLengthAssembly.finiteLength_of_refinedJacquet` | Theorem |
| `Langlands.FiniteLengthAssembly.finiteLength_of_surjective` | Theorem |
| `Langlands.FiniteLengthAssembly.finite_of_surjective` | Theorem |
| `Langlands.FiniteLengthAssembly.finite_summand` | Theorem |
| `Langlands.FiniteLengthAssembly.isAdmissible_levi_subrepresentation` | Theorem |
| `Langlands.FiniteLengthAssembly.isAdmissible_normalizedJacquet` | Theorem |
| `Langlands.FiniteLengthAssembly.length_comp_surjective` | Theorem |
| `Langlands.FiniteLengthAssembly.length_eq_add_of_complement` | Theorem |
| `Langlands.FiniteLengthAssembly.normalizedJacquet_eq_twist` | Theorem |
| `Langlands.FiniteLengthAssembly.refinedJacquetMap_surjective` | Theorem |
| `Langlands.FiniteLengthAssembly.refinement_measure_lt` | Theorem |
| `Langlands.FiniteLengthAssembly.refinement_measure_lt._proof_1_1` | Theorem |
| `Langlands.Parabolic.normalizedJacquetFiniteLength` | Theorem |

### [IrreducibleProductEmbedding](../../Langlands/Representation/Classification/IrreducibleProductEmbedding.lean)

| Exact Lean declaration | Kind |
| --- | --- |
| `Langlands.Classification.irreducibleProductEmbedding` | Theorem |
| `Langlands.Classification.irreducibleProduct_embedding` | Theorem |
| `Langlands.Classification.irreducible_supercuspidalProduct_embedding` | Theorem |
| `Langlands.Classification.normalizedProduct_embedding_of_factor_embeddings` | Theorem |
| `Langlands.FiniteTensor.externalMap_injective` | Theorem |

### [IrreducibleProductEmbeddingStatement](../../Langlands/Representation/Classification/IrreducibleProductEmbeddingStatement.lean)

| Exact Lean declaration | Kind |
| --- | --- |
| `Langlands.Classification.IrreducibleProductEmbeddingTheorem` | Other |

### [IrreducibleProductFiniteLengthProof](../../Langlands/Representation/Classification/IrreducibleProductFiniteLengthProof.lean)

| Exact Lean declaration | Kind |
| --- | --- |
| `Langlands.Classification.irreducibleProductFiniteLength` | Theorem |
| `_private.Langlands.Representation.Classification.IrreducibleProductFiniteLengthProof.0.Langlands.Classification.flattenSupercuspidalFactors` | Other |
| `_private.Langlands.Representation.Classification.IrreducibleProductFiniteLengthProof.0.Langlands.Classification.flattenSupercuspidalFactors_obj` | Theorem |

### [NormalizedProductFiniteLengthProof](../../Langlands/Representation/Classification/NormalizedProductFiniteLengthProof.lean)

| Exact Lean declaration | Kind |
| --- | --- |
| `Langlands.Classification.ProductLengthProof.finiteLength_of_injective` | Theorem |
| `Langlands.Classification.ProductLengthProof.finiteLength_of_range_eq_ker` | Theorem |
| `Langlands.Classification.ProductLengthProof.finiteLength_of_surjective` | Theorem |
| `Langlands.Classification.ProductLengthProof.irreducibleLevi` | Theorem |
| `Langlands.Classification.ProductLengthProof.leviPreservation` | Theorem |
| `Langlands.Classification.ProductLengthProof.step` | Theorem |
| `Langlands.Classification.normalizedInductionFiniteLength` | Theorem |

### [NormalizedProductFiniteLengthStatement](../../Langlands/Representation/Classification/NormalizedProductFiniteLengthStatement.lean)

| Exact Lean declaration | Kind |
| --- | --- |
| `Langlands.Classification.IrreducibleProductFiniteLength` | Other |

### [Supercuspidal](../../Langlands/Representation/Classification/Supercuspidal.lean)

| Exact Lean declaration | Kind |
| --- | --- |
| `Langlands.GeneralLinear.BlockShape.conjugateUnipotent` | Other |
| `Langlands.GeneralLinear.IsSupercuspidal` | Other |
| `Langlands.GeneralLinear.SupercuspidalRep` | Other |
| `Langlands.GeneralLinear.isSupercuspidal_of_equiv` | Theorem |
| `Langlands.GeneralLinear.supercuspidalProperty` | Other |
| `Langlands.Jacquet.coinvariantsEquiv` | Other |
| `Langlands.Jacquet.coinvariantsEquiv._proof_1` | Theorem |
| `Langlands.Jacquet.coinvariantsEquiv._proof_2` | Theorem |
| `Langlands.Jacquet.coinvariantsEquiv._proof_3` | Theorem |
| `Langlands.Jacquet.coinvariantsEquiv._proof_4` | Theorem |
| `Langlands.Jacquet.coinvariants_subsingleton_iff` | Theorem |

### [SupercuspidalContragredientAux](../../Langlands/Representation/Classification/SupercuspidalContragredientAux.lean)

| Exact Lean declaration | Kind |
| --- | --- |
| `Langlands.GeneralLinear.isSupercuspidal_iff_standard` | Theorem |
| `Langlands.Jacquet.coinvariantsConjEquiv` | Other |
| `Langlands.Jacquet.coinvariantsConjEquiv._proof_1` | Theorem |
| `Langlands.Jacquet.coinvariantsConjEquiv._proof_2` | Theorem |
| `Langlands.Jacquet.coinvariantsConjEquiv._proof_3` | Theorem |
| `Langlands.Jacquet.coinvariantsConjEquiv._proof_4` | Theorem |
| `Langlands.Jacquet.coinvariantsConjEquiv._proof_5` | Theorem |
| `Langlands.Jacquet.coinvariantsConjEquiv._proof_6` | Theorem |
| `Langlands.Jacquet.coinvariants_conj_subsingleton_iff` | Theorem |
| `Langlands.isIrreducible_iff_of_equiv` | Theorem |

### [SupercuspidalSupport](../../Langlands/Representation/Classification/SupercuspidalSupport.lean)

| Exact Lean declaration | Kind |
| --- | --- |
| `Langlands.SmoothRep.IsSubquotient.of_iso_right` | Theorem |
| `Langlands.SmoothRep.hom_hom_injective` | Theorem |
| `Langlands.SmoothRep.hom_hom_surjective` | Theorem |
| `Langlands.SmoothRep.isSubquotient_iff_exists` | Theorem |
| `Langlands.SmoothRep.isSubquotient_iff_exists.match_1_1` | Other |

### [SupercuspidalTwist](../../Langlands/Representation/Classification/SupercuspidalTwist.lean)

| Exact Lean declaration | Kind |
| --- | --- |
| `Langlands.GeneralLinear.BlockShape.determinant_eq_one_of_mem_unipotentSubgroup` | Theorem |

## Classification modules imported without reached declarations

The following four modules belong to the proof's recursive import graph,
but neither root reaches a constant defined in them:

- `Langlands.Representation.Classification.ConstituentRelations`.
- `Langlands.Representation.Classification.FiniteLengthStatement`.
- `Langlands.Representation.Classification.Segments`.
- `Langlands.Representation.Classification.SupercuspidalContragredientStatement`.

These import-only modules cannot be promoted to theorem dependencies merely
because their files were loaded. Conversely, the 67 reached constants above
remain dependencies even though the comparison theorem has no additional
finite-length parameter. The whole-graded-ring Aubert–Zelevinsky theorem
has its separate, larger classification inventory linked from the matrix.
